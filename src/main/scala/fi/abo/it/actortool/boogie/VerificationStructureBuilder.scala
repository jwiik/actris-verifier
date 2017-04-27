package fi.abo.it.actortool.boogie

import fi.abo.it.actortool._ 
import scala.collection.mutable.ListBuffer
import Elements._

trait VerificationStructureBuilder[T <: DFActor, V <: VerificationStructure[T]] {
  def buildStructure(entity: T): V
  
  protected def createUniquenessCondition(names: List[BDecl]): List[Boogie.Expr] = {
    names match {
      case first::rest => {
        val conditions = rest flatMap { 
          c => if (first.decl.x.t == c.decl.x.t) List(Boogie.VarExpr(first.name) !=@ Boogie.VarExpr(c.name)) else Nil
        }
        conditions:::createUniquenessCondition(rest)
      }
      case Nil => Nil
    }
  }
  
  protected def buildPriorityMap(actor: DFActor): Map[AbstractAction,List[AbstractAction]] = {
    if (actor.isNetwork) {
      return (actor.contractActions map { a => (a,Nil: List[AbstractAction]) }).toMap
    }
    
    var orderedActions: Map[AbstractAction,List[AbstractAction]] = (actor.actorActions filter { a => !a.init } map {a => (a,Nil: List[AbstractAction])}).toMap
    
    actor.priority match {
      case Some(pr) => {
        for ((a1,a2) <- pr.orders) {
          // Assuming valid label
          val act1 = actor.actorActions.find{ a => a.fullName == a1.id }.get
          val act2 = actor.actorActions.find{ a => a.fullName == a2.id }.get
          // act1 is the higher prio action. We now add act1 as a higher prio action to act2
          val current = act1 :: orderedActions(act2)
          orderedActions = orderedActions + (act2 -> current)
        }
      }
      case None =>
    }
    orderedActions
  }
  
}

class ActorVerificationStructureBuilder(val typeCtx: Resolver.Context) 
         extends VerificationStructureBuilder[BasicActor, ActorVerificationStructure] {
  
  def buildStructure(actor: BasicActor): ActorVerificationStructure = {
    val prefix = actor.id+B.Sep
    
    val stateChanRenamings = (actor.variables map { p => (p.id, Id("Ch" + B.Sep + p.id)) } ).toMap
    
    val portChans = (actor.inports ::: actor.outports) map { p => BDecl(p.id, ChanType(p.portType)) }
    val stateChans = (actor.variables map { p => BDecl(stateChanRenamings(p.id).id, ChanType(p.typ)) } )
    val chans = portChans ::: stateChans

    val uniquenessConiditions = createUniquenessCondition(portChans)
    val uniquenessCondition = 
      if (!uniquenessConiditions.isEmpty) uniquenessConiditions.reduceLeft((a,b) => (a && b))
      else B.Bool(true)

    val actorVars = new ListBuffer[BDecl]()
    
    for (decl <- actor.variables) {
      val newName = decl.id
      actorVars  += BDecl(newName,decl.typ)
    }
    
    val actorParamDecls = actor.parameters map {p => BDecl(p.id,p.typ)}
    
    val basicAssumes =
      (actor.inports:::actor.outports map { p => B.Assume(B.Int(0) <= B.I(p.id) && B.I(p.id) <= B.R(p.id) && B.R(p.id) <= B.C(p.id)) }) :::
      (actor.variables map { p => B.Assume(B.Int(0) <= B.R(stateChanRenamings(p.id).id) && B.C(stateChanRenamings(p.id).id) ==@ B.R(stateChanRenamings(p.id).id) + B.Int(1)) })

      
    val initAssumes = 
      (actor.inports:::actor.outports map { p => B.Assume(B.I(p.id) ==@ B.Int(0) && B.R(p.id) ==@ B.Int(0) && B.C(p.id) ==@ B.Int(0)) }) :::
      (actor.variables map { p => B.Assume(B.R(stateChanRenamings(p.id).id) ==@ B.Int(0) && B.C(stateChanRenamings(p.id).id) ==@ B.Int(0))  })

    val priorityList = buildPriorityMap(actor)
    
    val funDeclRenamings = (actor.getFunctionDecls map { fd => (fd.name,Id(prefix+fd.name)) }).toMap
    
    return new ActorVerificationStructure(
        actor,
        actor.actorActions,
        actor.contractActions,
        actor.inports,
        actor.outports,
        actor.actorInvariants,
        actor.getFunctionDecls,
        portChans:::stateChans,
        actorVars.toList,
        actorParamDecls,
        uniquenessCondition,
        priorityList,
        basicAssumes,
        initAssumes,
        funDeclRenamings,
        stateChanRenamings,
        prefix)
  }
  
  
  
}

class NetworkVerificationStructureBuilder(val typeCtx: Resolver.Context) 
         extends VerificationStructureBuilder[Network, NetworkVerificationStructure] {
  
  val tokensFinder = new TokensFinder()
  
  def buildStructure(network: Network): NetworkVerificationStructure = {
    val actions = network.contractActions
    val userNwInvariants = network.actorInvariants
    val chInvariants = network.channelInvariants
    val connections = network.structure.get.connections
    val entities = network.entities.get.entities
    
    val namePrefix = network.id+B.Sep
    
    val buffer = new ListBuffer[(String,Id)]
    
    val chanDecls = new ListBuffer[BDecl]
    for (c <- connections) {
      buffer += ((c.id,makeId(namePrefix+c.id,c.typ)))
      chanDecls += BDecl(namePrefix+c.id,c.typ)
    }
    
    val explicitTokensAsserts = (tokensFinder.visit(userNwInvariants) ::: tokensFinder.visit(chInvariants)).toSet
    val implicitTokensChs = connections.filter { c => !explicitTokensAsserts.contains(c.id)  }
    val implicitTokensAsserts = implicitTokensChs map { c =>
      val predicate = FunctionApp("tokens",List(makeId(c.id,c.typ),IntLiteral(0)))
      Resolver.resolveExpr(predicate, typeCtx) match {
        case Resolver.Success(_) =>
        case Resolver.Errors(errs) => assert(false,errs)
      }
      assert(predicate.typ != null)
      ActorInvariant(Assertion(predicate,false,Some("Unread tokens might be left on channel " + c.id)),true,false)
    }
    val nwInvariants = userNwInvariants ::: implicitTokensAsserts
    
    // Add input/output port names as synonyms to the connected channels
    for (ip <- network.inports) {
      val ch = network.structure.get.getInputChannel(ip.id)
      ch match {
        case Some(c) => buffer += ((ip.id,makeId(namePrefix+c.id,c.typ)))
        case None =>
      }
    }
    for (op <- network.outports) {
      val ch = network.structure.get.getOutputChannel(op.id)
      ch match {
        case Some(c) => buffer += ((op.id,makeId(namePrefix+c.id,c.typ)))
        case None =>
      }
    }
    
    val (sourceMap,targetMap) = {
      val tempRenamings = buffer.toMap
      val source = scala.collection.mutable.HashMap.empty[PortRef,String]
      val target = scala.collection.mutable.HashMap.empty[PortRef,String]
      for (c <- connections) {
        source(c.from) = tempRenamings(c.id).id
        target(c.to) = tempRenamings(c.id).id
      }
      (source.toMap,target.toMap)
    }
    


    val subactorVarDecls = new ListBuffer[BDecl]
    val entityDecls = new ListBuffer[BDecl]
    val entityDataBuffer = new ListBuffer[(Instance,EntityData)]
    
    for (e <- entities) {
      val variables = new ListBuffer[String]
      val renameBuffer = new ListBuffer[(String,Expr)]
      val actor = e.actor
      
      val parameterArguments = actor.parameters.zip(e.arguments).map{ case (d,e) => (d.id,e) }.toMap
      
      buffer += ((e.id,makeId(namePrefix+e.id,ActorType(e.actor))))
     
      for (p <- actor.inports) {
        val newName = targetMap(PortRef(Some(e.id),p.id))
        renameBuffer += ((p.id,makeId(newName,ChanType(p.portType))))
      }
      
      for (p <- actor.outports) {
        val newName = sourceMap(PortRef(Some(e.id),p.id))
        renameBuffer += ((p.id,makeId(newName,ChanType(p.portType))))
      }
      
      for (p <- actor.parameters) {
        //val newName = "AP"+B.Sep+e.id+B.Sep+p.id
        //subactorVarDecls += BDecl(newName,p.typ)
        renameBuffer += ((p.id,parameterArguments(p.id)))
      }
      
      for (v <- actor.variables) {
        val newName = "AV"+B.Sep+e.id+B.Sep+v.id
        subactorVarDecls += BDecl(newName,v.typ)
        variables += newName
        renameBuffer += ((v.id,makeId(newName,v.typ)))
      }
      
      val actionData = (actor.actorActions map { a => (a,collectEntityData(e,a,targetMap)) }).toMap
      val priorityMap = buildPriorityMap(actor)

      
      val entityData = new EntityData(Nil,renameBuffer.toMap,variables.toList, actionData, priorityMap)
      //entitySpecificVariables += variables.toList
      //entitySpecificRenames += renameBuffer.toMap
      entityDataBuffer += ((e,entityData))
      entityDecls += BDecl(namePrefix+e.id, ActorType(e.actor))
      
    }
    val entityData = entityDataBuffer.toMap
    
    val tempRenames = buffer.toMap
    
    val networkRenamings = buffer.toMap
    val publicInvs = 
      entities flatMap { 
        entity => {
          for (inv <- entity.actor.streamInvariants) yield {
            val renamings = networkRenamings ++ entityData(entity).renamings
            (inv,renamings)
          }
        }
      }
    
    val chanDeclList = chanDecls.toList
    val entityDeclList = entityDecls.toList
    
    val uniquenessConidition1 = 
      if (entityDeclList.size > 1) List(createUniquenessCondition(entityDeclList).reduceLeft((a,b) => (a && b)))
      else Nil

    val uniquenessConidition2 = {
      val condition = createUniquenessCondition(chanDeclList)
      if (condition.size > 1) List(condition.reduceLeft((a,b) => (a && b)))
      else Nil
    }
    val uniquenessConditions = uniquenessConidition1 ::: uniquenessConidition2
    
    val actionRatePreds = 
      (for (a <- network.contractActions) yield {
        val predicates = 
          (network.inports map { ip => B.B(networkRenamings(ip.id).id) ==@ B.Int(a.inportRate(ip.id)) }) :::
          (network.outports map { op => B.B(networkRenamings(op.id).id) ==@ B.Int(a.outportRate(op.id)) })
        (a,predicates.reduceLeft((a,b) => (a && b)))
      }).toMap
    
    
    val actionRateDisjunction = if (actionRatePreds.isEmpty) B.Bool(true) else actionRatePreds.values.reduceLeft((a,b) => (a || b))
      
    val basicAssumes =
      (for (c <- connections) yield {
        val name = tempRenames(c.id)
        val list1 = List(
          B.Int(0) <= B.I(name.id),
          B.I(name.id) <= B.R(name.id),
          B.R(name.id) <= B.C(name.id))
        val list2 = (if (c.isOutput) List(B.I(name.id) ==@ B.R(name.id)) else Nil)
        (list1 ::: list2).map(x => B.Assume(x))
      }).flatten ::: List(B.Assume(actionRateDisjunction))
      
    new NetworkVerificationStructure(
        network, 
        actions, 
        nwInvariants, 
        chInvariants,
        publicInvs,
        connections, 
        entities, 
        sourceMap, 
        targetMap, 
        networkRenamings, 
        entityData,
        entityDeclList:::chanDeclList,
        subactorVarDecls.toList,
        uniquenessConditions,
        actionRatePreds,
        basicAssumes,
        namePrefix)
  }
  
  def collectEntityData(instance: Instance, action: ActorAction, targetMap: Map[PortRef, String]) = {
    val actor = instance.actor
    val vars = new ListBuffer[BDecl]()
    
    val replacements = scala.collection.mutable.HashMap.empty[Id,Expr]
    
    for (ipat <- action.inputPattern) {
      val cId = targetMap(PortRef(Some(instance.id),ipat.portId))      
      for ((v,ind) <- ipat.vars.zipWithIndex) {
        val c = Elements.ch(cId,v.typ)
        val index = 
          if (ind == 0) Elements.rd(c.id,c.typ.asInstanceOf[ChanType]) 
          else Minus(Elements.rd(c.id,c.typ.asInstanceOf[ChanType]),IntLiteral(ind))
        val acc = Elements.chAcc(c,index)
        replacements += (v -> acc)
      }
    }
    
    val patternVarRenamings: Map[String,Id] = 
      if (instance.actor.isNetwork) Map.empty
      else {
        (for (ipat <- action.inputPattern) yield {
          for (v <- ipat.vars) yield {
            val inVar = ipat.portId + B.Sep + v.id
            vars += BDecl(inVar,B.Local(inVar,B.type2BType(v.typ)))
            (v.id,makeId(inVar,v.typ))
          }
        }).flatten.toMap
      }
    
    val assignedVars = action.body flatMap { a => a match {
      case Assign(x,_) => {
        x match {
          case id: Id => List(id)
          //case fa: FieldAccessor => List(fa)
          case _ => assert(false); Nil
        }
      }
      case _ => Nil
    }}
    
    new ActionData(vars.toList, patternVarRenamings, replacements.toMap, assignedVars.toSet)

  }
  
  class TokensFinder {
    
    def visit(invs: List[Invariant]): List[String] = invs.flatMap { x => visit(x.expr) }
    
    def visit(expr: Expr): List[String] =
      expr match {
        case And(left,right) => visit(left) ::: visit(right)
        case FunctionApp("tokens",params) => List(params(0).asInstanceOf[Id].id)
        case _ => Nil
      }
    
  }
  
}
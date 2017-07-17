package fi.abo.it.actortool.boogie

import fi.abo.it.actortool._
import fi.abo.it.actortool.util.PriorityMapBuilder
import scala.collection.mutable.ListBuffer
import Elements._
import fi.abo.it.actortool.util.ConnectionMap

trait VerificationStructureBuilder[T <: DFActor, V <: VerificationStructure[T]] {
  
  val translator: StmtExpTranslator
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
  
  protected def createVariableDeclarations(entity: T): (List[BDecl],List[Boogie.Expr]) = {
    val decls = new ListBuffer[BDecl]
    val assumes = new ListBuffer[Boogie.Expr]
    
    for ((s,i) <- entity.contractActions.zipWithIndex) {
      val decl = BDecl(s.fullName, IntType)
      decls += decl
      assumes += Boogie.VarExpr(s.fullName) ==@ B.Int(i)
    }
    
    if (!entity.contractActions.isEmpty) {
      assumes += entity.contractActions map { s => B.Mode(B.This) ==@ Boogie.VarExpr(s.fullName) } reduceLeft((a,b) => a || b)
    }
    
    
    entity match {
      case ba: BasicActor => 
        val (vDecls,vAssumes) = createVariableDeclarations(ba.variables,Map.empty)
        decls ++= vDecls
        assumes ++= vAssumes
      case nw: Network =>
    }
    
    (decls.toList,assumes.toList)
  }
  
  protected def createVariableDeclarations(varDecls: List[Declaration], renamings: Map[String,Id]): (List[BDecl],List[Boogie.Expr]) = {
    val decls = new ListBuffer[BDecl]
    val assumes = new ListBuffer[Boogie.Expr]
    for (d <- varDecls) {
      decls += BDecl(d.id,d.typ)
      if (d.constant) assumes += Boogie.VarExpr(d.id) ==@ translator.transExpr(d.value.get, TranslatorContext(renamings, false))
    }
    (decls.toList,assumes.toList)
  }
  
  protected def createVariableDeclarationsNoTranslate(varDecls: List[Declaration], typeCtx: Resolver.Context): (List[BDecl],List[Expr]) = {
    val decls = new ListBuffer[BDecl]
    val assumes = new ListBuffer[Expr]
    for (d <- varDecls) {
      decls += BDecl(d.id,d.typ)
      
      if (d.constant){
        val id = Id(d.id)
        id.typ = d.typ
        val exp = Eq(id, d.value.get)
        exp.typ = BoolType
        assumes += exp
      }
    }
    (decls.toList,assumes.toList)
  }
  
  protected def buildPriorityMap(actor: DFActor, subComponent: Boolean, alwaysUseContracts: Boolean) = 
    PriorityMapBuilder.buildPriorityMap(actor, subComponent, alwaysUseContracts)
  
}


class ActorVerificationStructureBuilder(val translator: StmtExpTranslator, val typeCtx: Resolver.Context, alwaysUseContracts: Boolean) 
         extends VerificationStructureBuilder[BasicActor, ActorVerificationStructure] {
  
         
  def buildStructure(actor: BasicActor): ActorVerificationStructure = {
    val prefix = actor.id+B.Sep
    val decls = new ListBuffer[BDecl]
    val commonAssumes = new ListBuffer[Boogie.Assume]
    
    
    
    val portChans = (actor.inports ::: actor.outports) map { p => BDecl(p.id, ChanType(p.portType)) }
    decls ++= portChans
    
    val stateChanRenamings = actor.variables.map{ p => (p.id, Id(p.id + B.Sep + "ch").withType(p.typ) ) }.toMap
    val stateChans = actor.variables map { 
      p => BDecl(stateChanRenamings(p.id).id, ChanType(p.typ)) 
      
    }
    decls ++= stateChans
    
    //val chans = portChans //::: stateChans
    
    val uniquenessConiditions = createUniquenessCondition(portChans ::: stateChans)
    val uniquenessCondition = 
      if (!uniquenessConiditions.isEmpty) uniquenessConiditions.reduceLeft((a,b) => (a && b))
      else B.Bool(true)

    val (varDecls,varAssumes) = createVariableDeclarations(actor)
    decls ++= varDecls
    commonAssumes ++= varAssumes map { B.Assume(_) }
    
    val actorParamDecls = actor.parameters map {p => BDecl(p.id,p.typ)}
    
    val basicAssumes =
      (commonAssumes.toList) :::
      (actor.inports:::actor.outports map { p => B.Assume(B.Int(0) <= B.I(p.id) && B.I(p.id) <= B.R(p.id) && B.R(p.id) <= B.C(p.id)) }):::
      (stateChans map { bd => B.Assume(B.Int(0) <= B.I(bd.name) && B.I(bd.name) <= B.R(bd.name) && (B.R(bd.name) + B.Int(1)) ==@ B.C(bd.name)) })
        
    val initAssumes = 
      (commonAssumes.toList) :::
      (actor.inports:::actor.outports map { p => B.Assume(B.I(p.id) ==@ B.Int(0) && B.R(p.id) ==@ B.Int(0) && B.C(p.id) ==@ B.Int(0)) }):::
      (stateChans map { bd => B.Assume(B.I(bd.name) ==@ B.Int(0) && B.R(bd.name) ==@ B.Int(0) && B.C(bd.name) ==@ B.Int(0)) })

    val priorityList = buildPriorityMap(actor, false, alwaysUseContracts)
    
    val funDeclRenamings = (actor.functionDecls map { fd => (fd.name,Id(prefix+fd.name)) }).toMap
    
    val aData = 
      (for (a <- actor.actorActions) yield {
        val (decls,initialValues) = createVariableDeclarationsNoTranslate(a.variables,typeCtx)
        val assignedVars = AssignedVarsFinder.find(a.body)
        (a,new ActionData(decls,Map.empty,Map.empty,assignedVars,initialValues))
      }).toMap
    
    return new ActorVerificationStructure(
        actor,
        actor.actorActions,
        actor.contractActions,
        actor.inports,
        actor.outports,
        actor.actorInvariants,
        actor.functionDecls,
        decls.toList,
        actorParamDecls,
        uniquenessCondition,
        priorityList,
        basicAssumes,
        initAssumes,
        funDeclRenamings,
        stateChanRenamings, // state chan renamings
        aData,
        prefix)
  }
  
  
  
}

class NetworkVerificationStructureBuilder(val translator: StmtExpTranslator, val typeCtx: Resolver.Context, alwaysUseContracts: Boolean) 
         extends VerificationStructureBuilder[Network, NetworkVerificationStructure] {
  
  val tokensFinder = new TokensFinder()
  
  def buildStructure(network: Network): NetworkVerificationStructure = {
    val actions = network.contractActions
    val userNwInvariants = network.actorInvariants
    val chInvariants = network.channelInvariants
    val connections = network.structure.get.connections
    val entities = network.entities.get.entities
    
    val contractModeDecls = new ListBuffer[BDecl]
    val contractModeAssumes = new ListBuffer[Boogie.Assume]
    
    val namePrefix = network.id+B.Sep
    
    val buffer = new ListBuffer[(String,Id)]
    
    val chanDecls = new ListBuffer[BDecl]
    for (c <- connections) {
      buffer += ((c.id,makeId(namePrefix+c.id,c.typ)))
      chanDecls += BDecl(namePrefix+c.id,c.typ)
    }
    
    val (varDecls,varAssumes) = createVariableDeclarations(network)
    contractModeDecls ++= varDecls
    contractModeAssumes ++= varAssumes map { B.Assume(_) }
    
    val explicitTokensAsserts = (tokensFinder.visit(userNwInvariants) ::: tokensFinder.visit(chInvariants)).toSet
    val implicitTokensChs = connections.filter { c => !explicitTokensAsserts.contains(c.id)  }
    val implicitTokensAsserts = implicitTokensChs map { c =>
      val predicate = FunctionApp("tokens",List(Id(c.id).withType(c.typ) ,IntLiteral(0)))
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
    
    val connMap = ConnectionMap.build(connections, buffer.toMap)
    
    val subactorVarDecls = new ListBuffer[BDecl]
    val entityDecls = new ListBuffer[BDecl]
    val entityDataBuffer = new ListBuffer[(Instance,EntityData)]
    
    for (e <- entities) {
      val variables = new ListBuffer[String]
      val renameBuffer = new ListBuffer[(String,Expr)]
      val actor = e.actor
      
      val parameterArguments = actor.parameters.zip(e.arguments).map{ case (d,e) => (d.id,e) }.toMap
      
      buffer += ((e.id,makeId(namePrefix+e.id,ActorType(actor))))
     
      for (p <- actor.inports) {
        val newName = connMap.getDst(e.id,p.id)
        renameBuffer += ((p.id,makeId(newName,ChanType(p.portType))))
      }
      
      for (p <- actor.outports) {
        val newName = connMap.getSrc(PortRef(Some(e.id),p.id))
        renameBuffer += ((p.id,makeId(newName,ChanType(p.portType))))
      }
      
      for (p <- actor.parameters) {
        //val newName = "AP"+B.Sep+e.id+B.Sep+p.id
        //subactorVarDecls += BDecl(newName,p.typ)
        renameBuffer += ((p.id,parameterArguments(p.id)))
      }
      
      
      val actionData = (actor.actorActions map { a => (a,collectEntityData(e,a,connMap)) }).toMap
      val priorityMap = buildPriorityMap(actor,true,alwaysUseContracts)

      
      val entityData = new EntityData(Nil,renameBuffer.toMap,variables.toList, actionData, priorityMap)
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
        connMap, 
        networkRenamings, 
        entityData,
        entityDeclList:::chanDeclList:::contractModeDecls.toList,
        subactorVarDecls.toList,
        uniquenessConditions,
        actionRatePreds,
        basicAssumes:::contractModeAssumes.toList,
        namePrefix)
  }
  
  def collectEntityData(instance: Instance, action: ActorAction, connMap: ConnectionMap) = {
    val actor = instance.actor
    val vars = new ListBuffer[BDecl]()
    
    val replacements = scala.collection.mutable.HashMap.empty[Id,Expr]
    
    for (ipat <- action.inputPattern) {
      val cId = connMap.getDst(instance.id,ipat.portId)      
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
        ((for (ipat <- action.inputPattern) yield {
          for (v <- ipat.vars) yield {
            val inVar = instance.id + B.Sep + ipat.portId + B.Sep + v.id
            vars += BDecl(inVar,B.Local(inVar,B.type2BType(v.typ)))
            (v.id,makeId(inVar,v.typ))
          }
        }).flatten :::
        (action.variables.map { 
          v => {
            val actionVar = instance.id + B.Sep + action.fullName + B.Sep + v.id
            vars += BDecl(actionVar,B.Local(actionVar,B.type2BType(v.typ)))
            (v.id,makeId(actionVar,v.typ))
          }
        })
        ).toMap
      }
    
    val assignedVars = AssignedVarsFinder.find(action.body)
    new ActionData(vars.toList, patternVarRenamings, replacements.toMap, assignedVars.toSet,List.empty)

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
package fi.abo.it.actortool.boogie

import fi.abo.it.actortool._ 
import scala.collection.mutable.ListBuffer

trait VerificationStructureBuilder[T <: DFActor, V <: VerificationStructure[T]] {
  def buildStructure(entity: T): V
  
  protected def createUniquenessCondition(names: List[BDecl]): List[Boogie.Expr] = {
    names match {
      case first::rest => {
        val conditions = rest flatMap { 
          c => if (first.decl.x.t == c.decl.x.t) List(Boogie.VarExpr(first.name) !=@ Boogie.VarExpr(c.name)) else Nil
        }
//        val conditions = for (c <- rest) yield {
//          Boogie.VarExpr(first.name) !=@ Boogie.VarExpr(c.name)
//        }
        conditions:::createUniquenessCondition(rest)
      }
      case Nil => Nil
    }
  }
}

class ActorVerificationStructureBuilder(implicit val bvMode: Boolean) 
         extends VerificationStructureBuilder[BasicActor, ActorVerificationStructure] {
  
  def buildStructure(actor: BasicActor): ActorVerificationStructure = {
    
    val prefix = actor.id+B.Sep
        
    val portChans = (actor.inports ::: actor.outports) map { p => BDecl(p.id, ChanType(p.portType)) }
    val uniquenessConidition = createUniquenessCondition(portChans).reduceLeft((a,b) => (a && b))
    
//    val portChans = 
//      ((for (p <- actor.inports) yield BDecl(p.id, ChanType(p.portType)))
//      :::
//      (for (p <- actor.outports) yield BDecl(p.id, ChanType(p.portType))))
            
    val actorVars = new ListBuffer[BDecl]()
    
    val states = actor.schedule match {
      case Some(s) => 
        actorVars += BDecl("this#", B.ThisDecl)
        s.states
      case None => Nil
    }
    
    val bActorStates = for (s <- states) yield {
      //actorVars += bLocal(currentState,BType.State)
      Boogie.Const(prefix+s,true,BType.State)
    }
    
    val allowedStatesInvariant = 
      if (!states.isEmpty) {
        Some((for (s <- states) yield {
          B.This ==@ Boogie.VarExpr(prefix+s)
        }).reduceLeft((a,b) => (a || b)))
      }
      else None
    
    
    //val oldAssigns = new ListBuffer[Boogie.Assign]()
    for (decl <- actor.variables) {
      val newName = decl.id
      actorVars  += BDecl(newName,decl.typ)
    }
    
    val actorParamDecls = actor.parameters map {p => BDecl(p.id,p.typ)}
    
    val basicAssumes =
      (actor.inports map { p => B.Assume(B.Int(0) <= B.R(p.id)) }) :::
      (actor.outports map { p => B.Assume(B.Int(0) <= B.C(p.id)) })
    
    val initAssumes = 
      (actor.inports map { p => B.Assume(B.R(p.id) ==@ B.Int(0)) }) :::
      (actor.outports map { p => B.Assume(B.C(p.id) ==@ B.Int(0)) })
    
      
    return new ActorVerificationStructure(
        actor,
        actor.actions,
        actor.inports,
        actor.outports,
        actor.actorInvariants,
        portChans,
        actorVars.toList,
        actorParamDecls,
        uniquenessConidition,
        actor.schedule,
        states,
        bActorStates,
        allowedStatesInvariant,
        basicAssumes,
        initAssumes,
        prefix)
  }
  
  
  
}

class NetworkVerificationStructureBuilder(implicit val bvMode: Boolean) 
         extends VerificationStructureBuilder[Network, NetworkVerificationStructure] {
  
  def buildStructure(network: Network): NetworkVerificationStructure = {
    val actions = network.actions
    val nwInvariants = network.actorInvariants
    val chInvariants = network.channelInvariants
    val connections = network.structure.get.connections
    val entities = network.entities.get.entities
    
    val namePrefix = network.id+B.Sep
    
    val buffer = new ListBuffer[(String,String)]
    
    val chanDecls = new ListBuffer[BDecl]
    for (c <- connections) {
      buffer += ((c.id,namePrefix+c.id))
      chanDecls += BDecl(namePrefix+c.id,ChanType(c.typ))
    }
    
    // Add input/output port names as synonyms to the connected channels
    for (ip <- network.inports) {
      val ch = network.structure.get.getInputChannel(ip.id)
      ch match {
        case Some(c) => buffer += ((ip.id,namePrefix+c.id))
        case None =>
      }
    }
    for (op <- network.outports) {
      val ch = network.structure.get.getOutputChannel(op.id)
      ch match {
        case Some(c) => buffer += ((op.id,namePrefix+c.id))
        case None =>
      }
    }
    
    val (sourceMap,targetMap) = {
      val tempRenamings = buffer.toMap
      val source = scala.collection.mutable.HashMap.empty[PortRef,String]
      val target = scala.collection.mutable.HashMap.empty[PortRef,String]
      for (c <- connections) {
        source(c.from) = tempRenamings(c.id)
        target(c.to) = tempRenamings(c.id)
      }
      (source.toMap,target.toMap)
    }
    


    val subactorVarDecls = new ListBuffer[BDecl]
    val entityDecls = new ListBuffer[BDecl]
    val entityDataBuffer = new ListBuffer[(Instance,EntityData)]
    
    for (e <- entities) {
      //val entitySpecificRenames = new ListBuffer[Map[String,String]]
      //val entitySpecificVariables = new ListBuffer[List[String]]
      val variables = new ListBuffer[String]
      val renameBuffer = new ListBuffer[(String,Expr)]
      val actor = e.actor
      
      val parameterArguments = actor.parameters.zip(e.arguments).map{ case (d,e) => (d.id,e) }.toMap
      
      buffer += ((e.id,namePrefix+e.id))
     
      for (p <- actor.inports) {
        val newName = targetMap(PortRef(Some(e.id),p.id))
        renameBuffer += ((p.id,Id(newName)))
      }
      
      for (p <- actor.outports) {
        val newName = sourceMap(PortRef(Some(e.id),p.id))
        renameBuffer += ((p.id,Id(newName)))
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
        renameBuffer += ((v.id,Id(newName)))
      }
      
      val actionData = (actor.actions map { a => (a,collectEntityData(e,a,targetMap)) }).toMap
     
      
      val entityData = new EntityData(Nil,renameBuffer.toMap,variables.toList,actionData)
      //entitySpecificVariables += variables.toList
      //entitySpecificRenames += renameBuffer.toMap
      entityDataBuffer += ((e,entityData))
      entityDecls += BDecl(namePrefix+e.id, ActorType(e.actor))
      
    }
    val entityData = entityDataBuffer.toMap
    
    val tempRenames = buffer.toMap
    
    val networkRenamings = buffer.map{ case (s1,s2) => (s1,Id(s2)) }.toMap
    
    val publicInvs = 
      entities flatMap { 
        entity => {
          for (inv <- entity.actor.publicActorInvariants) yield {
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
    val uniquenessConidition2 = 
      if (chanDeclList.size > 1) List(createUniquenessCondition(chanDeclList).reduceLeft((a,b) => (a && b)))
      else Nil
    val uniquenessConditions = uniquenessConidition1 ::: uniquenessConidition2
    
    
    
    val basicAssumes =
      (for (c <- connections) yield {
        val name = tempRenames(c.id)
        val list1 = List(
          B.Int(0) <= B.I(name),
          B.I(name) <= B.R(name),
          B.R(name) <= B.C(name))
        val list2 = (if (c.isOutput) List(B.I(name) ==@ B.R(name)) else Nil)
        (list1 ::: list2).map(x => B.Assume(x))
      }).flatten
    
    
    
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
        basicAssumes,
        namePrefix)
  }
  
  def collectEntityData(instance: Instance, action: Action, targetMap: Map[PortRef, String]) = {
    val actor = instance.actor
    val vars = new ListBuffer[BDecl]()
    
    val replacements = scala.collection.mutable.HashMap.empty[Id,Expr]
    
    for (ipat <- action.inputPattern) {
      val cId = targetMap(PortRef(Some(instance.id),ipat.portId))      
      for ((v,ind) <- ipat.vars.zipWithIndex) {
        val c = Elements.ch(cId,v.typ)
        val index = 
          if (ind == 0) Elements.rd0(c.id) 
          else Minus(Elements.rd0(c.id),IntLiteral(ind))
        val acc = Elements.chAcc(c,index)
        replacements += (v -> acc)
      }
    }
    
    val patternVarRenamings = (for (ipat <- action.inputPattern) yield {
      for (v <- ipat.vars) yield {
        val inVar = ipat.portId + B.Sep + v.id
        vars += BDecl(inVar,B.Local(inVar,B.type2BType(v.typ)))
        (v.id,Id(inVar))
      }
    }).flatten.toMap
    
    new ActionData(vars.toList, patternVarRenamings, replacements.toMap)

  }
  
}
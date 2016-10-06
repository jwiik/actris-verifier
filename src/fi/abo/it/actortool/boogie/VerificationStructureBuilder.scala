package fi.abo.it.actortool.boogie

import fi.abo.it.actortool._ 
import scala.collection.mutable.ListBuffer

trait VerificationStructureBuilder[T <: DFActor, V <: VerificationStructure[T]] {
  def buildStructure(entity: T): V
}

class ActorVerificationStructureBuilder(implicit val bvMode: Boolean) 
         extends VerificationStructureBuilder[BasicActor, ActorVerificationStructure] {
  
  def buildStructure(actor: BasicActor): ActorVerificationStructure = {
    
    val prefix = actor.id+B.Sep
    
    val portChans = 
      ((for (p <- actor.inports) yield B.Local(p.id, B.type2BType(ChanType(p.portType))))
      :::
      (for (p <- actor.outports) yield B.Local(p.id, B.type2BType(ChanType(p.portType))))
      )
      
    val actorVars = new ListBuffer[Boogie.LocalVar]()
    val states = actor.schedule match {
      case Some(s) => 
        actorVars += B.ThisDecl
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
      actorVars  += B.Local(newName,decl.typ)
    }
    
    val basicAssumes = {
      (for (p <- actor.inports ::: actor.outports) yield {
        val name = p.id
        val list = List(
          //B.Int(0) <= B.I(name),
          //B.I(name) <= B.R(name),
          B.Int(0) <= B.R(name),
          B.R(name) <= B.C(name))
        list.map {x => B.Assume(x)}
      }).flatten
    }
    
    val initAssumes = 
      (for (p <- actor.inports ::: actor.outports) yield {
        val name = p.id
        val list = List(
          B.R(name) ==@ B.Int(0),
          B.C(name) ==@ B.Int(0))
        list.map {x => B.Assume(x)}
      }).flatten
    
    return new ActorVerificationStructure(
        actor,
        actor.actions,
        actor.inports,
        actor.outports,
        actor.actorInvariants,
        portChans,
        actorVars.toList,
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
    for (c <- connections) buffer += ((c.id,namePrefix+c.id))
    
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
    
    val entitySpecificRenames = new ListBuffer[(Instance,Map[String,String])]
    val entitySpecificVariables = new ListBuffer[(Instance,List[String])]
    val subactorVarDecls = new ListBuffer[Boogie.LocalVar]

    val renameBuffer = new ListBuffer[(String,String)]()
    
    for (e <- entities) {
      val variables = new ListBuffer[String]()
      val actor = e.actor
      
      buffer += ((e.id,namePrefix+e.id))
     
      for (p <- actor.inports) {
        val newName = targetMap(PortRef(Some(e.id),p.id))
        renameBuffer += ((p.id,newName))
      }
      
      for (p <- actor.outports) {
        val newName = sourceMap(PortRef(Some(e.id),p.id))
        renameBuffer += ((p.id,newName))
      }
      
      for (p <- actor.parameters) {
        val newName = "AP"+B.Sep+e.id+B.Sep+p.id
        subactorVarDecls += B.Local(newName,B.type2BType(p.typ))
        renameBuffer += ((p.id,newName))
      }
      
      for (v <- actor.variables) {
        val newName = "AV"+B.Sep+e.id+B.Sep+v.id
        subactorVarDecls += B.Local(newName,B.type2BType(v.typ))
        variables += newName
        renameBuffer += ((v.id,newName))
      }
      
      entitySpecificVariables += ((e,variables.toList))
      entitySpecificRenames += ((e,renameBuffer.toMap))
      
    }
    
    val networkRenamings = buffer.toMap
    val entityRenamings = entitySpecificRenames.toMap
    val entityVariables = entitySpecificVariables.toMap
    
    val basicAssumes =
      (for (c <- connections) yield {
        val name = networkRenamings(c.id)
        val list1 = List(
          B.Int(0) <= B.I(name),
          B.I(name) <= B.R(name),
          B.R(name) <= B.C(name))
        val list2 = (if (c.isOutput) List(B.I(name) ==@ B.R(name)) else Nil)
        (list1 ::: list2).map(x => B.Assume(x))
      }).flatten
      
      
    new NetworkVerificationStructure(
        network, actions, nwInvariants, chInvariants, connections, entities, sourceMap, targetMap, 
        networkRenamings, entityRenamings, entityVariables, subactorVarDecls.toList, basicAssumes, namePrefix)
  }
  
}
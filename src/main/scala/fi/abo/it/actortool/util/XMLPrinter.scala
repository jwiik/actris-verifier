package fi.abo.it.actortool.util

import fi.abo.it.actortool._
import xml.NodeSeq
import xml.Node
import xml.PrettyPrinter

object XMLPrinter {
  
  def printPretty(decls: List[TopDecl]): String = {
    new PrettyPrinter(150,2).format(print(decls))
  }
  
  def print(decls: List[TopDecl]): Node = {
    <program>{
      for (d <- decls) yield {
        print(d)
      }
    }</program>
  }
  
  def print(decl: TopDecl) = {
    decl match {
      case BasicActor(id,parameters,inports,outports,members) =>
        <actor id={id}>{ printMembers(members) }</actor>
      case Network(id,parameters,inports,outports,members) => {
        <network id={id}>{ printMembers(members) }</network>
      }
      case _ => NodeSeq.Empty
    }
  }
  
  def printMembers(members: List[Member]) = { members map printMember }
  
  def printMember(member: Member) = {
    member match {
      case a@ActorAction(lbl,false,inpats,outpats,guards,requires,ensures,vars,body) => {
        <action id={ a.fullName }>{
          (for (p <- inpats) yield {
            <read port={ p.portId } rate={ p.rate.toString } />
          }) :::
          (for (p <- outpats) yield {
            <write port={ p.portId } rate={ p.rate.toString } />
          })
        }</action>
      }
      case Entities(insts) => {
        <instances> {
					for (i <- insts) yield {
					  <instance id={ i.id } actor={ i.actorId } />
					}
				}</instances>
      }
      case Structure(connections) => {
        <structure>{
          for (c <- connections) yield {
					  <connection id={ c.id }>{
					    val from = c.from match {
					      case PortRef(Some(a),p) => <from actor={ a } port={ p } />
					      case PortRef(None,p) => <from port={ p } />
					    }
					    val to = c.to match {
					      case PortRef(Some(a),p) => <to actor={ a } port={ p } />
					      case PortRef(None,p) => <to port={ p } />
					    }
					    from ++ to
					  }</connection>
					}
        }</structure>
      }
      case _ => NodeSeq.Empty
    }
  }
  
  //      case ContractAction(lbl,inpats,outpats,guards,requires,ensures) => 
//      case d: Declaration => 
//      case fd: FunctionDecl => 
//      case pd: ProcedureDecl => 
//      case ActorInvariant(Assertion(exp,free,msg),gen,stream) => 
//      case ChannelInvariant(Assertion(exp,free,msg),gen) => 
//      case Entities(instances) =>
//      case Structure(connections) =>
//      case Priority(orders) =>
//        
//    }
  
  def printIf(cond: Boolean, text: String) = if (cond) text else ""
  
  def printPortRef(c: PortRef) = {
    c.actor match {
      case Some(a) => a + "." + c.name
      case None => c.name
    }
  }
  
}
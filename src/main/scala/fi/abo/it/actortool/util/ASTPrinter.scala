package fi.abo.it.actortool.util

import fi.abo.it.actortool._

class ASTPrinter {
  
  private val nl = System.getProperty("line.separator");
  
  var indentLvl = 0
    
  def indentAdd = { indentLvl = indentLvl + 1; "" }
  def indentRem = { indentLvl = indentLvl - 1; "" }
  def indent = "  " * indentLvl
  
  def print(decls: List[TopDecl]): String = {
    (decls map print).mkString(nl)
  }
  
  def print(decl: TopDecl): String = {
    decl match {
      case BasicActor(annot,id,parameters,inports,outports,members) => {
        indent + "actor " + id +
        "(" + (parameters map { p => p.typ.id + " " + p.id }).mkString(",") + ") " +
        (inports map { ip => ip.portType.id + " " +ip.id }).mkString(", ") +
        " ==> " +
        (outports map { op => op.portType.id + " " + op.id }).mkString(", ") + " :" + nl +
        indentAdd +
        printMembers(members) +
        indentRem + nl + "end"
      }
      case Network(annot,id,parameters,inports,outports,members) => {
        indent + "network " + id +
        "(" + (parameters map { p => p.typ.id + " " + p.id }).mkString(",") + ") " +
        (inports map { ip => ip.portType.id + " " +ip.id }).mkString(", ") +
        " ==> " +
        (outports map { op => op.portType.id + " " + op.id }).mkString(", ") + " :" + nl +
        indentAdd +
        printMembers(members) +
        indentRem + nl + "end"
      }
    }
  }
  
  def printMembers(members: List[Member]): String = {
    (members map printMember).mkString(nl)
  }
  
  def printMember(member: Member): String = {
    member match {
      case ActorAction(lbl,init,inpats,outpats,guards,requires,ensures,vars,body) => {
        indent + 
        (if (lbl.isDefined) lbl.get + ": " else "") + 
        (if (init) "initialize " else "action ") +
        (inpats map { ip => ip.portId + ":[" + (ip.vars map printExpr).mkString(",")  + "]" }).mkString(", ") +
        " ==> " +
        (outpats map { op => op.portId + ":[" + (op.exps map printExpr).mkString(",")  + "]" }).mkString(", ") +
        (guards map { g => nl +indent + "guard " + printExpr(g) }).mkString(nl) + 
        (requires map { r => nl +indent + "requires " + printExpr(r) }).mkString(nl) +
        (ensures map { q => nl + indent + "ensures " + printExpr(q) }).mkString(nl) + 
        (if (body.isEmpty) "" else nl + indent + "do " + nl + indentAdd + printStmts(body) + indentRem + nl) +
        indent + "end"
      }
      case ContractAction(lbl,inpats,outpats,guards,requires,ensures) => {
        indent + 
        (if (lbl.isDefined) lbl.get + ": " else "") + 
        "contract " +
        (inpats map { ip => ip.portId + ":" + ip.rate }).mkString(", ") +
        " ==> " +
        (outpats map { op => op.portId + ":" + op.rate }).mkString(", ") + indentAdd +
        (guards map { g => nl +indent + "guard " + printExpr(g) }).mkString(nl) + 
        (requires map { r => nl +indent + "requires " + printExpr(r) }).mkString(nl) +
        (ensures map { q => nl + indent + "ensures " + printExpr(q) }).mkString(nl) + nl + indentRem +
        indent + "end"
      }
      case d: Declaration => {
        indent + printDecl(d) + ";"
      }
      case ActorInvariant(Assertion(exp,free,msg),gen,stream) => {
        indent + "invariant " + (if (stream) "stream " else "") + printExpr(exp)
      }
      case ChannelInvariant(Assertion(exp,free,msg),gen) => {
        indent + "chinvariant " + printExpr(exp)
      }
      case Entities(instances) =>
        indent + "entities" + nl + indentAdd +
        (instances map { e => indent + e.id + " = " + e.actorId  }).mkString(";"+nl) +
        indentRem + nl + 
        indent + "end"
      case Structure(connections) =>
        indent + "structure" + nl + indentAdd +
        (connections map { c => indent + printPortRef(c.from) + " --> " + printPortRef(c.to) }).mkString(";"+nl) +
        indentRem + nl + 
        indent + "end"
        
    }
  }
  
  def printPortRef(c: PortRef) = {
    c.actor match {
      case Some(a) => a + "." + c.name
      case None => c.name
    }
  }
  
  def printStmts(stmt: List[Stmt]): String = {
    (stmt map printStmt).mkString(nl)
  }
  
  def printStmt(stmt: Stmt): String = {
    stmt match {
      case Assign(id,e) => indent + printExpr(id) + " := " + printExpr(e) + ";"
    }
  }
  
  def printExpr(expr: Expr): String = {
    expr match {
      case be: BinaryExpr => "(" + printExpr(be.left) + ") " + be.operator + " (" + printExpr(be.right) + ")"
      case Id(id) => id
      case IntLiteral(i) => i.toString
      case FunctionApp(n,args) => n + "(" + (args map printExpr).mkString(",") + ")"
      case IndexAccessor(e,idx) => printExpr(e) + "[" + printExpr(idx) + "]"
      case SpecialMarker(s) => s
      case Forall(vars,expr,pat) => "(forall " + (vars map printDecl).mkString(", ") + " :: " + printExpr(expr) + ")" 
    }
  }
  
  def printDecl(d: Declaration): String = {
    d.typ.id + " " + d.id + (if (d.constant) " = " + d.value.get else "")
  }
}
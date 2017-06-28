package fi.abo.it.actortool.util

import fi.abo.it.actortool._

object ASTPrinter {
  def get = new ASTPrinter(false)
  def orcc = new ASTPrinter(true)
}

class ASTPrinter(orccCompatible: Boolean) {
  
  val orccOperatorMap = Map(
    "!" -> "not ",
    "&&" -> " and "
  )
  
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
        "(" + (parameters map { p => printType(p.typ) + " " + p.id }).mkString(",") + ") " +
        (inports map { ip => printType(ip.portType) + " " +ip.id }).mkString(", ") +
        " ==> " +
        (outports map { op => printType(op.portType) + " " + op.id }).mkString(", ") + " :" + nl +
        indentAdd +
        printMembers(members) +
        indentRem + nl + "end"
      }
      case Network(annot,id,parameters,inports,outports,members) => {
        indent + "network " + id +
        "(" + (parameters map { p => printType(p.typ) + " " + p.id }).mkString(",") + ") " +
        (inports map { ip => printType(ip.portType) + " " +ip.id }).mkString(", ") +
        " ==> " +
        (outports map { op => printType(op.portType) + " " + op.id }).mkString(", ") + " :" + nl +
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
        (if (lbl.isDefined) getId(lbl.get) + ": " else "") + 
        (if (init) "initialize " else "action ") +
        (inpats map { ip => ip.portId + ":[" + (ip.vars map printExpr).mkString(",")  + "]" }).mkString(", ") +
        " ==> " +
        (outpats map { op => op.portId + ":[" + (op.exps map printExpr).mkString(",")  + "]" }).mkString(", ") +
        {
          if (!orccCompatible) (guards map { g => nl +indent + "guard " + printExpr(g) }).mkString("")
          else if (guards.isEmpty) "" else nl + indent + "guard " + (guards map { g => printExpr(g) }).mkString(", ")
        } +
        {
          if (!orccCompatible)
            (requires map { r => nl +indent + "requires " + printExpr(r) }).mkString("") +
            (ensures map { q => nl + indent + "ensures " + printExpr(q) }).mkString("")
          else ""
        } + 
        (if (vars.isEmpty) "" else nl + indent + "var " + indentAdd + vars.map(d => nl + indent + printDecl(d)).mkString(",") + indentRem) +
        (if (body.isEmpty) "" else nl + indent + "do " + nl + indentAdd + printStmts(body) + indentRem + nl) +
        indent + "end"
      }
      case ContractAction(lbl,inpats,outpats,guards,requires,ensures) => {
        indent + 
        (if (lbl.isDefined) getId(lbl.get) + ": " else "") + 
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
      case fd: FunctionDecl => {
        indent + "function " + fd.name + "(" + (fd.inputs map printDecl).mkString(",") + ") --> " + printType(fd.output) + ":" + nl +
        indentAdd + indent + printExpr(fd.expr) + indentRem + nl +
        indent + "end"
      }
      case pd: ProcedureDecl => {
        indent + "procedure " + pd.name + "(" + (pd.inputs map printDecl).mkString(",") + ")" + nl +
        indent + "var" + nl + indentAdd +
        indent + (pd.inputs map printDecl).mkString(",") + nl + indentRem +
        indent + "begin" + nl + indentAdd +
        printStmts(pd.body) + indentRem + nl +
        indent + "end"
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
      case MapAssign(id,e) => indent + printExpr(id) + " := " + printExpr(e) + ";"
      case IfElse(cond,thn,elsifs,els) => 
        indent + "if " + printExpr(cond) + " then" + nl +
        indentAdd + printStmts(thn) + indentRem + nl +
        {
          if (!orccCompatible) {
            (for (ei <- elsifs) yield {
              indent + "else if " + printExpr(ei.cond) + " then" + nl + 
              indentAdd + indent + printStmts(ei.stmt) + indentRem
            }).mkString + nl +
            (if (!els.isEmpty) {
              indent + "else" + nl +
              indentAdd + indent + printStmts(els) + indentRem
            }
            else "")
          }
          else {
            if (elsifs.isEmpty && els.isEmpty) ""
            else {
              indent + "else" + nl +
              indentAdd +
              {
                printStmts(convertElseIfs(elsifs, els))
              } +
              indentRem + nl
            } 
          }
        } +
        indent + "end"
      case While(cond,invs,stmt) =>
        indent + "while " + printExpr(cond) + nl +
        invs.map(i => indent + "invariant " + printExpr(i)).mkString(nl) +
        indent + "do" + nl +
        indentAdd +
        printStmts(stmt) +
        indentRem +
        indent + "end"
      case Assert(e) => indent + "assert " + printExpr(e) + ";"
      case Assume(e) => indent + "assume " + printExpr(e) + ";"
      case Havoc(vars) => indent + "havoc " + (vars map printExpr).mkString(",") + ";"
    }
  }
  
  def convertElseIfs(elseIfs: List[ElseIf], els: List[Stmt]): List[Stmt] = {
    elseIfs match {
      case hd::tail => List(IfElse(hd.cond,hd.stmt,Nil,convertElseIfs(tail,els)))
      case Nil => els
    }
  }
  
  def printExpr(expr: Expr): String = {
    expr match {
      case be: BinaryExpr => "(" + printExpr(be.left) + " "  + getOp(be.operator) + " " + printExpr(be.right) + ")"
      case Not(e) => getOp("!")+"(" + printExpr(e) + ")"
      case UnMinus(e) => "-("+printExpr(e)+")"
      case Id(id) => getId(id)
      case IntLiteral(i) => i.toString
      case BoolLiteral(b) => b.toString
      case HexLiteral(x) => "0x"+x 
      case FunctionApp(n,args) => printFunctionApp(n, args)
      case IndexAccessor(e,idx) => printExpr(e) + "[" + printExpr(idx) + "]"
      case SpecialMarker(s) => s
      case Forall(vars,expr,pat) => "(forall " + (vars map printDecl).mkString(", ") + " :: " + printExpr(expr) + ")"
      case IfThenElse(cond,thn,els) => "if " + printExpr(cond) + " then " + printExpr(thn) + " else " + printExpr(els) + " end"
    }
  }
  
  def printType(tp: Type): String = {
    if (!orccCompatible) tp.id
    else {
      tp match {
        case IntType(s) => 
          val size = if (s == -1) 32 else s
          "int(size="+size+")"
        case UintType(s) => 
          val size = if (s == -1) 32 else s
          "uint(size="+size+")"
        case BvType(s,true) => "int(size="+s+")"
        case BvType(s,false) => "uint(size="+s+")"
        case BoolType => "bool"
        case StateType(_,_) => "int"
        case MapType(dom,rng,size) => {
          if (dom.isBv || dom.isInt) printType(ListType(rng,size))
          else throw new RuntimeException()
        }
        case ListType(rng,size) => "List(type:" + printType(rng) + ", size="+size+")"
        case _ => throw new RuntimeException()
      }
    }
  }
  
  def printFunctionApp(name: String, args: List[Expr]) = {
    if (!orccCompatible) name + "(" + (args map printExpr).mkString(",") + ")"
    else {
      name match {
        case "int2bv" => printExpr(args(0))
        case "int" => printExpr(args(0))
        case "bvresize" => printExpr(args(0))
        case _ => name + "(" + (args map printExpr).mkString(",") + ")"
      }
    }
  }
  
  def getId(id: String) = if (!orccCompatible) id else id.replace("#", "__").replace("$","__")
  
  def getOp(op: String) = {
    if (!orccCompatible) op
    else orccOperatorMap.getOrElse(op, op)
  }
  
  def printDecl(d: Declaration): String = {
    printType(d.typ) + " " + getId(d.id) + (if (d.value.isDefined)  (if (d.constant) " = " else " := ") + printExpr(d.value.get) else "")
  }
}
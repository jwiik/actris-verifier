package fi.abo.it.actortool.promela

object Promela {
  
  trait Decl
  trait Stmt
  trait Expr
  trait Type
  trait VarInit
  
  case class ProcType(name: String, params: List[ParamDecl], decls: List[VarDecl], stmt: List[Stmt]) extends Decl
  case class Init(stmt: List[Stmt]) extends Decl
  
  case class ParamDecl(id: String, tp: Type)
  case class VarDecl(id: String, tp: Type, value: Option[VarInit]) extends Decl with Stmt
  case class ChInit(size: Int, tp: Type) extends VarInit
  
  case class Atomic(stmt: List[Stmt]) extends Stmt
  case class If(options: List[GuardStmt]) extends Stmt
  case class Iteration(options: List[GuardStmt]) extends Stmt
  case class Assign(trgt: Expr, value: Expr) extends Stmt
  case class Run(procId: String, params: List[Expr]) extends Stmt
  case class Send(ch: String, exp: Expr) extends Stmt
  case class Receive(ch: String, exp: Expr) extends Stmt
  case class GuardStmt(guard: Expr, stmt: List[Stmt]) extends Stmt
  case object Skip extends Stmt
  
  case class BinaryExpr(left: Expr, op: String, right: Expr) extends Expr
  case class FunCall(name: String, args: List[Expr]) extends Expr
  case class VarExp(id: String) extends Expr
  case class IntLiteral(i: Int) extends Expr with VarInit
  case class BoolLiteral(b: Boolean) extends Expr with VarInit
  
  
  case class NamedType(s: String) extends Type
  
  
  private val nl = System.getProperty("line.separator");
  
  class PromelaPrinter {
    
    var indentLvl = 0
    
    def indentAdd = { indentLvl = indentLvl + 1; "" }
    def indentRem = { indentLvl = indentLvl - 1; "" }
    def indent = "  " * indentLvl
    
    def print(d: Decl): String = {
      d match {
        case vd: VarDecl =>
          printVarDecl(vd) + nl
        case ProcType(name,params,decls,stmt) => 
          indent + "proctype " + name + 
          "(" + 
          printParamDecls(params) +
          ") {" + nl +
          indentAdd + 
          printVarDecls(decls) +
          printStmts(stmt) +
          indentRem + 
          indent + "}" + nl
        case Init(stmts) => 
          "init {" + nl +
          indentAdd +
          printStmts(stmts) +
          indentRem +
          "}" + nl
      }
    }
    
    def printParamDecls(varDecls: List[ParamDecl]): String = {
      (varDecls map { vd => indent + printType(vd.tp) + " " + vd.id }).mkString("; ")
    }
    
    def printVarDecls(varDecls: List[VarDecl]): String = {
      (varDecls map { vd => printVarDecl(vd) }).mkString(nl) + nl
    }
    
    def printVarDecl(vd: VarDecl) = 
      indent + printType(vd.tp) + " " + vd.id + 
      (if (vd.value.isDefined) " = " + printVarInit(vd.value.get) else "") + ";"
      
    
    def printVarInit(varInit: VarInit): String = {
      varInit match {
        case ChInit(size,tp) => "[" + size + "] of {" + printType(tp) + "}"
        case il: IntLiteral => printExpr(il)
        case bl: BoolLiteral => printExpr(bl)
      }
    }
    
    def printStmts(stmt: List[Stmt]): String = {
      (stmt map { s => printStmt(s) }).mkString(nl) + nl
    }
    
    def printStmt(stmt: Stmt): String = {
      stmt match {
        case If(opts: List[GuardStmt]) => 
          indent + "if" + nl + 
          indent + (opts map { o => ":: " + printExpr(o.guard) + " -> " + nl + indentAdd + printStmts(o.stmt) + indentRem }).mkString(nl) +
          indent + "fi"
        case Iteration(opts: List[GuardStmt]) => 
          indent + "do" + nl + 
          indent + (opts map { o => ":: " + printExpr(o.guard) + " -> " + nl + indentAdd + printStmts(o.stmt) + indentRem }).mkString(nl) +
          indent + "od"
        case Assign(t,exp) => 
          indent + printExpr(t) + " = " + printExpr(exp) + ";"
        case Atomic(stmt) => 
          indent + "atomic {"+ nl +
          indentAdd +
          printStmts(stmt) +
          indentRem +
          indent + "}"
        case Send(cId, exp) => indent + cId + " ! (" + printExpr(exp) + ");"
        case Receive(cId, exp) => indent + cId + " ? (" + printExpr(exp) + ");" 
        case Run(pId, params) =>
          indent + "run " + pId + "(" + (params.map { e => printExpr(e) }).mkString(",") + ");"
        case vd: VarDecl => printVarDecl(vd)
        case Skip => indent + "skip;"
      }
    }
    
    def printExpr(e: Expr): String = {
      e match {
        case BinaryExpr(l,o,r) => printExpr(l) + " " + o + " " + printExpr(r)
        case VarExp(id) => id
        case FunCall(name,args) => name + "(" + (args.map { a => printExpr(a) }).mkString(",") + ")"
        case IntLiteral(i) => i.toString
        case BoolLiteral(true) => "true"
        case BoolLiteral(false) => "false"
        
      }
    }
    
    def printType(tp: Type): String = {
      tp match {
        case NamedType(n) => n
      }
    }
  }
    
}


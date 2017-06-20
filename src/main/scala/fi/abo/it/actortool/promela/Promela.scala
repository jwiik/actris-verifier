package fi.abo.it.actortool.promela

object Promela {
  
  trait Decl
  trait Stmt
  trait VarInit
  trait Expr extends VarInit
  trait Type
  
  case class ProcType(name: String, params: List[ParamDecl], decls: List[VarDecl], stmt: List[Stmt]) extends Decl
  case class Init(stmt: List[Stmt]) extends Decl
  case class Ltl(label: String, expr: Expr) extends Decl
  
  case class ParamDecl(id: String, tp: Type)
  case class VarDecl(id: String, tp: Type, value: Option[VarInit]) extends Decl with Stmt
  case class ChInit(size: Int, tp: Type) extends VarInit
  
  case class Atomic(stmt: List[Stmt]) extends Stmt
  case class If(options: List[OptionStmt]) extends Stmt
  case class Iteration(options: List[OptionStmt]) extends Stmt
  case class Assign(trgt: Expr, value: Expr) extends Stmt
  case class Run(procId: String, params: List[Expr]) extends Stmt
  case class Send(ch: String, exp: Expr) extends Stmt
  case class Receive(ch: String, exp: Expr) extends Stmt
  case class Peek(ch: String, exp: Expr) extends Stmt
  case class GuardStmt(guard: Stmt, stmt: List[Stmt]) extends Stmt
  case class OptionStmt(stmt: List[Stmt]) extends Stmt
  case class PrintStmt(str: String) extends Stmt
  case class PrintStmtValue(str: String, values: List[Expr]) extends Stmt
  case class ExprStmt(expr: Expr) extends Stmt
  case object Skip extends Stmt
  case object Else extends Stmt
  case class Comment(str: String) extends Stmt
  
  case class BinaryExpr(left: Expr, op: String, right: Expr) extends Expr
  case class UnaryExpr(op:String, exp: Expr) extends Expr
  case class FunCall(name: String, args: List[Expr]) extends Expr
  case class IndexAccessor(exp: Expr, idx: Expr) extends Expr
  case class ConditionalExpr(cond: Expr, thn: Expr, els: Expr) extends Expr
  case class VarExp(id: String) extends Expr
  case class IntLiteral(i: Int) extends Expr
  case class BoolLiteral(b: Boolean) extends Expr
  
  
  case class NamedType(s: String) extends Type
  case class ArrayType(cntType: Type, size: Int) extends Type
  
  
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
          printStmts(stmt) + nl +
          indentRem +
          indent + "}" + nl
        case Init(stmts) => 
          "init {" + nl +
          indentAdd +
          printStmts(stmts) + nl +
          indentRem +
          "}" + nl
        case Ltl(lbl,exp) => 
          "ltl " + lbl + "{" +
          printExpr(exp) +
          "}" + nl
      }
    }
    
    def printParamDecls(varDecls: List[ParamDecl]): String = {
      (varDecls map { vd => indent + printType(vd.tp) + " " + vd.id }).mkString("; ")
    }
    
    def printParamDecl(pd: ParamDecl) {
      indent + printType(pd.tp) + " " + pd.id
    }
    
    def printVarDecls(varDecls: List[VarDecl]): String = {
      (varDecls map { vd => printVarDecl(vd) }).mkString(nl) + nl
    }
    
    def printVarDecl(vd: VarDecl) = 
      indent + printType(vd.tp) + " " + vd.id + 
      {
        vd.tp match {
          case ArrayType(_,size) => "[" + size.toString + "]"
          case _ => ""
        }
      } +
      (if (vd.value.isDefined) " = " + printVarInit(vd.value.get) else "") + ";"
      
    
    def printVarInit(varInit: VarInit): String = {
      varInit match {
        case ChInit(size,tp) => "[" + size + "] of {" + printType(tp) + "}"
        case e: Expr => printExpr(e)
      }
    }
    
    def printStmts(stmt: List[Stmt]): String = {
      (stmt map { s => printStmt(s) }).mkString(nl)
    }
    
    def printStmt(stmt: Stmt): String = {
      stmt match {
        case If(opts) => 
          indent + "if" + nl + 
          printStmts(opts) + nl +
          indent + "fi"
        case Iteration(opts) => 
          indent + "do" + nl + 
          printStmts(opts) + nl +
          indent + "od"
        case Assign(t,exp) => 
          indent + printExpr(t) + " = " + printExpr(exp) + ";"
        case Atomic(stmt) => 
          indent + "atomic {"+ nl +
          indentAdd +
          printStmts(stmt) + nl +
          indentRem +
          indent + "}"
        case OptionStmt(stmt) =>
          indent + "::" + nl + indentAdd + printStmts(stmt) + indentRem
        case GuardStmt(grd,stmt) =>
          indent + printStmt(grd) + " -> " + nl + indentAdd + printStmts(stmt) + indentRem
        case Send(cId, exp) => indent + cId + " ! (" + printExpr(exp) + ");"
        case Receive(cId, exp) => indent + cId + " ? (" + printExpr(exp) + ");"
        case Peek(cId, exp) => indent + cId + " ? <" + printExpr(exp) + ">;"
        case Run(pId, params) =>
          indent + "run " + pId + "(" + (params.map { e => printExpr(e) }).mkString(",") + ");"
        case vd: VarDecl => printVarDecl(vd)
        case PrintStmt(str) => indent + "printf(\"" + str + "\");"
        case PrintStmtValue(str,args) => indent + "printf(\"" + str + "\"," + (args.map { e => printExpr(e) }).mkString(",") + ");"
        case ExprStmt(expr) => printExpr(expr)
        case Skip => "skip"
        case Else => "else"
        case Comment(str) => indent + "// " + str 
      }
    }
    
    def printExpr(e: Expr): String = {
      e match {
        case BinaryExpr(l,"&&",r) => "(" + printExpr(l) + " " + "&&\n" + indentAdd + indent + " " + printExpr(r) + ")" + indentRem
        case BinaryExpr(l,o,r) => "(" + printExpr(l) + " " + o + " " + printExpr(r) + ")"
        case UnaryExpr(o,e) => o + "(" + printExpr(e) + ")"  
        case VarExp(id) => id
        case FunCall(name,args) => name + "(" + (args.map { a => printExpr(a) }).mkString(",") + ")"
        case IndexAccessor(exp,idx) => printExpr(exp)+ "[" + printExpr(idx) + "]"
        case ConditionalExpr(cond,thn,els) => "(" + printExpr(cond) + " -> " + printExpr(thn) + " : " + printExpr(els) + ")"
        case IntLiteral(i) => i.toString
        case BoolLiteral(true) => "true"
        case BoolLiteral(false) => "false"
        
      }
    }
    
    def printType(tp: Type): String = {
      tp match {
        case NamedType(n) => n
        case ArrayType(cntType,_) => printType(cntType)
      }
    }
  }
    
}


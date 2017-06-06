package fi.abo.it.actortool.util

import fi.abo.it.actortool._

class FunctionCallReplacer extends ASTReplacingVisitor[String,FunctionDecl] {
  
  private val argReplacer = new ArgumentReplacer
  private var funcDecls: Map[String,FunctionDecl] = Map.empty
  
  def setFunctionDeclarations(funDecls: Map[String,FunctionDecl]) {
    funcDecls = funDecls
  }
  
  def setFunctionDeclarations(funDecls: List[FunctionDecl]) {
    funcDecls = (funDecls map { fd => (fd.name,fd) }).toMap
  }

  def replaceFunctionCalls(e: Expr): Expr = visitExpr(e)(funcDecls)
  def replaceFunctionCalls(s: Stmt): Stmt = visitStmt(s)(funcDecls)
  
  override def visitExpr(expr: Expr)(implicit map: Map[String,FunctionDecl]): Expr = {
    expr match {
      case FunctionApp(name,args) => {
        val newArgs = args map visitExpr
        map.get(name) match {
          case Some(fd) => {
            val replacements = (for ((param,arg)  <- fd.inputs.zip(newArgs)) yield (param.id,arg)).toMap
            argReplacer.visitExpr(fd.expr)(replacements)
          }
          case None => FunctionApp(name,newArgs)
        }
      }
      case _ => super.visitExpr(expr)
    }
  }
  
  class ArgumentReplacer extends ASTReplacingVisitor[String,Expr] {
    override def visitExpr(expr: Expr)(implicit map: Map[String,Expr]): Expr = {
      expr match {
        case id@Id(name) => {
          map.get(name) match {
            case Some(e) => e
            case None => id
          }
        }
        case _ => super.visitExpr(expr)
      }
    }
  }
}
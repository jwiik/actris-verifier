package fi.abo.it.actortool

import scala.collection.mutable.ListBuffer

/**
 * @author Jonatan Wiik
 */
object IdReplacer extends ASTReplacingVisitor[Id,Expr] {
  override def visitExpr(expr: Expr)(implicit map: Map[Id,Expr]): Expr = {
    expr match {
      case id: Id => {
        map.get(id) match {
          case Some(repl) => {
            repl.typ = id.typ
            return repl
          }
          case None =>
        }
      }
      case _ =>
    }
    super.visitExpr(expr)
  }
}


object IdToIdReplacer extends ASTReplacingVisitor[Id,Id] {
  override def visitId(id: Id)(implicit map: Map[Id,Id]): Id = {
    val replacement = map.get(id) match {
      case None => id
      case Some(newId) => newId
    }
    replacement.typ = id.typ
    replacement
  }
}

object TokensDefFinder extends ASTVisitor[ListBuffer[(String,Expr)]] {
  override def visitExpr(expr: Expr)(implicit info: ListBuffer[(String,Expr)]) {
    expr match {
      case delay@FunctionApp("tokens",List(ch,amount)) => info += ((ch.asInstanceOf[Id].id, amount))
      case _ =>
    }
    super.visitExpr(expr)
  }
}

abstract class ASTVisitor[T] {
  
  def visitStmt(stmt: List[Stmt])(implicit info: T) { for (s <- stmt) visitStmt(s) }
  
  def visitStmt(stmt: Stmt)(implicit info: T) {
    stmt match {
      case Assignment(id,exp) => visitAssignable(id); visitExpr(exp)
      case Assert(e) => visitExpr(e)
      case Assume(e) => visitExpr(e)
      case Havoc(vars) => for (v <- vars) visitId(v)
      case IfElse(ifc,ifs,eifs,els) => visitExpr(ifc); visitStmt(ifs); visitIfElses(eifs); visitStmt(els)
      case While(c,inv,s) => visitExpr(c); visitExpr(inv); visitStmt(s)
    }
  }
  
  def visitIfElses(eifs: List[ElseIf])(implicit info: T) {
    for (eif <- eifs) yield eif match {
      case ElseIf(c,s) => visitExpr(c); visitStmt(s)
    }
  }
  
  def visitExpr(expr: List[Expr])(implicit info: T) { for (e <- expr) yield visitExpr(e) }
  
  def visitExpr(expr: Expr)(implicit info: T) {
    expr match {
      case id: Id => visitId(id)
      case Iff(l,r) => visitExpr(l); visitExpr(r)
      case Implies(l,r) => visitExpr(l); visitExpr(r)
      case Not(e) => visitExpr(e)
      case And(l,r) => visitExpr(l); visitExpr(r)
      case Or(l,r) => visitExpr(l); visitExpr(r)
      case Eq(l,r) => visitExpr(l); visitExpr(r)
      case NotEq(l,r) => visitExpr(l); visitExpr(r)
      case AtLeast(l,r) => visitExpr(l); visitExpr(r)
      case AtMost(l,r) => visitExpr(l); visitExpr(r)
      case Less(l,r) => visitExpr(l); visitExpr(r)
      case Greater(l,r) => visitExpr(l); visitExpr(r)
      case Plus(l,r) => visitExpr(l); visitExpr(r)
      case Minus(l,r) => visitExpr(l); visitExpr(r)
      case Times(l,r) => visitExpr(l); visitExpr(r)
      case Div(l,r) => visitExpr(l); visitExpr(r)
      case Mod(l,r) => visitExpr(l); visitExpr(r)
      case LShift(l,r) => visitExpr(l); visitExpr(r)
      case RShift(l,r) => visitExpr(l); visitExpr(r)
      case UnMinus(e) => visitExpr(e)
      case IfThenElse(c,t,e) => visitExpr(c); visitExpr(t); visitExpr(e)
      case Forall(v,e,None) => visitExpr(e)
      case Forall(v,e,Some(p)) => visitExpr(e); visitExpr(p)
      case Exists(v,e,None) => visitExpr(e)
      case Exists(v,e,Some(p)) => visitExpr(e); visitExpr(p)
      case IndexAccessor(l,i) => visitExpr(l); visitExpr(i)
      case FunctionApp(n,args) => visitExpr(args)
      case is: IndexSymbol => visitExpr(is.indexedExpr)
      case il: IntLiteral =>
      case bl: BoolLiteral =>
      case fl: FloatLiteral =>
    }
  }
  
  def visitAssignable(asgn: Assignable)(implicit info: T) {
    asgn match {
      case id: Id => visitId(id)
    }
  }
  
  def visitId(id: Id)(implicit info: T) {}
}

abstract class ASTReplacingVisitor[A<:ASTNode,B<:ASTNode] {
  def visitStmt(stmt: List[Stmt])(implicit map: Map[A,B]): List[Stmt] ={
    for (s <- stmt) yield visitStmt(s)
  }
  
  def visitStmt(stmt: Stmt)(implicit map: Map[A,B]): Stmt = {
    stmt match {
      case Assignment(id,exp) => Assignment(visitAssignable(id),visitExpr(exp))
      case Assert(e) => Assert(visitExpr(e))
      case Assume(e) => Assume(visitExpr(e))
      case Havoc(vars) => Havoc(for (v <- vars) yield visitId(v))
      case IfElse(ifc,ifs,eifs,els) => IfElse(visitExpr(ifc),visitStmt(ifs),visitIfElses(eifs),visitStmt(els))
      case While(c,inv,s) => While(visitExpr(c),visitExpr(inv),visitStmt(s))
    }
  }
  
  def visitIfElses(eifs: List[ElseIf])(implicit map: Map[A,B]): List[ElseIf] = {
    for (eif <- eifs) yield eif match {
      case ElseIf(c,s) => ElseIf(visitExpr(c),visitStmt(s))
    }
  }
  
  def visitExpr(expr: List[Expr])(implicit map: Map[A,B]): List[Expr] =
    for (e <- expr) yield visitExpr(e)
  
  def visitExpr(expr: Expr)(implicit map: Map[A,B]): Expr = {
    val newExpr = expr match {
      case id: Id => visitId(id)
      case Iff(l,r) => Iff(visitExpr(l),visitExpr(r))
      case Implies(l,r) => Implies(visitExpr(l),visitExpr(r))
      case Not(e) => Not(visitExpr(e))
      case And(l,r) => And(visitExpr(l),visitExpr(r))
      case Or(l,r) => Or(visitExpr(l),visitExpr(r))
      case Eq(l,r) => Eq(visitExpr(l),visitExpr(r))
      case NotEq(l,r) => NotEq(visitExpr(l),visitExpr(r))
      case AtLeast(l,r) => AtLeast(visitExpr(l),visitExpr(r))
      case AtMost(l,r) => AtMost(visitExpr(l),visitExpr(r))
      case Less(l,r) => Less(visitExpr(l),visitExpr(r))
      case Greater(l,r) => Greater(visitExpr(l),visitExpr(r))
      case Plus(l,r) => Plus(visitExpr(l),visitExpr(r))
      case Minus(l,r) => Minus(visitExpr(l),visitExpr(r))
      case Times(l,r) => Times(visitExpr(l),visitExpr(r))
      case Div(l,r) => Div(visitExpr(l),visitExpr(r))
      case Mod(l,r) => Mod(visitExpr(l),visitExpr(r))
      case RShift(l,r) => RShift(visitExpr(l),visitExpr(r))
      case LShift(l,r) => LShift(visitExpr(l),visitExpr(r))
      case UnMinus(e) => UnMinus(visitExpr(e))
      case IfThenElse(c,t,e) => IfThenElse(visitExpr(c),visitExpr(t),visitExpr(e))
      case Forall(v,e,None) => Forall(v,visitExpr(e),None)
      case Forall(v,e,Some(p)) => Forall(v,visitExpr(e),Some(visitExpr(p)))
      case Exists(v,e,None) => Exists(v,visitExpr(e),None)
      case Exists(v,e,Some(p)) => Exists(v,visitExpr(e),Some(visitExpr(p)))
      case IndexAccessor(l,i) => IndexAccessor(visitExpr(l),visitExpr(i))
      case FunctionApp(n,args) => FunctionApp(n,visitExpr(args))
      case is: IndexSymbol =>
        is.indexedExpr = visitExpr(is.indexedExpr); is
      case il: IntLiteral => il
      case bl: BoolLiteral => bl
      case fl: FloatLiteral => fl
    }
    newExpr.typ = expr.typ
    newExpr
  }
  
  def visitAssignable(asgn: Assignable)(implicit map: Map[A,B]): Assignable = {
    asgn match {
      case id: Id => visitId(id)
    }
  }
  
  def visitId(id: Id)(implicit map: Map[A,B]): Id = {
    id
  }
}
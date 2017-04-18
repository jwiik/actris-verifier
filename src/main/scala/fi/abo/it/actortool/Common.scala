package fi.abo.it.actortool

import scala.collection.mutable.ListBuffer

/**
 * @author Jonatan Wiik
 */

object Elements {
  def rd(id: String, chType: ChanType) = {
    val fa = FunctionApp("rd",List(makeId(id,chType): Expr))
    fa.typ = IntType(-1)
    fa
  }
  def tot(id: String, chType: ChanType) = {
    val fa = FunctionApp("tot",List(makeId(id,chType): Expr))
    fa.typ = IntType(-1)
    fa
  }
  def bullet(id: String, chType: ChanType) = {
    val fa = FunctionApp("str",List(makeId(id,chType): Expr))
    fa.typ = IntType(-1)
    fa
  }
  def rdb(id: String, chType: ChanType) = {
    val fa = FunctionApp("rd@",List(makeId(id,chType): Expr))
    fa.typ = IntType(-1)
    fa
  }
  def totb(id: String, chType: ChanType) = {
    val fa = FunctionApp("tot@",List(makeId(id,chType): Expr))
    fa.typ = IntType(-1)
    fa
  }
  
  def ch(name: String, carriedType: Type) = {
    val i = Id(name)
    i.typ = ChanType(carriedType)
    i
  }
  
  def chAcc(ch: Id, idx: Expr) = {
    val t = ch.typ.asInstanceOf[ChanType].contentType
    val ia = IndexAccessor(ch,idx)
    ia.typ = t
    ia
  }
  
  def lit(i: Int) = { val li = IntLiteral(i); li.typ = IntType(-1); li}
  
  def makeId(id: String, t: Type) = { val i = Id(id); i.typ = t; i }
} 

object TypeUtil {

  def getLub(t1: Type, t2: Type): Option[Type] = {
    if (t1.isBool && t2.isBool) return Some(BoolType)
    else if (t1.isSignedInt && t2.isSignedInt) 
      return Some(IntType(math.max(t1.asInstanceOf[IntType].size, t2.asInstanceOf[IntType].size)))
    else if (t1.isUnsignedInt && t2.isUnsignedInt) 
      return Some(UintType(math.max(t1.asInstanceOf[UintType].size, t2.asInstanceOf[UintType].size)))
    else if (t1.isSignedInt && t2.isUnsignedInt) {
      val si = t1.asInstanceOf[IntType].size
      val su = t2.asInstanceOf[UintType].size
      return Some(if (si > su) IntType(si) else IntType(su + 1))
    } else if (t1.isUnsignedInt && t2.isSignedInt) {
      val su = t1.asInstanceOf[UintType].size
      val si = t2.asInstanceOf[IntType].size
      return Some(if (si > su) IntType(si) else IntType(su + 1))
    }
    else if (t1.isBv && t2.isBv) {
      val su = t1.asInstanceOf[BvType].size
      val si = t2.asInstanceOf[BvType].size
      if (su == si) Some(t1) else None
    } else return None
  }

  def getGlb(t1: Type, t2: Type): Option[Type] = {
    if (t1.isBool && t2.isBool) return Some(BoolType)
    else if (t1.isSignedInt && t2.isSignedInt) 
      return Some(IntType(math.min(t1.asInstanceOf[IntType].size, t2.asInstanceOf[IntType].size)))
    else if (t1.isUnsignedInt && t2.isUnsignedInt) 
      return Some(UintType(math.min(t1.asInstanceOf[UintType].size, t2.asInstanceOf[UintType].size)))
    else if (t1.isSignedInt && t2.isUnsignedInt) {
      val si = t1.asInstanceOf[IntType].size
      val su = t2.asInstanceOf[UintType].size
      return Some(if (si > su) IntType(su + 1) else IntType(si))
    } else if (t1.isUnsignedInt && t2.isSignedInt) {
      val su = t1.asInstanceOf[UintType].size
      val si = t2.asInstanceOf[IntType].size
      return Some(if (si > su) IntType(su + 1) else IntType(si))
    } else return None
  }

  def isCompatible(t1: Type, t2: Type): Boolean = 
    (t1.isBool && t2.isBool) || 
    (t1.isInt && t2.isInt) ||
    (t1.isBv && t2.isBv && t1.asInstanceOf[BvType].size == t2.asInstanceOf[BvType].size) ||
    (t1.isIndexed && t2.isIndexed && 
        isCompatible(t1.asInstanceOf[ListType].resultType, t2.asInstanceOf[ListType].resultType) && 
        isCompatible(t1.asInstanceOf[ListType].indexType, t2.asInstanceOf[ListType].indexType) &&
        t1.asInstanceOf[ListType].size == t2.asInstanceOf[ListType].size) ||
    (t1.isRef && t2.isRef && t1.asInstanceOf[RefType].id == t2.asInstanceOf[RefType].id)
  
  def getSize(n: Long): Int = {
    if (n == 0) { 1 }
    else {
      val bitLength = java.math.BigInteger.valueOf(n).bitLength
      if (n > 0) bitLength else bitLength + 1
    }
  }

  def createIntOrUint(n: Long) = {
    if (n >= 0) UintType( -1 /*getSize(n)*/)
    else IntType( -1 /*getSize(n)*/)
  }

}

object ConjunctionSplitter extends ASTVisitor[ListBuffer[Expr]] {
  
  def split(expr: Expr): List[Expr] = {
    val buffer = new ListBuffer[Expr]
    visitExpr(expr)(buffer);
    buffer.toList
  }
  
  override def visitExpr(expr: Expr)(implicit conjs: ListBuffer[Expr]) {
    expr match {
      case And(left,right) => visitExpr(left); visitExpr(right)
      case x => conjs += x 
    }
  }
}




object IdReplacer extends ASTReplacingVisitor[Id, Expr] {
  override def visitExpr(expr: Expr)(implicit map: Map[Id, Expr]): Expr = {
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

object IdToIdReplacer extends ASTReplacingVisitor[Id, Id] {
  override def visitId(id: Id)(implicit map: Map[Id, Id]): Id = {
    val replacement = map.get(id) match {
      case None        => id
      case Some(newId) => newId
    }
    replacement.typ = id.typ
    replacement
  }
}

object TokensDefFinder extends ASTVisitor[ListBuffer[(String, Expr)]] {
  override def visitExpr(expr: Expr)(implicit info: ListBuffer[(String, Expr)]) {
    expr match {
      case delay @ FunctionApp("delay", params) => {
        val (ch, amount) = (params(0), params(1))
        info += ((ch.asInstanceOf[Id].id, amount))
      }
      case _ =>
    }
    super.visitExpr(expr)
  }
}

abstract class ASTVisitor[T] {

  def visitStmt(stmt: List[Stmt])(implicit info: T) { for (s <- stmt) visitStmt(s) }

  def visitStmt(stmt: Stmt)(implicit info: T) {
    stmt match {
      case Assign(id, exp)             => visitExpr(id); visitExpr(exp)
      case MapAssign(id, exp)          => visitExpr(id); visitExpr(exp)
      case Assert(e)                   => visitExpr(e)
      case Assume(e)                   => visitExpr(e)
      case Havoc(vars)                 => for (v <- vars) visitId(v)
      case IfElse(ifc, ifs, eifs, els) =>
        visitExpr(ifc); visitStmt(ifs); visitIfElses(eifs); visitStmt(els)
      case While(c, inv, s)            => visitExpr(c); visitExpr(inv); visitStmt(s)
    }
  }

  def visitIfElses(eifs: List[ElseIf])(implicit info: T) {
    for (eif <- eifs) yield eif match {
      case ElseIf(c, s) => visitExpr(c); visitStmt(s)
    }
  }

  def visitExpr(expr: List[Expr])(implicit info: T) { for (e <- expr) yield visitExpr(e) }

  def visitExpr(expr: Expr)(implicit info: T) {
    expr match {
      case id: Id => visitId(id)
      case Iff(l, r) =>
        visitExpr(l); visitExpr(r)
      case Implies(l, r) =>
        visitExpr(l); visitExpr(r)
      case Not(e) => visitExpr(e)
      case And(l, r) =>
        visitExpr(l); visitExpr(r)
      case Or(l, r) =>
        visitExpr(l); visitExpr(r)
      case Eq(l, r) =>
        visitExpr(l); visitExpr(r)
      case NotEq(l, r) =>
        visitExpr(l); visitExpr(r)
      case AtLeast(l, r) =>
        visitExpr(l); visitExpr(r)
      case AtMost(l, r) =>
        visitExpr(l); visitExpr(r)
      case Less(l, r) =>
        visitExpr(l); visitExpr(r)
      case Greater(l, r) =>
        visitExpr(l); visitExpr(r)
      case Plus(l, r) =>
        visitExpr(l); visitExpr(r)
      case Minus(l, r) =>
        visitExpr(l); visitExpr(r)
      case Times(l, r) =>
        visitExpr(l); visitExpr(r)
      case Div(l, r) =>
        visitExpr(l); visitExpr(r)
      case Mod(l, r) =>
        visitExpr(l); visitExpr(r)
      case LShift(l, r) =>
        visitExpr(l); visitExpr(r)
      case RShift(l, r) =>
        visitExpr(l); visitExpr(r)
      case BwAnd(l,r) => visitExpr(l); visitExpr(r)
      case BwOr(l,r) => visitExpr(l); visitExpr(r)
      case BwXor(l,r) => visitExpr(l); visitExpr(r)
      case BwNot(l) => visitExpr(l)
      case UnMinus(e) => visitExpr(e)
      case IfThenElse(c, t, e) =>
        visitExpr(c); visitExpr(t); visitExpr(e)
      case Forall(v, e, None) => visitExpr(e)
      case Forall(v, e, Some(p)) => visitExpr(e); visitExpr(p)
      case Exists(v, e, None) => visitExpr(e)
      case Exists(v, e, Some(p)) => visitExpr(e); visitExpr(p)
      case IndexAccessor(l, i) => visitExpr(l); visitExpr(i)
      case FieldAccessor(e, f) => visitExpr(e)
      case FunctionApp(n, args) => visitExpr(args)
      case ListLiteral(els) => for (e <- els) visitExpr(e)
      case il: IntLiteral =>
      case hxl: HexLiteral =>
      case bl: BoolLiteral =>
      case fl: FloatLiteral =>
      case sm: SpecialMarker =>
    }
  }

  def visitId(id: Id)(implicit info: T) {}
}

abstract class ASTReplacingVisitor[A <: ASTNode, B <: ASTNode] {
  def visitStmt(stmt: List[Stmt])(implicit map: Map[A, B]): List[Stmt] = {
    for (s <- stmt) yield visitStmt(s)
  }

  def visitStmt(stmt: Stmt)(implicit map: Map[A, B]): Stmt = {
    stmt match {
      case Assign(id, exp)             => Assign(visitId(id), visitExpr(exp))
      case MapAssign(exp1, exp2)       => MapAssign(visitExpr(exp1), visitExpr(exp2))
      case Assert(e)                   => Assert(visitExpr(e))
      case Assume(e)                   => Assume(visitExpr(e))
      case Havoc(vars)                 => Havoc(for (v <- vars) yield visitId(v))
      case IfElse(ifc, ifs, eifs, els) => IfElse(visitExpr(ifc), visitStmt(ifs), visitIfElses(eifs), visitStmt(els))
      case While(c, inv, s)            => While(visitExpr(c), visitExpr(inv), visitStmt(s))
    }
  }

  def visitIfElses(eifs: List[ElseIf])(implicit map: Map[A, B]): List[ElseIf] = {
    for (eif <- eifs) yield eif match {
      case ElseIf(c, s) => ElseIf(visitExpr(c), visitStmt(s))
    }
  }

  def visitExpr(expr: List[Expr])(implicit map: Map[A, B]): List[Expr] =
    for (e <- expr) yield visitExpr(e)

  def visitExpr(expr: Expr)(implicit map: Map[A, B]): Expr = {
    val newExpr = expr match {
      case id: Id                => visitId(id)
      case Iff(l, r)             => Iff(visitExpr(l), visitExpr(r))
      case Implies(l, r)         => Implies(visitExpr(l), visitExpr(r))
      case Not(e)                => Not(visitExpr(e))
      case And(l, r)             => And(visitExpr(l), visitExpr(r))
      case Or(l, r)              => Or(visitExpr(l), visitExpr(r))
      case Eq(l, r)              => Eq(visitExpr(l), visitExpr(r))
      case NotEq(l, r)           => NotEq(visitExpr(l), visitExpr(r))
      case AtLeast(l, r)         => AtLeast(visitExpr(l), visitExpr(r))
      case AtMost(l, r)          => AtMost(visitExpr(l), visitExpr(r))
      case Less(l, r)            => Less(visitExpr(l), visitExpr(r))
      case Greater(l, r)         => Greater(visitExpr(l), visitExpr(r))
      case Plus(l, r)            => Plus(visitExpr(l), visitExpr(r))
      case Minus(l, r)           => Minus(visitExpr(l), visitExpr(r))
      case Times(l, r)           => Times(visitExpr(l), visitExpr(r))
      case Div(l, r)             => Div(visitExpr(l), visitExpr(r))
      case Mod(l, r)             => Mod(visitExpr(l), visitExpr(r))
      case RShift(l, r)          => RShift(visitExpr(l), visitExpr(r))
      case LShift(l, r)          => LShift(visitExpr(l), visitExpr(r))
      case BwAnd(l, r)           => BwAnd(visitExpr(l), visitExpr(r))
      case BwOr(l, r)            => BwOr(visitExpr(l), visitExpr(r))
      case BwXor(l, r)           => BwXor(visitExpr(l), visitExpr(r))
      case BwNot(l)              => BwNot(visitExpr(l))
      case UnMinus(e)            => UnMinus(visitExpr(e))
      case IfThenElse(c, t, e)   => IfThenElse(visitExpr(c), visitExpr(t), visitExpr(e))
      case Forall(v, e, None)    => Forall(v, visitExpr(e), None)
      case Forall(v, e, Some(p)) => Forall(v, visitExpr(e), Some(visitExpr(p)))
      case Exists(v, e, None)    => Exists(v, visitExpr(e), None)
      case Exists(v, e, Some(p)) => Exists(v, visitExpr(e), Some(visitExpr(p)))
      case ia: IndexAccessor     => visitAssignable(ia)
      case fa: FieldAccessor     => visitAssignable(fa)
      case FunctionApp(n, args)  => FunctionApp(n, visitExpr(args))
      case ListLiteral(els)      => ListLiteral(for (e <- els) yield visitExpr(e))
      case il: IntLiteral   => il
      case hxl: HexLiteral  => hxl
      case bl: BoolLiteral  => bl
      case fl: FloatLiteral => fl
      case sm: SpecialMarker => sm 
    }
    newExpr.typ = expr.typ
    newExpr
  }
  
  def visitAssignable(asgn: Assignable)(implicit map: Map[A, B]): Assignable = {
    asgn match {
      case id: Id => visitId(id)
      case IndexAccessor(l, i)   => IndexAccessor(visitExpr(l), visitExpr(i))
      case FieldAccessor(e, f)   => FieldAccessor(visitExpr(e), f)
    }
  }

  def visitId(id: Id)(implicit map: Map[A, B]): Id = {
    id
  }
}
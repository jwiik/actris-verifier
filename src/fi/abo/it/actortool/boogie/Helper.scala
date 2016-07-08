package fi.abo.it.actortool.boogie

import scala.util.parsing.input.Position
//import fi.abo.it.actortool.boogie.Boogie
//import fi.abo.it.actortool.boogie.Boogie.DeclComment
import fi.abo.it.actortool.boogie.Boogie.VarExpr
import fi.abo.it.actortool.boogie.Boogie.MapSelect
import fi.abo.it.actortool.boogie.Boogie.BType
import fi.abo.it.actortool.boogie.Boogie.NamedType
//import fi.abo.it.actortool.boogie.Boogie.LocalVar
//import fi.abo.it.actortool.boogie.Boogie.UnaryExpr
import fi.abo.it.actortool._


object BMap extends Enumeration {
  type BMap = String
  final val L = "L"
  final val C = "C"
  final val R = "R"
  final val M = "M"
  final val St = "St"
  final val SqnCh = "SqnCh"
  final val SqnActor = "SqnAct"
  final val This = "this#"
  final val BaseL = "Base#L"
}

object BType {
  def Chan(arg: BType) = Boogie.IndexedType("Chan", arg)
  def M = NamedType("MType")
  def C = NamedType("CType")
  def Bool = NamedType("bool");
  def Real = NamedType("real");
  def Int = NamedType("int");
  def BV(size: Int) = Boogie.BVType(size)
  def State = NamedType("State")
  def Actor = NamedType("Actor")
  def List(cType: BType) = Boogie.IndexedType("List", cType)
}

object Helper {
  import Boogie.Expr
  
  final val Sep = "#"
  
  def type2BType(t: Type)(implicit bvMode: Boolean): Boogie.BType = {
    assert(t != null)
    t match {
      case IntType(x) => if (bvMode) BType.BV(32) else BType.Int // BType.BV(x)
      case BoolType => BType.Bool
      case FloatType => BType.Real
      case HalfType => BType.Real
      case UintType(_) => if (bvMode) BType.BV(32) else BType.Int // BType.BV(x)
      case ChanType(contentType) => BType.Chan(type2BType(contentType))
      case ActorType(_) => BType.Actor
      case ListType(contentType,_) => BType.List(type2BType(contentType))
      case UnknownType =>
        assert(false, "Unknown types should not occur during the translation")
        null
    }
  }
  
  def bLocal(id: String, tp: Type)(implicit bvMode: Boolean) = new Boogie.LocalVar(id, type2BType(tp))
  def bLocal(id: String, tp: BType) = new Boogie.LocalVar(id, tp)
  def bThisDecl = bLocal(BMap.This,BType.Actor)
  
  def bBool(b: Boolean) = Boogie.BoolLiteral(b)
  
  def bInt(i: Int)(implicit bvMode: Boolean): Boogie.Expr = bInt(i.toString)
  
  def bInt(i: String)(implicit bvMode: Boolean) = {
    if (bvMode) Boogie.BVLiteral(i, 32)
    else Boogie.IntLiteral(i)
  }
  
  def bVar(id: String) = Boogie.VarExpr(id)
  
  def bAssert(e: Expr, pos: Position, msg: String) = new Boogie.Assert(e, pos, msg)
  def bAssert(e: Expr) = new Boogie.Assert(e,null,"Condition might not hold") 
  def bAssume(e: Expr) = Boogie.Assume(e)
  def bAssert2Assume(assert: Boogie.Assert) = new Boogie.Assume(assert.e)
 
  def bCredit(connName: String) = (VarExpr(BMap.C) apply VarExpr(connName))
  def bCredit(channel: Boogie.Expr) = (VarExpr(BMap.C) apply channel)
  
  def bCredInit(connName: String) = (VarExpr(BMap.L) apply VarExpr(connName))
  def bCredInit(channel: Boogie.Expr) = (VarExpr(BMap.L) apply channel)
  
  def bRead(connName: String) = (VarExpr(BMap.R) apply VarExpr(connName))
  def bRead(channel: Boogie.Expr) = (VarExpr(BMap.R) apply channel)
  
  def bTotal(connName: String)(implicit bvMode: Boolean) = (bRead(connName) plus bCredit(connName))
  def bTotal(channel: Boogie.Expr)(implicit bvMode: Boolean) = (bRead(channel) plus bCredit(channel))
  
  def bSqnCh(connName: String, ind: Boogie.Expr): Boogie.Expr = bSqnCh(VarExpr(connName),ind)
  def bSqnCh(channel: Boogie.Expr, ind: Boogie.Expr): Boogie.Expr = (VarExpr(BMap.SqnCh) apply channel) apply ind
  
  def bSqnAct(actorName: String): Boogie.Expr = bSqnAct(VarExpr(actorName))
  def bSqnAct(actor: Boogie.Expr): Boogie.Expr = (VarExpr(BMap.SqnActor) apply actor)
  
  def bSqn(ch: Boogie.Expr, ind: Boogie.Expr): Boogie.Expr = (VarExpr(BMap.SqnCh) apply ch) apply ind
  
  def bChannel(connName: String): Expr = (VarExpr(BMap.M) apply VarExpr(connName))
  def bChannelIdx(connName: String, ind: Boogie.Expr): Expr = ((VarExpr(BMap.M) apply VarExpr(connName)) apply ind)
  def bChannel(channel: Boogie.Expr): Expr = (VarExpr(BMap.M) apply channel)
  def bChannelIdx(channel: Boogie.Expr, ind: Boogie.Expr): Expr = ((VarExpr(BMap.M) apply channel) apply ind)
  
  def bState(id: String) = VarExpr(BMap.St) apply VarExpr(id)
  def bState(actor: Boogie.Expr) = VarExpr(BMap.St) apply actor
  val bThis = bState(BMap.This)
  val bBaseL = VarExpr(BMap.BaseL)
  
  def bFun(id: String, arg: Boogie.Expr*) = Boogie.FunctionApp(id,arg.toList)
  
  val intlst = VarExpr("AT#intlst");

}
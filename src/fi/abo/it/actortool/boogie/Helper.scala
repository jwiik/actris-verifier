package fi.abo.it.actortool.boogie

import scala.util.parsing.input.Position

import fi.abo.it.actortool.boogie.Boogie.VarExpr
import fi.abo.it.actortool.boogie.Boogie.BType
import fi.abo.it.actortool.boogie.Boogie.NamedType
import fi.abo.it.actortool._




object BMap extends Enumeration {
  type BMap = String
  final val C = "C"
  final val R = "R"
  final val M = "M"
  final val I = "I"
  final val T = "T"
  final val St = "St"
  final val SqnCh = "SqnCh"
  final val SqnActor = "SqnAct"
  final val This = "this#"
//  final val BaseL = "Base#L"
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

case class BDecl(val name: String, val decl: Boogie.LocalVar) {
  def this(name1: String, typ: Type) = this(name1, B.Local(name1, B.type2BType(typ)))
}
object BDecl {
  def apply(name1: String, typ: Type) = new BDecl(name1,typ)
}

object B {
  
  
  object AssertCount {
    private var i = -1
    def next = { i = i+1; "#"+(i.toString) }
  }
  
  final val Sep = "#"
  
  def type2BType(t: Type): Boogie.BType = {
    assert(t != null)
    t match {
      case IntType(x) =>  BType.Int // BType.BV(x)
      case BoolType => BType.Bool
      case FloatType => BType.Real
      case HalfType => BType.Real
      case UintType(_) => BType.Int // BType.BV(x)
      case ChanType(contentType) => BType.Chan(type2BType(contentType))
      case ActorType(_) => BType.Actor
      case ListType(contentType,_) => BType.List(type2BType(contentType))
      case UnknownType =>
        assert(false, "Unknown types should not occur during the translation")
        null
    }
  }
  
  def Local(id: String, tp: Type)(implicit bvMode: Boolean) = new Boogie.LocalVar(id, type2BType(tp))
  def Local(id: String, tp: BType) = new Boogie.LocalVar(id, tp)
  def ThisDecl = Local(BMap.This,BType.Actor)
  
  def Bool(b: Boolean) = Boogie.BoolLiteral(b)
  
  def Int(i: Int): Boogie.Expr = Int(i.toString)
  
  def Int(i: String) = {
    Boogie.IntLiteral(i)
  }
  
  def Var(id: String) = Boogie.VarExpr(id)
  
  def Assert(e: Boogie.Expr, pos: Position, msg: String): Boogie.Assert = 
    new Boogie.Assert(e, pos, msg + " (" + AssertCount.next + ")")
  def Assert(e: Boogie.Expr, msg: String): Boogie.Assert = Assert(e, null, msg)
  def Assert(e: Boogie.Expr): Boogie.Assert = Assert(e,null,"Condition might not hold") 
  def Assume(e: Boogie.Expr) = Boogie.Assume(e)
  def Assert2Assume(assert: Boogie.Assert) = new Boogie.Assume(assert.e)
 
  def C(channel: Boogie.Expr): Boogie.Expr = (VarExpr(BMap.C) apply channel)
  def R(channel: Boogie.Expr): Boogie.Expr = (VarExpr(BMap.R) apply channel)
  def I(channel: Boogie.Expr): Boogie.Expr = (VarExpr(BMap.I) apply channel)
  def T(channel: Boogie.Expr): Boogie.Expr = (VarExpr(BMap.T) apply channel)
  
  def R(channel: String): Boogie.Expr = R(Boogie.VarExpr(channel))
  def C(channel: String): Boogie.Expr = C(Boogie.VarExpr(channel))
  def I(channel: String): Boogie.Expr = I(Boogie.VarExpr(channel))
  def T(channel: String): Boogie.Expr = T(Boogie.VarExpr(channel))
  
  def Urd(channel: String): Boogie.Expr = C(channel) - R(channel)
  def Urd(channel: Boogie.Expr): Boogie.Expr = C(channel) - R(channel)
//  
//  def Read(channel: String): Boogie.Expr = R(channel)
//  def Read(channel: Boogie.Expr): Boogie.Expr = R(channel)
//  
//  def Total(channel: String)(implicit bvMode: Boolean): Boogie.Expr = C(channel)
//  def Total(channel: Boogie.Expr)(implicit bvMode: Boolean): Boogie.Expr = C(channel)
  
  def SqnCh(connName: String, ind: Boogie.Expr): Boogie.Expr = SqnCh(VarExpr(connName),ind)
  def SqnCh(channel: Boogie.Expr, ind: Boogie.Expr): Boogie.Expr = (VarExpr(BMap.SqnCh) apply channel) apply ind
  
  def SqnAct(actorName: String): Boogie.Expr = SqnAct(VarExpr(actorName))
  def SqnAct(actor: Boogie.Expr): Boogie.Expr = (VarExpr(BMap.SqnActor) apply actor)
  
  def Channel(connName: String): Boogie.Expr = (VarExpr(BMap.M) apply VarExpr(connName))
  def ChannelIdx(connName: String, ind: Boogie.Expr): Boogie.Expr = 
    ((VarExpr(BMap.M) apply VarExpr(connName)) apply ind)
  def Channel(channel: Boogie.Expr): Boogie.Expr = (VarExpr(BMap.M) apply channel)
  def ChannelIdx(channel: Boogie.Expr, ind: Boogie.Expr): Boogie.Expr = 
    ((VarExpr(BMap.M) apply channel) apply ind)
  
  def State(id: String) = VarExpr(BMap.St) apply VarExpr(id)
  def State(actor: Boogie.Expr) = VarExpr(BMap.St) apply actor
  
  def Fun(id: String, arg: Boogie.Expr*) = Boogie.FunctionApp(id,arg.toList)
  
  val This = State(BMap.This)
  //val BaseL = VarExpr(BMap.BaseL)
  val intlst = VarExpr("AT#intlst");
  
}
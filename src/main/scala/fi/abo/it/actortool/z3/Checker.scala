package fi.abo.it.actortool.z3

import z3.scala._
import fi.abo.it.actortool._
import fi.abo.it.actortool.util.ASTPrinter

trait Result {
  val result: Boolean
  def getResultInt(id: String): Option[Int]
  def getResultBool(id: String): Option[Boolean]
  def getResultHex(id: String): Option[Int]
  def getRawResult(id: String): Option[Z3AST]
  def getFunctionInterpretation(id: String): Option[(Seq[(Seq[Z3AST], Z3AST)], Z3AST)]
}

class Checker {
  
  val z3 = new Z3Context("MODEL" -> true)
  
  object Types {
    val Int = z3.mkIntSort
    val Chan = z3.mkIntSort
    def Bv(size: Int) = z3.mkBVSort(size)
  }
  
  
  
  class Z3ModelResult(val result: Boolean, val z3Model: Z3Model, z3Consts: Map[String,Z3AST], z3FuncDecls: Map[String,Z3FuncDecl]) extends Result {
    def getResultInt(id: String) = {
      val res = z3Model.eval(z3Consts(id), true)
      if (res.isDefined) z3Model.context.getNumeralInt(res.get).value
      else None
    }
    def getResultBool(id: String) = {
      val res = z3Model.eval(z3Consts(id), true)
      if (res.isDefined) z3Model.context.getBoolValue(res.get)
      else None
    }
    def getResultHex(id: String) = {
      val res = z3Model.eval(z3Consts(id), true)
      if (res.isDefined) {
        val str = z3Model.context.astToString(res.get)
        if (str.startsWith("#x")) Some(Integer.parseInt(str.drop(2), 16))
        else if (str.startsWith("#b")) Some(Integer.parseInt(str.drop(2), 2))
        else throw new RuntimeException(str)
      }
      else None
    }
    def getRawResult(id: String) = z3Model.eval(z3Consts(id), true)
    
    def getFunctionInterpretation(id: String) = {
      z3Model.getFuncInterpretation(z3FuncDecls(id))
    }
    
  }
  
  class Context(
      val z3Constants: Map[String,Z3AST], 
      val z3FuncDecls: Map[String,Z3FuncDecl])
  
  def getSatisfyingModel(
      constraints: List[Expr],
      ports: List[Declaration],
      constants: List[Declaration]): Result = {
    
    val solver = z3.mkSolver
    
    val ChanSort = z3.mkIntSort()
    
    val z3Constants = (constants.map { d => (d.id, z3.mkConst(d.id, transType(d.typ))) }).toMap
    val z3Ports = (ports.map { d => (d.id, z3.mkConst(d.id, transType(d.typ))) }).toMap
    
    val z3Funcs = 
      Map(
          "I#" -> z3.mkFuncDecl("I#", Types.Chan, Types.Int),
          "R#" -> z3.mkFuncDecl("R#", Types.Chan, Types.Int),
          "C#" -> z3.mkFuncDecl("C#", Types.Chan, Types.Int),
          "M#" -> z3.mkFuncDecl("M#", Seq(Types.Chan,Types.Int), Types.Int))
    
    val startCtx = new Context(z3Constants,z3Funcs)
    val z3ConstantConstraints = 
      (ports.map { d => z3.mkEq(z3Ports(d.id), transExpr(d.value.get)(startCtx) ) }) :::
      (constants.map { d => z3.mkEq(z3Constants(d.id), transExpr(d.value.get)(startCtx) ) })
    
    val funcAxioms = List(
        z3Ports.map { v => z3.mkLT(z3.mkInt(0, Types.Int), z3.mkApp(z3Funcs("I#"),v._2)) },
        z3Ports.map { v => z3.mkLT(z3.mkApp(z3Funcs("I#"),v._2), z3.mkApp(z3Funcs("R#"),v._2)) },
        z3Ports.map { v => z3.mkLT(z3.mkApp(z3Funcs("R#"),v._2), z3.mkApp(z3Funcs("C#"),v._2)) }
        ).flatten
    
    val allConstants = z3Constants++z3Ports
    val ctx = new Context(allConstants,z3Funcs)
    
    //val typeConstraints = z3Variables map { case (name,const) => getTypeConstraint(const, )  }
    val z3Constraints =  constraints map { c => transExpr(c)(ctx) }
    
    for (c <- z3ConstantConstraints) solver.assertCnstr(c)
    //for (c <- typeConstraints) solver.assertCnstr(c)
    for (c <- funcAxioms) solver.assertCnstr(c)
    for (c <- z3Constraints) solver.assertCnstr(c)
    
    solver.check match {
      case Some(true) => {
        val model = solver.getModel
        new Z3ModelResult(true,model,allConstants,z3Funcs)
      }
      case Some(false) => throw new RuntimeException()
      case None => throw new RuntimeException()
    }
  }
  
  def getTypeConstraint(const: Z3AST, tp: Type): Z3AST = {
    tp match {
      case IntType => 
        mkLimitPred(z3.mkInt(Int.MinValue, Types.Int), const, z3.mkInt(Int.MaxValue, Types.Int))
      case BvType(size,signed) => {
        mkBvLimitPred(
            z3.mkNumeral((-scala.math.pow(2,size-1)).toString, Types.Bv(size)), 
            const, 
            z3.mkNumeral((scala.math.pow(2,size-1)-1).toString, Types.Bv(size)),
            signed)
      }
    }
  }
  
  def mkBvLimitPred(min: Z3AST, v: Z3AST, max: Z3AST, signed: Boolean): Z3AST = 
    if (signed) z3.mkAnd(z3.mkBVSle(min,v),z3.mkBVSle(v,max))
    else z3.mkAnd(z3.mkBVUle(min,v),z3.mkBVUle(v,max))
  
  def mkLimitPred(min: Z3AST, v: Z3AST, max: Z3AST): Z3AST = 
    z3.mkAnd(z3.mkLE(min,v),z3.mkLE(v,max))
  
  def transType(tp: Type): Z3Sort = {
    tp match {
      case IntType => Types.Int
      case BvType(size,_) => Types.Bv(size)
    }
  }
  
  def transExpr(e: Expr)(implicit ctx: Context): Z3AST = {
    e match {
      case And(l,r) => z3.mkAnd(transExpr(l),transExpr(r))
      case Implies(l,r) => z3.mkImplies(transExpr(l),transExpr(r))
      case Less(l,r) => z3.mkLT(transExpr(l), transExpr(r))
      case AtMost(l,r) => z3.mkLE(transExpr(l), transExpr(r))
      case AtLeast(l,r) => z3.mkGE(transExpr(l), transExpr(r))
      case BwAnd(l,r) => z3.mkBVAnd(transExpr(l), transExpr(r))
      case Eq(l,r) => z3.mkEq(transExpr(l), transExpr(r))
      case NotEq(l,r) => z3.mkNot(z3.mkEq(transExpr(l), transExpr(r)))
      case UnMinus(e) => z3.mkUnaryMinus(transExpr(e))
      case Plus(l,r) => z3.mkAdd(transExpr(l),transExpr(r))
      case Minus(l,r) => z3.mkSub(transExpr(l),transExpr(r))
      case IntLiteral(i) => z3.mkInt(i, Types.Int)
      case hx@HexLiteral(i) => z3.mkNumeral(Integer.parseInt(i, 16).toString, transType(hx.typ))
      case FunctionApp("int2bv",List(IntLiteral(i),IntLiteral(s))) => z3.mkInt(i,Types.Bv(s))
      case Id(id) => ctx.z3Constants(id)
//      case IndexAccessor(Id(id),SpecialMarker("@")) => {
//        val z3Id = ctx.inputNamings((id,0))
//        ctx.z3Consts(z3Id)
//      }
//      case IndexAccessor(Id(id),Plus(SpecialMarker("@"),IntLiteral(i))) => {
//        val z3Id = ctx.inputNamings((id,i))
//        ctx.z3Consts(z3Id)
//      }
      case IndexAccessor(id,idx) => z3.mkApp(ctx.z3FuncDecls("M#"), List(transExpr(id),transExpr(idx)):_*)
      case FunctionApp("@",args) => z3.mkApp(ctx.z3FuncDecls("I#"), (args map transExpr):_*)
      case sm@SpecialMarker("@") => {
        val name = sm.extraData("accessor").asInstanceOf[String]
        z3.mkApp(ctx.z3FuncDecls("I#"), ctx.z3Constants(name))
      }
    }
  }
  
}
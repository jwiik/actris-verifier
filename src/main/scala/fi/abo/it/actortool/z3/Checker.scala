package fi.abo.it.actortool.z3

import z3.scala._
import fi.abo.it.actortool._

class Checker {
  
  val z3 = new Z3Context("MODEL" -> true)
  
  object Types {
    val Int = z3.mkIntSort
    def Bv(size: Int) = z3.mkBVSort(size)
  }
  
  trait Result {
    val result: Boolean
    def getResultInt(id: String): Option[Int]
    def getResultBool(id: String): Option[Boolean]
    def getResultHex(id: String): Option[Int]
    def getRawResult(id: String): Option[Z3AST]
  }
  
  class Z3ModelResult(val result: Boolean, val z3Model: Z3Model, z3Consts: Map[String,Z3AST]) extends Result {
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
  }
  
  class Context(val inputNamings: Map[(String,Int),String], val inputTypes: Map[String,Type], val z3Consts: Map[String,Z3AST])
  
  def getSatisfyingModel(
      constraints: List[Expr],
      constants: List[Declaration],
      inputNamings: Map[(String,Int),String], 
      inputTypes: Map[String,Type]): Result = {
    
    val solver = z3.mkSolver
    
    val variables = inputNamings.values
    
    
    val z3Constants = (constants.map { d => (d.id, z3.mkConst(d.id, transType(d.typ))) }).toMap
    
    val startCtx = new Context(inputNamings,inputTypes,Map.empty)
    val z3ConstantConstraints = (constants.map { d => z3.mkEq(z3Constants(d.id), transExpr(d.value.get)(startCtx) ) })
    
    val z3Variables = (variables.map { id => (id, z3.mkConst(id, transType(inputTypes(id)))) }).toList
    
    val z3AllVariables = (z3Constants ++ z3Variables.toMap)
    
    val ctx = new Context(inputNamings,inputTypes,z3AllVariables)
    
    val typeConstraints = z3Variables map { case (name,const) => getTypeConstraint(const, inputTypes(name))  }
    val z3Constraints =  constraints map { c => transExpr(c)(ctx) }
    
    for (c <- z3ConstantConstraints) solver.assertCnstr(c)
    for (c <- typeConstraints) solver.assertCnstr(c)
    for (c <- z3Constraints) solver.assertCnstr(c)
    
    
    solver.check match {
      case Some(true) => {
        val model = solver.getModel
        new Z3ModelResult(true,model,z3AllVariables)
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
      case AtMost(l,r) => z3.mkLE(transExpr(l), transExpr(r))
      case BwAnd(l,r) => z3.mkBVAnd(transExpr(l), transExpr(r))
      case Eq(l,r) => z3.mkEq(transExpr(l), transExpr(r))
      case NotEq(l,r) => z3.mkNot(z3.mkEq(transExpr(l), transExpr(r)))
      case UnMinus(e) => z3.mkUnaryMinus(transExpr(e))
      case IntLiteral(i) => z3.mkInt(i, Types.Int)
      case hx@HexLiteral(i) => z3.mkNumeral(Integer.parseInt(i, 16).toString, transType(hx.typ))
      case FunctionApp("int2bv",List(IntLiteral(i),IntLiteral(s))) => z3.mkInt(i,Types.Bv(s))
      case Id(id) => ctx.z3Consts(id)
      case IndexAccessor(Id(id),SpecialMarker("@")) => {
        val z3Id = ctx.inputNamings((id,0))
        ctx.z3Consts(z3Id)
      }
      case IndexAccessor(Id(id),Plus(SpecialMarker("@"),IntLiteral(i))) => {
        val z3Id = ctx.inputNamings((id,i))
        ctx.z3Consts(z3Id)
      }
    }
  }
  
}
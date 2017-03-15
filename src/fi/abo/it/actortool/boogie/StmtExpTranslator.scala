package fi.abo.it.actortool.boogie

import fi.abo.it.actortool._
import scala.collection.mutable.ListBuffer
import fi.abo.it.actortool.boogie.Boogie.UnaryExpr
import fi.abo.it.actortool.ActorTool.TranslationException

class StmtExpTranslator(val ftMode: Boolean) {
  /*
   * Translation of statements and expressions
   */
  
  private class Context(val renamings: Map[String,Expr]) {
    private val wfChecks = new ListBuffer[Boogie.Expr]
    def addAssertion(e: Boogie.Expr) { wfChecks += e }
    def getAssertions = wfChecks.toList map { e => B.Assert(e) }
    def childContext = new Context(renamings)
  }
  
  def transStmt(stmts: List[Stmt])(implicit renamings: Map[String,Expr]): List[Boogie.Stmt] = {
    transStmtI(stmts)(new Context(renamings))
  }
  
  def transExpr(exp: Expr)(implicit renamings: Map[String,Expr]): Boogie.Expr = {
    transExprI(exp)(new Context(renamings))
  }

  def transStmtI(stmts: List[Stmt])(implicit context: Context): List[Boogie.Stmt] = {
    val bStmts = new ListBuffer[Boogie.Stmt]()
    for (s <- stmts) {
      val ctx = context.childContext
      bStmts ++= (s match {
        case Assign(id,exp) => {
          val stmt = List(Boogie.Assign(transExprI(id),transExprI(exp)))
          ctx.getAssertions ::: stmt
        }
        case MapAssign(e1,e2) => {
          BoogiePrelude.addComponent(MapPL)
          val elem = transExprI(e2)(ctx)
          val acc = e1.asInstanceOf[IndexAccessor]
          val map = acc.exp
          val index = acc.suffix
          val stmt = 
            List(Boogie.Assign(transExprI(map)(ctx),B.Fun("Map#Store",transExprI(map)(ctx),transExprI(index)(ctx),elem)))
          ctx.getAssertions ::: stmt
        }
        case Assert(e) => {
          val stmt = List(B.Assert(transExprI(e)(ctx), e.pos, "Condition might not hold"))
          ctx.getAssertions ::: stmt
        }
        case Assume(e) => {
          val stmt = List(B.Assume(transExprI(e)(ctx)))
          ctx.getAssertions ::: stmt
        }
        case Havoc(ids) => {
          val s = (for (i <- ids) yield {
            assert(false) // Havoc should not appear in bodies
            if (i.typ.isRef) {
              Boogie.Havoc(Boogie.VarExpr(BMap.H))
            }
            else {
              Boogie.Havoc(transExprI(i)(ctx)) 
            }
          })
          ctx.getAssertions ::: s
        }
        case IfElse(ifCond,ifStmt,elseIfs,elseStmt) => {
          if (!elseIfs.isEmpty) {
            throw new RuntimeException("If-statements with else-if branches not supported yet")
          }
          val stmt = List(Boogie.If(transExprI(ifCond)(ctx),transStmtI(ifStmt)(ctx),transStmtI(elseStmt)(ctx)))
          ctx.getAssertions ::: stmt
        }
        case While(_,_,_) =>
          throw new RuntimeException("Loops not supported yet")
          
      })
    }
    bStmts.toList
  }
  
  
  def transExprI(exp: Expr)(implicit context: Context): Boogie.Expr = {
    //println(exp)
    assert(exp.typ != null, exp.toString)
    exp match {
      case And(e1,e2) => transExprI(e1) && transExprI(e2)
      case Or(e1,e2) => transExprI(e1) || transExprI(e2)
      case Implies(e1,e2) => transExprI(e1) ==> transExprI(e2)
      case Iff(e1,e2) => transExprI(e1) <==> transExprI(e2)
      case Not(e) => UnaryExpr("!",transExprI(e)) 
      case Less(e1,e2) =>
        if (e1.typ.isBv) B.Fun("AT#BvUlt",transExprI(e1),transExprI(e2)) 
        else transExprI(e1) < transExprI(e2)
      case Greater(e1,e2) => transExprI(e1) > transExprI(e2)
      case AtLeast(e1,e2) => transExprI(e1) >= transExprI(e2)
      case AtMost(e1,e2) => 
        if (e1.typ.isBv) B.Fun("AT#BvUle",transExprI(e1),transExprI(e2)) 
        else transExprI(e1) <= transExprI(e2)
      case Eq(e1,e2) => transExprI(e1) ==@ transExprI(e2)
      case NotEq(e1,e2) => transExprI(e1) !=@ transExprI(e2)
      case Plus(e1,e2) => 
        if (e1.typ.isBv) B.Fun("AT#BvAdd",transExprI(e1),transExprI(e2)) 
        else transExprI(e1) + transExprI(e2)
      case Minus(e1,e2) =>
        if (e1.typ.isBv) B.Fun("AT#BvSub",transExprI(e1),transExprI(e2)) 
        else transExprI(e1) - transExprI(e2)
      case Times(e1,e2) => transExprI(e1) * transExprI(e2)
      case Div(e1,e2) => 
        BoogiePrelude.addComponent(DivModAbsPL)
        Boogie.FunctionApp("AT#Div",List(transExprI(e1),transExprI(e2)))
        //transExpr(e1) / transExpr(e2)
      case Mod(e1,e2) =>
        BoogiePrelude.addComponent(DivModAbsPL)
        Boogie.FunctionApp("AT#Mod",List(transExprI(e1),transExprI(e2)))
        //transExpr(e1) % transExpr(e2)
      case rsh@RShift(e1,e2) =>
        if (rsh.typ.isBv) {
          getBitVectorFunction("AT#BvLshr", List(transExprI(e1),transExprI(e2)), rsh.typ)
        }
        else {
          BoogiePrelude.addComponent(BitwisePL)
          Boogie.FunctionApp("AT#RShift",List(transExprI(e1),transExprI(e2)))
        }
      case lsh@LShift(e1,e2) =>
        if (lsh.typ.isBv) {
          getBitVectorFunction("AT#BvShl", List(transExprI(e1),transExprI(e2)), lsh.typ)
        }
        else {
          BoogiePrelude.addComponent(BitwisePL)
          Boogie.FunctionApp("AT#LShift",List(transExprI(e1),transExprI(e2)))
        }
        
      case op@BwAnd(e1,e2) =>
        getBitVectorFunction("AT#BvAnd", List(transExprI(e1),transExprI(e2)), op.typ)
      case op@BwOr(e1,e2) =>
        getBitVectorFunction("AT#BvOr", List(transExprI(e1),transExprI(e2)), op.typ)
      case op@BwXor(e1,e2) =>
        getBitVectorFunction("AT#BvXor", List(transExprI(e1),transExprI(e2)), op.typ)
      case op@BwNot(e) =>
        getBitVectorFunction("AT#BvNot", List(transExprI(e)), op.typ)
      case UnMinus(e) => UnaryExpr("-",transExprI(e))
      case IfThenElse(c,e1,e2) => Boogie.Ite(transExprI(c),transExprI(e1),transExprI(e2))
      case Forall(vars,e,pat) => 
        Boogie.Forall(Nil,
          for (v <- vars) yield Boogie.BVar(v.id, B.type2BType(v.typ)),
          pat match {
            case None => Nil
            case Some(p) => List(Boogie.Trigger(List(transExprI(p))))
          },
          transExprI(e)
        )
      case Exists(vars,e,pat) => 
        Boogie.Exists(Nil,
          for (v <- vars) yield Boogie.BVar(v.id,B.type2BType(v.typ)),
          pat match {
            case None => Nil
            case Some(p) => List(Boogie.Trigger(List(transExprI(p))))
          },
          transExprI(e)
        )
      case fa@FunctionApp(name,params) => {
        name match {
          case "rd" => B.R(transExprI(params(0)))
          case "urd" => B.C(transExprI(params(0))) - B.R(transExprI(params(0)))
          case "tot" => B.C(transExprI(params(0)))
          case "rd@" => B.R(transExprI(params(0))) - B.I(transExprI(params(0)))
          case "tot@" => B.C(transExprI(params(0))) - B.I(transExprI(params(0)))
          case "str" => B.I(transExprI(params(0)))
          case "@" => B.I(transExprI(params(0)))
          case "next" => 
            val ch = transExprI(params(0))
            if (fa.parameters.size > 1) B.ChannelIdx(ch,B.R(ch) minus transExprI(params(1)))
            else B.ChannelIdx(ch,B.R(ch))
          case "prev" => 
            val ch = transExprI(params(0))
            if (fa.parameters.size > 1) B.ChannelIdx(ch,B.R(ch) - transExprI(params(1)))
            else B.ChannelIdx(ch,B.R(ch) - B.Int(1))
          case "last" => 
            val ch = transExprI(params(0))
            if (fa.parameters.size > 1) B.ChannelIdx(ch, B.C(ch) - transExprI(params(1)))
            else B.ChannelIdx(ch, B.C(ch) - B.Int(1))
          case "history" => 
            val ch = transExprI(params(0))
            generateRangePredicate(params, B.Int(0), B.I(ch))
          case "current" => 
            val ch = transExprI(params(0))
            generateRangePredicate(params, B.I(ch), B.C(ch))
          case "every" => 
            val ch = transExprI(params(0))
            generateRangePredicate(params, B.Int(0), B.C(ch)) 
          case "tokens" =>
            B.C(transExprI(params(0))) - B.R(transExprI(params(0))) ==@ transExprI(params(1))
          case "min" => {
            Boogie.FunctionApp("AT#Min", params.map(p => transExprI(p)))
          }
          case "subvar" => {
            Boogie.VarExpr("AV" + B.Sep + params(0).asInstanceOf[Id].id + B.Sep + params(1).asInstanceOf[Id].id)
          }
          case x => {
            // User-defined function
            val args = params.map(p => transExprI(p))
            Boogie.FunctionApp("UDef"+B.Sep+x, args)
          }
        }
      }
      case IndexAccessor(e,i) => {
        val tExpr = transExprI(e)
        val index = transExprI(i)
        if (e.typ.isChannel) B.ChannelIdx(tExpr,index)
        if (e.typ.isMap) {
          //context.addAssertion(B.Bool(false))
          BoogiePrelude.addComponent(MapPL)
          B.Fun("Map#Select", tExpr,index)
        }
        else tExpr apply index
      }
      case FieldAccessor(e,f) => {
        val tExpr = transExprI(e)
        B.Field(tExpr, e.typ.asInstanceOf[RefType].id, f)
      }
      case ListLiteral(lst) => {
        var listlit: Boogie.Expr = B.intlst
        var i = 0
        for (e <- lst) {
          val transE = transExprI(e)
          listlit = Boogie.MapStore(listlit,B.Int(i),transE)
          i = i+1
        }
        listlit
      }

      case il@IntLiteral(i) =>
        if (il.typ.isBv) {
          assert(il.typ != null)
          val size = il.typ.asInstanceOf[AbstractIntType].size
          Boogie.BVLiteral(i.toString,32)
        }
        else B.Int(i)
        
        
      case hl@HexLiteral(x) => {
        //val bigInt = x.toList.map("0123456789abcdef".indexOf(_)).map(BigInt(_)).reduceLeft(_ * 16 + _)
        val bigInt = Integer.parseInt(x, 16)
        //B.Int(bigInt.toString) // To decimal conversion
        B.IntBV(bigInt.toString,hl.typ.asInstanceOf[BvType].size)
      }
      case BoolLiteral(b) => Boogie.BoolLiteral(b)
      case FloatLiteral(f) => Boogie.RealLiteral(f.toDouble)
      case sm@SpecialMarker(mark) => {
        val name = sm.extraData("accessor").asInstanceOf[String]
        val rename = context.renamings.getOrElse(name, {val i = Id(name); i.typ = sm.typ; i})
        val accessorName = transExprI(rename)
        mark match {
          case "@" => B.I(accessorName)
          case "next" => B.R(accessorName)
          case "prev" => B.R(accessorName) - B.Int(1)
          case "last" => B.C(accessorName) - B.Int(1)
        }
      }
      case id@Id(name) => context.renamings.get(name) match {
        case None => Boogie.VarExpr(name)
        case Some(replacement) => {
          //assert(replacement.typ == id.typ, replacement + ": " + replacement.typ + " -- " + id + ": " + id.typ)
          transExprI(replacement)
        }
      } 
    }
  }
  
  def generateRangePredicate(params: List[Expr], start: Boogie.Expr, end: Boogie.Expr)(implicit context: Context) = {
    if (params.size == 2) {
      val ch = transExprI(params(0))
      val ind = transExprI(params(1))
      start <= ind && ind < end
    }
    else if (params.size == 4) {
      val ch = transExprI(params(0))
      val ind = transExprI(params(1))
      val off1 = transExprI(params(2))
      val off2 = transExprI(params(3))
      start+off1 <= ind && ind < end-off2
    }
    else {
      // Should have been caught in resolver already
      throw new RuntimeException()
    }
  }
  
  def getBitVectorFunction(name: String, args: List[Boogie.Expr], typ: Type) = {
    val size = typ.asInstanceOf[BvType].size
    BoogiePrelude.addComponent(BitvectorPL.createPL(size))
    Boogie.FunctionApp(name+size,args)
  }
}
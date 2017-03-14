package fi.abo.it.actortool.boogie

import fi.abo.it.actortool._
import scala.collection.mutable.ListBuffer
import fi.abo.it.actortool.boogie.Boogie.UnaryExpr
import fi.abo.it.actortool.ActorTool.TranslationException

class StmtExpTranslator(val ftMode: Boolean) {
  /*
   * Translation of statements and expressions
   */

  def transStmt(stmts: List[Stmt])(implicit renamings: Map[String,Expr]): List[Boogie.Stmt] = {
    val bStmts = new ListBuffer[Boogie.Stmt]()
    for (s <- stmts) {
      bStmts ++= (s match {
        case Assign(id,exp) => List(Boogie.Assign(transExpr(id),transExpr(exp)))
        case Assert(e) => List(B.Assert(transExpr(e), e.pos, "Condition might not hold"))
        case Assume(e) => List(B.Assume(transExpr(e)))
        case Havoc(ids) => for (i <- ids) yield {
          assert(false) // Havoc should not appear in bodies
          if (i.typ.isRef) {
            Boogie.Havoc(Boogie.VarExpr(BMap.H))
          }
          else {
            Boogie.Havoc(transExpr(i)) 
          }
        }
        case IfElse(ifCond,ifStmt,elseIfs,elseStmt) => {
          if (!elseIfs.isEmpty) {
            throw new RuntimeException("If-statements with else-if branches not supported yet")
          }
          List(Boogie.If(transExpr(ifCond),transStmt(ifStmt),transStmt(elseStmt)))
        }
        case While(_,_,_) =>
          throw new RuntimeException("Loops not supported yet")
          
      })
    }
    bStmts.toList
  }
  
  
  def transExpr(exp: Expr)(implicit renamings: Map[String,Expr]): Boogie.Expr = {
    //println(exp)
    assert(exp.typ != null, exp.toString)
    exp match {
      case And(e1,e2) => transExpr(e1) && transExpr(e2)
      case Or(e1,e2) => transExpr(e1) || transExpr(e2)
      case Implies(e1,e2) => transExpr(e1) ==> transExpr(e2)
      case Iff(e1,e2) => transExpr(e1) <==> transExpr(e2)
      case Not(e) => UnaryExpr("!",transExpr(e)) 
      case Less(e1,e2) =>
        if (e1.typ.isBv) B.Fun("AT#BvUlt",transExpr(e1),transExpr(e2)) 
        else transExpr(e1) < transExpr(e2)
      case Greater(e1,e2) => transExpr(e1) > transExpr(e2)
      case AtLeast(e1,e2) => transExpr(e1) >= transExpr(e2)
      case AtMost(e1,e2) => 
        if (e1.typ.isBv) B.Fun("AT#BvUle",transExpr(e1),transExpr(e2)) 
        else transExpr(e1) <= transExpr(e2)
      case Eq(e1,e2) => transExpr(e1) ==@ transExpr(e2)
      case NotEq(e1,e2) => transExpr(e1) !=@ transExpr(e2)
      case Plus(e1,e2) => 
        if (e1.typ.isBv) B.Fun("AT#BvAdd",transExpr(e1),transExpr(e2)) 
        else transExpr(e1) + transExpr(e2)
      case Minus(e1,e2) =>
        if (e1.typ.isBv) B.Fun("AT#BvSub",transExpr(e1),transExpr(e2)) 
        else transExpr(e1) - transExpr(e2)
      case Times(e1,e2) => transExpr(e1) * transExpr(e2)
      case Div(e1,e2) => 
        BoogiePrelude.addComponent(DivModAbsPL)
        Boogie.FunctionApp("AT#Div",List(transExpr(e1),transExpr(e2)))
        //transExpr(e1) / transExpr(e2)
      case Mod(e1,e2) =>
        BoogiePrelude.addComponent(DivModAbsPL)
        Boogie.FunctionApp("AT#Mod",List(transExpr(e1),transExpr(e2)))
        //transExpr(e1) % transExpr(e2)
      case RShift(e1,e2) =>
        BoogiePrelude.addComponent(BitwisePL)
        Boogie.FunctionApp("AT#RShift",List(transExpr(e1),transExpr(e2)))
      case lsh@LShift(e1,e2) =>
        if (lsh.typ.isBv) {
          BoogiePrelude.addComponent(BitvectorPL.createPL(lsh.typ.asInstanceOf[BvType]))
          Boogie.FunctionApp("AT#BvShl",List(transExpr(e1),transExpr(e2)))
        }
        else {
          BoogiePrelude.addComponent(BitwisePL)
          Boogie.FunctionApp("AT#LShift",List(transExpr(e1),transExpr(e2)))
        }
        
      case BWAnd(e1,e2) =>
        BoogiePrelude.addComponent(BitwisePL)
        Boogie.FunctionApp("AT#BvAnd",List(transExpr(e1),transExpr(e2)))
      case UnMinus(e) => UnaryExpr("-",transExpr(e))
      case IfThenElse(c,e1,e2) => Boogie.Ite(transExpr(c),transExpr(e1),transExpr(e2))
      case Forall(vars,e,pat) => 
        Boogie.Forall(Nil,
          for (v <- vars) yield Boogie.BVar(v.id, B.type2BType(v.typ)),
          pat match {
            case None => Nil
            case Some(p) => List(Boogie.Trigger(List(transExpr(p))))
          },
          transExpr(e)
        )
      case Exists(vars,e,pat) => 
        Boogie.Exists(Nil,
          for (v <- vars) yield Boogie.BVar(v.id,B.type2BType(v.typ)),
          pat match {
            case None => Nil
            case Some(p) => List(Boogie.Trigger(List(transExpr(p))))
          },
          transExpr(e)
        )
      case fa@FunctionApp(name,params) => {
        name match {
          case "rd" => B.R(transExpr(params(0)))
          case "urd" => B.C(transExpr(params(0))) - B.R(transExpr(params(0)))
          case "tot" => B.C(transExpr(params(0)))
          case "rd@" => B.R(transExpr(params(0))) - B.I(transExpr(params(0)))
          case "tot@" => B.C(transExpr(params(0))) - B.I(transExpr(params(0)))
          case "str" => B.I(transExpr(params(0)))
          case "@" => B.I(transExpr(params(0)))
          case "next" => 
            val ch = transExpr(params(0))
            if (fa.parameters.size > 1) B.ChannelIdx(ch,B.R(ch) minus transExpr(params(1)))
            else B.ChannelIdx(ch,B.R(ch))
          case "prev" => 
            val ch = transExpr(params(0))
            if (fa.parameters.size > 1) B.ChannelIdx(ch,B.R(ch) - transExpr(params(1)))
            else B.ChannelIdx(ch,B.R(ch) - B.Int(1))
          case "last" => 
            val ch = transExpr(params(0))
            if (fa.parameters.size > 1) B.ChannelIdx(ch, B.C(ch) - transExpr(params(1)))
            else B.ChannelIdx(ch, B.C(ch) - B.Int(1))
          case "history" => 
            val ch = transExpr(params(0))
            generateRangePredicate(params, B.Int(0), B.I(ch))
          case "current" => 
            val ch = transExpr(params(0))
            generateRangePredicate(params, B.I(ch), B.C(ch))
          case "every" => 
            val ch = transExpr(params(0))
            generateRangePredicate(params, B.Int(0), B.C(ch)) 
          case "tokens" =>
            B.C(transExpr(params(0))) - B.R(transExpr(params(0))) ==@ transExpr(params(1))
          case "min" => {
            Boogie.FunctionApp("AT#Min", params.map(p => transExpr(p)))
          }
          case "subvar" => {
            Boogie.VarExpr("AV" + B.Sep + params(0).asInstanceOf[Id].id + B.Sep + params(1).asInstanceOf[Id].id)
          }
          case x => {
            // User-defined function
            val args = params.map(p => transExpr(p))
            Boogie.FunctionApp("UDef"+B.Sep+x, args)
          }
        }
      }
      case IndexAccessor(e,i) => {
        val tExpr = transExpr(e)
        val index = transExpr(i)
        if (e.typ.isChannel) B.ChannelIdx(tExpr,index)
        else tExpr apply transExpr(i)
      }
      case FieldAccessor(e,f) => {
        val tExpr = transExpr(e)
        B.Field(tExpr, e.typ.asInstanceOf[RefType].id, f)
      }
      case ListLiteral(lst) => {
        var listlit: Boogie.Expr = B.intlst
        var i = 0
        for (e <- lst) {
          val transE = transExpr(e)
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
        val rename = renamings.getOrElse(name, {val i = Id(name); i.typ = sm.typ; i})
        val accessorName = transExpr(rename)
        mark match {
          case "@" => B.I(accessorName)
          case "next" => B.R(accessorName)
          case "prev" => B.R(accessorName) - B.Int(1)
          case "last" => B.C(accessorName) - B.Int(1)
        }
      }
      case id@Id(name) => renamings.get(name) match {
        case None => Boogie.VarExpr(name)
        case Some(replacement) => {
          //assert(replacement.typ == id.typ, replacement + ": " + replacement.typ + " -- " + id + ": " + id.typ)
          transExpr(replacement)
        }
      } 
    }
  }
  
  def generateRangePredicate(params: List[Expr], start: Boogie.Expr, end: Boogie.Expr)(implicit renamings: Map[String,Expr]) = {
    if (params.size == 2) {
      val ch = transExpr(params(0))
      val ind = transExpr(params(1))
      start <= ind && ind < end
    }
    else if (params.size == 4) {
      val ch = transExpr(params(0))
      val ind = transExpr(params(1))
      val off1 = transExpr(params(2))
      val off2 = transExpr(params(3))
      start+off1 <= ind && ind < end-off2
    }
    else {
      // Should have been caught in resolver already
      throw new RuntimeException()
    }
  }
}
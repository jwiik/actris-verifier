package fi.abo.it.actortool.boogie

import fi.abo.it.actortool._
import scala.collection.mutable.ListBuffer
import Helper._
import fi.abo.it.actortool.boogie.Boogie.UnaryExpr
import fi.abo.it.actortool.ActorTool.TranslationException

class StmtExpTranslator(val ftMode: Boolean, implicit val bvMode: Boolean) {
    /*
   * Translation of statements and expressions
   */
  
  
  def transStmt(stmts: List[Stmt])(implicit renamings: Map[String,String]): List[Boogie.Stmt] = {
    val bStmts = new ListBuffer[Boogie.Stmt]()
    for (s <- stmts) {
      bStmts ++= (s match {
        case Assign(id,exp) => List(Boogie.Assign(transExpr(id),transExpr(exp)))
        case IndexAssign(id,idx,exp) => List(Boogie.AssignMap(transExpr(id),transExpr(idx),transExpr(exp)))
        case Assert(e) => List(bAssert(transExpr(e), e.pos, "Condition might not hold"))
        case Assume(e) => List(bAssume(transExpr(e)))
        case Havoc(ids) => for (i <- ids) yield { Boogie.Havoc(transExpr(i)) }
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
  
  
  def transExpr(exp: Expr)(implicit renamings: Map[String,String]): Boogie.Expr = {
    exp match {
      case And(e1,e2) => transExpr(e1) && transExpr(e2)
      case Or(e1,e2) => transExpr(e1) || transExpr(e2)
      case Implies(e1,e2) => transExpr(e1) ==> transExpr(e2)
      case Iff(e1,e2) => transExpr(e1) <==> transExpr(e2)
      case Not(e) => UnaryExpr("!",transExpr(e)) 
      case Less(e1,e2) =>
        if (bvMode) bFun("AT#BvUlt",transExpr(e1),transExpr(e2)) 
        else transExpr(e1) < transExpr(e2)
      case Greater(e1,e2) => transExpr(e1) > transExpr(e2)
      case AtLeast(e1,e2) => transExpr(e1) >= transExpr(e2)
      case AtMost(e1,e2) => 
        if (bvMode) bFun("AT#BvUle",transExpr(e1),transExpr(e2)) 
        else transExpr(e1) <= transExpr(e2)
      case Eq(e1,e2) => transExpr(e1) ==@ transExpr(e2)
      case NotEq(e1,e2) => transExpr(e1) !=@ transExpr(e2)
      case Plus(e1,e2) => 
        if (bvMode) bFun("AT#BvAdd",transExpr(e1),transExpr(e2)) 
        else transExpr(e1) + transExpr(e2)
      case Minus(e1,e2) =>
        if (bvMode) bFun("AT#BvSub",transExpr(e1),transExpr(e2)) 
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
      case LShift(e1,e2) =>
        BoogiePrelude.addComponent(BitwisePL)
        Boogie.FunctionApp("AT#LShift",List(transExpr(e1),transExpr(e2)))
      case BWAnd(e1,e2) =>
        BoogiePrelude.addComponent(BitwisePL)
        Boogie.FunctionApp("AT#BvAnd",List(transExpr(e1),transExpr(e2)))
      case UnMinus(e) => UnaryExpr("-",transExpr(e))
      case IfThenElse(c,e1,e2) => Boogie.Ite(transExpr(c),transExpr(e1),transExpr(e2))
      case Forall(vars,e,pat) => 
        Boogie.Forall(Nil,
          for (v <- vars) yield Boogie.BVar(v.id,type2BType(v.typ)),
          pat match {
            case None => Nil
            case Some(p) => List(Boogie.Trigger(List(transExpr(p))))
          },
          transExpr(e)
        )
      case Exists(vars,e,pat) => 
        Boogie.Exists(Nil,
          for (v <- vars) yield Boogie.BVar(v.id,type2BType(v.typ)),
          pat match {
            case None => Nil
            case Some(p) => List(Boogie.Trigger(List(transExpr(p))))
          },
          transExpr(e)
        )
      case fa@FunctionApp(name,params) => {
        name match {
          case "rd" => bRead(transExpr(params(0)))
          case "urd" => bCredit(transExpr(params(0)))
          case "tot" => bTotal(transExpr(params(0)))
          case "limit" => bLimit(transExpr(params(0)))
          case "init" => bI(transExpr(params(0)))
          case "sqn" => {
            if (!ftMode) 
              throw new TranslationException(fa.pos, "Function " + name + " is only supported in FT-mode")
            val t = transExpr(params(0))
            val accessor = params(0).asInstanceOf[IndexAccessor]
            val channel = transExpr(accessor.exp)
            val index = transExpr(accessor.suffix)
            bSqnCh(channel,index)
          }
          case "currsqn" => {
            if (!ftMode) 
              throw new TranslationException(fa.pos, "Function " + name + " is only supported in FT-mode")
            bSqnAct(transExpr(params(0)))
          }
          case "next" => 
            val ch = transExpr(params(0))
            bChannelIdx(ch,bRead(ch))
          case "prev" => 
            val ch = transExpr(params(0))
            bChannelIdx(ch,bRead(ch) minus bInt(1))
          case "tokens" =>
            // Happens if tokens function is used in an invalid position (not inhaled/exhaled)
            throw new TranslationException(fa.pos, "Function tokens used in invalid position") 
          case "state" => {
            val actor = params(0).typ.asInstanceOf[ActorType].actor
            val id = params(1).asInstanceOf[Id].id
            bState(transExpr(params(0))) ==@ Boogie.VarExpr(actor.fullName+Sep+id)
          }
          case "min" => {
            Boogie.FunctionApp("AT#Min", params.map(p => transExpr(p)))
          }
          case x => {
            // User-defined function
            val args = params.map(p => transExpr(p))
            Boogie.FunctionApp("UDef"+Sep+x, args)
          }
        }
      }
      case IndexAccessor(e,i) => {
        val tExpr = transExpr(e)
        val index = transExpr(i)
        if (e.typ.isChannel) bChannelIdx(tExpr,index)
        else tExpr apply transExpr(i)
      }
      case ListLiteral(lst) => {
        var listlit: Boogie.Expr = intlst
        var i = 0
        for (e <- lst) {
          val transE = transExpr(e)
          listlit = Boogie.MapStore(listlit,bInt(i),transE)
          i = i+1
        }
        listlit
      }

      case il@IntLiteral(i) =>
        if (bvMode) {
          assert(il.typ != null)
          val size = il.typ.asInstanceOf[AbstractIntType].size
          Boogie.BVLiteral(i.toString,32)
        }
        else bInt(i)
        
        
      case HexLiteral(x) => {
        val bigInt = x.toList.map("0123456789abcdef".indexOf(_)).map(BigInt(_)).reduceLeft(_ * 16 + _)
        bInt(bigInt.toString) // To decimal conversion
      }
      case BoolLiteral(b) => Boogie.BoolLiteral(b)
      case FloatLiteral(f) => Boogie.RealLiteral(f.toDouble)
      case Id(id) => renamings.get(id) match {
        case None => Boogie.VarExpr(id)
        case Some(newId) => Boogie.VarExpr(newId)
      } 
    }
  }
}
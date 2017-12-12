package fi.abo.it.actortool.boogie

import fi.abo.it.actortool._
import scala.collection.mutable.ListBuffer
import fi.abo.it.actortool.boogie.Boogie.UnaryExpr
import fi.abo.it.actortool.ActorTool.TranslationException
import scala.util.parsing.input.Position
import fi.abo.it.actortool.ActorTool.TranslationException
import fi.abo.it.actortool.ActorTool.TranslationException
import fi.abo.it.actortool.ActorTool.TranslationException
import fi.abo.it.actortool.ActorTool.TranslationException
import fi.abo.it.actortool.ActorTool.TranslationException

object TranslatorContext {
  
  def apply(renamings: Map[String,Expr], subBullet: Boolean) = 
    new TranslatorContext(renamings,subBullet,Map.empty)
  
  def apply(renamings: Map[String,Expr], subBullet: Boolean, stateChannels: Map[String,Expr]) = 
    new TranslatorContext(renamings,subBullet,stateChannels)
  
}

class TranslatorContext(val renamings: Map[String,Expr], val subBullet: Boolean, val stateChannels: Map[String,Expr]) {
  
  private val childContexts = new ListBuffer[TranslatorContext]
  def newChildContext = {
    val ctx = new TranslatorContext(renamings,subBullet,stateChannels)
    childContexts += ctx
    ctx
  }
}

class StmtExpTranslator {
  /*
   * Translation of statements and expressions
   */
  
  def transStmt(stmts: List[Stmt], subBullet: Boolean): List[Boogie.Stmt] = {
    val ctx = TranslatorContext(Map.empty,subBullet)
    transStmtI(stmts)(ctx)
  }
  
  def transExpr(exp: Expr, subBullet: Boolean): Boogie.Expr = {
    val ctx = TranslatorContext(Map.empty,subBullet)
    transExprI(exp)(ctx)
  }
  
  def transStmt(stmts: List[Stmt], ctx: TranslatorContext): List[Boogie.Stmt] = {
    transStmtI(stmts)(ctx)
  }
  
  def transExpr(exp: Expr, ctx: TranslatorContext): Boogie.Expr = {
    transExprI(exp)(ctx)
  }

  def transStmtI(stmts: List[Stmt])(implicit context: TranslatorContext): List[Boogie.Stmt] = {
    val bStmts = new ListBuffer[Boogie.Stmt]()
    for (s <- stmts) {
      val ctx = context.newChildContext
      s match {
        case Assign(id,exp) => {
          bStmts += Boogie.Assign(transExprI(id),transExprI(exp))
        }
        case MapAssign(e1,e2) => {
          BoogiePrelude.addComponent(MapPL)
          val elem = transExprI(e2)(ctx)
          val acc = e1.asInstanceOf[IndexAccessor]
          val map = acc.exp
          val index = acc.suffix
          bStmts += Boogie.Assign(transExprI(map)(ctx),B.Fun("Map#Store",transExprI(map)(ctx),transExprI(index)(ctx),elem))
        }
        case Assert(e) => {
          bStmts += B.Assert(transExprI(e)(ctx), e.pos, "Condition might not hold")
        }
        case Assume(e) => {
          bStmts += B.Assume(transExprI(e)(ctx))
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
          bStmts ++= s
        }
        case IfElse(ifCond,ifStmt,elseIfs,elseStmt) => {
          bStmts += Boogie.If(transExprI(ifCond)(ctx),transStmtI(ifStmt)(ctx), buildElseIfStmt(elseIfs, elseStmt) )
        }
        case While(_,_,_) => throw new RuntimeException("Loops not supported yet")
        case fe: ForEach => throw new RuntimeException("Loops not supported yet")
        case pd: ProcCall => throw new RuntimeException("Procedure calls has not been inlined")
      }
    }
    bStmts.toList
  }
  
  def buildElseIfStmt(elseIf: List[ElseIf], els: List[Stmt])(implicit context: TranslatorContext): List[Boogie.Stmt] = {
    elseIf match {
      case x::tail => List(Boogie.If(transExprI(x.cond)(context), transStmtI(x.stmt)(context), buildElseIfStmt(tail, els)))
      case Nil => transStmtI(els)(context)
    }
  }
  
  
  def transExprI(exp: Expr)(implicit context: TranslatorContext): Boogie.Expr = {
    //println(exp)
    assert(exp.typ != null, exp.toString)
    exp match {
      case And(e1,e2) => transExprI(e1) && transExprI(e2)
      case Or(e1,e2) => transExprI(e1) || transExprI(e2)
      case Implies(e1,e2) => transExprI(e1) ==> transExprI(e2)
      case Iff(e1,e2) => transExprI(e1) <==> transExprI(e2)
      case Not(e) => UnaryExpr("!",transExprI(e)) 
      case op@Less(e1,e2) =>
        if (e1.typ.isBv) {
          getBitVectorFunction(op.operator, List(transExprI(e1),transExprI(e2)), e1.typ)
        }
        else transExprI(e1) < transExprI(e2)
      case op@Greater(e1,e2) => 
        if (e1.typ.isBv) {
          getBitVectorFunction(op.operator, List(transExprI(e1),transExprI(e2)), e1.typ)
        }
        else transExprI(e1) > transExprI(e2)
      case op@AtLeast(e1,e2) => 
        if (e1.typ.isBv) {
          getBitVectorFunction(op.operator, List(transExprI(e1),transExprI(e2)), e1.typ)
        }
        else transExprI(e1) >= transExprI(e2)
      case op@AtMost(e1,e2) => 
        if (e1.typ.isBv) {
          getBitVectorFunction(op.operator, List(transExprI(e1),transExprI(e2)), e1.typ)
        }
        else transExprI(e1) <= transExprI(e2)
      case Eq(e1,e2) => transExprI(e1) ==@ transExprI(e2)
      case NotEq(e1,e2) => transExprI(e1) !=@ transExprI(e2)
      case op@Plus(e1,e2) => 
        if (e1.typ.isBv) {
          getBitVectorFunction(op.operator, List(transExprI(e1),transExprI(e2)), e1.typ)
        }
        else transExprI(e1) + transExprI(e2)
      case op@Minus(e1,e2) =>
        if (e1.typ.isBv) {
          getBitVectorFunction(op.operator, List(transExprI(e1),transExprI(e2)), e1.typ)
        }
        else transExprI(e1) - transExprI(e2)
      case op@Times(e1,e2) => 
        if (e1.typ.isBv) {
          getBitVectorFunction(op.operator, List(transExprI(e1),transExprI(e2)), e1.typ)
        }
        else transExprI(e1) * transExprI(e2)
      case op@Div(e1,e2) => 
        if (op.typ.isBv) {
          getBitVectorFunction(op.operator, List(transExprI(e1),transExprI(e2)), e1.typ)
        }
        else {
          BoogiePrelude.addComponent(DivModAbsPL)
          Boogie.FunctionApp("AT#Div",List(transExprI(e1),transExprI(e2)))
        }
        //transExpr(e1) / transExpr(e2)
      case op@Mod(e1,e2) =>
        if (op.typ.isBv) {
          getBitVectorFunction(op.operator, List(transExprI(e1),transExprI(e2)), e1.typ)
        }
        else {
          BoogiePrelude.addComponent(DivModAbsPL)
          Boogie.FunctionApp("AT#Mod",List(transExprI(e1),transExprI(e2)))
        }
        //transExpr(e1) % transExpr(e2)
      case rsh@RShift(e1,e2) =>
        if (rsh.typ.isBv) {
          getBitVectorFunction(rsh.operator, List(transExprI(e1),transExprI(e2)), e1.typ)
        }
        else {
          BoogiePrelude.addComponent(BitwisePL)
          Boogie.FunctionApp("AT#RShift",List(transExprI(e1),transExprI(e2)))
        }
      case lsh@LShift(e1,e2) =>
        if (lsh.typ.isBv) {
          getBitVectorFunction(lsh.operator, List(transExprI(e1),transExprI(e2)), e1.typ)
        }
        else {
          BoogiePrelude.addComponent(BitwisePL)
          Boogie.FunctionApp("AT#LShift",List(transExprI(e1),transExprI(e2)))
        }
        
      case op@BwAnd(e1,e2) =>
        getBitVectorFunction(op.operator, List(transExprI(e1),transExprI(e2)), op.typ)
      case op@BwOr(e1,e2) =>
        getBitVectorFunction(op.operator, List(transExprI(e1),transExprI(e2)), op.typ)
      case op@BwXor(e1,e2) =>
        getBitVectorFunction(op.operator, List(transExprI(e1),transExprI(e2)), op.typ)
      case op@BwNot(e) =>
        getBitVectorFunction(op.operator, List(transExprI(e)), op.typ)
      case op@UnMinus(e) => {
        if (op.typ.isBv) getBitVectorFunction("--", List(transExprI(e)), op.typ)
        else UnaryExpr("-",transExprI(e))
      }
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
          case "rd@" => B.R(transExprI(params(0))) - getBullet(transExprI(params(0)),context.subBullet)
          case "tot@" => B.C(transExprI(params(0))) - getBullet(transExprI(params(0)),context.subBullet)
          case "str" => getBullet(transExprI(params(0)),context.subBullet)
          case "@" => getBullet(transExprI(params(0)),context.subBullet)
          case "rate" => B.B(transExprI(params(0)))
          case "next" | "last" | "prev" => getNextPrevLast(fa.name, params)
          case "history" => 
            val ch = transExprI(params(0))
            generateRangePredicate(params, B.Int(0), getBullet(ch,context.subBullet))
          case "current" => 
            val ch = transExprI(params(0))
            generateRangePredicate(params, getBullet(ch,context.subBullet), B.C(ch))
          case "every" => 
            val ch = transExprI(params(0))
            generateRangePredicate(params, B.Int(0), B.C(ch)) 
          case "tokens" =>
            B.C(transExprI(params(0))) - B.R(transExprI(params(0))) ==@ transExprI(params(1))
          case "min" => {
            Boogie.FunctionApp("AT#Min", params.map(p => transExprI(p)))
          }
          case "int2bv" => {
            val size = params(1).asInstanceOf[IntLiteral].value
            params(0) match {
              case IntLiteral(n) => 
                Boogie.BVLiteral(n.toString,size)
              case UnMinus(IntLiteral(n)) => 
                getBitVectorFunction("--", List(Boogie.BVLiteral(n.toString,size)), fa.typ) 
              case x => 
                throw new TranslationException(params(0).pos,"The first argument to int2bv should an integer literal")
            }
          }
          case "int" => {
            val size = params(1).asInstanceOf[IntLiteral].value
            params(0) match {
              case IntLiteral(n) => 
                Boogie.BVLiteral(n.toString,size)
              case UnMinus(IntLiteral(n)) => 
                getBitVectorFunction("--", List(Boogie.BVLiteral(n.toString,size)), fa.typ) 
              case x => 
                throw new TranslationException(params(0).pos,"The first argument to int should an integer literal")
            }
          }
          case "uint" => {
            val size = params(1).asInstanceOf[IntLiteral].value
            params(0) match {
              case IntLiteral(n) => 
                Boogie.BVLiteral(n.toString,size)
              case UnMinus(IntLiteral(n)) => throw new RuntimeException()
              case x => 
                throw new TranslationException(params(0).pos,"The first argument to int should an integer literal")
            }
          }
          case "bv2int" => {
            val size = params(0).typ.asInstanceOf[BvType].size
            BoogiePrelude.addComponent(BitvectorPL.createPL(size))
            BoogiePrelude.addComponent(Bitvector2IntPL.createPL(size))
            Boogie.FunctionApp("AT#Bv2Int"+size,List(transExprI(params(0))))
          }
          case "bvconcat" => {
            val param1 = transExprI(params(0))
            val param2 = transExprI(params(1))
            Boogie.BinaryExpr("++", param1, param2)
          }
          case "bvextract" => {
            val param1 = transExprI(params(0))
            val param2 = transExprI(params(1))
            val param3 = transExprI(params(2))
            Boogie.BvExtract(param1, param2, param3)
          }
          case "bvresize" => {
            val param1 = transExprI(params(0))
            params(1) match {
              case IntLiteral(newSize) => {
                val argSize = params(0).typ.asInstanceOf[BvType].size
                if (newSize < argSize) {
                  Boogie.BvExtract(param1,B.Int(newSize),B.Int(0))
                }
                else if (newSize > argSize) {
                  Boogie.BinaryExpr("++",Boogie.BVLiteral("0",newSize-argSize),param1)
                }
                else {
                  param1
                }
              }
              case x => {
                throw new TranslationException(params(1).pos,"The second argument should an int literal")
              }
            }
            //val param2 = transExprI(params(1))
          }
          case "abs" => {
            val bParams = params map { transExprI(_) }
            if (fa.typ.isBv) {
              if (fa.typ.asInstanceOf[BvType].signed) getBitVectorFunction("abs", bParams, fa.typ)
              else bParams(0)
            }
            else Boogie.FunctionApp("abs", bParams)
          }
          case "chsum" => {
            val param = transExprI(params(0))
            val limit = B.R(param)
            val mm = Boogie.VarExpr(BMap.M)
            BoogiePrelude.addComponent(ChAggregates)
            Boogie.FunctionApp("AT#ChSum",List(mm,param,limit))
          }
          case "mode" => {
            B.Mode(B.This) ==@ transExprI(params(0))
          }
          case "state" => {
            context.renamings.get("St#") match {
              // This happens if we are e.g. translating an invariant of a subactor
              case Some(s) => transExprI(s) ==@ transExprI(params(0))
              case None => Boogie.VarExpr("St#") ==@ transExprI(params(0))
            }
          }
          case "old" => {
            val id = params(0).asInstanceOf[Id]
            val nId = context.renamings.getOrElse(id.id,id).asInstanceOf[Id]
            Boogie.VarExpr("old"+B.Sep+nId.id)
          }
          case x => {
            // User-defined function
            val args = params.map(p => transExprI(p))
            context.renamings.get(x) match {
              case Some(name) =>
                Boogie.FunctionApp(name.asInstanceOf[Id].id, args)
              case None =>
                println(context.renamings)
                throw new TranslationException(fa.pos, "Error, unknown function '" + x + "'")
            }
          }
        }
      }
      case IndexAccessor(e,i) => {
        val tExpr = transExprI(e)
        val index = transExprI(i)
        if (e.typ.isChannel) B.ChannelIdx(tExpr,index)
        else if (e.typ.isMap || e.typ.isList) {
          //context.addAssertion(i.pos, "Index might be out of bounds", B.Bool(true))
          BoogiePrelude.addComponent(MapPL)
          B.Fun("Map#Select", tExpr,index)
        }
        else {
          e match {
            case Id(id) => {
              context.stateChannels.get(id) match {
                case Some(ch) => {
                  assert(ch.typ.isChannel)
                  B.ChannelIdx(transExprI(ch),index)
                }
                case None => throw new RuntimeException()
              }
            }
            case _ => throw new RuntimeException()
          }
          
        }
      }
      case FieldAccessor(e,f) => {
        val tExpr = transExprI(e)
        B.Field(tExpr, e.typ.asInstanceOf[RefType].id, f)
      }
      case ListLiteral(lst) => {
        var listlit: Boogie.Expr = B.ListEmpty(transExprI(lst(0)))
        var i = 0
        for (e <- lst) {
          val transE = transExprI(e)
          listlit = B.Fun("Map#Store",listlit,B.Int(i),transE)
          i = i+1
        }
        listlit
      }
      case MapLiteral(dom,lst) => {
        val domDummy = getDummyValue(dom)
        var listlit: Boogie.Expr = B.MapEmpty(domDummy,transExprI(lst(0)))
        var i = 0
        for (e <- lst) {
          val transE = transExprI(e)
          listlit = B.Fun("Map#Store",listlit,getValue(dom,i),transE)
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
        val bigInt = java.lang.Long.parseLong(x.toUpperCase, 16)
        //B.Int(bigInt.toString) // To decimal conversion
        B.IntBV(bigInt.toString,hl.typ.asInstanceOf[BvType].size)
      }
      case BoolLiteral(b) => Boogie.BoolLiteral(b)
      case FloatLiteral(f) => Boogie.RealLiteral(f.toDouble)
      case sm@SpecialMarker(mark) => {
        val name = sm.extraData("accessor").asInstanceOf[String]

        val accessorName = getVirtualChannel(name, sm.typ)
        mark match {
          case "@" => getBullet(accessorName,context.subBullet)
          case "next" => B.R(accessorName)
          case "prev" => B.R(accessorName) - B.Int(1)
          case "last" => B.C(accessorName) - B.Int(1)
        }
      }
      case id@Id(name) => {
        if (name == "this") B.This
        else {
          context.renamings.get(name) match {
            case None => Boogie.VarExpr(name)
            case Some(replacement) => {
              //assert(replacement.typ == id.typ, replacement + ": " + replacement.typ + " -- " + id + ": " + id.typ)
              transExprI(replacement)
            }
          }
        }
      }
      case c: Comprehension => throw new TranslationException(c.pos,"Comprehensions should be replaced before translating to Boogie")
      case r: Range => throw new TranslationException(r.pos,"Range expressions should be replaced before translating to Boogie")
    }
  }
  
  def getNextPrevLast(fn: String, params: List[Expr])(implicit context: TranslatorContext) = {
    
    val ch = {
      if (!params(0).typ.isChannel) {
        params(0) match {
          case Id(id) => {
            getVirtualChannel(id, params(0).typ)
          }
          case _ => throw new RuntimeException()
        }
      }
      else {
        assert(params(0).typ.isChannel)
        transExprI(params(0))
      }
    }
    
    val idx = fn match {
      case "next" => B.R(ch)
      case "last" => B.C(ch)
      case "prev" => B.R(ch) - B.Int(1)
    }
    if (params.size > 1) B.ChannelIdx(ch, idx - transExprI(params(1)))
    else B.ChannelIdx(ch,idx)
  }
  
  def getVirtualChannel(name: String, tp: Type)(implicit context: TranslatorContext) = {
    val rename = context.renamings.getOrElse(name, { Id(name).withType(tp) })
    val virtualName = context.stateChannels.getOrElse(name, rename)
    transExprI(virtualName)
  }
  
  def getDummyValue(tp: Type) = tp match {
    case IntType => B.Int(0)
    case BvType(sz,_) => Boogie.BVLiteral("0",sz)
    case _ => throw new RuntimeException()
  }
  
  def getValue(tp: Type, num: Int) = tp match {
    case IntType => B.Int(num)
    case BvType(sz,_) => Boogie.BVLiteral(num.toString,sz)
    case _ => throw new RuntimeException()
  }
  
  def getBullet(ch: Boogie.Expr, subBullet: Boolean) = if (subBullet) B.Isub(ch) else B.I(ch)
  
  def generateRangePredicate(params: List[Expr], start: Boogie.Expr, end: Boogie.Expr)(implicit context: TranslatorContext) = {
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
  
  def getBitVectorFunction(operator: String, args: List[Boogie.Expr], typ: Type) = {
    val size = typ.asInstanceOf[BvType].size
    val signed = typ.asInstanceOf[BvType].signed
    
    val function = (operator,signed) match {
      case ("--",_) => "AT#BvNeg"
      case ("+",_) => "AT#BvAdd"
      case ("-",_) => "AT#BvSub"
      case ("*",_) => "AT#BvMul"
      case ("/",true) => "AT#BvSdiv"
      case ("/",false) => "AT#BvUdiv"
      case ("%",true) => "AT#BvSmod"
      case ("%",false) => "AT#BvUmod"
      case ("<",true) => "AT#BvSlt"
      case ("<",false) => "AT#BvUlt"
      case ("<=",true) => "AT#BvSle"
      case ("<=",false) => "AT#BvUle"
      case (">",true) => "AT#BvSgt"
      case (">",false) => "AT#BvUgt"
      case (">=",true) => "AT#BvSge"
      case (">=",false) => "AT#BvUge"
      case ("<<",_) => "AT#BvShl"
      case (">>",true) => "AT#BvAshr"
      case (">>",false) => "AT#BvLshr"
      case ("&",_) => "AT#BvAnd"
      case ("|",_) => "AT#BvOr"
      case ("~",_) => "AT#BvNot"
      case ("^",_) => "AT#BvXor"
      case ("abs",true) => "AT#BvAbs"
      case (_,_) => throw new TranslationException(typ.pos, "Unhandled operator: " + operator)
    }
    
    BoogiePrelude.addComponent(BitvectorPL.createPL(size))
    Boogie.FunctionApp(function+size,args)
  }
}
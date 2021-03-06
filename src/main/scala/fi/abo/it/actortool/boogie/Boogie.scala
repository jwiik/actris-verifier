//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
package fi.abo.it.actortool.boogie

import scala.util.parsing.input.Position
import scala.util.parsing.input.NoPosition
import fi.abo.it.actortool.FilePosition
import fi.abo.it.actortool.NoFilePosition

object Boogie {
 
 sealed abstract class Decl
 case class Const(id: String, unique: Boolean, t: BType) extends Decl
 case class Proc(id: String, ins: List[BVar], outs: List[BVar],
                 mod: List[String], PrePost: List[String],
                 body: List[Stmt]) extends Decl
 case class Function(id: String, ins: List[BVar], out: BVar) extends Decl
 case class Axiom(expr: Expr) extends Decl
 case class DeclComment(c: String) extends Decl
 case class DeclHeaderComment(title: String) extends Decl

 sealed abstract class BType
 case class NamedType(s: String) extends BType
 case class IndexedType(id: String, indices: List[BType]) extends BType
 
 // Added by JW
 case class BVType(size: Int) extends BType
 //

 case class Tag(s: String)
 sealed abstract class Stmt {
   def Locals = List[BVar]()
   var tags: List[Tag] = Nil
 }
 case class Comment(comment: String) extends Stmt
 case class Assert(e: Expr) extends Stmt {
   def this(e: Expr, p: Position, txt: String) = { this(e); this.pos = p; this.message = txt } 
   def this(e: Expr, p: Position, txt: String, subsumption: Int) = { this(e, p, txt); this.subsumption = Some(subsumption) } 
   var pos = NoPosition : Position
   var message = "" : String
   var subsumption = None: Option[Int]
 }
 case class Assume(e: Expr) extends Stmt
 case class Assign(lhs: Expr, rhs: Expr) extends Stmt
 case class AssignMap(lhs: Expr, index: Expr, rhs: Expr) extends Stmt
 case class Havoc(x: Expr) extends Stmt
 case class MapUpdate(map: Expr, arg0: Expr, arg1: Option[Expr], rhs: Expr) extends Stmt {
   def this(map: Expr, arg0: Expr, rhs: Expr) = this(map, arg0, None, rhs)
   def this(map: Expr, arg0: Expr, arg1: Expr, rhs: Expr) = this(map, arg0, Some(arg1), rhs)
 }
 case class If(guard: Expr, thn: List[Stmt], els: List[Stmt]) extends Stmt {
   override def Locals = (thn flatMap (_.Locals)) ::: (els flatMap (_.Locals))
 }
 case class LocalVar(x: BVar) extends Stmt {
   def this(id: String, tp: BType) = this(BVar(id, tp))
   override def Locals = List(x)
 }

 sealed abstract class Expr {
   def &&(that: Expr) = BinaryExpr("&&", this, that)
   def ||(that: Expr) = BinaryExpr("||", this, that)
   def ==@(that: Expr) = BinaryExpr("==", this, that)
   def !=@(that: Expr) = BinaryExpr("!=", this, that)
   def Equals(that: Expr) = BinaryExpr("==", this, that)
   def ==>(that: Expr) = BinaryExpr("==>", this, that)
   def <==>(that: Expr) = BinaryExpr("<==>", this, that)
   def unary_! = UnaryExpr("!", this)
   def <=(that: Expr) = BinaryExpr("<=", this, that)
//   def lte(that: Expr)(implicit bvMode: Boolean) = 
//     if (bvMode) FunctionApp("AT#BvUle",List(this,that)) else BinaryExpr("<=", this, that)
   def <(that: Expr) = BinaryExpr("<", this, that)
   def >=(that: Expr) = BinaryExpr(">=", this, that)
   def >(that: Expr) = BinaryExpr(">", this, that)
   def +(that: Expr) = BinaryExpr("+", this, that)
   def plus(that: Expr) = BinaryExpr("+", this, that)
   def minus(that: Expr) =  BinaryExpr("-", this, that)
   def -(that: Expr) = BinaryExpr("-", this, that)
   def *(that: Expr) = BinaryExpr("*", this, that)
   def /(that: Expr) = BinaryExpr("div", this, that)
   def %(that: Expr) = BinaryExpr("mod", this, that)
   def := (that: Expr) = Assign(this, that)
   def apply(e: Expr, f: Expr) = new MapSelect(this, e, Some(f))
   def apply(e: Expr) = new MapSelect(this, e, None)
   def thenElse(thenE: Expr, elseE: Expr) = new Ite(this, thenE, elseE)
   def select(e: Expr, s: String) = new MapSelect(this, e, s) // useful for working on heap
   def forall(x: BVar) = new Forall(x, this)
   def exists(x: BVar) = new Exists(x, this)
   def store(e: Expr, f: Expr, rhs: Expr) = MapUpdate(this, e, Some(f), rhs)
 }
 
 // Modified by JW: made it possible to use strings for int literals
 case class IntLiteral(n: String) extends Expr {
   def this(n: Int) = this(n.toString)
 }
 object IntLiteral {
   def apply(n: Int) = new IntLiteral(n)
 }
 // Added by JW
 case class BVLiteral(n: String, size: Int) extends Expr
 //
 case class RealLiteral(d: Double) extends Expr
 case class BoolLiteral(b: Boolean) extends Expr
 case class Null() extends Expr
 case class VarExpr(id: String) extends Expr {
   def this(v: BVar) = this(v.id)
 }
 case class MapSelect(map: Expr, arg0: Expr, arg1: Option[Expr]) extends Expr {
   def this(map: Expr, arg0: Expr) = this(map, arg0, None) // for one-dimensional maps
   def this(map: Expr, arg0: Expr, arg1: String) = this(map, arg0, Some(VarExpr(arg1)))
   def this(map: Expr, arg0: Expr, arg1: String, arg2: String) = // for 3-dimensional maps
     this(MapSelect(map, arg0, Some(VarExpr(arg1))), VarExpr(arg2), None)
 }
 case class MapStore(map: Expr, arg0: Expr, rhs: Expr) extends Expr
 case class Old(e: Expr) extends Expr
 case class UnaryExpr(op: String, e: Expr) extends Expr
 case class BinaryExpr(op: String, e0: Expr, e1: Expr) extends Expr
 case class FunctionApp(f: String, args: List[Expr]) extends Expr {
   def this(f: String, a0: Expr) = this(f, List(a0))
   def this(f: String, a0: Expr, a1: Expr) = this(f, List(a0, a1))
   def this(f: String, a0: Expr, a1: Expr, a2: Expr) = this(f, List(a0, a1, a2))
 }
 case class Trigger(ts: List[Expr]) extends Expr {
   def this(t: Expr) = this(List(t))
 }
 case class Forall(ta: List[TVar], xs: List[BVar], triggers: List[Trigger], body: Expr) extends Expr {
   def this(x: BVar, body: Expr) = this(Nil, List(x), Nil, body)   
   def this(xs: List[BVar], trigger: Trigger, body: Expr) = this(Nil, xs, List(trigger), body)
   def this(t: TVar, x: BVar, body: Expr) = this(List(t), List(x), Nil, body)
 }
 case class Exists(ta: List[TVar], xs: List[BVar], triggers: List[Trigger], body: Expr) extends Expr {
   def this(x: BVar, body: Expr) = this(Nil, List(x), List(), body)
   def this(xs: List[BVar], trigger: Trigger, body: Expr) = this(Nil, xs, List(trigger), body)
 }
 case class Lambda(ta: List[TVar], xs: List[BVar], body: Expr) extends Expr
 
 case class Ite(con: Expr, thn: Expr, els: Expr) extends Expr
 
 case class BvExtract(e1: Expr, e2: Expr, e3: Expr) extends Expr

 case class BVar(id: String, t: BType) {
   def this(id: String, t: BType, uniquifyName: Boolean) =
     this(if (uniquifyName) {
            val n = S_BVar.VariableCount
            S_BVar.VariableCount = S_BVar.VariableCount + 1
            id + "#_" + n
          } else {
            id
          }, t)
   val where: Expr = null
 }
 object S_BVar { var VariableCount = 0 }
 def NewBVar(id: String, t: BType, uniquifyName: Boolean) = {
   val v = new Boogie.BVar(id, t, uniquifyName)
   val e = new Boogie.VarExpr(v)
   (v,e)
 }
 case class TVar(id: String) {
   def this(id: String, uniquifyName: Boolean) =
     this(if (uniquifyName) {
            val n = S_TVar.VariableCount
            S_TVar.VariableCount = S_TVar.VariableCount + 1
            id + "#_" + n
          } else {
            id
          })
   val where: Expr = null
 }
 object S_TVar { var VariableCount = 0 }
 def NewTVar(id: String) = {
   val v = new Boogie.TVar(id, true)
   val e = new Boogie.NamedType(v.id)
   (v,e)
 }

 // def out(s: String) = Console.out.print(s)
 private var indentLevel = 1
 def indent: String = {
   def doIndent(i: Int): String = {
     if(i==0) { "" } else { "  " + doIndent(i-1) }
   }
   doIndent(indentLevel);
 }

 def IndentMore(what: => String) = {
   val prev = indentLevel
   indentLevel = indentLevel + 1
   val result = what
   indentLevel = prev
   result
 }
 private val nl = System.getProperty("line.separator");
 
 def Print[T](list: List[T], sep: String, p: T => String): String = list match {
   case Nil => ""
   case x :: Nil => p(x)
   case x :: xs => p(x) + sep + Print(xs, sep, p)
 }
 def PrintType(t: BType): String = t match {
   case nt@ NamedType(s) =>
     s
   case IndexedType(id,l) =>
     id + " " + l.map{ t =>  "(" + PrintType(t) + ")" }.mkString(" ")
   // Added by JW
   case BVType(size) => "bv"+size
   //
 }
 def Print(d: Decl): String = {
   indentLevel = 1
   d match {
     case Const(id, u, t) =>
       "const " + (if (u) "unique " else "" ) + id + ": " + PrintType(t) + ";" + nl
     case p: Proc =>
       "procedure " + p.id +
         "(" + Print(p.ins, ", ", PrintVar) + ")" +
         // JW: Made returns clause optional 
         (if (!p.outs.isEmpty) {" returns (" + Print(p.outs, ", ", PrintVar) + ")"}
         else "") +
         //
         nl +
         (p.mod match {
           case Nil => ""
           case x :: xs =>
             indent +  "modifies " +
               Print(p.mod, ", ", { s: String => s }) +
               ";" + nl
         }) +
         // JW: Modified
         (if (!p.PrePost.isEmpty) Print(p.PrePost, nl, { spec: String => indent + spec }) + nl
         else "") +
         // End modified
         "{" + nl +
         Print(p.body flatMap (_.Locals), "", { v:BVar => indent + "var " + PrintVar(v) + ";" + nl}) +
         Print(p.body, "", PrintStmt) +
         "}" + nl
     case Function(id, ins, out) =>
       "function " + id + "(" + Print(ins, ", ", PrintVar) + ") returns (" + PrintVar(out) + ");" + nl
     case Axiom(e) =>
       indentLevel = 0
       "axiom " + PrintExpr(e) + ";" + nl
     case DeclComment(s) =>
       nl +
         "// " + s + nl
     case DeclHeaderComment(s) =>
       nl +
         nl +
         "// -------------------------------------------" + nl +
         "// " + s + nl +
         "// -------------------------------------------" + nl
   }
 }
 def PrintVar(v: BVar): String = {
   v.id + ": " + PrintType(v.t) +
   (if (v.where != null) {" where " + PrintExpr(v.where) } else { "" })
 }
 def PrintStmt(s: Stmt): String = s match {
   case Comment(msg) => indent +  "// " +  msg + nl
   case assert@Assert(e) =>
     // JW: Removed handling for rise4fun etc and improved hadnling of asserts without position
     val pos = "" + 
      (if (assert.pos != null) 
        (assert.pos match {
         case NoPosition => ""
         case NoFilePosition => ""
         case pos: Position => pos + ": " 
        }) 
       else "")
     indent +  "assert " + "{:msg \"" + pos + assert.message + "\"}" + (assert.subsumption match {case Some(n) => "{:subsumption " + n + "}"; case None => ""}) + " " + PrintExpr(e) + ";" + nl
   case Assume(e) => indent + "assume " + PrintExpr(e) +  ";" + nl
   case If(guard, thn, els) =>
     if (thn == Nil && els == Nil) "" else
     indent + "if (" +
     (if (guard == null) "*" else PrintExpr(guard)) +
     ") {" +  nl + 
     IndentMore { Print(thn, "", PrintStmt)  } + 
     indent +  "}" +
     (if (els == Nil) nl else
       " else {"  + nl + 
       IndentMore { Print(els, "", PrintStmt)  } + 
       indent + "}" + nl
     )
   case Assign(lhs, rhs) =>
     indent + PrintExpr(lhs) + " := " + PrintExpr(rhs) + ";" + nl
   case AssignMap(lhs, index, rhs) =>
     indent + PrintExpr(lhs) + "[" + PrintExpr(index) + "] := " + PrintExpr(rhs) + ";" + nl
   case Havoc(lhs) =>
     indent + "havoc " + PrintExpr(lhs) + ";" + nl
   case MapUpdate(map, a0, a1, rhs) =>
     indent + PrintExpr(map) + "[" +
     PrintExpr(a0) +
     (a1 match { case Some(e) => { ", " + PrintExpr(e) }; case None => { "" }}) +
     "] := " + 
     PrintExpr(rhs) + ";" + nl
   case _:LocalVar => "" /* print nothing */
 }
 def PrintExpr(e: Expr): String = {
   PrintExpr(e, false)
 }
 def PrintExpr(e: Expr, useParens: Boolean): String = e match {
   case IntLiteral(n) => n.toString
   // Added by JW
   case BVLiteral(n,size) => n+"bv"+size
   //
   case RealLiteral(d) => d.toString
   case BoolLiteral(b) => b.toString
   case Null() => "null"
   case VarExpr(id) => id
   case MapSelect(map, arg0, arg1) =>
     PrintExpr(map) + "[" + PrintExpr(arg0, false) + 
     (arg1 match {case Some(e) => { ", " + PrintExpr(e) }; case None => { "" }}) +
     "]"
   case MapStore(map, arg0, rhs) =>
     PrintExpr(map) + "[" + PrintExpr(arg0) + " := " + PrintExpr(rhs, false) + "]"
   case Old(e) => "old(" + PrintExpr(e, false) + ")"
   case UnaryExpr(op, e) =>
     (if (useParens)  { "(" } else "") +
     op + PrintExpr(e, true) +
     (if (useParens) ")" else "" )
   case BinaryExpr(op, e0, e1) =>
     // reduce parentheses in a special common case:
     val binIsAndImpIff = op=="&&" || op=="==>" || op=="<==>";
     def IsAnd(e: Expr) = e match { case BinaryExpr(op,_,_) if op=="&&" => true case _ => false }
     (if (useParens) "(" else "") + PrintExpr(e0, !(binIsAndImpIff && IsAnd(e0))) + 
     " " + op + " " + 
     PrintExpr(e1, !(binIsAndImpIff && IsAnd(e1))) +
     (if (useParens) ")" else "")
   case FunctionApp(f, args) =>
     f + "(" +
     Print(args, ", ", { e: Expr => PrintExpr(e, false) }) +
     ")"
   case Ite(con, thn, els) =>
     "(if " + PrintExpr(con) + " then " + PrintExpr(thn) + " else " + PrintExpr(els) + ")"
   case Trigger(ts) => Print(ts,", ", PrintExpr)
   case Forall(ts, xs, triggers, body) =>
     "(forall" +
     (if (ts.length == 0) " " else "<" + Print(ts, ", ", { x: TVar => x.id }) + "> ") +
     Print(xs, ", ", { x: BVar => x.id +  ": " + PrintType(x.t) }) +
     " :: " + nl +
     IndentMore {
       Print(triggers , "", { t: Trigger => indent + "{ " +  PrintExpr(t) + " }" + nl }) +
       indent + PrintExpr(body)
     } + nl +
     indent + ")"
   case Exists(ts, xs, triggers, body) =>
     "(exists " +
     (if (ts.length == 0) " " else "<" + Print(ts, ", ", { x: TVar => x.id }) + "> ") +     
     Print(xs, ", ", { x: BVar => x.id +  ": " + PrintType(x.t) }) +
     " :: " + nl +
     IndentMore {
       Print(triggers , "", { t: Trigger => indent + "{ " +  PrintExpr(t) + " }" + nl }) +
         indent + PrintExpr(body)
     } + nl +
     indent + ")"
   case Lambda(ts, xs, body) =>
     "(lambda" +
     (if (ts.length == 0) " " else "<" + Print(ts, ", ", { x: TVar => x.id }) + "> ") +
     Print(xs, ", ", { x: BVar => x.id +  ": " + PrintType(x.t) }) +
     " :: " +
     PrintExpr(body) +
     ")"
   case BvExtract(e1,e2,e3) => {
     PrintExpr(e1) + "[" + PrintExpr(e2) + ":" + PrintExpr(e3) + "]"
   }
 }
}

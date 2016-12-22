//package fi.abo.it.actortool.boogie

//import scala.collection.mutable.ListBuffer
//import fi.abo.it.actortool.ActorInvariant
//import fi.abo.it.actortool.ChannelInvariant
//import fi.abo.it.actortool.And
//import fi.abo.it.actortool.Implies
//import fi.abo.it.actortool.FunctionApp
//import fi.abo.it.actortool.Id
//import fi.abo.it.actortool.Expr

//class Inhalator(expTranslator: StmtExpTranslator) extends Halator(expTranslator, true, false)
//class Exhalator(expTranslator: StmtExpTranslator) extends Halator(expTranslator, false, false)
//
//abstract class Halator(val trans: StmtExpTranslator, val inhale: Boolean, val subAction: Boolean) {
//    
//  def visit(inv: ChannelInvariant, renamings: Map[String,Expr]): (List[String],List[Boogie.Stmt]) = 
//    visit(inv, "Invariant might not hold", renamings)
//  
//  def visit(inv: ActorInvariant, renamings: Map[String,Expr]): (List[String],List[Boogie.Stmt]) = 
//    visit(inv, "Invariant might not hold", renamings)
//  
//  def visit(inv: ActorInvariant, msg: String, renamings: Map[String,Expr]): (List[String],List[Boogie.Stmt]) = {
//    val buffer = new ListBuffer[Boogie.Stmt]
//    val chans = new ListBuffer[String]
//    visit(inv.expr, inv.assertion.free)(buffer,chans,msg,renamings);
//    (chans.toList, buffer.toList)
//  }
//  
//  def visit(inv: ChannelInvariant, msg: String, renamings: Map[String,Expr]): (List[String],List[Boogie.Stmt]) = {
//    val buffer = new ListBuffer[Boogie.Stmt]
//    val chans = new ListBuffer[String]
//    visit(inv.expr, inv.assertion.free)(buffer,chans,msg,renamings);
//    (chans.toList, buffer.toList)
//  }
//  
//  def visit(e: Expr, msg: String, renamings: Map[String,Expr]): (List[String],List[Boogie.Stmt]) = {
//    val buffer = new ListBuffer[Boogie.Stmt]
//    val chans = new ListBuffer[String]
//    visit(e, false)(buffer,chans,msg,renamings);
//    (chans.toList, buffer.toList)
//  }
//  
//  def visit(expr: Expr, free: Boolean)(
//      implicit buffer: ListBuffer[Boogie.Stmt], chans: ListBuffer[String], msg: String, renamings: Map[String,Expr]) {
//    expr match {
//      case And(left,right) => visit(left, free); visit(right, free)
////      case Implies(left,right) => {
////        val branchBuffer = new ListBuffer[Boogie.Stmt]
////        visit(right, free)(branchBuffer,msg,renamings)
////        buffer += Boogie.If(trans.transExpr(left),branchBuffer.toList,List.empty) 
////      }
//      case fa@FunctionApp("tokens",params) => {
//        val cId = params(0).asInstanceOf[Id].id
//        chans += cId
//        val pred = B.C(trans.transExpr(params(0))) - B.R(trans.transExpr(params(0))) ==@ trans.transExpr(params(1))
//        if (inhale) buffer += B.Assume(pred)
//        else buffer += B.Assert(pred, fa.pos, msg)
////        if (!subAction) {
////          val chCredit = B.T(trans.transExpr(params(0)))
////          if (inhale) {
////            buffer += Boogie.Assign(chCredit, chCredit + trans.transExpr(params(1)))
////          }
////          else {
////            buffer += Boogie.Assign(chCredit, chCredit + trans.transExpr(params(1)))
////          }
////        }
//      }
//      case x => {
//        if (inhale) buffer += B.Assume(trans.transExpr(x)) 
//        else if (!free) {
//          buffer += B.Assert(trans.transExpr(x), x.pos, msg)
//        }
//      }
//    }
//  }
//  
//}
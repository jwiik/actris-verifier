package fi.abo.it.actortool.promela

import scala.collection.mutable.ListBuffer
import fi.abo.it.actortool._

object Instrumentation {
  
  val cCode = 
"""
  if (now.__INSTR_COST < BEST_COST) {
    BEST_COST = now.__INSTR_COST;
    printf(">> New best: %d\n\n", BEST_COST);
    putrail();
    Nr_Trails--;
  }
"""
  
  val P = Promela
  
  //val ACC_BUFFER_SUM = "__INSTR_ACC_BUFFER_SUM"
  val BUFFER_SUM = "__INSTR_BUFFER_SUM"
  val MAX_BUFFER_SUM = "__INSTR_MAX_BUFFER_SUM"
  val NUM_FIRINGS = "__INSTR_NUM_FIRINGS"
  val ACTOR_SWITCHES = "__INSTR_ACTOR_SWITCHES"
  val ACTION_SWITCHES = "__INSTR_ACTION_SWITCHES"
  val COST = "__INSTR_COST"
  
  val PREV_ACTOR = "__INSTR_PREV_ACTOR"
  val PREV_ACTION = "__INSTR_PREV_ACTION"
  
  val MAX_SIZE_ARRAY = "__INSTR_MAX_SIZE"

  def mkInstrumentationCall(actor: P.Expr, action: P.Expr) = P.Call("__instrument",List(actor,action))
  
  def mkInstrumentationDef(
      chansWithMax: List[(Connection,Int)] , 
      renamings: RenamingContext, 
      weights: Map[String,Int], 
      endState: P.Expr) = {
    
    val buffWeight = weights.getOrElse("B",0)
    val actorSwWeight = weights.getOrElse("A",0)
    val actionSwWeight = weights.getOrElse("a",0)
    
    if (buffWeight < 0 || actorSwWeight < 0 || actionSwWeight < 0) {
      throw new RuntimeException("Invalid schedule cost function weights!")
    }
    
    val instrumentBody = new ListBuffer[P.Stmt]
    val costTerms = new ListBuffer[P.Expr]
    
    // Only calculate what is really needed
    if (buffWeight > 0) {
//      val chans = chansWithMax.map {
//        case (ch,max) => P.FunCall("len",List(P.VarExp(renamings.R(ch.id)))) / P.IntLiteral(max) : P.Expr 
//      }
        
      if (!chansWithMax.isEmpty) {
        for (((ch,max),idx) <- chansWithMax.zipWithIndex) {
          val lenCall = P.FunCall("len",List(P.VarExp(renamings.R(ch.id))))
          instrumentBody += P.Assign(
              P.IndexAccessor(P.VarExp(MAX_SIZE_ARRAY), P.IntLiteral(idx)),
              P.ConditionalExpr(
                lenCall > P.IndexAccessor(P.VarExp(MAX_SIZE_ARRAY), P.IntLiteral(idx)),
                lenCall,
                P.IndexAccessor(P.VarExp(MAX_SIZE_ARRAY), P.IntLiteral(idx))
              )
          )
          
//          instrumentBody += P.If(List(
//            P.OptionStmt(
//                List(P.GuardStmt(
//                    P.ExprStmt(lenCall > P.IndexAccessor(P.VarExp(MAX_SIZE_ARRAY), P.IntLiteral(idx))),
//                    List(
//                        P.Assign(P.IndexAccessor(P.VarExp(MAX_SIZE_ARRAY), P.IntLiteral(idx)), lenCall)
//                    )))
//            ),
//            P.OptionStmt(
//               List(P.GuardStmt(
//                   P.Else,
//                   List(P.Skip))))
//            )
//          )
        }
      }
//        instrumentBody += 
//          P.Assign(P.VarExp(BUFFER_SUM), chans.reduceLeft((a,b) => P.BinaryExpr(a,"+",b)))
//        
//        instrumentBody += P.If(List(
//         P.OptionStmt(
//             List(P.GuardStmt(
//                 P.ExprStmt(P.VarExp(BUFFER_SUM) > P.VarExp(MAX_BUFFER_SUM)),
//                 List(
//                     P.Assign(P.VarExp(MAX_BUFFER_SUM), P.VarExp(BUFFER_SUM))
//                 )))
//         ),
//         P.OptionStmt(
//             List(P.GuardStmt(
//                 P.Else,
//                 List(P.Skip))))
//         )
//        )
        
        
//        instrumentBody += 
//          P.Assign(
//              P.VarExp(MAX_BUFFER_SUM), 
//              P.BinaryExpr(P.VarExp(MAX_BUFFER_SUM), "+", chans.reduceLeft((a,b) => P.BinaryExpr(a,"+",b))))
//      }
      
      costTerms += {
        val sumTerms = chansWithMax.zipWithIndex.map { 
          case ((ch,max),i) => P.IndexAccessor(P.VarExp(MAX_SIZE_ARRAY), P.IntLiteral(i)) / P.IntLiteral(max) : P.Expr 
        }
        val term = sumTerms.reduceLeft { (a,b) => a+b }
        
        if (buffWeight != 1) (P.IntLiteral(buffWeight) * term)
        else term
      }
    }
    
    if (actorSwWeight > 0) {
      instrumentBody += P.If(List(
         P.OptionStmt(
             List(P.GuardStmt(
                 P.ExprStmt(P.VarExp(PREV_ACTOR) !=@ P.VarExp("actor")),
                 List(
                     P.Assign(P.VarExp(PREV_ACTOR), P.VarExp("actor")),
                     P.Assign(P.VarExp(ACTOR_SWITCHES), P.VarExp(ACTOR_SWITCHES) + P.IntLiteral(1))
                 )))
         ),
         P.OptionStmt(
             List(P.GuardStmt(
                 P.Else,
                 List(P.Skip))))
         )
      )
      costTerms += {        
        if (actorSwWeight != 1) (P.IntLiteral(actorSwWeight) * P.VarExp(ACTOR_SWITCHES))
        else P.VarExp(ACTOR_SWITCHES)
      }
    }
    
    val costExpr =
      if (costTerms.isEmpty) {
        P.IntLiteral(0)
      }
      else {
        costTerms.reduceLeft{ (a,b) => a + b }
      }
    
    instrumentBody += P.Assign(P.VarExp(NUM_FIRINGS),P.VarExp(NUM_FIRINGS) + P.IntLiteral(1))
    
    instrumentBody += P.Assign(P.VarExp(COST), costExpr)
     instrumentBody += P.If(List(
       P.OptionStmt(List(P.GuardStmt(P.ExprStmt(P.VarExp(NUM_FIRINGS) ==@ P.VarExp("__RUNS")),List(P.CCode(cCode))))),
       P.OptionStmt(List(P.GuardStmt(P.Else,List(P.Skip)))) 
    ))
      
    P.InlineDef("__instrument",List("actor","action"), List(P.DStep( instrumentBody.toList )))
  }
}

object InstrumentationCall extends Function3[String,String,String,String] {
  def apply(actor: String, instanceId: String, actionId: String) = {
    "__instrument(P"+actor+"->"+instanceId+","+actionId+");"
  }
}

//object InstrCTemplate extends Function3[DFActor,RenamingContext,Map[String,Int],String] {
//  def apply(actor: DFActor, renamings: RenamingContext, weights: Map[String,Int]) = {
//    val buffWeight = weights.getOrElse("B",1)
//    val actorSwWeight = weights.getOrElse("A",1)
//    val actionSwWeight = weights.getOrElse("a",1)
//    
//    val chanSum = actor match {
//      case nw: Network => {
//        val chans = nw.structure.get.connections.filter{ c => !c.isInput && !c.isOutput }.map{ c => "q_len(now." + renamings.R(c.id) + ")" }
//        chans.reduceLeft((a,b) => "(" + a + "+" + b + ")")
//      }
//      case ba: BasicActor => "0"
//    }
// 
//    val code = template
//      .replaceAll("@ChanSum@", chanSum)
//      .replaceAll("@BuffW@",buffWeight.toString)
//      .replaceAll("@ActorSwW@",actorSwWeight.toString)
//      .replaceAll("@ActionSwW@",actionSwWeight.toString)
//      
//    code
//  }
//  
//  val template = 
//""" 
//  int __BEST_COST = 1000000;
//  
//  int best_c() {
//    if (now.__INSTR_COST < __BEST_COST) {
//      return 1;
//    }
//    else {
//      return 0;
//    }
//  }
//  
//  int best() {
//    if (now.__INSTR_COST < __BEST_COST) {
//      __BEST_COST = now.__INSTR_COST;
//      printf(">> New best: %d\n", __BEST_COST);
//      putrail();
//      //Nr_Trails--;
//    }
//    return 0;
//  }
//"""
//  
///*
//  int more_exp() {
//    if (now.__INSTR_COST >= __BEST_COST) {
//      return 1;
//    }
//    else {
//      return 0;
//    }
//  }
//  int __instrument(int actor, int action) {
//    now.__C_INSTR_ACC_BUFFER_SUM = (now.__C_INSTR_ACC_BUFFER_SUM + @ChanSum@);
//    now.__C_INSTR_NUM_FIRINGS = (now.__C_INSTR_NUM_FIRINGS + 1);
//    if (actor != now.__C_INSTR_PREV_ACTOR) {
//      now.__C_INSTR_ACTOR_SWITCHES = (now.__C_INSTR_ACTOR_SWITCHES + 1);
//      now.__C_INSTR_ACTION_SWITCHES = (now.__C_INSTR_ACTION_SWITCHES + 1);
//    }
//    else {
//      if (action != now.__C_INSTR_PREV_ACTION) {
//        now.__C_INSTR_ACTION_SWITCHES = (now.__C_INSTR_ACTION_SWITCHES + 1);
//      }
//    }
//    now.__INSTR_COST = (((@BuffW@ * (now.__C_INSTR_ACC_BUFFER_SUM / now.__C_INSTR_NUM_FIRINGS)) + (@ActionSwW@ * now.__C_INSTR_ACTION_SWITCHES)) + (@ActorSwW@ * now.__C_INSTR_ACTOR_SWITCHES));
//    now.__C_INSTR_PREV_ACTOR = actor;
//    now.__C_INSTR_PREV_ACTION = action;
//    return 0;
//
//  }
//*/
//}

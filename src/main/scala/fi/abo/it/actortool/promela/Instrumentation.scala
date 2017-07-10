package fi.abo.it.actortool.promela

import scala.collection.mutable.ListBuffer
import fi.abo.it.actortool._

object Instrumentation {
  
  val P = Promela
  
  val ACC_BUFFER_SUM = "__INSTR_ACC_BUFFER_SUM"
  val NUM_FIRINGS = "__INSTR_NUM_FIRINGS"
  val ACTOR_SWITCHES = "__INSTR_ACTOR_SWITCHES"
  val ACTION_SWITCHES = "__INSTR_ACTION_SWITCHES"
  val COST = "__INSTR_COST"
  
  val PREV_ACTOR = "__INSTR_PREV_ACTOR"
  val PREV_ACTION = "__INSTR_PREV_ACTION"

  def mkInstrumentationCall(actor: P.Expr, action: P.Expr) = P.Call("__instrument",List(actor,action))
  
  def mkInstrumentationDef(actor: DFActor, renamings: RenamingContext, weights: Map[String,Int]) = {
    
    val buffWeight = P.IntLiteral(weights.getOrElse("B",1))
    val actorSwWeight = P.IntLiteral(weights.getOrElse("A",1))
    val actionSwWeight = P.IntLiteral(weights.getOrElse("a",1))
    
    val instrumentBody = new ListBuffer[P.Stmt]
    actor match {
      case nw: Network => {
        val chans = nw.structure.get.connections.filter{ c => !c.isInput && !c.isOutput }.map{ c => P.FunCall("len",List(P.VarExp(renamings.R(c.id))) ): P.Expr }
 
        instrumentBody += P.Assign(P.VarExp(ACC_BUFFER_SUM), P.BinaryExpr(P.VarExp(ACC_BUFFER_SUM), "+", chans.reduceLeft((a,b) => P.BinaryExpr(a,"+",b))))
        instrumentBody += P.Assign(P.VarExp(NUM_FIRINGS), P.BinaryExpr(P.VarExp(NUM_FIRINGS), "+", P.IntLiteral(1)))
        
        instrumentBody += {
          val thn = P.GuardStmt( 
              P.ExprStmt(P.BinaryExpr(P.VarExp("actor"), "!=", P.VarExp(PREV_ACTOR))),
              List(
                  P.Assign(P.VarExp(ACTOR_SWITCHES), P.BinaryExpr(P.VarExp(ACTOR_SWITCHES), "+", P.IntLiteral(1))),
                  P.Assign(P.VarExp(ACTION_SWITCHES), P.BinaryExpr(P.VarExp(ACTION_SWITCHES), "+", P.IntLiteral(1)))
              )
            )
          val els = P.GuardStmt( 
              P.Else,
              {
                val nestedThn = P.GuardStmt( 
                  P.ExprStmt(P.BinaryExpr(P.VarExp("action"), "!=", P.VarExp(PREV_ACTION))),
                  List(
                      P.Assign(P.VarExp(ACTION_SWITCHES), P.BinaryExpr(P.VarExp(ACTION_SWITCHES), "+", P.IntLiteral(1)))
                  )
                )
                val nestedEls = P.GuardStmt( 
                  P.Else,
                  List(P.Skip)
                )
                List(P.If( List( P.OptionStmt(List(nestedThn)), P.OptionStmt(List(nestedEls)) ) ))
              }
              
            )
          
          val opts = List(P.OptionStmt(List(thn)), P.OptionStmt(List(els)))
          
          P.If(opts)
        }
        
        instrumentBody += P.Assign(P.VarExp(COST), buffWeight*(P.VarExp(ACC_BUFFER_SUM) / P.VarExp(NUM_FIRINGS)) + (actionSwWeight * P.VarExp(ACTION_SWITCHES)) + (actorSwWeight * P.VarExp(ACTOR_SWITCHES)))
        
        
        instrumentBody += P.Assign(P.VarExp(PREV_ACTOR), P.VarExp("actor"))
        instrumentBody += P.Assign(P.VarExp(PREV_ACTION), P.VarExp("action"))
        
      }
      case ba: BasicActor => {
        instrumentBody += P.Skip
      }
    }
    P.InlineDef("__instrument",List("actor","action"), instrumentBody.toList)
  }
}

object InstrumentationCall extends Function3[String,String,String,String] {
  def apply(actor: String, instanceId: String, actionId: String) = {
    "__instrument(P"+actor+"->"+instanceId+","+actionId+");"
  }
}

object InstrCTemplate extends Function3[DFActor,RenamingContext,Map[String,Int],String] {
  def apply(actor: DFActor, renamings: RenamingContext, weights: Map[String,Int]) = {
    val buffWeight = weights.getOrElse("B",1)
    val actorSwWeight = weights.getOrElse("A",1)
    val actionSwWeight = weights.getOrElse("a",1)
    
    val chanSum = actor match {
      case nw: Network => {
        val chans = nw.structure.get.connections.filter{ c => !c.isInput && !c.isOutput }.map{ c => "q_len(now." + renamings.R(c.id) + ")" }
        chans.reduceLeft((a,b) => "(" + a + "+" + b + ")")
      }
      case ba: BasicActor => "0"
    }
 
    val code = template
      .replaceAll("@ChanSum@", chanSum)
      .replaceAll("@BuffW@",buffWeight.toString)
      .replaceAll("@ActorSwW@",actorSwWeight.toString)
      .replaceAll("@ActionSwW@",actionSwWeight.toString)
      
    code
  }
  
  val template = 
""" 
  int __BEST_COST = 1000000;
  
  int best() {
    if (now.__INSTR_COST < __BEST_COST) {
      __BEST_COST = now.__INSTR_COST;
      printf(">> New best: %d\n", __BEST_COST);
      putrail();
      //Nr_Trails--;
    }
    return 0;
  }
"""
  
/*
  int more_exp() {
    if (now.__INSTR_COST >= __BEST_COST) {
      return 1;
    }
    else {
      return 0;
    }
  }
  int __instrument(int actor, int action) {
    now.__C_INSTR_ACC_BUFFER_SUM = (now.__C_INSTR_ACC_BUFFER_SUM + @ChanSum@);
    now.__C_INSTR_NUM_FIRINGS = (now.__C_INSTR_NUM_FIRINGS + 1);
    if (actor != now.__C_INSTR_PREV_ACTOR) {
      now.__C_INSTR_ACTOR_SWITCHES = (now.__C_INSTR_ACTOR_SWITCHES + 1);
      now.__C_INSTR_ACTION_SWITCHES = (now.__C_INSTR_ACTION_SWITCHES + 1);
    }
    else {
      if (action != now.__C_INSTR_PREV_ACTION) {
        now.__C_INSTR_ACTION_SWITCHES = (now.__C_INSTR_ACTION_SWITCHES + 1);
      }
    }
    now.__INSTR_COST = (((@BuffW@ * (now.__C_INSTR_ACC_BUFFER_SUM / now.__C_INSTR_NUM_FIRINGS)) + (@ActionSwW@ * now.__C_INSTR_ACTION_SWITCHES)) + (@ActorSwW@ * now.__C_INSTR_ACTOR_SWITCHES));
    now.__C_INSTR_PREV_ACTOR = actor;
    now.__C_INSTR_PREV_ACTION = action;
    return 0;

  }
*/
}

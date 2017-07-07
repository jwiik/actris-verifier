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
  
  def mkInstrumentationDef(actor: DFActor, renamings: RenamingContext) = {
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
        
        instrumentBody += P.Assign(P.VarExp(COST),(P.VarExp(ACC_BUFFER_SUM) / P.VarExp(NUM_FIRINGS)) + P.VarExp(ACTION_SWITCHES) + P.VarExp(ACTOR_SWITCHES))
        
        
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
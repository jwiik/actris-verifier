package fi.abo.it.actortool.util

import fi.abo.it.actortool._

class ActionPeekAnalyzer {
  
  def analyze(action: ActorAction): Map[String,Int] = {
    val idFinder = new IdFinder
    val inputVars =
      (action.inputPattern flatMap { pat => pat.vars.zipWithIndex map { case (v,i) => (v.id,(pat.portId,i)) } }).toMap
    for (g <- action.guards) {
      idFinder.visitExpr(g)(inputVars)
    }
    return idFinder.getPeekDepth
  }
  
  class IdFinder extends ASTVisitor[Map[String,(String,Int)]] {
    
    private val peekDepth = collection.mutable.Map[String,Int]()
    
    def getPeekDepth = peekDepth.toMap
    
    override def visitExpr(expr: Expr)(implicit info: Map[String,(String,Int)]) {
      expr match {
        case Id(id) => 
          if (info.contains(id)) {
            val (port,depth) = info(id)
            if (!peekDepth.contains(port) || (peekDepth(port)+1) < depth) {
              peekDepth += (port -> (depth+1))
            }
          }
        case x => super.visitExpr(x)
      }
    }
    
  }
  
  
}
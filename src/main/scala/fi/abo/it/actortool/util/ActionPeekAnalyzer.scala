package fi.abo.it.actortool.util

import fi.abo.it.actortool._

class ActionPeekAnalyzer {
  
  def analyze(action: ActorAction, priorities: Map[AbstractAction,List[AbstractAction]]): Map[String,Int] = {
    val higherPrioPeeks = priorities(action).map { a => analyze(a.asInstanceOf[ActorAction],priorities) }
    val idFinder = new IdFinder
    val inputVars =
      (action.inputPattern flatMap { pat => pat.vars.zipWithIndex map { case (v,i) => (v.id,(pat.portId,i)) } }).toMap
    for (g <- action.guards) {
      idFinder.visitExpr(g)(inputVars)
    }
    val peeks = getMaxPeek(idFinder.getPeekDepth :: higherPrioPeeks)
    
    return peeks
  }
  
  def getMaxPeek(peeks: List[Map[String,Int]]) = {
    var map = Map.empty[String,Int]
    for (p <- peeks) {
      for ((port,depth) <- p) {
        if (map.contains(port)) {
          if (map(port) < depth) {
            map = map + (port -> depth)
          }
        }
        else {
          map = map + (port -> depth)
        }
      }
    }
    map
  }
  
  def analyze(actions: List[ActorAction], priorities: Map[AbstractAction,List[AbstractAction]]): Map[String,Int] = {
    var map: Map[String,Int] = Map.empty 
    for (a <- actions) {
      for ((p,r) <- analyze(a,priorities)) {
        assert(r <= 1, "Peeks deeper than 1 not supported yet")
        if (!map.contains(p) || map(p) < r) {
          map += (p -> r)
        }
      }
    }
    map
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
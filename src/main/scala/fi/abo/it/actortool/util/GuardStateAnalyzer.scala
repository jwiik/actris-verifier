package fi.abo.it.actortool.util

import fi.abo.it.actortool._

object GuardStateAnalyzer {
  
  def analyze(actions: List[AbstractAction], variables: Seq[Declaration]): Set[String] = {
    val vars = variables.map { _.id }
    val finder = new IdFinder()
    actions map { a => analyze(finder,a.guards,vars) }
    return finder.getVariables
  }
  
  def analyze(finder: IdFinder, guards: Seq[Expr], variables: Seq[String]): Set[String] = {
    guards map { g => finder.visitExpr(g)(variables.toSet) }
    return finder.getVariables
  }
  
  class IdFinder extends ASTVisitor[Set[String]] {
    
    private var stateVars = Set[String]()
    
    def getVariables = stateVars
    
    override def visitExpr(expr: Expr)(implicit variables: Set[String]) {
      expr match {
        case Id(id) => if (variables.contains(id)) {
          stateVars += id
        }
        case x => super.visitExpr(x)
      }
    }
    
  }
  
}
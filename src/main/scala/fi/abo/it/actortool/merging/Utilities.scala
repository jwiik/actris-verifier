package fi.abo.it.actortool.merging

import fi.abo.it.actortool._

object ContractGuardToActorGuardTranslator extends ASTReplacingVisitor[Map[(String,Int), Expr]] {
  
  val Sep = Constants.Sep
  
  override def visitExpr(expr: Expr)(implicit map: Map[(String,Int), Expr]): Expr = {
    expr match {
      case IndexAccessor(Id(ch),SpecialMarker("@")) => map(ch,0)
      case fa@FunctionApp("int",arguments) => FunctionApp("int",arguments map visitExpr)
      case fa: FunctionApp => throw new RuntimeException("Functions not allowed in guards")
      case x => super.visitExpr(x)
    }
  }
  
}
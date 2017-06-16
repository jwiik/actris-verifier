package fi.abo.it.actortool.merging

import fi.abo.it.actortool._

object ContractGuardToActorGuardTranslator extends ASTReplacingVisitor[(String,Int), Id] {
  
  val Sep = Constants.Sep
  
  override def visitExpr(expr: Expr)(implicit map: Map[(String,Int), Id]): Expr = {
    expr match {
      case IndexAccessor(Id(ch),SpecialMarker("@")) => map(ch,0)
      case fa@FunctionApp("int2bv",arguments) => FunctionApp("int2bv",arguments map visitExpr)
      case fa: FunctionApp => throw new RuntimeException("Functions not allowed in guards")
      case x => super.visitExpr(x)
    }
  }
  
}
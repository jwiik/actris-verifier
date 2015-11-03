package fi.abo.it.actortool

object Inferencer {
  private var inferenceModules: List[InferenceModule] = List(StaticProperties)
  
  def infer(program: List[Actor]) = {
    for (module <- inferenceModules) {
      for (a <- program) module.infer(a)
    }
  }
}

object StaticProperties extends InferenceModule {
  def infer(actor: Actor) = actor match {
    case n: Network => {
      for (m <- n.members) m match {
        case Structure(connections) => {
          for (c <- connections) {
            n.addChannelInvariant(ChannelInvariant(AtMost(IntLiteral(0),FunctionApp("rd",List(Id(c.id): Expr))),true))
            n.addChannelInvariant(ChannelInvariant(AtMost(IntLiteral(0),FunctionApp("urd",List(Id(c.id): Expr))),true))
            c.from match {
              case PortRef(None,x) => n.addChannelInvariant(ChannelInvariant(Eq(
                  FunctionApp("tot",List(Id(c.id): Expr)),
                  FunctionApp("initial",List(Id(c.id): Expr))
                ),true))
              case _ =>
            }
            c.to match {
              case PortRef(None,x) => n.addChannelInvariant(ChannelInvariant(Eq(
                  FunctionApp("rd",List(Id(c.id): Expr)),
                  IntLiteral(0)
                ),true))
              case _ =>
            }
          }
        }
        case _ =>
      }
    }
    case _ =>
  }
} 

abstract class InferenceModule {
  def infer(actor: Actor)
}

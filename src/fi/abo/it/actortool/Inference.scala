package fi.abo.it.actortool

import collection.mutable.ListBuffer
import scala.util.parsing.input.Position

sealed trait InferenceOutcome 
sealed case class Success() extends InferenceOutcome
sealed case class Errors(errors: List[(Position,String)]) extends InferenceOutcome

class Context {
  private val errors = new ListBuffer[(Position,String)]
  def error(pos: Position, msg: String) { errors += ((pos,msg)) }
  def outcome: InferenceOutcome = { if (errors.isEmpty) Success() else Errors(errors.toList) }
}

object Elements {
  def rd(id: String) = FunctionApp("rd",List(Id(id): Expr))
  def urd(id: String) = FunctionApp("urd",List(Id(id): Expr))
  def tot(id: String) = FunctionApp("tot",List(Id(id): Expr))
  def initial(id: String) = FunctionApp("initial",List(Id(id): Expr))
  def intlit(i: Int) = IntLiteral(i)
} 

import Elements._

object Inferencer {
  
  private var inferenceModules: List[InferenceModule] = List(StaticProperties,SDFClass)
  
  def infer(program: List[TopDecl]) = {
    for (module <- inferenceModules) {
      for (a <- program) module.infer(a)
    }
  }
}

object StaticProperties extends InferenceModule {
  def network(n: Network)(implicit ctx: Context) {
    for (m <- n.members) m match {
      case Structure(connections) => {
        for (c <- connections) {
          n.addChannelInvariant(AtMost(intlit(0),rd(c.id)))
          n.addChannelInvariant(AtMost(intlit(0),urd(c.id)))
          c.from match {
            case PortRef(None,x) => n.addChannelInvariant(Eq(tot(c.id),initial(c.id)))
            case _ =>
          }
          c.to match {
            case PortRef(None,x) => n.addChannelInvariant(Eq(rd(c.id),intlit(0)))
            case _ =>
          }
        }
      }
      case _ =>
    }
  }
  
}

object SDFClass extends InferenceModule {
  
  val SdfAnnot = "sdf"
  
  def network(n: Network)(implicit ctx: Context) = {
    
    val countInvariants = new ListBuffer[Expr]
    val valueInvariants = new ListBuffer[Expr]
    
    val delayedChannels =  {
      val buffer = new ListBuffer[(String,Expr)]
      TokensDefFinder.visitExpr(n.actorInvariants map {nwi => nwi.expr})(buffer);
      buffer.toMap
    }
    
    val sdfAnnotEnts = 
      (for (m <- n.members) yield m match {
        case e: Entities => e.entities.filter { i => i.actor.hasAnnotation(SdfAnnot) }
        case _ => Nil
      }).flatten
    
    for (e <- sdfAnnotEnts) {
      val action = e.actor.actions.filter{ a => !a.init }(0)
      
      val quantVar = Id("idx")
      val replacements = {
        val inputs = (for (ipat <- action.inputPattern) yield {
            val inChan = n.structure.get.incomingConnection(e.id, ipat.portId).get
            var i = 0
            for (v <- ipat.vars) yield {
              val cId = Id(inChan.id); cId.typ = ChanType(v.typ)
              val acc = if (i == 0) IndexAccessor(cId,quantVar) else IndexAccessor(cId,Minus(quantVar,IntLiteral(i)))
              acc.typ = v.typ
              i = i+1
              (v -> acc)
            }
          }).flatten
          
        val params = (for ((p,a) <- (e.actor.parameters zip e.arguments)) yield {(Id(p.id) -> a)})
        (inputs:::params).toMap
      }

      
      
      
      for (op <- e.actor.outports) {
        for (ip <- e.actor.inports) {
          val inRate = action.portInputCount(ip.portId)
          val outRate = action.portOutputCount(op.portId)
          
          val inChan = n.structure.get.incomingConnection(e.id, ip.portId).get
          val outChans = n.structure.get.outgoingConnections(e.id, op.portId)
          
          (inRate,outRate) match {
            case (1,1) => for (oc <- outChans) {
              val tokenAmountInv =
                if (delayedChannels contains oc.id) Eq(rd(inChan.id),Minus(tot(oc.id),delayedChannels(oc.id)))
                else Eq(rd(inChan.id),tot(oc.id))
              countInvariants += tokenAmountInv
                            
              
              
              val outPatRev = action.portOutputPattern(op.portId).get.exps.reverse
              
              var i = 0
              for (e <- outPatRev) {
                val (highBound, idx) = delayedChannels.get(oc.id) match {
                  case None => 
                    if (i == 0) (tot(oc.id), quantVar)
                    else (tot(oc.id), Minus(quantVar,intlit(i)))
                  case Some(d) => (Minus(tot(oc.id),d), Minus(Plus(quantVar,d),intlit(i)))
                }
                val eReplaced = IdReplacer.visitExpr(e)(replacements)
                val cId = Id(oc.id); cId.typ = ChanType(e.typ)
                val acc = IndexAccessor(cId,idx); acc.typ = e.typ
                val bound = And(AtMost(intlit(0),quantVar),Less(quantVar,highBound))
                val quantExp = Implies(bound,Eq(acc,eReplaced))
                valueInvariants += Forall(List(Declaration(quantVar.id,IntType(32),false)), quantExp, None)
              }
              
            } // case
          } // match
        } // for
      } // for
    } // for
    n.addChannelInvariants(countInvariants.toList)
    n.addChannelInvariants(valueInvariants.toList)
  } // def network
  
}

abstract class InferenceModule {
  final def infer(decl: TopDecl): InferenceOutcome = {
    val ctx = new Context
    decl match {
      case n: Network => network(n)(ctx)
      case _ =>
    }
    ctx.outcome
  }
  
  def network(n: Network)(implicit ctx: Context)
}

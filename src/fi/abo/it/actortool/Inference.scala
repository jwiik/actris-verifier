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
  def lit(i: Int) = { val li = IntLiteral(i); li.typ = IntType(32); li}
} 

import Elements._

object Inferencer {
  final val Modules = List(StaticProperties,NWPreToInvariant,SDFClass).map(m => (m.name,m)).toMap
  private val DefaultModules = Set(StaticProperties,NWPreToInvariant,SDFClass)
      
  def infer(program: List[TopDecl], modules: List[String]) = {
    val inferenceModules = modules match {
      case Nil => DefaultModules
      case List("default") => DefaultModules
      case list => (StaticProperties::(list map { l => Modules(l) })).toSet
    }
    
    for (module <- inferenceModules) {
      for (a <- program) module.infer(a)
    }
  }
}

object StaticProperties extends InferenceModule {
  override val name = "basic-wf"
  
  def network(n: Network)(implicit ctx: Context) {
    for (m <- n.members) m match {
      case Structure(connections) => {
        for (c <- connections) {
          n.addChannelInvariant(AtMost(lit(0),rd(c.id)))
          n.addChannelInvariant(AtMost(lit(0),urd(c.id)))
          c.from match {
            case PortRef(None,x) => n.addChannelInvariant(Eq(tot(c.id),initial(c.id)))
            case _ =>
          }
          c.to match {
            case PortRef(None,x) => n.addChannelInvariant(Eq(rd(c.id),lit(0)))
            case _ =>
          }
        }
      }
      case _ =>
    }
  }
}

object NWPreToInvariant extends InferenceModule {
  override val name = "nw-precondition"
  
  def network(n: Network)(implicit ctx: Context) = {    
    if (n.actions.size == 1) {
      val action = n.actions(0)
      val replacements = new ListBuffer[(Id,Expr)]
      for (ipat <- action.inputPattern) {
        val channel = n.structure.get.getInputChannel(ipat.portId).get
        
        for ((v,i) <- ipat.vars.view.zipWithIndex) {
          val chId = Id(channel.id); chId.typ = ChanType(v.typ)
          val accessor = IndexAccessor(chId,lit(i)); accessor.typ = v.typ
          replacements += ((v,accessor))
        }
        val replMap = replacements.toMap
        val renamedReqs = action.requires map { p => IdReplacer.visitExpr(p)(replMap) } 
        n.addChannelInvariants(renamedReqs)
      }
    }
  }
  
}

object SDFClass extends InferenceModule {
  override val name = "sdf-annot"
  
  val SdfAnnot = "sdf"
  val quantVar = Id("idx$"); quantVar.typ = IntType(32)

  def network(n: Network)(implicit ctx: Context) = {
    
    val countInvariants = new ListBuffer[Expr]
    val valueInvariants = new ListBuffer[Expr]
    
    val delayedChannels =  {
      val buffer = new ListBuffer[(String,Expr)]
      TokensDefFinder.visitExpr(n.actorInvariants map {nwi => nwi.expr})(buffer);
      (buffer map {case (ch,amount) => (ch,amount)}).toMap
    }
    
    val sdfAnnotEnts = 
      (for (m <- n.members) yield m match {
        case e: Entities => e.entities.filter { i => i.actor.hasAnnotation(SdfAnnot) }
        case _ => Nil
      }).flatten
      
      
    
    for (e <- sdfAnnotEnts) {
      val action = e.actor.actions.filter{ a => !a.init }(0)
      
      for (op <- e.actor.outports) {
        
        val outRate = action.portOutputCount(op.portId)
        
        val outChans = n.structure.get.outgoingConnections(e.id, op.portId)
        
        for (oc <- outChans) {
          
          val replacements = {
            val inputs = (for (ipat <- action.inputPattern) yield {
              val inRate = action.portInputCount(ipat.portId)
              val inChan = n.structure.get.incomingConnection(e.id, ipat.portId).get
              var i = 0
              for (v <- ipat.vars) yield {
                val cId = Id(inChan.id); cId.typ = ChanType(v.typ)
                val rated = (inRate,outRate) match {
                  case (1,1) => quantVar
                  case (x,1) => Times(lit(x),quantVar)
                  case (1,y) => Div(quantVar,lit(y))
                  case (x,y) => Times(Div(lit(x),lit(y)),quantVar)
                }
                val idx = if (i == 0) rated else Plus(rated,lit(i))
                val delayAdjustedIdx =
                  if (delayedChannels contains oc.id) Minus(idx,delayedChannels(oc.id))
                  else idx
                val acc = IndexAccessor(cId,delayAdjustedIdx)
                acc.typ = v.typ
                i = i+1
                (v -> acc)
              }
            }).flatten
            val params = (for ((p,a) <- (e.actor.parameters zip e.arguments)) yield {(Id(p.id) -> a)})
            (inputs:::params).toMap
          }
          
          for (ip <- e.actor.inports) {
            val inRate = action.portInputCount(ip.portId)
            val inChan = n.structure.get.incomingConnection(e.id, ip.portId).get
            val ratedTot = 
              if (inRate == 1) tot(oc.id)
              else Times(lit(inRate),tot(oc.id))
            val ratedRd =
              if (outRate == 1) rd(inChan.id)
              else Times(lit(outRate),rd(inChan.id))
            
            val ratedDelayedTot = 
              if (delayedChannels contains oc.id) Minus(ratedTot,delayedChannels(oc.id))
              else ratedTot
              
            countInvariants += Eq(ratedRd,ratedDelayedTot)
          }
          
          val outFuncs = action.portOutputPattern(op.portId).get.exps
          var k = 0
          for (fk <- outFuncs) {
            val lowBound = delayedChannels.get(oc.id) match {
              case None => lit(0)
              case Some(d) => d
            }
            val quantBounds = And(AtMost(lowBound,quantVar),Less(quantVar,tot(oc.id)))
            val bounds = // If there is more than one output we need differentiate with mod
              if (1 < outFuncs.size) And(quantBounds,Eq(Mod(quantVar,lit(outRate)),lit(k)))
              else quantBounds
            
            val fkRenamed = IdReplacer.visitExpr(fk)(replacements)
            val cId = Id(oc.id); cId.typ = ChanType(fk.typ)
            val acc = IndexAccessor(cId,quantVar); acc.typ = fk.typ
            
            val quantExp = Implies(bounds,Eq(acc,fkRenamed))
            
            valueInvariants += Forall(List(quantVar), quantExp)
            k = k+1
          }
        }
      } // for
    } // for
    n.addChannelInvariants(countInvariants.toList)
    n.addChannelInvariants(valueInvariants.toList)
  } // def network
  
}

abstract class InferenceModule {
  
  val name: String
  
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

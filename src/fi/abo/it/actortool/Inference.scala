package fi.abo.it.actortool

import collection.mutable.ListBuffer
import scala.util.parsing.input.Position
import Elements._

object Inferencer {
  
  sealed trait InferenceOutcome 
  sealed case class Success() extends InferenceOutcome
  sealed case class Errors(errors: List[(Position,String)]) extends InferenceOutcome
  
  class Context {
    private val errors = new ListBuffer[(Position,String)]
    def error(pos: Position, msg: String) { errors += ((pos,msg)) }
    def outcome: InferenceOutcome = { if (errors.isEmpty) Success() else Errors(errors.toList) }
  }
  
  final val Modules = List(StaticClass,NWPreToInvariant,FTProperties).map(m => (m.name,m)).toMap
  private val DefaultModules = Set(StaticClass,NWPreToInvariant)
      
  def infer(program: List[TopDecl], modules: List[String], ftMode: Boolean): InferenceOutcome = {
    val inferenceModules = modules match {
      case Nil => DefaultModules
      case List("default") => if (!ftMode) DefaultModules else DefaultModules ++ Set(FTProperties)
      case list => (list map { l => Modules(l) }).toSet
    }
    
    val ctx = new Context
    
    for (module <- inferenceModules) {
      for (a <- program) module.infer(ctx,a)
    }
    
    return ctx.outcome
  }
  
  object NWPreToInvariant extends InferenceModule {
    override val name = "nw-precondition"
    val quantVar = Id("idx$"); quantVar.typ = IntType(32)
    
    object IndexReplacer extends ASTReplacingVisitor[IndexAccessor,IndexAccessor] {
      override def visitExpr(expr: Expr)(implicit map: Map[IndexAccessor,IndexAccessor]): Expr = {
        expr match {
          case IndexAccessor(ch,index) => index match {
            case SpecialMarker("@") => return IndexAccessor(ch,quantVar)
            case _ => return super.visitExpr(expr)
          }
          case _ => return super.visitExpr(expr)
        }
      }
    }
    
    def network(n: Network)(implicit ctx: Context): Unit = {
      if (n.inports.size != 1) return
      val inport = n.inports(0)
      
      val onlyOnes = n.actions.forall { a => a.inputPattern.forall { ip => ip.vars.size == 1 } }
      if (!onlyOnes) return
      
      val disjuncts = for (action <- n.actions) yield {
        val pres = for (pre <- action.requires) yield {
          val bounds = And(AtMost(Elements.str(inport.id),quantVar),Less(quantVar,Elements.tot0(inport.id)))
          val quantified = IndexReplacer.visitExpr(pre)(Map.empty)
          Forall(List(quantVar), Implies(bounds,quantified)): Expr
        }
        pres.foldLeft(BoolLiteral(true): Expr)((a,b) => And(a,b))
      }
      if (!disjuncts.isEmpty) {
        val disjunction = disjuncts.reduceLeft((a,b) => Or(a,b))
        n.addChannelInvariant(disjunction, false)
      }
    }
    
  }
  
  object StaticClass extends InferenceModule {
    override val name = "sdf-annot"
    
    val StaticAnnot = "static"
    val quantVar = Id("idx$"); quantVar.typ = IntType(32)
  
    def network(n: Network)(implicit ctx: Context) = {
      
      val countInvariants = new ListBuffer[Expr]
      val valueInvariants = new ListBuffer[Expr]
      
      val entities = 
        (for (m <- n.members) yield m match {
          case e: Entities => e.entities.filter { 
            i => {
              val static = isStatic(i.actor)
              if (i.actor.hasAnnotation(StaticAnnot) && !static) {
                ctx.error(i.actor.pos, "Actor '" + i.actor.id + "' is marked as static but cannot be verified to conform to the restrictions")
              }
              static && !i.actor.hasAnnotation(NoInferAnnot)
            }
          }
          case _ => Nil
        }).flatten
      
      val delayedChannels =  {
        val buffer = new ListBuffer[(String,Expr)]
        TokensDefFinder.visitExpr(n.actorInvariants map {nwi => nwi.expr})(buffer);
        buffer.toMap
      }

      for (e <- entities) {
        val action = e.actor.actions.filter{ a => !a.init }(0)
        
        for (op <- e.actor.outports) {
          
          val outRate = action.portOutputCount(op.id)
          
          val outChans = n.structure.get.outgoingConnections(e.id, op.id)
          
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
              val inRate = action.portInputCount(ip.id)
              val inChan = n.structure.get.incomingConnection(e.id, ip.id).get
              val ratedTot = 
                if (inRate == 1) tot0(oc.id)
                else Times(lit(inRate),tot0(oc.id))
              
              val ratedRd =
                if (outRate == 1) rd0(inChan.id)
                else Times(lit(outRate),rd0(inChan.id))
              
              val ratedDelayedTot = 
                if (delayedChannels contains oc.id) Minus(ratedTot,delayedChannels(oc.id))
                else ratedTot
                
              countInvariants += Eq(ratedRd,ratedDelayedTot)
              
              val ratedAt1 = 
                if (inRate == 1) str(oc.id)
                else Times(lit(inRate),str(oc.id))
                
              val ratedAt2 = 
                if (outRate == 1) str(inChan.id)
                else Times(lit(inRate),str(inChan.id))
                
              countInvariants += Eq(ratedAt1,ratedAt2)
            }
            
            val outFuncs = action.portOutputPattern(op.id).get.exps
            var k = 0
            for (fk <- outFuncs) {
              val lowBound = delayedChannels.get(oc.id) match {
                case None => str(oc.id)
                case Some(d) => Plus(str(oc.id),d)
              }
              val quantBounds = And(AtMost(lowBound,quantVar),Less(quantVar,tot0(oc.id)))
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
      n.addChannelInvariants(countInvariants.toList, false)
      n.addChannelInvariants(valueInvariants.toList, false)
    } // def network
    
    
    def isStatic(actor: DFActor): Boolean = {
      
      if (actor.isInstanceOf[Network]) return false
      
      var portRates = Map[String,Int]()
      
      val ports = (actor.inports:::actor.outports map { _.id }).toSet
      
      for (action <- actor.actions.filter { !_.init }) {
        
        var seenPorts = ports
        
        for (pat <- action.inputPattern ::: action.outputPattern) {
          seenPorts = seenPorts - pat.portId
          portRates.get(pat.portId) match {
            case Some(rate) =>
              if (pat.list.size != rate) return false
            case None =>
              portRates += (pat.portId -> pat.list.size)
          }
        }
        
        for (p <- seenPorts) {
          portRates.get(p) match {
            case Some(rate) =>
              if (0 != rate) return false
            case None =>
              portRates += (p -> 0)
          }
        }
      }
      return true
    }
    
  }
  
  object FTProperties extends InferenceModule {
    override val name = "ft-properties"
    
    val quantVar = Id("idx$"); quantVar.typ = IntType(32)
    val soundnessChecks = true
    
    override def network(n: Network)(implicit ctx: Context) {
      val action = n.actions(0)
      for (ipat <- action.inputPattern) {
        val channel = n.structure.get.getInputChannel(ipat.portId).get
        
        // Generate chinvariant: forall i . 0 <= i && i < tot(a) ==> sqn(a[i]) = i
        // where a is a network input channel
        val lowBound = lit(0)
        val quantBounds = And(AtMost(lowBound,quantVar),Less(quantVar,tot0(channel.id)))
        val cId = Id(channel.id); cId.typ = ChanType(ipat.vars(0).typ)
        val accessor = IndexAccessor(cId,quantVar); accessor.typ = ipat.vars(0).typ
        val sqn = sqnAcc(accessor); sqn.typ = IntType(32)
        val quantExp = Implies(quantBounds,Eq(sqn,quantVar))
        n.addChannelInvariant(Forall(List(quantVar),quantExp), !soundnessChecks)
        
      }
      
    }
  }
  
  abstract class InferenceModule {
    
    val name: String
    
    val NoInferAnnot = "noinfer"
    
    final def infer(ctx: Context, decl: TopDecl) = {
      decl match {
        case n: Network => network(n)(ctx)
        case _ =>
      }
      ctx.outcome
    }
    
    def network(n: Network)(implicit ctx: Context)
  }

}


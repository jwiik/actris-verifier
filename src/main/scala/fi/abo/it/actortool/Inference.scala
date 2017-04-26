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
  
  final val Modules = List(StaticClass,BulletInvariants,NWPreToInvariant).map(m => (m.name,m)).toMap
  private val DefaultModules = Set(StaticClass,BulletInvariants,NWPreToInvariant)
      
  def infer(program: List[TopDecl], typeCtx: Resolver.Context, modules: List[String], assumeInvariants: Boolean): InferenceOutcome = {
    val inferenceModules = modules match {
      case Nil => DefaultModules
      case List("default") => DefaultModules
      case list => (list map { l => Modules(l) }).toSet
    }
    
    val ctx = new Context
    
    for (module <- inferenceModules) {
      for (a <- program) module.infer(ctx,typeCtx,a, assumeInvariants)
    }
    
    return ctx.outcome
  }
  
  object NWPreToInvariant extends InferenceModule {
    override val name = "nw-precondition"
    val quantVar = Id("idx$"); quantVar.typ = IntType(-1)
    
    override def network(n: Network, typeCtx: Resolver.Context)(implicit ctx: Context, assumeInvs: Boolean): Unit = {
      generatePreconditionDisjunction(n, typeCtx)
      generateInputTokenLimit(n,typeCtx)
    }
    
    def generatePreconditionDisjunction(n: Network, typeCtx: Resolver.Context)(implicit ctx: Context, assumeInvs: Boolean) {
      val disjuncts = n.contractActions flatMap { action => {
        if (action.requires.isEmpty) Nil
        else List(action.requires reduceLeft { (a,b) => And(a,b) })
      }}
      if (!disjuncts.isEmpty) {
        val invariant = disjuncts reduceLeft { (a,b) => Or(a,b) }
        Resolver.resolveExpr(invariant, typeCtx)
        n.addChannelInvariant(invariant, assumeInvs)
      }
    }
    
    def generateInputTokenLimit(n: Network, typeCtx: Resolver.Context)(implicit ctx: Context, assumeInvs: Boolean) {
      val disjuncts: List[Expr] =
        n.actions map {
          action => {
            val preds = 
              for (ip <- n.inports) yield {
                action.inputPattern.find { pat => pat.portId == ip.id } match {
                  case Some(pattern) => AtMost(totb(ip.id,ChanType(ip.portType)), IntLiteral(pattern.rate))
                  case None => Eq(totb(ip.id,ChanType(ip.portType)), IntLiteral(0))
                }
              }
            preds.reduceLeft { (a,b) => And(a,b) }
          }
        }
      if (!disjuncts.isEmpty) {
        val invariant =  disjuncts reduceLeft { (a,b) => Or(a,b) }
        Resolver.resolveExpr(invariant, typeCtx)
        n.addChannelInvariant(invariant, assumeInvs)
      }
    }
    
  }
  
  object StaticClass extends StaticPropertyInferenceModule {
    override val name = "sdf-annot"
    
    val StaticAnnot = "static"
    val NoInferAnnot = "noinfer"
    val quantVar = Id("idx$"); quantVar.typ = IntType(-1)
    
    override def actor(actor: BasicActor, typeCtx: Resolver.Context)(implicit ctx: Context, assumeInvs: Boolean): Unit = {
      if (checkIfAmendable(actor, typeCtx)) {
        generateCountInvariants(actor, typeCtx)
        generateValueInvariants(actor, typeCtx)
      }
    }
    
    override def network(n: Network, typeCtx: Resolver.Context)(implicit ctx: Context, assumeInvs: Boolean): Unit = {
      if (checkIfAmendable(n, typeCtx)) {
        generateCountInvariants(n, typeCtx)
      }
    }
    
    def checkIfAmendable(actor: DFActor, typeCtx: Resolver.Context)(implicit ctx: Context): Boolean = {
      val static = isRateStatic(actor)
      if (actor.hasAnnotation(StaticAnnot) && !static) {
        ctx.error(actor.pos, "Actor '" + actor.id + "' is marked as static but cannot be verified to conform to the restrictions")
      }
      
      if (!static || actor.hasAnnotation(NoInferAnnot)) false
      else true
      
    }
    
    def collectData(actor: BasicActor, typeCtx: Resolver.Context)(implicit ctx: Context): (ActorAction,Map[String,Int]) = {
      val firstAction = actor.actorActions.filter{ a => !a.init }(0)
      val initAction = actor.actorActions.find{ a => a.init }
      
      val delayedChannels = initAction match {
        case Some(a) => {
          (a.outputPattern map { p => (p.portId, p.exps.size) }).toMap
        }
        case None => Map.empty[String,Int]
      }
      (firstAction,delayedChannels)
    }
    
    def generateCountInvariants(actor: DFActor, typeCtx: Resolver.Context)(implicit ctx: Context, assumeInvs: Boolean): Unit = {
      val countInvariants = new ListBuffer[Expr]

      val (firstAction,delayedChannels) = 
        if (actor.isActor) collectData(actor.asInstanceOf[BasicActor], typeCtx)
        else (actor.contractActions(0),Map.empty[String,Int])
      
      for (op <- actor.outports) {
        
        val outRate = firstAction.outportRate(op.id)
          
        val replacements = {
          val inputs = (for (ipat <- firstAction.inputPattern) yield {
            val inRate = firstAction.inportRate(ipat.portId)
            val portType = actor.getInport(ipat.portId).get.portType
            var i = 0
            for (v <- 0 to ipat.rate) yield {
              val cId = Id(ipat.portId); cId.typ = ChanType(portType)
              val rated = (inRate,outRate) match {
                case (1,1) => quantVar
                case (x,1) => Times(lit(x),quantVar)
                case (1,y) => Div(quantVar,lit(y))
                case (x,y) => Times(Div(lit(x),lit(y)),quantVar)
              }
              val idx = if (i == 0) rated else Plus(rated,lit(i))
              val delayAdjustedIdx =
                if (delayedChannels contains op.id) Minus(idx,lit(delayedChannels(op.id)))
                else idx
              val acc = IndexAccessor(cId,delayAdjustedIdx)
              acc.typ = portType
              i = i+1
              (v -> acc)
            }
          }).flatten
          //val params = (for ((p,a) <- (e.actor.parameters zip e.arguments)) yield {(Id(p.id) -> a)})
          (inputs/*:::params*/).toMap
        }
        
        for (ip <- actor.inports) {
          val inRate = firstAction.inportRate(ip.id)
          val ratedTot = 
            if (inRate == 1) tot(op.id,ChanType(op.portType))
            else Times(lit(inRate),tot(op.id,ChanType(op.portType)))
          
          val ratedRd =
            if (outRate == 1) rd(ip.id,ChanType(ip.portType))
            else Times(lit(outRate),rd(ip.id,ChanType(ip.portType)))
          
          val ratedDelayedTot = 
            if (delayedChannels contains op.id) Minus(ratedTot,lit(delayedChannels(op.id)))
            else ratedTot
            
          countInvariants += Eq(ratedRd,ratedDelayedTot)
        }
      }
      countInvariants.foreach { inv => Resolver.resolveExpr(inv, typeCtx) }
      actor.addInvariants(countInvariants.toList, assumeInvs)
    }
    
    def generateValueInvariants(actor: BasicActor, typeCtx: Resolver.Context)(implicit ctx: Context, assumeInvs: Boolean): Unit = {
      if (!isStateless(actor)) return
      
      val valueInvariants = new ListBuffer[Expr]
      val (firstAction,delayedChannels) = collectData(actor, typeCtx)
      
      for (op <- actor.outports) {
        
        val outRate = firstAction.outportRate(op.id)
        
        val replacements = {
          val inputs = (for (ipat <- firstAction.inputPattern) yield {
            val inRate = firstAction.inportRate(ipat.portId)
            var i = 0
            for (v <- ipat.vars) yield {
              val cId = Id(ipat.portId); cId.typ = ChanType(v.typ)
              val rated = (inRate,outRate) match {
                case (1,1) => quantVar
                case (x,1) => Times(lit(x),quantVar)
                case (1,y) => Div(quantVar,lit(y))
                case (x,y) => Times(Div(lit(x),lit(y)),quantVar)
              }
              val idx = if (i == 0) rated else Plus(rated,lit(i))
              val delayAdjustedIdx =
                if (delayedChannels contains op.id) Minus(idx,lit(delayedChannels(op.id)))
                else idx
              val acc = IndexAccessor(cId,delayAdjustedIdx)
              acc.typ = v.typ
              i = i+1
              (v -> acc)
            }
          }).flatten
          //val params = (for ((p,a) <- (e.actor.parameters zip e.arguments)) yield {(Id(p.id) -> a)})
          (inputs/*:::params*/).toMap
        }
        
        val exps = (for (i <- 0 to firstAction.portOutputPattern(op.id).get.rate-1) yield {
          (for (a <- actor.actorActions.filter{ !_.init  }) yield {
            (a.guard,a.portOutputPattern(op.id).get.asInstanceOf[OutputPattern].exps(i))
          })
        }).toList
        
        val lowBound = delayedChannels.get(op.id) match {
          case None => lit(0)
          case Some(d) => lit(d)
        }
        val quantBounds = And(AtMost(lowBound,quantVar),Less(quantVar,tot(op.id,ChanType(op.portType))))
          
        for ((list,k) <- exps.zipWithIndex) {
          
          val bounds = // If there is more than one output we need differentiate with mod
            if (1 < firstAction.portOutputPattern(op.id).get.asInstanceOf[OutputPattern].exps.size) 
              And(quantBounds,Eq(Mod(quantVar,lit(outRate)),lit(k)))
            else 
              quantBounds
          
          val guardedExps = for ((guard,exp) <- list) yield {
            
            val eRenamed = IdReplacer.visitExpr(exp)(replacements)
            val cId = Id(op.id); cId.typ = ChanType(exp.typ)
            val acc = IndexAccessor(cId,quantVar); acc.typ = exp.typ
            val eqExp = Eq(acc,eRenamed)
            guard match {
              case Some(g) => {
                Implies(IdReplacer.visitExpr(g)(replacements),eqExp)
              }
              case None => eqExp
            }
            
          }
          
          val conjunction = guardedExps.reduceLeft((a,b) => And(a,b))
          
          val quantExp = Implies(bounds,conjunction)
          valueInvariants += Forall(List(quantVar), quantExp)
        }
      } // for
      
      valueInvariants.foreach { inv => Resolver.resolveExpr(inv, typeCtx) }
      actor.addInvariants(valueInvariants.toList, assumeInvs)
    }
    
    
    
  }
  
  object BulletInvariants extends StaticPropertyInferenceModule {
    override val name = "bullet-invariants"
    
    val StaticAnnot = "static"
    val NoInferAnnot = "noinfer"
  
    override def network(n: Network, typeCtx: Resolver.Context)(implicit ctx: Context, assumeInvs: Boolean) = {
      
      val countInvariants = new ListBuffer[Expr]
      val valueInvariants = new ListBuffer[Expr]
      
      val entities = 
        (for (m <- n.members) yield m match {
          case e: Entities => e.entities.filter { 
            i => {
              val static = isRateStatic(i.actor)
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
        val action = 
          if (e.actor.isActor) e.actor.actorActions.filter{ a => !a.init }(0)
          else e.actor.contractActions(0)
        
        for (op <- e.actor.outports) {
          
          val outRate = action.outportRate(op.id)
          val outChan = n.structure.get.outgoingConnections(e.id, op.id).get
            
          for (ip <- e.actor.inports) {
            val inRate = action.inportRate(ip.id)
            val inChan = n.structure.get.incomingConnection(e.id, ip.id).get
            
            val ratedAt1 = 
              if (inRate == 1) bullet(outChan.id,ChanType(op.portType))
              else Times(lit(inRate),bullet(outChan.id,ChanType(op.portType)))
              
            val ratedAt2 = 
              if (outRate == 1) bullet(inChan.id,ChanType(ip.portType))
              else Times(lit(outRate),bullet(inChan.id,ChanType(ip.portType)))
              
            countInvariants += Eq(ratedAt1,ratedAt2)
          }
        } // for
      } // for
      countInvariants foreach { inv => Resolver.resolveExpr(inv, typeCtx) }
      n.addChannelInvariants(countInvariants.toList, assumeInvs)
    } // def network
  }
  
  abstract class InferenceModule {
    
    val name: String
    
    final def infer(ctx: Context, typeCtx: Resolver.Context, decl: TopDecl, assumeInvariants: Boolean) = {
      decl match {
        case n: Network => network(n,typeCtx)(ctx, assumeInvariants)
        case a: BasicActor => actor(a,typeCtx)(ctx, assumeInvariants)
        case _ =>
      }
      ctx.outcome
    }
    
    def network(n: Network, typeCtx: Resolver.Context)(implicit ctx: Context, assumeInvariants: Boolean): Unit = {}
    def actor(a: BasicActor, typeCtx: Resolver.Context)(implicit ctx: Context, assumeInvariants: Boolean): Unit = {}
  }
  
  abstract class StaticPropertyInferenceModule extends InferenceModule {
    
    def isStateless(actor: DFActor): Boolean = {
      actor.isInstanceOf[BasicActor] && actor.variables.isEmpty
    }
    
    def isRateStatic(actor: DFActor): Boolean = {
      var portRates = Map[String,Int]()
      val ports = (actor.inports:::actor.outports map { _.id }).toSet
      for (action <- actor.actorActions.filter { !_.init }) {
        var seenPorts = ports
        for (pat <- action.allPatterns) {
          seenPorts = seenPorts - pat.portId
          portRates.get(pat.portId) match {
            case Some(rate) =>
              if (pat.rate != rate) return false
            case None =>
              portRates += (pat.portId -> pat.rate)
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

}


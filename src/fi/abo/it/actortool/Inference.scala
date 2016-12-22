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
  
  final val Modules = List(StaticClass,BulletInvariants,NWPreToInvariant,FTProperties).map(m => (m.name,m)).toMap
  private val DefaultModules = Set(StaticClass,BulletInvariants,NWPreToInvariant)
      
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
    
    override def network(n: Network)(implicit ctx: Context): Unit = {
      val disjuncts = n.actions flatMap { action => {
        if (action.requires isEmpty) Nil
        else List(action.requires reduceLeft { (a,b) => And(a,b) })
      }}
      if (!disjuncts.isEmpty) {
        val invariant = disjuncts reduceLeft { (a,b) => Or(a,b) }
        n.addChannelInvariant(invariant, true)
      }
    }
    
//    object IndexReplacer extends ASTReplacingVisitor[IndexAccessor,IndexAccessor] {
//      override def visitExpr(expr: Expr)(implicit map: Map[IndexAccessor,IndexAccessor]): Expr = {
//        expr match {
//          case IndexAccessor(ch,index) => index match {
//            case SpecialMarker("@") => return IndexAccessor(ch,quantVar)
//            case _ => return super.visitExpr(expr)
//          }
//          case _ => return super.visitExpr(expr)
//        }
//      }
//    }
//    
//    override def network(n: Network)(implicit ctx: Context): Unit = {
//      if (n.inports.size != 1) return
//      val inport = n.inports(0)
//      
//      val onlyOnes = n.actions.forall { a => a.inputPattern.forall { ip => ip.vars.size == 1 } }
//      if (!onlyOnes) return
//      
//      val disjuncts = for (action <- n.actions) yield {
//        val pres = for (pre <- action.requires) yield {
//          val bounds = And(AtMost(Elements.str(inport.id),quantVar),Less(quantVar,Elements.tot0(inport.id)))
//          val quantified = IndexReplacer.visitExpr(pre)(Map.empty)
//          Forall(List(quantVar), Implies(bounds,quantified)): Expr
//        }
//        pres.foldLeft(BoolLiteral(true): Expr)((a,b) => And(a,b))
//      }
//      if (!disjuncts.isEmpty) {
//        val disjunction = disjuncts.reduceLeft((a,b) => Or(a,b))
//        n.addChannelInvariant(disjunction, false)
//      }
//    }
    
  }
  
  object StaticClass extends StaticPropertyInferenceModule {
    override val name = "sdf-annot"
    
    val StaticAnnot = "static"
    val NoInferAnnot = "noinfer"
    val quantVar = Id("idx$"); quantVar.typ = IntType(32)
    
    override def actor(actor: BasicActor)(implicit ctx: Context): Unit = {
      val countInvariants = new ListBuffer[Expr]
      val valueInvariants = new ListBuffer[Expr]
      
      val static = isStatic(actor)
      if (actor.hasAnnotation(StaticAnnot) && !static) {
        ctx.error(actor.pos, "Actor '" + actor.id + "' is marked as static but cannot be verified to conform to the restrictions")
      }
      
      if (!static || actor.hasAnnotation(NoInferAnnot)) return
      
      val firstAction = actor.actions.filter{ a => !a.init }(0)
      val initAction = actor.actions.find{ a => a.init }
      
      val delayedChannels = initAction match {
        case Some(a) => {
          (a.outputPattern map { p => (p.portId, p.exps.size) }).toMap
        }
        case None => Map.empty[String,Int]
      }
        
      for (op <- actor.outports) {
        
        val outRate = firstAction.portOutputCount(op.id)
          
        val replacements = {
          val inputs = (for (ipat <- firstAction.inputPattern) yield {
            val inRate = firstAction.portInputCount(ipat.portId)
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
        
        for (ip <- actor.inports) {
          val inRate = firstAction.portInputCount(ip.id)
          val ratedTot = 
            if (inRate == 1) tot0(op.id)
            else Times(lit(inRate),tot0(op.id))
          
          val ratedRd =
            if (outRate == 1) rd0(ip.id)
            else Times(lit(outRate),rd0(ip.id))
          
          val ratedDelayedTot = 
            if (delayedChannels contains op.id) Minus(ratedTot,lit(delayedChannels(op.id)))
            else ratedTot
            
          countInvariants += Eq(ratedRd,ratedDelayedTot)
        }
        
        
        val exps = (for (i <- 0 to firstAction.portOutputPattern(op.id).get.exps.size-1) yield {
          (for (a <- actor.actions.filter{ !_.init  }) yield {
            (a.guard,a.portOutputPattern(op.id).get.exps(i))
          })
        }).toList
        
        val lowBound = delayedChannels.get(op.id) match {
          case None => lit(0)
          case Some(d) => lit(d)
        }
        val quantBounds = And(AtMost(lowBound,quantVar),Less(quantVar,tot0(op.id)))
          
        for ((list,k) <- exps.zipWithIndex) {
          
          val bounds = // If there is more than one output we need differentiate with mod
            if (1 < firstAction.portOutputPattern(op.id).get.exps.size) 
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
      
      actor.addInvariants(countInvariants.toList, false)
      actor.addInvariants(valueInvariants.toList, false)
      
    }
  }
  
  object BulletInvariants extends StaticPropertyInferenceModule {
    override val name = "bullet-invariants"
    
    val StaticAnnot = "static"
    val NoInferAnnot = "noinfer"
  
    override def network(n: Network)(implicit ctx: Context) = {
      
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
          val outChan = n.structure.get.outgoingConnections(e.id, op.id).get
            
          for (ip <- e.actor.inports) {
            val inRate = action.portInputCount(ip.id)
            val inChan = n.structure.get.incomingConnection(e.id, ip.id).get
            
            val ratedAt1 = 
              if (inRate == 1) str(outChan.id)
              else Times(lit(inRate),str(outChan.id))
              
            val ratedAt2 = 
              if (outRate == 1) str(inChan.id)
              else Times(lit(outRate),str(inChan.id))
              
            countInvariants += Eq(ratedAt1,ratedAt2)
          }
        } // for
      } // for
      n.addChannelInvariants(countInvariants.toList, false)
    } // def network
  }
  
  object FTProperties extends InferenceModule {
    override val name = "ft-properties"
    
    val quantVar = Id("idx$"); quantVar.typ = IntType(32)
    val soundnessChecks = true
    
    override def network(n: Network)(implicit ctx: Context) {
//      val action = n.actions(0)
//      for (ipat <- action.inputPattern) {
//        val channel = n.structure.get.getInputChannel(ipat.portId).get
//        
//        // Generate chinvariant: forall i . 0 <= i && i < tot(a) ==> sqn(a[i]) = i
//        // where a is a network input channel
//        val lowBound = lit(0)
//        val quantBounds = And(AtMost(lowBound,quantVar),Less(quantVar,tot0(channel.id)))
//        val cId = Id(channel.id); cId.typ = ChanType(ipat.vars(0).typ)
//        val accessor = IndexAccessor(cId,quantVar); accessor.typ = ipat.vars(0).typ
//        val sqn = sqnAcc(accessor); sqn.typ = IntType(32)
//        val quantExp = Implies(quantBounds,Eq(sqn,quantVar))
//        n.addChannelInvariant(Forall(List(quantVar),quantExp), !soundnessChecks)
//        
//      }
//      
    }
  }
  
  abstract class InferenceModule {
    
    val name: String
    
    final def infer(ctx: Context, decl: TopDecl) = {
      decl match {
        case n: Network => network(n)(ctx)
        case a: BasicActor => actor(a)(ctx)
        case _ =>
      }
      ctx.outcome
    }
    
    def network(n: Network)(implicit ctx: Context): Unit = {}
    def actor(a: BasicActor)(implicit ctx: Context): Unit = {}
  }
  
  abstract class StaticPropertyInferenceModule extends InferenceModule {
    def isStatic(actor: DFActor): Boolean = {
      if (actor.isInstanceOf[Network]) return false
      if (!actor.variables.isEmpty) return false
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

}


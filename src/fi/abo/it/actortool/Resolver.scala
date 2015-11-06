package fi.abo.it.actortool

import scala.util.parsing.input.Position
import scala.util.parsing.input.Positional
import collection.mutable.ListBuffer

object Resolver {
  
  sealed abstract class ResolverOutcome
  case class Success() extends ResolverOutcome
  case class Errors(ss: List[(Position,String)]) extends ResolverOutcome
  
  sealed abstract class Context(val parent: Context) {
    def error(p: Position, msg: String)
    def lookUp(id: String): Option[Declaration] = None
    def currentAccessedElement: Option[Expr] = None
  }
  
  sealed class RootContext(val parentCtx: Context, val actors: Map[String,Actor]) extends Context(parentCtx) {
    val errors: ListBuffer[(Position,String)] = new ListBuffer()
    def error(p: Position, msg: String) = { errors += ((p,msg))}
    override def lookUp(id: String): Option[Declaration] = None
  }
  
  sealed abstract class ChildContext(val parentCtx: Context, val vars: Map[String,Declaration]) extends Context(parentCtx) {
    override def lookUp(id: String): Option[Declaration] = if (vars contains id) Some(vars(id)) else parentCtx.lookUp(id)
    override def error(p: Position, msg: String) = parentCtx.error(p,msg)
  }
  
  sealed class ActorContext(override val parentCtx: RootContext, override val vars: Map[String,Declaration], 
      val inports: Map[String,InPort], val outports: Map[String,OutPort]) extends ChildContext(parentCtx,vars) {
    
    private var channels = Map[String,Declaration]()
    
    def addChannels(channels: Map[String,Declaration]) = {
      this.channels = channels
    }
    
    override def lookUp(id: String): Option[Declaration] = {
      if (vars contains id) Some(vars(id))
      else if (channels contains id) Some(channels(id))
      else  parentCtx.lookUp(id)
    }
  }
  
  
  sealed class ActionContext(override val parentCtx: Context, 
      override val vars: Map[String,Declaration]) extends ChildContext(parentCtx,vars)
  
  sealed class QuantifierContext(override val parentCtx: Context, 
      override val vars: Map[String,Declaration]) extends ChildContext(parentCtx,vars)
  
  sealed class AccessorContext(override val parentCtx: Context, accessor: Expr) extends ChildContext(parentCtx,Map.empty) {
    override def currentAccessedElement = Some(accessor)
  }

  def resolve(prog: List[Actor]): ResolverOutcome = {
    var decls = Map[String,Actor]()
    
    for (decl <- prog) {
      if (decls contains decl.id) {
        return Errors(List((decl.pos,"Duplicate actor name: " + decl.id)))
      }
      decls = decls + (decl.id -> decl) 
    }
    
    val rootCtx = new RootContext(null,decls)
    
    for (decl <- prog) {
      var inports = Map[String,InPort]()
      var outports = Map[String,OutPort]()
      for (p <- decl.inports) {
        if (inports contains p.id) rootCtx.error(p.pos, "Duplicate port: " + p.id)
        inports = inports + (p.id -> p)
      }
      for (p <- decl.outports) {
        if ((inports contains p.id) || (outports contains p.id)) {
          rootCtx.error(p.pos, "Duplicate port: " + p.id)
        }
        outports = outports + (p.id -> p)
      }
      decl match {
        case a: BasicActor => {
          var vars = Map[String,Declaration]()
          
          for (m <- a.members) m match {
            case d: Declaration => vars = vars + (d.id -> d)
            case _ =>
          }

          val ctx = new ActorContext(rootCtx, vars, inports, outports)
          var schedule: Option[Schedule] = None
          val actions = new ListBuffer[Action]()
          for (m <- a.members) m match {
            case ac: Action => 
              resolveAction(ctx,ac)
              actions += ac
            case ActorInvariant(e,_) => resolveExpr(ctx,e,BoolType)
            case ci: ChannelInvariant =>
              return Errors(List((ci.pos, "Basic actors cannot have channel invariants")))
            case e: Entities =>
              return Errors(List((e.pos, "Basic actors cannot have a entities block")))
            case s: Structure =>
              return Errors(List((s.pos, "Basic actors cannot have a structure block")))
            case Declaration(_,_,_) => // Already handled
            case sc: Schedule => schedule = Some(sc)
          }
          schedule match {
            case Some(s) => resolveSchedule(ctx, actions.toList, s)
            case None =>
          }
          
        }  
        case n: Network => {
          var inports = Map[String,InPort]()
          var outports = Map[String,OutPort]()
          var entities: Map[String,Actor] = null
          for (p <- n.inports) {
            inports = inports + (p.id -> p)
          }
          for (p <- n.outports) {
            outports = outports + (p.id -> p)
          }
          
          val ctx = new ActorContext(rootCtx, Map[String,Declaration](), inports, outports) 

          var hasEntities, hasStructure = false
          var channels = Map.empty[String,Declaration]
          for (m <- n.members) {
            m match {
              case e: Entities =>
                if (hasEntities) 
                  return Errors(List((e.pos,"Multiple entities blocks in network " + n.id)))
                entities = resolveEntities(ctx,e)
                hasEntities = true
              case s: Structure =>
                if (!hasEntities)
                  return Errors(List((s.pos,"Structure block encountered before entities block")))
                if (hasStructure)
                  return Errors(List((s.pos,"Multiple structure blocks in network " + n.id)))
                channels = resolveStructure(ctx,entities,s)
                hasStructure = true
              case _ =>
            }
          }
          
          ctx.addChannels(channels)
                    
          for (m <- n.members) {
            m match {
              case ac@Action(lbl,init,inPat,outPat,guard,pres,posts,vars,body) => {
                guard match {
                  case Some(g) => 
                    return Errors(List((g.pos,"Network actions are not allowed to have guards")))
                  case None => // OK
                }
                body match {
                  case Some(body) => 
                    return Errors(List((ac.pos,"Network actions are not allowed to have bodies")))
                  case None => // OK
                }
                resolveAction(ctx, ac)
              }
              case e: Entities =>  // Already handled
              case s: Structure => // Already handled 
              case ActorInvariant(e,_) => resolveExpr(ctx,e,BoolType)
              case ChannelInvariant(e,_) => resolveExpr(ctx,e,BoolType)
              case d: Declaration => return Errors(List((d.pos, "Networks cannot have declarations")))
              case sch: Schedule => return Errors(List((sch.pos,"Networks cannot have schedules")))
            }
          }
          if (!hasEntities) return Errors(List((n.pos, "No entities block in " + n.id)))
          if (!hasStructure) return Errors(List((n.pos, "No structure block in " + n.id)))
        }
      } 
    } // End for
    if (rootCtx.errors.isEmpty) Success() else Errors(rootCtx.errors.toList)
  }
  
  def resolveAction(actorCtx: ActorContext, action: Action) {
    if (action.init && action.inputPattern.length > 0) {
      actorCtx.error(action.pos, "Input patterns not allowed for intialize actions")
    }
    var vars = Map[String,Declaration]()
    var portWithPat = Set[String]()
    for (inPat <- action.inputPattern) {
      if (portWithPat contains inPat.portId) {
        actorCtx.error(inPat.pos, "Multiple patterns for port: " + inPat.portId)
        return
      }
      else portWithPat = portWithPat + inPat.portId
      if (! (actorCtx.inports contains inPat.portId)) {
        actorCtx.error(inPat.pos, "Undeclared inport: " + inPat.portId)
        return
      }
      val pDecl = actorCtx.inports(inPat.portId)
      for (v <- inPat.vars) {
        if (vars contains v.id) actorCtx.error(inPat.pos, "Variable name already used: " + v.id)
        val d = Declaration(v.id,pDecl.portType,false)
        v.typ = actorCtx.inports(inPat.portId).portType
        vars = vars + (d.id -> d)
      }
    }
    val ctx = new ActionContext(actorCtx,vars)
    action.guard match {
      case Some(g) => resolveExpr(ctx, g, BoolType)
      case None =>
    }
    
    for (pre <- action.requires) resolveExpr(ctx, pre, BoolType)
    for (post <- action.ensures) resolveExpr(ctx, post, BoolType)
    
    for (outPat <- action.outputPattern) {
      if (portWithPat contains outPat.portId) {
        actorCtx.error(outPat.pos, "Multiple patterns for port: " + outPat.portId)
        return
      }
      else portWithPat = portWithPat + outPat.portId
      if (! (actorCtx.outports contains outPat.portId)) {
        actorCtx.error(outPat.pos, "Undeclared outport: " + outPat.portId)
        return
      }
      val pDecl = actorCtx.outports(outPat.portId)
      for (e <- outPat.exps) {
        assert(pDecl.portType != null)
        resolveExpr(ctx,e,pDecl.portType)
      }
    }
    action.body match {
      case Some(stmt) => resolveStmt(ctx,stmt)
      case None =>
    }
  }
  
  def resolveEntities(ctx: ActorContext, e: Entities): Map[String,Actor] = {
    var instances = Map[String,Actor]()
    for (instance <- e.entities) {
      if (!(ctx.parentCtx.actors contains instance.actorId)) {
        ctx.error(instance.pos, "Unknown actor " + instance.actorId)
        return instances
      }
      if (instances contains instance.id) {
        ctx.error(instance.pos, "Instance id already used " + instance.id)
        return instances
      }
      val actor = ctx.parentCtx.actors(instance.actorId)
      instance.actor = actor
      instances = instances + (instance.id -> actor)
    }
    instances
  }
  
  def resolveStructure(ctx: ActorContext, entities: Map[String,Actor], structure: Structure) = {
    var channels = Map[String,Declaration]()
    for (c <- structure.connections) {
      val from = c.from match {
        case PortRef(Some(a),p) =>
          entities.get(a) match {
            case None =>
              ctx.error(c.from.pos, "Unknown actor: " + a)
              None
            case Some(actor) =>
              actor.getOutport(p)
          }
        case PortRef(None,p) =>
          ctx.inports.get(p) match {
            case None =>
              ctx.error(c.from.pos, "Unknown network inport: " + p)
              None
            case Some(ip) => Some(ip)
          }
      }
      val to = c.to match {
        case PortRef(Some(a),p) =>
          entities.get(a) match {
            case None =>
              ctx.error(c.to.pos, "Unknown actor: " + a)
              None
            case Some(actor) =>
              actor.getInport(p)
          }
        case PortRef(None,p) =>
          ctx.outports.get(p) match {
            case None =>
              ctx.error(c.to.pos, "Unknown network outport: " + p)
              None
            case Some(op) => Some(op)
          }
      }
      (from, to) match {
        case (None,_) => ctx.error(c.from.pos, "Unknown port")
        case (_,None) => ctx.error(c.to.pos, "Unknown port")
        case (Some(f),Some(t)) =>
          if (f.portType != t.portType) ctx.error(c.from.pos, "Incompatible port types")
          c.typ = f.portType
          channels = channels + (c.id -> Declaration(c.id,ChanType(c.typ),true))
      }
    }
    channels
  }
  
  def resolveSchedule(ctx: Context, actions: List[Action], sch: Schedule): Set[String] = {
    import scala.collection.mutable.ListMap
    val states = new scala.collection.mutable.HashSet[String]
    val trans = new ListMap[String,ListMap[String,String]]
    
    val actionMap = actions.map(a => (a.fullName,a)).toMap
    
    states += sch.initState
    for (t <- sch.transitions) {
      states += t.from
      states += t.to
      if (! (actionMap contains t.action)) {
        ctx.error(t.pos, "Undeclared action: " + t.action)
      }
      if (!(trans contains t.action)) {
        trans(t.action) = new ListMap[String,String]
      }
      
      if (trans(t.action) contains t.from) {
        ctx.error(t.pos, "Duplicate transition from state " + t.from + " with action " + t.action)
      }
      else {
        trans(t.action) += (t.from -> t.to)
      }
    } 
    
    for (t <- trans.keys) {
      actionMap(t).transitions = trans(t).toList
    }
    states.toSet
  }
  
  def resolveExpr(ctx: Context, exp: Expr, t: Type) {
    if (t != resolveExpr(ctx,exp)) ctx.error(exp.pos, "Expected type " + t.id)
  }
  
  def resolveExpr(ctx: Context, exp: Expr): Type = {
    exp match {
      case op: Plus => resolveNumericBinaryExpr(ctx, op)
      case op: Minus => resolveNumericBinaryExpr(ctx, op)
      case op: Times => resolveNumericBinaryExpr(ctx, op)
      case op: Div => resolveNumericBinaryExpr(ctx, op)
      case op: Mod => resolveNumericBinaryExpr(ctx, op)
      case m@UnMinus(e) =>
        val t = resolveExpr(ctx,e)
        if (!t.isNumeric) ctx.error(m.pos, "Expected numeric type, found: " + t.id)
        m.typ = t
        m.typ
      case op: And => resolvePredicate(ctx,op)
      case op: Or => resolvePredicate(ctx,op)
      case op: Implies => resolvePredicate(ctx,op)
      case op: Iff => resolvePredicate(ctx,op)
      case n@Not(e) =>
        val t = resolveExpr(ctx,e)
        if (!t.isBool) ctx.error(n.pos, "Expected bool, found: " + t.id)
        n.typ = BoolType
        n.typ
      case op: Less => resolveRelationalExpr(ctx, op)
      case op: Greater => resolveRelationalExpr(ctx, op)
      case op: AtLeast => resolveRelationalExpr(ctx, op)
      case op: AtMost => resolveRelationalExpr(ctx, op)
      case op: Eq => resolveEqRelationalExpr(ctx, op)
      case op: NotEq => resolveEqRelationalExpr(ctx, op)
      case q: Forall => resolveQuantifier(ctx,q)
      case q: Exists => resolveQuantifier(ctx,q)
      case ite@IfThenElse(cond,then,els) =>
        val tCond = resolveExpr(ctx, cond)
        if (!tCond.isBool) ctx.error(cond.pos, "Expected bool, found: " + tCond.id)
        val tThen = resolveExpr(ctx, then)
        val tElse = resolveExpr(ctx, els)
        if (tThen != tElse) ctx.error(exp.pos, "Illegal argument types: " + tThen.id + " and " + tElse.id)
        ite.typ = tThen
        tThen
      case ac@IndexAccessor(e1,e2) =>
        val tExp = resolveExpr(ctx,e1)
        val accessorCtx = new AccessorContext(ctx,e1)
        if (!tExp.isIndexed) {
          ctx.error(e1.pos, "Expected indexed type, found: " + tExp.id)
          UnknownType
        } 
        else {
          val indexedType = tExp.asInstanceOf[IndexedType]
          val tInd = resolveExpr(accessorCtx,e2)
          if (tInd != indexedType.indexType) 
            ctx.error(e2.pos, "Expected " + indexedType.indexType + ", found: " + tInd.id)
          ac.typ = indexedType.resultType
          indexedType.resultType
        }
      case fa@FunctionApp("rd",params) => resolveChannelCountFunction(ctx, fa)
      case fa@FunctionApp("urd",params) => resolveChannelCountFunction(ctx, fa)
      case fa@FunctionApp("tot",params) => resolveChannelCountFunction(ctx, fa)
      case fa@FunctionApp("initial",params) => resolveChannelCountFunction(ctx, fa)
      case fa@FunctionApp("tokens",params) => resolveDelayFunction(ctx, fa)
      case is@IndexSymbol(name) => {
//        if (!params.isEmpty) {
//          if (1 < params.size) ctx.error(fa.pos, "Function last takes at most one parameter")
//          val argType = resolveExpr(ctx,params(0))
//          if (!argType.isInt) ctx.error(params(0).pos,"Expected integer type")
//        }
        ctx.currentAccessedElement match {
          case Some(e) => is.indexedExpr = e
          case None => ctx.error(is.pos, "Index '"+name+"' not used in an accessor context")
        }
        is.typ = IntType(32)
        IntType(32)
      }
      case fa@FunctionApp(name,params) => {
        ctx.error(fa.pos,"Undefined function: " + name)
        UnknownType
      }
      case BoolLiteral(_) => BoolType
      case IntLiteral(_) => IntType(32)
      case FloatLiteral(_) => throw new IllegalArgumentException()
      case v@Id(id) =>
        ctx.lookUp(id) match {
          case Some(d) => 
            v.typ = d.typ
            v.typ
          case None => 
            ctx.error(exp.pos, "Unknown variable: " + id)
            UnknownType
        }
        
    }
  }
  
  def resolveNumericBinaryExpr(ctx: Context, exp: BinaryExpr): Type = {
    val t1 = resolveExpr(ctx, exp.left)
    val t2 = resolveExpr(ctx, exp.right)
    if (!t1.isNumeric) ctx.error(exp.left.pos, "Expected numeric type, found: " + t1.id)
    if (!t2.isNumeric) ctx.error(exp.right.pos, "Expected numeric type, found: " + t2.id)
    if (t1 != t2) ctx.error(exp.pos, "Illegal argument types: " + t1.id + " and " + t2.id)
    exp.typ = t1
    exp.typ
  }
  
  def resolvePredicate(ctx: Context, exp: BinaryExpr): Type = {
    val t1 = resolveExpr(ctx, exp.left)
    val t2 = resolveExpr(ctx, exp.right)
    if (!t1.isBool) ctx.error(exp.left.pos, "Expected type bool: " + exp.left)
    if (!t2.isBool) ctx.error(exp.right.pos, "Expected type bool: " + exp.right)
    exp.typ = BoolType
    exp.typ
  }
  
  def resolveRelationalExpr(ctx: Context, exp: BinaryExpr): Type = {
    val t1 = resolveExpr(ctx, exp.left)
    val t2 = resolveExpr(ctx, exp.right)
    if (!t1.isNumeric) ctx.error(exp.left.pos, "Expected numeric type: " + exp.left)
    if (!t2.isNumeric) ctx.error(exp.right.pos, "Expected numeric type: " + exp.right)
    if (t1 != t2) ctx.error(exp.pos, "Illegal argument types: " + t1.id + " and " + t2.id)
    exp.typ = BoolType
    exp.typ
  }
  
  def resolveEqRelationalExpr(ctx: Context, exp: BinaryExpr): Type = {
    val t1 = resolveExpr(ctx, exp.left)
    val t2 = resolveExpr(ctx, exp.right)
    if (t1 != t2) ctx.error(exp.pos, "Illegal argument types: " + t1.id + " and " + t2.id)
    exp.typ = BoolType
    exp.typ
  }
  
  def resolveQuantifier(ctx: Context, quant: Quantifier): Type = {
    var decls = Map[String,Declaration]()
    for (d <- quant.vars) {
      decls = decls + (d.id -> d)
    }
    val quantCtx = new QuantifierContext(ctx, decls)
    val t = resolveExpr(quantCtx, quant.expr)
    if (!t.isBool) ctx.error(quant.expr.pos, "Expected type bool: " + quant.expr)
    quant.pattern match {
      case Some(e) => resolveExpr(quantCtx,e)
      case None =>
    }
    quant.typ = BoolType
    quant.typ
  }
  
  def resolveChannelCountFunction(ctx: Context, fa: FunctionApp): Type = {
      if (fa.parameters.size != 1) {
        ctx.error(fa.pos,"Function " + fa.name + " takes exactly 1 argument")
        IntType(32)
      }
      val paramType = resolveExpr(ctx,fa.parameters(0))
      if (!paramType.isChannel) {
        ctx.error(fa.pos,"The argument to function " + fa.name + " must be a channel")
      }
      fa.typ = IntType(32)
      IntType(32)
  }
  
  def resolveDelayFunction(ctx: Context, fa: FunctionApp): Type = {
    if (fa.parameters.size != 2) {
        ctx.error(fa.pos,"Function " + fa.name + " takes exactly 2 argument")
        IntType(32)
    }
    val paramType = resolveExpr(ctx,fa.parameters(0))
    if (!paramType.isChannel) {
      ctx.error(fa.parameters(0).pos,"The first argument to function " + fa.name + " must be a channel")
    }
    val amountType = resolveExpr(ctx,fa.parameters(1))
    if (!amountType.isInt) {
      ctx.error(fa.parameters(1).pos,"The second argument to function " + fa.name + " must be a integer")
    }
    BoolType
  }
  
  def resolveStmt(ctx: Context, stmts: List[Stmt]): Unit =
    for (stmt <- stmts) resolveStmt(ctx, stmt)
  
  def resolveStmt(ctx: Context, stmt: Stmt): Unit = stmt match {
    case Assignment(id,exp) =>
      val it = resolveExpr(ctx,id)
      val et = resolveExpr(ctx, exp)
      if (it != et) 
        ctx.error(id.pos, "Cannot assign value of type " + et.id + " to variable of type " + it.id)
    case While(cond,invs,body) =>
      resolveExpr(ctx,cond,BoolType)
      for (i <- invs) resolveExpr(ctx,i,BoolType)
      resolveStmt(ctx,body)
    case IfElse(ifCond,ifStmt,elseIfs,elseStmt) =>
      resolveExpr(ctx,ifCond,BoolType)
      resolveStmt(ctx,ifStmt)
      for (elseIf <- elseIfs) {
        resolveExpr(ctx,elseIf.cond,BoolType)
        resolveStmt(ctx,elseIf.stmt)
      }
      resolveStmt(ctx,elseStmt)
    case Havoc(vars) => for (v <- vars) resolveExpr(ctx,v)
    case Assert(e) => resolveExpr(ctx,e,BoolType)
    case Assume(e) => resolveExpr(ctx,e,BoolType)
    
  }
}

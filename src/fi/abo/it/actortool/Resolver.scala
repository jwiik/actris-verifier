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
    def actors = Map.empty[String,Actor]
  }
  
  sealed class RootContext(val parentCtx: Context, override val actors: Map[String,Actor]) extends Context(parentCtx) {
    val errors: ListBuffer[(Position,String)] = new ListBuffer()
    def error(p: Position, msg: String) = { errors += ((p,msg))}
    override def lookUp(id: String): Option[Declaration] = None
  }
  
  sealed class EmptyContext extends RootContext(null,Map.empty)
  
  sealed abstract class ChildContext(val parentCtx: Context, val vars: Map[String,Declaration]) extends Context(parentCtx) {
    override def lookUp(id: String): Option[Declaration] = if (vars contains id) Some(vars(id)) else parentCtx.lookUp(id)
    override def error(p: Position, msg: String) = parentCtx.error(p,msg)
  }
  
  sealed class ActorContext(override val parentCtx: RootContext, override val vars: Map[String,Declaration], 
      val inports: Map[String,InPort], val outports: Map[String,OutPort]) extends ChildContext(parentCtx,vars) {
    
    private var channels = Map[String,Connection]()
    private var entities = Map[String,Actor]()
    
    def addChannels(channels: Map[String,Connection]) = {
      this.channels = channels
    }
    
    def addEntities(entities: Map[String,Actor]) = {
      this.entities = entities
    }
    
    def getEntity(id: String) = entities.get(id)
    
    override def lookUp(id: String): Option[Declaration] = {
      if (vars contains id) Some(vars(id))
      else if (channels contains id) 
        Some(Declaration(channels(id).id,ChanType(channels(id).typ),true,None))
      else if (entities contains id) 
        Some(Declaration(entities(id).id,ActorType(entities(id)),true,None))
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

  def resolve(prog: List[TopDecl]): ResolverOutcome = {
    var decls = Map[String,TopDecl]()
    
    val actors: scala.collection.mutable.Map[String,Actor] = new scala.collection.mutable.HashMap()
    val units: scala.collection.mutable.Map[String,DataUnit] = new scala.collection.mutable.HashMap()
    
    for (decl <- prog) {
      if (decls contains decl.id) {
        return Errors(List((decl.pos,"Duplicate actor name: " + decl.id)))
      }
      decls = decls + (decl.id -> decl) 
      
      decl match {
        case du: DataUnit => units += (du.id -> du)
        case ba: BasicActor => actors += (ba.id -> ba)
        case nw: Network => actors += (nw.id -> nw)
      }
    }
    
    val rootCtx = new RootContext(null,actors.toMap)
    
    for (decl <- actors.values) {
      val inports = scala.collection.mutable.HashMap[String,InPort]()
      val outports = scala.collection.mutable.HashMap[String,OutPort]()
      for (p <- decl.inports) {
        if (inports contains p.id) rootCtx.error(p.pos, "Duplicate port: " + p.id)
        inports += (p.id -> p)
      }
      for (p <- decl.outports) {
        if ((inports contains p.id) || (outports contains p.id)) {
          rootCtx.error(p.pos, "Duplicate port: " + p.id)
        }
        outports += (p.id -> p)
      }
      
      val vars = scala.collection.mutable.HashMap[String,Declaration]()
      for (p <- decl.parameters) {
        vars += (p.id -> p)
        p.value match {
          case None =>
          case Some(v) => resolveExpr(rootCtx,v)
        }
      }
      
      decl match {
        case a: BasicActor => {
          
          
          for (m <- a.members) m match {
            case d: Declaration => vars += (d.id -> d)
            case _ =>
          }
          
          val ctx = new ActorContext(rootCtx, vars.toMap, inports.toMap, outports.toMap)
          var schedule: Option[Schedule] = None
          val actions = new ListBuffer[Action]()
          for (m <- a.members) m match {
            case ac: Action => 
              resolveAction(ctx,ac,false)
              actions += ac
            case ActorInvariant(e,_) => resolveExpr(ctx,e,BoolType)
            case ci: ChannelInvariant =>
              return Errors(List((ci.pos, "Basic actors cannot have channel invariants")))
            case e: Entities =>
              return Errors(List((e.pos, "Basic actors cannot have a entities block")))
            case s: Structure =>
              return Errors(List((s.pos, "Basic actors cannot have a structure block")))
            case Declaration(_,_,_,_) => // Already handled
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
          
          val ctx = new ActorContext(rootCtx, Map.empty, inports, outports) 

          var hasEntities, hasStructure = false
          var channels = Map.empty[String,Connection]
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
          ctx.addEntities(entities)
                    
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
                vars match {
                  case x::rest => 
                    return Errors(List((ac.pos,"Network actions cannot declare variables")))
                  case Nil =>
                }
                resolveAction(ctx, ac, true)
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
  
  def resolveAction(actorCtx: ActorContext, action: Action, nwAction: Boolean) {
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
        val d = Declaration(v.id,pDecl.portType,false,None)
        v.typ = actorCtx.inports(inPat.portId).portType
        vars = vars + (d.id -> d)
      }
    }
    for (v <- action.variables) {
      if (vars contains v.id) actorCtx.error(v.pos, "Variable name already used: " + v.id)
      vars = vars + (v.id -> v)
    } 
    
    val ctx = new ActionContext(actorCtx,vars)
    action.guard match {
      case Some(g) => resolveExpr(ctx, g, BoolType)
      case None =>
    }
    
    for (pre <- action.requires) resolveExpr(ctx, pre, BoolType)
    
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
      val port = actorCtx.outports(outPat.portId)
      assert(port.portType != null)
      for (e <- outPat.exps) {
        if (nwAction) {
          e match {
            case id@Id(name) => ctx.lookUp(name) match {
              case None => 
                val decl = Declaration(name,port.portType,false,None)
                vars = vars + (name -> decl)
                action.addPlaceHolderVar(decl)
                id.typ = port.portType
              case Some(_) => resolveExpr(ctx,e,port.portType)
            }
            case _ => resolveExpr(ctx,e,port.portType)
          }
        }
        else {
          resolveExpr(ctx,e,port.portType)
        }
      }
    }
    
    val postCtx = new ActionContext(actorCtx,vars)
    for (post <- action.ensures) resolveExpr(postCtx, post, BoolType)
    
    action.body match {
      case Some(stmt) => resolveStmt(ctx,stmt)
      case None =>
    }
  }
  
  def resolveEntities(ctx: ActorContext, e: Entities): Map[String,Actor] = {
    val instances = scala.collection.mutable.HashMap[String,Actor]()
    for (instance <- e.entities) {
      if (!(ctx.parentCtx.actors contains instance.actorId)) {
        ctx.error(instance.pos, "Unknown actor " + instance.actorId)
        return instances.toMap
      }
      
      val actor = ctx.parentCtx.actors(instance.actorId)
      val signature = for (p <- actor.parameters) yield p.typ
      val arguments = for (p <- instance.arguments) yield { resolveExpr(ctx,p) }
      
      if (signature.size != arguments.size) {
        ctx.error(instance.pos, "The actor " + actor.fullName + " takes " + signature.size + " parameters")
        return instances.toMap
      }
      
      for ((s,a) <- (signature zip arguments)) {
        if (!TypeUtil.isCompatible(a,s)) {
          ctx.error(instance.pos, "Expected type " + s.id + " found: " + a.id)
          return instances.toMap
        }
      }
      
      if (instances contains instance.id) {
        ctx.error(instance.pos, "Instance id already used " + instance.id)
        return instances.toMap
      }
      
      instance.actor = actor
      instances += (instance.id -> actor)
    }
    instances.toMap
  }
  
  def resolveStructure(ctx: ActorContext, entities: Map[String,Actor], structure: Structure) = {
    var channels = Map[String,Connection]()
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
          channels = channels + (c.id -> c)
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
    states.toSet
  }
  
  def resolveExpr(exp: Expr): ResolverOutcome = {
    val ctx = new EmptyContext()
    resolveExpr(ctx,exp)
    if (ctx.errors.isEmpty) Success() else Errors(ctx.errors.toList)
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
      case op: RShift => resolveBWExpr(ctx,op) // t1
      case op: LShift => resolveBWExpr(ctx,op) // LubSumPow
      case op: BWAnd => resolveBWExpr(ctx,op)
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
          if (!TypeUtil.isCompatible(tInd,indexedType.indexType)) 
            ctx.error(e2.pos, "Expected " + indexedType.indexType.id + ", found: " + tInd.id)
          ac.typ = indexedType.resultType
          indexedType.resultType
        }
      case fa@FunctionApp("rd",params) => resolveChannelCountFunction(ctx, fa)
      case fa@FunctionApp("urd",params) => resolveChannelCountFunction(ctx, fa)
      case fa@FunctionApp("tot",params) => resolveChannelCountFunction(ctx, fa)
      case fa@FunctionApp("initial",params) => resolveChannelCountFunction(ctx, fa)
      case fa@FunctionApp("next",params) => resolveChannelAccessFunction(ctx, fa)
      case fa@FunctionApp("prev",params) => resolveChannelAccessFunction(ctx, fa)
      case fa@FunctionApp("tokens",params) => resolveDelayFunction(ctx, fa)
      case fa@FunctionApp("state",params) => {
        if (params.size != 2) {
          ctx.error(fa.pos, "Expected two arguments")
          UnknownType
        }
        else {
          val tActor = resolveExpr(ctx,params(0))
          val state = params(1) match {
            case Id(id) => id
            case x => 
              ctx.error(x.pos, "The second argument to 'state' must be a state identifier")
              return UnknownType
          }
          tActor match {
            case ActorType(a) =>
              a match {
                case n: Network =>
                  ctx.error(params(0).pos, "Function 'state' cannot be used on networks")
                  UnknownType
                case ba: BasicActor =>
                  ba.schedule match {
                    case Some(schedule) =>
                      if (schedule.states contains state) {
                        return BoolType
                      }
                      else {
                        ctx.error(params(0).pos, "Actor " + ba.fullName + " has no state named " + state)
                        return UnknownType
                      }
                    case None => 
                      ctx.error(params(0).pos, "Actor " + ba.fullName + " has no FSM schedule")
                      return UnknownType
                  }
              }
            case _ =>
              ctx.error(params(0).pos, "Actor instance expected, found: " + tActor.id)
              UnknownType
          }
        }
      }
      case fa@FunctionApp(name,params) => {
        ctx.error(fa.pos,"Undefined function: " + name)
        UnknownType
      }
      case ll@ListLiteral(lst) => {
        val size = lst.size
        assert(size > 0)
        var cntType = resolveExpr(ctx,lst(0))
        for (e <- lst.drop(1)) {
          val t = resolveExpr(ctx,e)
          val lub = TypeUtil.getLub(cntType, t)
          if (lub.isDefined) {
            cntType = lub.get
          }
          else {
            ctx.error(e.pos,"List elements do not have consistent types. Found " + cntType.id + " and " + t.id)
          }
        }
        ListType(cntType,size)
      }
      case l@BoolLiteral(_) => l.typ = BoolType; BoolType
      case l@IntLiteral(n) => l.typ = TypeUtil.createIntOrUint(n); l.typ
      case hx@HexLiteral(x) => hx.typ = UintType(x.length*4); hx.typ
      case l@FloatLiteral(_) => throw new IllegalArgumentException()
      case v@Id(id) =>
        if (v.typ != null) {
          v.typ
        }
        else {
          ctx.lookUp(id) match {
            case Some(d) => 
              v.typ = d.typ
              v.typ
            case None => 
              ctx.error(exp.pos, "Unknown variable: " + id)
              v.typ = UnknownType
              UnknownType
          }
        }
        
    }
  }
  
  def getSmallestSize(n: Int, signed: Boolean): Int = {
    var p = 1
    while ((-(2^p) <= n) && n <= (2^p)-1) { p = p+1 }
    return p
  }
  
  
  def resolveNumericBinaryExpr(ctx: Context, exp: BinaryExpr): Type = {
    val t1 = resolveExpr(ctx, exp.left)
    val t2 = resolveExpr(ctx, exp.right)
    if (!t1.isNumeric) ctx.error(exp.left.pos, "Expected numeric type, found: " + t1.id)
    if (!t2.isNumeric) ctx.error(exp.right.pos, "Expected numeric type, found: " + t2.id)
    if (!TypeUtil.isCompatible(t1, t2)) ctx.error(exp.pos, "Illegal argument types: " + t1.id + " and " + t2.id)
    
    exp.typ = TypeUtil.getLub(t1, t2) match {
      case None => UnknownType
      case Some(t) => t
    }
    
    exp.typ
  }
  
  def resolvePredicate(ctx: Context, exp: BinaryExpr): Type = {
    val t1 = resolveExpr(ctx, exp.left)
    val t2 = resolveExpr(ctx, exp.right)
    if (!t1.isBool) ctx.error(exp.left.pos, "Expected type bool, found: " + t1.id)
    if (!t2.isBool) ctx.error(exp.right.pos, "Expected type bool, found: " + t2.id)
    exp.typ = BoolType
    exp.typ
  }
  
  def resolveRelationalExpr(ctx: Context, exp: BinaryExpr): Type = {
    val t1 = resolveExpr(ctx, exp.left)
    val t2 = resolveExpr(ctx, exp.right)
    if (!t1.isNumeric) ctx.error(exp.left.pos, "Expected numeric type: " + exp.left)
    if (!t2.isNumeric) ctx.error(exp.right.pos, "Expected numeric type: " + exp.right)
    if (!TypeUtil.isCompatible(t1, t2)) ctx.error(exp.pos, "Illegal argument types: " + t1.id + " and " + t2.id)
    exp.typ = BoolType
    exp.typ
  }
  
  def resolveEqRelationalExpr(ctx: Context, exp: BinaryExpr): Type = {
    val t1 = resolveExpr(ctx, exp.left)
    val t2 = resolveExpr(ctx, exp.right)
    if (!TypeUtil.isCompatible(t1, t2)) ctx.error(exp.pos, "Illegal argument types: " + t1.id + " and " + t2.id)
    exp.typ = BoolType
    exp.typ
  }
  
  def resolveBWExpr(ctx: Context, exp: BinaryExpr): Type = {
    val t1 = resolveExpr(ctx, exp.left)
    val t2 = resolveExpr(ctx, exp.right)
    
    if (!t1.isUnsignedInt) ctx.error(exp.left.pos, "Shift operation only applicable on integers, found: " + t1.id)
    if (!t2.isUnsignedInt) ctx.error(exp.right.pos, "Shift operation only applicable on integers, found: " + t2.id)
    
    exp.typ = t1
    t1
    
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
        return IntType(32)
      }
      val paramType = resolveExpr(ctx,fa.parameters(0))
      if (!paramType.isChannel) {
        ctx.error(fa.pos,"The argument to function " + fa.name + " must be a channel")
      }
      fa.typ = IntType(32)
      IntType(32)
  }
  
  def resolveChannelAccessFunction(ctx: Context, fa: FunctionApp): Type = {
    if (fa.parameters.size != 1) {
      ctx.error(fa.pos,"Function " + fa.name + " takes exactly 1 argument")
      return UnknownType
    }
    val paramType = resolveExpr(ctx,fa.parameters(0))
    if (!paramType.isChannel) {
      ctx.error(fa.pos,"The argument to function " + fa.name + " must be a channel")
      return UnknownType
    }
    fa.typ = paramType.asInstanceOf[ChanType].contentType
    fa.typ
  }
  
  def resolveDelayFunction(ctx: Context, fa: FunctionApp): Type = {
    if (fa.parameters.size != 2) {
        ctx.error(fa.pos,"Function " + fa.name + " takes exactly 3 argument")
        return BoolType
    }
    val paramType = resolveExpr(ctx,fa.parameters(0))
    if (!paramType.isChannel) {
      ctx.error(fa.parameters(0).pos,"The first argument to function " + fa.name + " must be a channel")
    }
    val amountType = resolveExpr(ctx,fa.parameters(1))
    if (!amountType.isInt) {
      ctx.error(fa.parameters(1).pos,"The second argument to function " + fa.name + " must be a integer")
    }
//    val contentType = paramType.asInstanceOf[ChanType].contentType
//    val initType = resolveExpr(ctx,fa.parameters(2))
//    if (initType != contentType) {
//      ctx.error(fa.parameters(2).pos,"Expected: " + contentType + "found: " + initType.id)
//    }
    BoolType
  }
  
  def isConstant(ctx: Context, id: Id) = id match {
    case Id(i) => {
      ctx.lookUp(i) match {
        case Some(decl) => decl.constant
        case None => false
      }
    }
  }
  
  def resolveStmt(ctx: Context, stmts: List[Stmt]): Unit =
    for (stmt <- stmts) resolveStmt(ctx, stmt)
  
  def resolveStmt(ctx: Context, stmt: Stmt): Unit = stmt match {
    case Assign(id,exp) =>
      if (isConstant(ctx,id)) ctx.error(id.pos, "Assignment to constant " + id.id) 
      val it = resolveExpr(ctx,id)
      val et = resolveExpr(ctx, exp)
      if (!TypeUtil.isCompatible(it, et)) 
        ctx.error(id.pos, "Cannot assign value of type " + et.id + " to variable of type " + it.id)
    case IndexAssign(id,idx,exp) =>
      if (isConstant(ctx,id)) ctx.error(id.pos, "Assignment to constant " + id.id) 
      val it = resolveExpr(ctx,id)
      val et = resolveExpr(ctx, exp)
      val xt = resolveExpr(ctx,idx)
      if (!it.isList) {
        ctx.error(id.pos,  id.id + " is not a list."); return
      }
      else {
        if (it.asInstanceOf[ListType].contentType != et) {
          ctx.error(id.pos, "Cannot assign a value of type " + et.id + " to a list of type " + it.id); return
        }
      }
      if (!xt.isInt) ctx.error(idx.pos, "List indices must be integers.")
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

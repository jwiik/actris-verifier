package fi.abo.it.actortool

import scala.util.parsing.input.Position
import scala.util.parsing.input.Positional
import collection.mutable.ListBuffer
import fi.abo.it.actortool.ActorTool.TranslationException

object Resolver {
  
  sealed abstract class ResolverOutcome
  case class Success(val rootCtx: Context) extends ResolverOutcome
  case class Errors(ss: List[(Position,String)]) extends ResolverOutcome
  
  sealed abstract class Context(val parentNode: ASTNode, val parentCtx: Context) {
    def useTypeOfIds: Boolean
    def getErrors = List.empty[(Position,String)]
    def error(p: Position, msg: String)
    def lookUp(id: String): Option[Declaration] = None
    def currentAccessedElement: Option[Expr] = None
    def actors = Map.empty[String,DFActor]
    def lookupFunction(name: String): Option[FunctionDecl] = None
    def containerActor: Option[DFActor] = None
    def lookupEntity(id: String): Option[Instance] = None
    def lookupChannel(id: String): Option[Connection] = None
    def lookupInport(id: String): Option[InPort] = None
    def lookupOutport(id: String): Option[OutPort] = None
    def lookupRefTypeDecl(id: String): Option[TypeDecl] = None 
    def variables: List[Declaration]
  }
  
  sealed class RootContext(override val parentNode: ASTNode, override val actors: Map[String,DFActor], val constants: Map[String,Declaration], val userTypes: Map[String,TypeDecl]) extends Context(parentNode, null) {
    var reuseIdTypes = false
    override def useTypeOfIds = reuseIdTypes
    override def getErrors = errors.toList
    private val errors: ListBuffer[(Position,String)] = new ListBuffer()
    def error(p: Position, msg: String) = { errors += ((p,msg))}
    override def lookupRefTypeDecl(id: String): Option[TypeDecl] = userTypes.get(id)
    override def variables = List.empty
    override def lookUp(id: String) = constants.get(id)
  }
  
  sealed class EmptyContext(override val useTypeOfIds: Boolean) extends RootContext(null,Map.empty,Map.empty,Map.empty)
  
  sealed abstract class ChildContext(override val parentNode: ASTNode, override val parentCtx: Context, val vars: Map[String,Declaration]) extends Context(parentNode, parentCtx) {
    override def lookUp(id: String): Option[Declaration] = if (vars contains id) Some(vars(id)) else parentCtx.lookUp(id)
    override def getErrors = parentCtx.getErrors
    override def error(p: Position, msg: String) = parentCtx.error(p,msg)
    override def lookupFunction(name: String): Option[FunctionDecl] = parentCtx.lookupFunction(name)
    override def containerActor = parentCtx.containerActor
    override def lookupEntity(id: String) = parentCtx.lookupEntity(id)
    override def lookupChannel(id: String) = parentCtx.lookupChannel(id)
    override def lookupInport(id: String) = parentCtx.lookupInport(id)
    override def lookupOutport(id: String) = parentCtx.lookupOutport(id)
    override def lookupRefTypeDecl(id: String) = parentCtx.lookupRefTypeDecl(id)
    override def variables = vars.values.toList
    override def useTypeOfIds = parentCtx.useTypeOfIds
  }
  
  sealed class ActorContext[T<:DFActor](val actor: T,
      override val parentCtx: RootContext, override val vars: Map[String,Declaration], 
      val inports: Map[String,InPort], val outports: Map[String,OutPort], 
      val functions: Map[String,FunctionDecl]) extends ChildContext(actor,parentCtx,vars) {
    
    private var channels = Map[String,Connection]()
    private var entities = Map[String,Instance]()
    
    def addChannels(channels: Map[String,Connection]) = {
      this.channels = channels
    }
    
    def addEntities(entities: Map[String,Instance]) = {
      this.entities = entities
    }
    
    override def lookupEntity(id: String) = entities.get(id)
    override def lookupChannel(id: String) = channels.get(id)
    override def lookupInport(id: String) = inports.get(id)
    override def lookupOutport(id: String) = outports.get(id)
    
    override def lookUp(id: String): Option[Declaration] = {
      if (vars contains id) Some(vars(id))
      else if (inports contains id)
        Some(Declaration(id,ChanType(inports(id).portType),false,None))
      else if (outports contains id)
        Some(Declaration(id,ChanType(outports(id).portType),false,None))
      else if (channels contains id) 
        Some(Declaration(channels(id).id,channels(id).typ,true,None))
      else if (entities contains id) 
        Some(Declaration(entities(id).id,ActorType(entities(id).actor),true,None))
      else  parentCtx.lookUp(id)
    }
    
    override def lookupFunction(name: String): Option[FunctionDecl] = {
      if (functions contains name) Some(functions(name))
      else parentCtx.lookupFunction(name)
    }
    
    override def containerActor = Some(actor)
  }
  
  sealed class ActionContext(val action: AbstractAction, override val parentCtx: Context, override val vars: Map[String,Declaration]) extends ChildContext(action, parentCtx,vars)
  
  sealed class BasicContext(val action: ASTNode, override val parentCtx: Context) extends ChildContext(action, parentCtx, Map.empty)
  sealed class FunctionBodyContext(val function: FunctionDecl, val inputs: Map[String,Declaration], override val parentCtx: Context) extends ChildContext(function,parentCtx,inputs)
  
  sealed class QuantifierContext(val quantifier: Quantifier, override val parentCtx: Context, 
      override val vars: Map[String,Declaration]) extends ChildContext(quantifier,parentCtx,vars)

  def resolve(prog: List[TopDecl], providedConstants: List[Declaration] = List.empty): ResolverOutcome = {
    var decls = Map[String,TopDecl]()
    
    val actors: scala.collection.mutable.Map[String,DFActor] = new scala.collection.mutable.HashMap()
    val units: scala.collection.mutable.Map[String,DataUnit] = new scala.collection.mutable.HashMap()
    var userTypes: Map[String,TypeDecl] = Map.empty
    
    for (decl <- prog) {
      if (decls contains decl.id) {
        return Errors(List((decl.pos,"Duplicate actor name: " + decl.id)))
      }
      decls = decls + (decl.id -> decl) 
      
      decl match {
        case du: DataUnit => units += (du.id -> du)
        case ba: BasicActor => actors += (ba.id -> ba)
        case nw: Network => actors += (nw.id -> nw)
        case td: TypeDecl => userTypes += (td.id -> td)
      }
    }
    val constCtx = new EmptyContext(false)
    val constants: scala.collection.mutable.Map[String,Declaration] = new scala.collection.mutable.HashMap()
    constants ++= providedConstants map { d => (d.id,d) }
    for ((_,u) <- units) {
      for (d <- u.constants) {
        if (constants contains d.id) {
          return Errors( List((d.pos,"Duplicate declaration of constant with name " + d.id)) )
        }
        d.value match {
          case None => return Errors( List((d.pos,"Constants must be declared with a value")) )
          case Some(e) => 
            resolveExpr(constCtx, e, d.typ) match {
              case e: Errors => return e
              case Success(_) =>
            }
        }
        constants(d.id) = d
      }
    }
    
    val rootCtx = new RootContext(null,actors.toMap,constants.toMap,userTypes)
    
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
      val functions = scala.collection.mutable.HashMap[String,FunctionDecl]()
      
      for (p <- decl.parameters) {
        vars += (p.id -> p)
        p.value match {
          case None =>
          case Some(v) => resolveExpr(rootCtx,v)
        }
      }
      
      vars += ("this" -> Declaration("this",ActorType(decl),true,None))
      for ((s,i) <- decl.contractActions.zipWithIndex) {
        vars += (s.fullName -> Declaration(s.fullName,ModeType,true,Some(IntLiteral(i))))
      }
      
      decl match {
        case a: BasicActor => {

          for (m <- a.members) m match {
            case d: Declaration => {
              if (vars contains d.id) {
                rootCtx.error(d.pos, "Constant or variable with name '" + d.id + "' already declared")
              }
              rootCtx.lookUp(d.id) match {
                case Some(v) => rootCtx.error(d.pos, "Constant or variable with name '" + d.id + "' already declared")
                case None =>
              }
              vars += (d.id -> d)
            }
            case fd: FunctionDecl => {
              functions += (fd.name -> fd)
            }
            case _ =>
          }
          
          val ctx = new ActorContext(a, rootCtx, vars.toMap, inports.toMap, outports.toMap, functions.toMap)
          var schedule: Option[Schedule] = None
          var priority: Option[Priority] = None
          val actions = new ListBuffer[ActorAction]()
          for (m <- a.members) m match {
            case ca: ContractAction =>
              resolveContractAction(ctx,ca)
            case ac: ActorAction => 
              resolveAction(ctx,ac)
              actions += ac
            case ActorInvariant(Assertion(e,_,_),_,_) => resolveExpr(ctx,e,BoolType)
            case ChannelInvariant(Assertion(e,_,_),_) => resolveExpr(ctx,e,BoolType)
              //return Errors(List((ci.pos, "Basic actors cannot have channel invariants")))
            case e: Entities =>
              return Errors(List((e.pos, "Basic actors cannot have a entities block")))
            case s: Structure =>
              return Errors(List((s.pos, "Basic actors cannot have a structure block")))
            case d: Declaration =>
              if (!d.typ.isState) {
                // FIXME ugly hack
                d.value match {
                  case Some(e) => resolveExpr(ctx,e,d.typ)
                  case None =>
                }
              }
            case sc: Schedule => schedule = Some(sc)
            case pr: Priority => priority = Some(pr)
            case fd: FunctionDecl => {
              val inputs = (fd.inputs map { p => (p.id, p) }).toMap
              val funCtx = new FunctionBodyContext(fd,inputs,ctx)
              resolveExpr(funCtx, fd.expr, fd.output)
            }
          }
          val actionList = actions.toList
          schedule match {
            case Some(s) => resolveSchedule(ctx, actionList, s)
            case None =>
          }
          priority match {
            case Some(p) => resolvePriority(ctx, actionList, p)
            case None =>
          }
        }  
        case n: Network => {

//          if (n.actions.size > 1) {
//            return Errors(List((n.pos, "Networks can have at most 1 action")))
//          }
          
          var inports = Map[String,InPort]()
          var outports = Map[String,OutPort]()
          var entities: Map[String,Instance] = null
          for (p <- n.inports) {
            inports = inports + (p.id -> p)
          }
          for (p <- n.outports) {
            outports = outports + (p.id -> p)
          }
          
          val ctx = new ActorContext(n, rootCtx, vars.toMap, inports, outports, Map.empty) 

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
              case ca: ContractAction => resolveContractAction(ctx,ca)
              case ac@ActorAction(_,_,_,_,guard,_,_,vars,body) => {
                return Errors(List((ac.pos,"Networks cannot have normal actions, use 'contract' keyword instead")))
//                guard match {
//                  case Some(g) => 
//                    return Errors(List((g.pos,"Network actions are not allowed to have guards")))
//                  case None => // OK
//                }
//                body match {
//                  case Nil =>
//                  case x :: _ => 
//                    return Errors(List((ac.pos,"Network actions are not allowed to have bodies")))
//                }
//                vars match {
//                  case x::rest => 
//                    return Errors(List((ac.pos,"Network actions cannot declare variables")))
//                  case Nil =>
//                }
//                resolveAction(ctx, ac)
              }
              case e: Entities =>  // Already handled
              case s: Structure => // Already handled 
              case ActorInvariant(Assertion(e,_,_),_,_) => resolveExpr(ctx,e,BoolType)
              case ChannelInvariant(Assertion(e,_,_),_) => resolveExpr(ctx,e,BoolType)
              case d: Declaration => return Errors(List((d.pos, "Networks cannot have declarations")))
              case sch: Schedule => return Errors(List((sch.pos,"Networks cannot have action schedules")))
              case sch: Priority => return Errors(List((sch.pos,"Networks cannot have action priorities")))
              case fd: FunctionDecl => return Errors(List((fd.pos,"Functions cannot be declared in networks for now.")))
            }
          }
          if (!hasEntities) return Errors(List((n.pos, "No entities block in " + n.id)))
          if (!hasStructure) return Errors(List((n.pos, "No structure block in " + n.id)))
        }
      } 
    } // End for
    rootCtx.reuseIdTypes = true
    if (rootCtx.getErrors.isEmpty) Success(rootCtx) else Errors(rootCtx.getErrors.toList)
  }
  
  def resolveContractAction[T<:DFActor](actorCtx: ActorContext[T], action: ContractAction) {
    if (!checkActionWellformedness(actorCtx, action)) return
    
    for (ipat <- action.inputPattern) {
      actorCtx.inports.get(ipat.portId) match {
        case Some(ip) => ipat.typ = ip.portType
        case None => actorCtx.error(ipat.pos, "Invalid port in contract input pattern: " + ipat.portId)
      }
    }
    
    for (opat <- action.outputPattern) {
      actorCtx.outports.get(opat.portId) match {
        case Some(op) => opat.typ = op.portType
        case None => actorCtx.error(opat.pos, "Invalid port in contract output pattern: " + opat.portId)
      }
    }
    
    val ctx = new ActionContext(action, actorCtx, Map.empty)
    
    for (grd <- action.guards) resolveExpr(ctx, grd, BoolType)
    for (pre <- action.requires) resolveExpr(ctx, pre, BoolType)
    for (post <- action.ensures) resolveExpr(ctx, post, BoolType)
    
  }
  
  def resolveAction(actorCtx: ActorContext[BasicActor], action: ActorAction) {
    if (action.init && action.inputPattern.length > 0) {
      actorCtx.error(action.pos, "Input patterns not allowed for intialize actions")
      return
    }
    
    if (!checkActionWellformedness(actorCtx, action)) return
    
    var vars = Map[String,Declaration]()
    for (inPat <- action.inputPattern) {
      val pDecl = actorCtx.inports(inPat.portId)
      inPat.typ = pDecl.portType
      for (v <- inPat.vars) {
        if (vars contains v.id) actorCtx.error(inPat.pos, "Variable name already used: " + v.id)
        val d = Declaration(v.id,pDecl.portType,false,None)
        v.typ = actorCtx.inports(inPat.portId).portType
        vars = vars + (d.id -> d)
      }
    }
    
    for (v <- action.variables) {
      val varCtx = new ActionContext(action, actorCtx, vars)
      if (vars contains v.id) varCtx.error(v.pos, "Variable name already used: " + v.id)
      v.value match {
        case Some(e) => resolveExpr(varCtx, e, v.typ)
        case None =>
      }
      vars = vars + (v.id -> v)
    }
    
    val ctx = new ActionContext(action, actorCtx,vars)
    
    for (g <- action.guards) {
      resolveExpr(ctx, g, BoolType)
    }
    
    for (pre <- action.requires) resolveExpr(ctx, pre, BoolType)
    
    for (outPat <- action.outputPattern) {
      val port = actorCtx.outports(outPat.portId)
      outPat.typ = port.portType
      assert(port.portType != null)
      for ((e,i) <- (outPat.exps.zipWithIndex) ) {
        val eType = resolveExpr(ctx,e)
        if (eType.isList) {
          assert(false);
        }
        else {
          if (!TypeUtil.isCompatible(eType, port.portType)) {
            ctx.error(e.pos, 
                "Expression type " + eType.id + " does not match port type " + port.portType.id)
          }
        }
      }
    }
    
    val postCtx = new ActionContext(action,actorCtx,vars)
    for (post <- action.ensures) resolveExpr(postCtx, post, BoolType)
    
    resolveStmt(ctx,action.body)
  }
  
  def checkActionWellformedness[T<:DFActor](actorCtx: ActorContext[T], action: AbstractAction): Boolean = {
    var portWithPat = Set[String]()
    for (inPat <- action.inputPattern) {
      if (portWithPat contains inPat.portId) {
        actorCtx.error(inPat.pos, "Multiple patterns for port: " + inPat.portId)
        return false
      }
      else portWithPat = portWithPat + inPat.portId
      if (! (actorCtx.inports contains inPat.portId)) {
        actorCtx.error(inPat.pos, "Undeclared inport: " + inPat.portId)
        return false
      }
    }
    
    for (outPat <- action.outputPattern) {
      if (portWithPat contains outPat.portId) {
        actorCtx.error(outPat.pos, "Multiple patterns for port: " + outPat.portId)
        return false
      }
      else portWithPat = portWithPat + outPat.portId
      if (! (actorCtx.outports contains outPat.portId)) {
        actorCtx.error(outPat.pos, "Undeclared outport: " + outPat.portId)
        return false
      }
    }
    return true
  }
  
  def resolveEntities(ctx: ActorContext[Network], e: Entities): Map[String,Instance] = {
    val instances = scala.collection.mutable.HashMap[String,Instance]()
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
      instance.parent = ctx.actor
      instances += (instance.id -> instance)
    }
    instances.toMap
  }
  
  def resolveStructure(ctx: ActorContext[Network], entities: Map[String,Instance], structure: Structure) = {
    val usedPorts = new ListBuffer[PortRef]()
    var channels = Map[String,Connection]()
    for (c <- structure.connections) {
      if (usedPorts contains(c.from)) {
        ctx.error(c.from.pos, "The port has multiple connections")
      }
      else {
        usedPorts += c.from
      }
      if (usedPorts contains(c.to)) {
        ctx.error(c.to.pos, "The port has multiple connections")
      }
      else {
        usedPorts += c.to
      }
      val from = c.from match {
        case PortRef(Some(a),p) =>
          entities.get(a) match {
            case None =>
              ctx.error(c.from.pos, "Unknown actor: " + a)
              None
            case Some(entity) =>
              entity.actor.getOutport(p)
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
            case Some(entity) =>
              entity.actor.getInport(p)
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
          c.typ = ChanType(f.portType)
          channels = channels + (c.id -> c)
      }
    }
    channels
  }
  
  def resolveSchedule(ctx: Context, actions: List[ActorAction], sch: Schedule): Set[String] = {
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
  
  def resolvePriority(ctx: Context, actions: List[ActorAction], priority: Priority) = {
    
    for ((a1,a2) <- priority.orders) {
      if (a1.id == a2.id) {
        ctx.error(a1.pos, "Labels appear more than once in priority order: " + a1.id + ", " + a2.id )
      }
      if (!(actions.exists { a => a.fullName == a1.id })) {
        ctx.error(a1.pos, "No action with label " + a1.id)
      }
      if (!(actions.exists { a => a.fullName == a2.id })) {
        ctx.error(a2.pos, "No action with label " + a2.id)
      }
    }
  }
  
  def resolveExpr(exp: Expr, typeCtx: Context): ResolverOutcome = {
    assert(typeCtx.getErrors.isEmpty)
    val ctx = new BasicContext(exp,typeCtx)
    resolveExpr(ctx,exp)
    assert(exp.typ != null)
    val result = if (ctx.getErrors.isEmpty && exp.typ != null) Success(ctx) else Errors(ctx.getErrors.toList)
    result match {
      case Success(_) =>
      case Errors(errs) => {
        println(ctx.useTypeOfIds)
        throw new TranslationException(exp.pos, "Error resolving type of expression: '" + exp + "': " + (errs map { case (pos,msg) => pos + ": " + msg } ) )
        assert(false,errs)
      }
    }
    result
  }
  
  def resolveExpr(ctx: Context, exp: Expr, t: Type): ResolverOutcome = {
    val rType = resolveExpr(ctx,exp)
    if (t != rType) {
      ctx.error(exp.pos, "Expected type '" + t.id + "', found '" + rType.id  + "'")
    }
    //assert(exp.typ != null, exp)
    if (ctx.getErrors.isEmpty && exp.typ != null) Success(ctx) else Errors(ctx.getErrors.toList)
  }
  
  def resolveExpr(parentCtx: Context, exp: Expr): Type = {
    val ctx = new BasicContext(exp, parentCtx)
    exp match {
      case op: Plus => resolveNumericBinaryExpr(ctx, op)
      case op: Minus => resolveNumericBinaryExpr(ctx, op)
      case op: Times => resolveNumericBinaryExpr(ctx, op)
      case op: Div => resolveNumericBinaryExpr(ctx, op)
      case op: Mod => resolveNumericBinaryExpr(ctx, op)
      case op: RShift => resolveBitShifts(ctx,op) // t1
      case op: LShift => resolveBitShifts(ctx,op) // LubSumPow
      case op: BwAnd => resolveBWExpr(ctx,op)
      case op: BwOr => resolveBWExpr(ctx,op)
      case op: BwXor => resolveBWExpr(ctx,op)
      case op@BwNot(e) => {
        val t = resolveExpr(ctx,e)
        if (!t.isBv) ctx.error(op.pos, "Expected bit vector type, found: " + t.id)
        op.typ = t
        op.typ
      }
      case m@UnMinus(e) =>
        val t = resolveExpr(ctx,e)
        if (!t.isNumeric && !t.isBv) ctx.error(m.pos, "Expected numeric type, found: " + t.id)
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
      case ite@IfThenElse(cond,the,els) =>
        val tCond = resolveExpr(ctx, cond)
        if (!tCond.isBool) ctx.error(cond.pos, "Expected bool, found: " + tCond.id)
        val tThen = resolveExpr(ctx, the)
        val tElse = resolveExpr(ctx, els)
        if (tThen != tElse) ctx.error(exp.pos, "Illegal argument types: " + tThen.id + " and " + tElse.id)
        ite.typ = tThen
        tThen
      case ac@IndexAccessor(e1,e2) =>
        val tExp = resolveExpr(ctx,e1)
        if (!tExp.isIndexed) {
          ctx.error(e1.pos, "Expected indexed type, found: " + tExp.id)
          UnknownType
        } 
        else {
          val indexedType = tExp.asInstanceOf[IndexedType]
          val tInd = resolveExpr(ctx,e2)
          if (!TypeUtil.isCompatible(tInd,indexedType.indexType)) 
            ctx.error(e2.pos, "Expected " + indexedType.indexType.id + ", found: " + tInd.id)
          ac.typ = indexedType.resultType
          indexedType.resultType
        }
      case fa@FieldAccessor(e,f) =>
        val tExp = resolveExpr(ctx,e)
        if (!tExp.isRef) {
          ctx.error(e.pos, "Expected reference type, found: " + tExp.id)
          fa.typ = UnknownType;
          UnknownType
        } 
        else {
          val refType = tExp.asInstanceOf[RefType]
          ctx.lookupRefTypeDecl(refType.id) match {
            case Some(d) => {
              val builtin = f match {
                case "sqn" => Some(IntType)
                case _ => None
              }
              if (builtin.isDefined) {
                val builtinFieldType = builtin.get
                fa.typ = builtinFieldType
                builtinFieldType
              }
              else {
                // Its not a builtin field. Check if the field exists in the definition.
                val fieldOpt = d.fields.find { d => d.id == f  }
                fieldOpt match {
                  case Some(field) => fa.typ = field.typ; fa.typ
                  case None =>
                    ctx.error(e.pos, "Unknown field: " + f)
                    fa.typ = UnknownType
                    fa.typ
                }
              }
            }
            case None =>
              ctx.error(e.pos, "Undeclared reference type: " + refType.id)
              fa.typ = UnknownType
              fa.typ
          }
        }
      case fa@FunctionApp("urd",params) => resolveChannelCountFunction(ctx, fa)
      case fa@FunctionApp("rd@",params) => resolveChannelCountFunction(ctx, fa)
      case fa@FunctionApp("tot@",params) => resolveChannelCountFunction(ctx, fa)
      case fa@FunctionApp("rd",params) => resolveChannelCountFunction(ctx, fa)
      case fa@FunctionApp("tot",params) => resolveChannelCountFunction(ctx, fa)
      case fa@FunctionApp("rate",params) => resolveChannelCountFunction(ctx, fa)
//      case fa@FunctionApp("sqn",params) => resolveSqnFunction(ctx, fa)
//      case fa@FunctionApp("currsqn",params) => resolveSqnFunction(ctx, fa)
      case fa@FunctionApp("str",params) => resolveChannelCountFunction(ctx, fa)
      case fa@FunctionApp("@",params) => resolveChannelCountFunction(ctx, fa)
      case fa@FunctionApp("next",params) => resolveChannelAccessFunction(ctx, fa)
      case fa@FunctionApp("prev",params) => resolveChannelAccessFunction(ctx, fa)
      case fa@FunctionApp("last",params) => resolveChannelAccessFunction(ctx, fa)
      case fa@FunctionApp("tokens",params) => resolveDelayFunction(ctx, fa)
      case fa@FunctionApp("history",params) => resolveBoundPredicate(ctx,fa)
      case fa@FunctionApp("current",params) => resolveBoundPredicate(ctx,fa)
      case fa@FunctionApp("every",params) => resolveBoundPredicate(ctx,fa)
      case fa@FunctionApp("min",params) => resolveSimpleMathFunction(ctx,fa,2)
      case fa@FunctionApp("abs",params) => resolveSimpleMathFunction(ctx,fa,1)
      case fa@FunctionApp("mode",params) => {
        val t = resolveExpr(ctx,params(0))
        if (params.size != 1) ctx.error(fa.pos, "Function 'mode' takes one argument")
        if (!t.isMode) {
          ctx.error(fa.pos, "The argument to 'mode' should be a contract mode")
        }
        fa.typ = BoolType
        BoolType
      }
      case fa@FunctionApp("state",params) => {
        val t = resolveExpr(ctx,params(0))
        if (params.size != 1) ctx.error(fa.pos, "Function 'mode' takes one argument")
        if (!t.isState) {
          ctx.error(fa.pos, "The argument to 'state' should be an action schedule state")
        }
        fa.typ = IntType
        BoolType
      }
      case fa@FunctionApp("int2bv",_) => resolveBvLiteral(ctx, fa)
      case fa@FunctionApp("uint2bv",_) => resolveBvLiteral(ctx, fa)
      case fa@FunctionApp("int",_) => resolveBvLiteral(ctx, fa)
      case fa@FunctionApp("uint",_) => resolveBvLiteral(ctx, fa)
      case fa@FunctionApp("bv2int",params) => {
        if (params.size != 1) {
          ctx.error(fa.pos, "bv2int takes one argument, a bitvector")
        }
        val argT = resolveExpr(ctx, params(0))
        if (!argT.isBv) {
          ctx.error(fa.pos, "bv2int takes a bitvector as argument, found: " + argT.id)
        }
        fa.typ = IntType
        IntType
      }
      case fa@FunctionApp("bvconcat",params) => {
        if (params.size != 2) {
          ctx.error(fa.pos, "bvconcat takes two integer literals as argument")
        }
        val arg1T = resolveExpr(ctx, params(0))
        val arg2T = resolveExpr(ctx, params(1))
        if (arg1T.isBv && arg2T.isBv) {
          val bv1 = arg1T.asInstanceOf[BvType]
          val bv2 = arg2T.asInstanceOf[BvType]
          if (bv1.signed != bv2.signed) {
            ctx.error(fa.pos, "Cannot concatenate signed and unsigned bit vectors")
          }
          fa.typ = BvType(bv1.size+bv2.size,bv1.signed)
        }
        else if (!arg1T.isBv) {
          ctx.error(fa.pos, "The first argument to bvconcat, found: " + arg1T.id)
          fa.typ = UnknownType
        }
        else if (!arg2T.isBv) {
          ctx.error(fa.pos, "The second argument to bvconcat, found: " + arg2T.id)
          fa.typ = UnknownType
        }
        fa.typ
      }
      case fa@FunctionApp("bvextract",params) => {
        if (params.size != 3) {
          ctx.error(fa.pos, "bvextract takes 3 arguments")
          fa.typ = UnknownType
        }
        val arg1T = resolveExpr(ctx, params(0))
        val arg2T = resolveExpr(ctx, params(1))
        val arg3T = resolveExpr(ctx, params(2))
        if (!arg1T.isBv) {
          ctx.error(fa.pos, "bvextract excepts a bitvector as first argument")
          fa.typ = UnknownType
        }
        if (!arg2T.isInt) {
          ctx.error(fa.pos, "bvextract excepts a bitvector as first argument")
          fa.typ = UnknownType
        }
        if (!arg3T.isInt) {
          ctx.error(fa.pos, "bvextract excepts a bitvector as first argument")
          fa.typ = UnknownType
        }
        (params) match {
          case List(_,IntLiteral(n1),IntLiteral(n2)) => {
            if (n1 <= n2) {
              ctx.error(fa.pos,"bvextract expects the 2nd argument to be larger then the 3rd argument")
              fa.typ = UnknownType
            }
            else fa.typ = BvType(n1-n2,arg1T.asInstanceOf[BvType].signed)
          }
          case x => {
            fa.typ = UnknownType
            ctx.error(fa.pos, "bvextract expects the 2nd and 3rd arguments to be positive integer literals")
          }
        }
        fa.typ
      }
      case fa@FunctionApp("bvresize",params) => {
        if (params.size != 2) {
          ctx.error(fa.pos, "bvresize takes 2 arguments")
          fa.typ = UnknownType
        }
        val arg1T = resolveExpr(ctx, params(0))
        val arg2T = resolveExpr(ctx, params(1))
        if (!arg1T.isBv) {
          ctx.error(fa.pos, "The first argument to bvresize should be a bitvector")
          fa.typ = UnknownType
        }
        if (!arg2T.isInt) {
          ctx.error(fa.pos, "The second argument to bvresize should be int")
          fa.typ = UnknownType
        }
        params(1) match {
          case IntLiteral(n) => {
            val argSize = arg1T.asInstanceOf[BvType].size
            val signed = arg1T.asInstanceOf[BvType].signed
            fa.typ = BvType(n,signed)
          }
          case x => {
            ctx.error(x.pos,"The second argument to bvresize should an integer literal")
            fa.typ = UnknownType
          }
        }
        fa.typ
      }
      case fa@FunctionApp("chsum",params) => resolveSimpleFunction(ctx,fa,List(ChanType(IntType),IntType))
      case fa@FunctionApp(name,params) => {
        ctx.lookupFunction(name) match {
          case Some(fd) => {
            if (params.size == fd.inputs.size) {
              for ((arg,par) <- (params zip fd.inputs)) {
                val aType = resolveExpr(ctx, arg)
                if (!TypeUtil.isCompatible(aType,par.typ)) {
                  ctx.error(arg.pos, "Invalid type for function argument, expected " + par.typ.id + ", found " + aType.id)
                }
              }
              fa.typ = fd.output
              fd.output
            }
            else {
              ctx.error(fa.pos, "Function " + name + " takes " + fd.inputs.size + " arguments, got " + params.size)
              UnknownType
            }
          }
          case None => {
            ctx.error(fa.pos,"Undefined function: " + name)
            UnknownType
          }
        }
        
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
      case hx@HexLiteral(x) => hx.typ = BvType(x.length*4,false); hx.typ
      case l@FloatLiteral(_) => throw new IllegalArgumentException()
      case sm@SpecialMarker(m) => {
        val accessor = findParentAccessor(ctx)
        accessor match {
          case Some(ac) => {
            if (ac.exp.isInstanceOf[Id]) sm.addExtraData("accessor", ac.exp.asInstanceOf[Id].id)
            else ctx.error(sm.pos, "Marker '" + m + "' used with invalid accessor")
          }
          case None => ctx.error(sm.pos, "Marker '" + m + "' used in invalid position")
        }
        sm.typ = IntType
        IntType
      }
      case v@Id(id) =>
        if (ctx.useTypeOfIds && v.typ != null) {
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
  
  def findParentAccessor(ctx: Context): Option[IndexAccessor] = {
    val node = ctx.parentNode
    ctx.parentCtx.parentNode match {
      case ac: IndexAccessor => Some(ac)
      case _ => {
        if (ctx.parentCtx.parentNode.isInstanceOf[Expr]) findParentAccessor(ctx.parentCtx)
        else None
      }
      
    }
  }
  
  def resolveBvLiteral(ctx: Context, fa: FunctionApp): Type = {
    val params = fa.parameters
    if (params.size != 2) {
      ctx.error(fa.pos, "int2bv takes two integer literals as argument")
      return UnknownType
    }
    for (p <- params) resolveExpr(ctx, p)
    val value = params(0) match {
      case IntLiteral(n) => n
      case UnMinus(IntLiteral(n)) => -n
      case _ => ctx.error(params(0).pos, "The 1st argument to '" + fa.name +  "' has to be an integer literal")
    }
    val size = params(1).asInstanceOf[IntLiteral].value
    
    fa.typ = fa.name match {
      case "int2bv" => BvType(size,true)
      case "int" => BvType(size,true)
      case "uint2bv" => BvType(size,false)
      case "uint" => BvType(size,false)
    }
    assert(fa.typ != null)
    fa.typ
  }
  
  def resolveNumericBinaryExpr(ctx: Context, exp: BinaryExpr): Type = {
    val t1 = resolveExpr(ctx, exp.left)
    val t2 = resolveExpr(ctx, exp.right)
    if (!t1.isNumeric && !t1.isBv) ctx.error(exp.left.pos, "Expected numeric type, found: " + t1.id)
    if (!t2.isNumeric && !t2.isBv) ctx.error(exp.right.pos, "Expected numeric type, found: " + t2.id)
    if (!TypeUtil.isCompatible(t1, t2)) ctx.error(exp.pos, "Illegal argument types to operator '" + exp.operator + "': " + t1.id + " and " + t2.id)
    
    exp.typ = TypeUtil.getLub(t1, t2) match {
      case None => 
        ctx.error(exp.pos, "Incompatible types: " + t1 + " and " + t2)
        UnknownType
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
    if (!t1.isNumeric && !t1.isBv) ctx.error(exp.left.pos, "Expected numeric type: " + exp.left)
    if (!t2.isNumeric && !t2.isBv) ctx.error(exp.right.pos, "Expected numeric type: " + exp.right)
    if (!TypeUtil.isCompatible(t1, t2)) ctx.error(exp.pos, "Illegal argument types: " + t1.id + " and " + t2.id)
    exp.typ = BoolType
    exp.typ
  }
  
  def resolveEqRelationalExpr(ctx: Context, exp: BinaryExpr): Type = {
    val t1 = resolveExpr(ctx, exp.left)
    val t2 = resolveExpr(ctx, exp.right)
    if (!TypeUtil.isCompatible(t1, t2)) {
      ctx.error(exp.pos, "Illegal argument types: " + t1.id + " and " + t2.id)
    }
    exp.typ = BoolType
    exp.typ
  }
  
  def resolveBitShifts(ctx: Context, exp: BinaryExpr): Type = {
    assert(List("<<",">>") contains  (exp.operator))
    val t1 = resolveExpr(ctx, exp.left)
    val t2 = resolveExpr(ctx, exp.right)
    if (t1.isBv && t2.isBv) resolveBWExpr(ctx,exp)
    else if (t1.isInt && t2.isInt) {
      exp.typ = IntType
      IntType
    }
    else {
      ctx.error(exp.left.pos, "Operator not applicable to arguments of type '" + t1.id + "' and '" + t2.id + "'")
      UnknownType
    }
  }
  
  def resolveBWExpr(ctx: Context, exp: BinaryExpr): Type = {
    val t1 = resolveExpr(ctx, exp.left)
    val t2 = resolveExpr(ctx, exp.right)
    
    if (!t1.isBv) {
      ctx.error(exp.left.pos, "Operator only applicable bit vectors, found: " + t1.id)
      return UnknownType
    }
    if (!t2.isBv) {
      ctx.error(exp.right.pos, "Operator only applicable bit vectors, found: " + t2.id)
      return UnknownType
    }
    
    val bvt1 = t1.asInstanceOf[BvType]
    val bvt2 = t2.asInstanceOf[BvType]
    
    if (bvt1.size != bvt2.size) {
      ctx.error(exp.pos, "Mismatching bit vector sizes " + bvt1.size + " and " + bvt2.size)
    }
    
    exp.typ = t1
    t1
    
  }
  
  def resolveQuantifier(ctx: Context, quant: Quantifier): Type = {
    var decls = Map[String,Declaration]()
    for (d <- quant.vars) {
      decls = decls + (d.id -> d)
    }
    val quantCtx = new QuantifierContext(quant, ctx, decls)
    val t = resolveExpr(quantCtx, quant.expr)
    if (!t.isBool) ctx.error(quant.expr.pos, "Expected type bool: " + quant.expr)
    quant.pattern match {
      case Some(e) => resolveExpr(quantCtx,e)
      case None =>
    }
    quant.typ = BoolType
    quant.typ
  }
  
  val totFuncs = Set("tot", "tot0")
  def resolveChannelCountFunction(ctx: Context, fa: FunctionApp): Type = {
    if (fa.parameters.size != 1) {
      ctx.error(fa.pos,"Function " + fa.name + " takes exactly 1 argument")
      return IntType(-1)
    }
    val param = fa.parameters(0)
    val paramType1 = resolveExpr(ctx,param)
    if (!paramType1.isChannel) {
      ctx.error(fa.parameters(0).pos,"The 1st argument to function " + fa.name + " must be a channel")
    }
    
    // It is unsound to use tot on input channels. Check for such cases and fail.
//    if (totFuncs contains fa.name) { 
//      ctx.lookupChannel(param.asInstanceOf[Id].id) match {
//        case Some(c) => 
//          if (c.isInput) ctx.error(fa.pos, "Function '" + fa.name + "' cannot be used on input channels")
//        case None => 
//      }
//      ctx.lookupInport(param.asInstanceOf[Id].id) match {
//        case Some(c) => ctx.error(fa.pos, "Function '" + fa.name + "' cannot be used on input channels")
//        case None => 
//      }
//    }
    
    
    
    fa.typ = IntType(-1)
    IntType(-1)
  }
   
  def resolveBoundPredicate(ctx: Context, fa: FunctionApp): Type = {
    if (fa.parameters.size < 2) {
      ctx.error(fa.pos,"Function " + fa.name + " takes at least 2 arguments")
      return BoolType
    }
    val paramType1 = resolveExpr(ctx,fa.parameters(0))
    if (!paramType1.isChannel) {
      ctx.error(fa.parameters(0).pos,"The 1st argument to function " + fa.name + " must be a channel")
    }
    
    val paramType2 = resolveExpr(ctx,fa.parameters(1))
    if (!paramType2.isInt) {
      ctx.error(fa.parameters(0).pos,"The 2nd argument to function " + fa.name + " must be an integer")
    }
    
    if (fa.parameters.size > 2) {
      if (fa.parameters.size != 4) {
        ctx.error(fa.pos,"Expected 4 arguments to function " + fa.name + "")
        return BoolType
      }
      
      val paramType3 = resolveExpr(ctx,fa.parameters(2))
      if (!paramType3.isInt) {
        ctx.error(fa.parameters(0).pos,"The 3rd argument to function " + fa.name + " must be an integer")
      }
      val paramType4 = resolveExpr(ctx,fa.parameters(3))
      if (!paramType4.isInt) {
        ctx.error(fa.parameters(0).pos,"The 4th argument to function " + fa.name + " must be an integer")
      }
    }
    
    fa.typ = BoolType
    BoolType
  }
  
  def resolveSqnFunction(ctx: Context, fa: FunctionApp): Type = {
    if (fa.parameters.size != 1) {
      ctx.error(fa.pos,"Function " + fa.name + " takes 1 argument")
      return IntType(32)
    }

    val paramType = resolveExpr(ctx,fa.parameters(0))
    fa.name match {
      case "sqn" =>
        //if (!fa.parameters(0).isInstanceOf[IndexAccessor]) {
        //  ctx.error(fa.parameters(0).pos, "The argument to sqn has to be a channel index accessor")
        //}
      case "currsqn" =>
        resolveExpr(ctx,fa.parameters(0))
        if (!paramType.isActor) {
          ctx.error(fa.parameters(0).pos,"The argument to function " + fa.name + " must be an actor instance")
        }
    }
    fa.typ = IntType(32)
    IntType(32)
  }
  
  def resolveChannelAccessFunction(ctx: Context, fa: FunctionApp): Type = {
    if (fa.parameters.size != 1 && fa.parameters.size != 2) {
      ctx.error(fa.pos,"Function " + fa.name + " takes 1 or 2 arguments")
      return UnknownType
    }
    val paramType = resolveExpr(ctx,fa.parameters(0))
    if (!paramType.isChannel) {
      ctx.error(fa.pos,"The first argument to function " + fa.name + " must be a channel")
      return UnknownType
    }
    if (fa.parameters.size == 2) {
      val offsetType = resolveExpr(ctx,fa.parameters(1))
      if (!offsetType.isInt) {
        ctx.error(fa.pos,"The second argument to function " + fa.name + " must be an integer")
        return UnknownType
      }
    }
    fa.typ = paramType.asInstanceOf[ChanType].contentType
    fa.typ
  }
  
  def resolveDelayFunction(ctx: Context, fa: FunctionApp): Type = {
    if (fa.parameters.size != 2) {
        ctx.error(fa.pos,"Function " + fa.name + " takes exactly 2 argument")
        return BoolType
    }
    val paramType = resolveExpr(ctx,fa.parameters(0))
    if (!paramType.isChannel) {
      ctx.error(fa.parameters(0).pos,"The first argument to function " + fa.name + " must be a channel")
    }
    val amountType = resolveExpr(ctx,fa.parameters(1))
    if (!amountType.isInt) {
      ctx.error(fa.parameters(1).pos,"The second argument to function " + fa.name + " must be an integer")
    }
    fa.typ = BoolType
    BoolType
  }
  
   def resolveSimpleMathFunction(ctx: Context, fa: FunctionApp, numArgs: Int): Type = {
     if (fa.parameters.size != numArgs) {
       ctx.error(fa.pos, "Function '" + fa.name + "' expects " + numArgs + " arguments, found " + fa.parameters.size)
       fa.typ = UnknownType
       return fa.typ
     }
     val paramTypes = fa.parameters map { p => resolveExpr(ctx, p) }
     val p1T = paramTypes(0)
     for (pT <- paramTypes.tail) {
       if (p1T != pT) {
         ctx.error(fa.pos, "Arguments to '" + fa.name + "' should be of same type, found " + ( (paramTypes.map(_.id)).mkString(", ") ))
         fa.typ = UnknownType
         return fa.typ
       }
     }
     fa.typ = p1T
     fa.typ
   }
  
  def resolveSimpleFunction(ctx: Context, fa: FunctionApp, signature: List[Type]): Type = {
    if (signature.size-1 != fa.parameters.size) {
      ctx.error(fa.pos,"Function " + fa.name + " takes " + (signature.size-1) + " arguments")
    }
    val paramSig = signature.take(signature.size-1)
    for ((sig,arg) <- (paramSig zip fa.parameters)) {
      val argType = resolveExpr(ctx, arg)
      if (sig != argType) ctx.error(arg.pos,"Wrong type " + argType + " for argument " + arg)
      
    }
    fa.typ = signature.last
    fa.typ
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
  
  def resolveStmt(parentCtx: Context, stmt: Stmt): Unit = {
    val ctx = new BasicContext(stmt,parentCtx)
    stmt match {
      case Assign(id,exp) =>
        if (isConstant(ctx,id)) ctx.error(id.pos, "Assignment to constant " + id.id) 
        val it = resolveExpr(ctx,id)
        val et = resolveExpr(ctx, exp)
        if (!TypeUtil.isCompatible(it, et)) 
          ctx.error(id.pos, "Cannot assign value of type " + et.id + " to variable '" + id.id + "' of type " + it.id)
      case MapAssign(e1,e2) =>
        val it = resolveExpr(ctx,e1)
        val et = resolveExpr(ctx,e2)
        if (!TypeUtil.isCompatible(it, et)) 
          ctx.error(e1.pos, "Cannot assign value of type " + et.id + " to datatype")
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
}

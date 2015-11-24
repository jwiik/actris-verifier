package fi.abo.it.actortool

import scala.util.parsing.input.Position
import scala.collection.mutable.ListBuffer
import fi.abo.it.actortool.Boogie.DeclComment
import fi.abo.it.actortool.Boogie.VarExpr
import fi.abo.it.actortool.Boogie.MapSelect
import fi.abo.it.actortool.Boogie.BType
import fi.abo.it.actortool.Boogie.NamedType
import fi.abo.it.actortool.Boogie.LocalVar
import fi.abo.it.actortool.Boogie.UnaryExpr

class Translator {
  
  final val Sep = "#"
  final val Modifies = List("C","R","M","St")
  
  object Uniquifier {
    private var i = -1
    def get(id: String) = { i = i+1; id+Sep+(i.toString) }
  }
  
  object GeneratedInvariantCount {
    private var i = -1
    def next = { i = i+1; "#"+(i.toString) }
  }
  
  object BMap extends Enumeration {
    type BMap = String
    final val CInit = "C#init"
    final val C = "C"
    final val R = "R"
    final val M = "M"
    final val St = "St"
    final val This = "this#"
  }
  
  object BType {
    def Chan(arg: BType) = Boogie.IndexedType("Chan", arg)
    def M = NamedType("MType")
    def C = NamedType("CType")
    def Bool = NamedType("bool");
    def Real = NamedType("real");
    def Int = NamedType("int");
    def State = NamedType("State")
    def Actor = NamedType("Actor")
    def List(cType: BType) = Boogie.IndexedType("List", cType)
  }
  
  object AstElement {
    def ch(name: String, carriedType: Type) = {
      val i = Id(name)
      i.typ = ChanType(carriedType)
      i
    }
    def rd(ch: Id) = {
      val fa = FunctionApp("rd",List(ch))
      fa.typ = IntType(32)
      fa
    }
    def urd(ch: Id) = {
      val fa = FunctionApp("urd",List(ch))
      fa.typ = IntType(32)
      fa
    }
    def chAcc(ch: Id, idx: Expr) = {
      val t = ch.typ.asInstanceOf[ChanType].contentType
      val ia = IndexAccessor(ch,idx)
      ia.typ = t
      ia
    }
  }
  
  import Helper._
  import AstElement._
  
  var currActor: Actor = null
  var topDecls: Map[String,TopDecl] = null

  def translateProgram(decls: List[TopDecl]): List[Boogie.Decl] = {
    topDecls = (for (d <- decls.filter(a => a.isInstanceOf[Actor])) yield (d.id, d)).toMap
    decls flatMap {
      case a: BasicActor => translateActor(a)
      case n: Network => translateNetwork(n)
      case u: DataUnit => Nil
    }
  }
    
  def translateActor(actor: BasicActor): List[Boogie.Decl] = {
    val decls = new ListBuffer[Boogie.Decl]()
    val actions = new ListBuffer[Action]()
    val invariants = new ListBuffer[(Position,Boogie.Expr)]()
    val actorVars = new ListBuffer[Boogie.LocalVar]()
    
    val prefix = actor.id+Sep
    val states = actor.schedule match {
      case Some(s) => 
        actorVars += bThisDecl
        s.states
      case None => Nil
    }
    
    val bActorStates = for (s <- states) yield {
      //actorVars += bLocal(currentState,BType.State)
      Boogie.Const(prefix+s,true,BType.State)
    }
    
    if (!states.isEmpty) {
      val allowedStatesInvariant = 
        (for (s <- states) yield {
          bThis ==@ Boogie.VarExpr(prefix+s)
        }).reduceLeft((a,b) => (a || b))
      invariants += ((actor.pos,allowedStatesInvariant))
    }
      
    for (m <- actor.members) {
      m match {
        case ActorInvariant(e,_) => invariants += ((e.pos,transExpr(e)(Map.empty)))
        case a: Action => actions += a
        case Declaration(id,t,_,_) => actorVars += bLocal(id, t)
        case _ =>
      }
    }
    for (a <- actions) {
      decls ++= translateActorAction(a,invariants.toList,actorVars.toList,actor.schedule,prefix)
    }
    bActorStates:::decls.toList
  }
  
   def translateActorAction(
       a: Action, 
       invs: List[(Position,Boogie.Expr)],
       actorVars: List[Boogie.LocalVar],
       schedule: Option[Schedule],
       prefix: String): List[Boogie.Decl] = {
     
     val renamings = new ListBuffer[(String,String)]
     
     val inputVars = (for (inPat <- a.inputPattern) yield {
       for (v <- inPat.vars) yield {
         val name = "IV"+Sep+(inPat.portId)+Sep+v.id
         renamings += ((v.id, name))
         bLocal(name,v.typ)
       }
     }).flatten
     
     val actionVars = for (v <- a.variables) yield {
       val name = "ActionVar"+Sep+v.id
       renamings += ((v.id, name))
       bLocal(name,v.typ)
     }
     
     val renameMap = renamings.toMap
     
     val invAssumes = for ((pos,i) <- invs) yield Helper.bAssume(i)
     val preCondAssumes = for (p <- a.requires) yield Helper.bAssume(transExpr(p)(renameMap))
     
     val guardAssume = a.guard match {
       case None => Nil
       case Some(e) => List(bAssume(transExpr(e)(renameMap)))
     }
     
     val transitions = schedule match {
       case Some(sched) => sched.transitionsOnAction(a.fullName)
       case None => Nil
     }
     
     val stateGuards = for ((f,t) <- transitions) yield {
       (bThis ==@ Boogie.VarExpr(prefix+f))
     }
     val stateGuard = 
       if (stateGuards.isEmpty) Nil
       else List(bAssume(stateGuards.reduceLeft((a,b) => (a || b))))
     
     val body = a.body match {
       case None => List(bAssume(Boogie.BoolLiteral(true)))
       case Some(b) => transStmt(b)(renameMap) 
     }
     val stateUpdates = transitions match {
       case Nil => Nil
       case List((f,t)) => List(Boogie.Assign(bThis, Boogie.VarExpr(prefix+t)))
       case _ => assert(false); Nil
     }
     val invAsserts = for ((pos,i) <- invs) yield {
       bAssert(i,pos,"Action might not preserve invariant")
     }
     val postCondAsserts = for (q <- a.ensures) yield {
       bAssert(transExpr(q)(renameMap),q.pos,"Action postcondition might not hold")
     }
     val stmt =
       actorVars:::
       inputVars:::
       actionVars:::
       invAssumes:::
       preCondAssumes:::
       stateGuard:::
       guardAssume:::
       body:::
       stateUpdates:::
       postCondAsserts:::
       invAsserts
     List(Boogie.Proc(Uniquifier.get(prefix+a.fullName),Nil,Nil,Modifies,Nil,stmt))
   }
  
  def translateNetwork(network: Network): List[Boogie.Decl] = {
    val decls = new ListBuffer[Boogie.Decl]()
    val actions = network.actions
    val nwInvariants = network.actorInvariants
    val chInvariants = network.channelInvariants
    val connections = network.structure.get.connections
    val entities = network.entities.get.entities
    
    val namePrefix = network.id+Sep
    val delayedChannels =  {
      val buffer = new ListBuffer[(String,Expr)]
      TokensDefFinder.visitExpr(nwInvariants map {nwi => nwi.expr})(buffer);
      (buffer map {case (x,amount) => (x,(amount))}).toMap
    }
    
    val networkRenamings = {
      (for (c <- connections) yield ((c.id,namePrefix+c.id))):::
      (for (e <- entities) yield ((e.id,namePrefix+e.id)))
    }.toMap
    
    val bNwInvs = for (nwi <- nwInvariants) yield ((nwi,transExpr(nwi.expr)(networkRenamings)))
    val bChInvs = for (chi <- chInvariants) yield ((chi,transExpr(chi.expr)(networkRenamings)))
    
    val (sourceMap,targetMap) = {
      val source = scala.collection.mutable.HashMap.empty[PortRef,List[String]]
      val target = scala.collection.mutable.HashMap.empty[PortRef,String]
      for (c <- connections) {
        if (!(source contains c.from)) source += (c.from -> List(networkRenamings(c.id)))
        else source(c.from) = source(c.from):::List(networkRenamings(c.id))
        target(c.to) = networkRenamings(c.id)
      }
      (source.toMap,target.toMap)
    }
    //decls ++= translateNetworkInit(/*nwa,*/ bNwInvs, bChInvs, networkRenamings, sourceMap, targetMap, entities, connections, delayedChannels, network.id+Sep)

    for (a <- actions) {
      decls ++= translateNetworkAction(
          a,bNwInvs,bChInvs,networkRenamings,sourceMap,targetMap,entities,
          connections,delayedChannels,network.id+Sep)
    }

    decls.toList
  }
  
  def translateNetworkInit(
       //nwa: Action, 
       nwInvs: List[(ActorInvariant,Boogie.Expr)],
       chInvs: List[(ChannelInvariant,Boogie.Expr)],
       networkRenamings: Map[String,String], // Channels and entities
       sourceMap: Map[PortRef,List[String]],
       targetMap: Map[PortRef,String],
       entities: List[Instance],
       connections: List[Connection],
       delayedChannels: Map[String,(Expr)],
       prefix: String): List[Boogie.Decl] = {
    
    val asgn = new ListBuffer[Boogie.Stmt]
    val vars = new ListBuffer[Boogie.LocalVar]
    
    for (c <- connections) {
      asgn += bAssume(bCredit(networkRenamings(c.id)) ==@ bInt(0))
      asgn += bAssume(bRead(networkRenamings(c.id)) ==@ bInt(0))
    }
    
    for (inst <- entities) {
      val actor = inst.actor
      val actorParams = actor.parameters.map(p => {
        val newName = "ActorParam"+Sep+inst.id+Sep+p.id
        vars += bLocal(newName,type2BType(p.typ))
        (Id(p.id),Id(newName))
      }).toMap
      val parameterNames = actor.parameters map {x => Id(x.id)}
      for ((name,value) <- (parameterNames zip inst.arguments)) {
        // Add assumptions about the values of the actor parameters
        asgn += bAssume(transExpr(
              IdToIdReplacer.visitExpr(name)(actorParams)
            )(networkRenamings) ==@ transExpr(value)(networkRenamings))
      }
      
      for (m <- actor.members) m match {
        case ca@Action(_,true,_,_,_,_,_,_,_) => {
          for (opat <- ca.outputPattern) {
            val cIds = sourceMap(PortRef(Some(inst.id),opat.portId))
            for (cId <- cIds) {
              for (e <- opat.exps) {
                val renamedExp = IdToIdReplacer.visitExpr(e)(actorParams)
                asgn += Boogie.Assign(
                    bChannelIdx(cId,bRead(cId)+bCredit(cId)),transExpr(renamedExp)(networkRenamings))
                asgn += Boogie.Assign(bCredit(cId),bCredit(cId) + Boogie.IntLiteral(1))
              }
            }
          }
        }
        case _ =>
      }
    }
    asgn ++= (for ((nwi,bNwi) <- nwInvs) yield 
        bAssert(bNwi,nwi.pos,"Network initialization might not establish the network invariant"))
    
    val stmt = vars.toList:::asgn.toList
    List(Boogie.Proc(Uniquifier.get(prefix+"init"),Nil,Nil,Modifies,Nil,stmt))
  }
  
  def translateNetworkAction(
       nwa: Action, 
       nwInvs: List[(ActorInvariant,Boogie.Expr)],
       chInvs: List[(ChannelInvariant,Boogie.Expr)],
       networkRenamings: Map[String,String], // Channels and entities
       sourceMap: Map[PortRef,List[String]],
       targetMap: Map[PortRef,String],
       entities: List[Instance],
       connections: List[Connection],
       delayedChannels: Map[String,(Expr)],
       prefix: String): List[Boogie.Decl] = {
    
    val constDecls = new ListBuffer[Boogie.Const]
    val procVars = new ListBuffer[Boogie.LocalVar]
    
    val actionRenamings = new ListBuffer[(String,String)]
    for (v <- nwa.variables) {
      val newName = "ActionVar"+Sep+v.id
      procVars += bLocal(newName,type2BType(v.typ))
      actionRenamings += ((v.id,newName))
    }
    
    val renamings = networkRenamings ++ actionRenamings.toMap
    
    //val sourceMap = (for (c <- connections) yield ((c.from,boogieName(c.id)))).toMap
    //val targetMap = (for (c <- connections) yield ((c.to,boogieName(c.id)))).toMap
    
    val cInitAssumesBuffer = new ListBuffer[Boogie.Assume]()
    val readAssumesBuffer = new ListBuffer[Boogie.Assume]()
    
    for (e <- entities) {
      constDecls += Boogie.Const(networkRenamings(e.id),true,BType.Actor)
    }
    for (c <- connections) {
     constDecls += Boogie.Const(networkRenamings(c.id),true,BType.Chan(type2BType(c.typ)))
     if (!(delayedChannels contains c.id)) {
       c.from match {
         case PortRef(None,p) =>
           cInitAssumesBuffer += bAssume(bCredInit(networkRenamings(c.id)) ==@ bInt(nwa.portInputCount(p)))
         case PortRef(_,_) => 
           cInitAssumesBuffer += bAssume(bCredInit(networkRenamings(c.id)) ==@ bInt(0))
       }
     }
     readAssumesBuffer += bAssume(bRead(networkRenamings(c.id)) ==@ bInt(0))
    }
    
    val constDecl = constDecls.toList
    val cInitAssumes = cInitAssumesBuffer.toList
    val readAssumes = readAssumesBuffer.toList
    
    var replacements = Map[Id,IndexAccessor]()
    for (ipat <- nwa.inputPattern) {
//      for (source <- sourceMap(PortRef(None,ipat.portId))) {
//        val inChan = Id(source)
//      }
      assert(sourceMap(PortRef(None,ipat.portId)).size == 1)
      val inChan = Id(sourceMap(PortRef(None,ipat.portId))(0))
      var i = 0
      for (v <- ipat.vars) {
        inChan.typ = ChanType(v.typ)
        val acc = IndexAccessor(inChan,IntLiteral(i))
        acc.typ = v.typ
        replacements = replacements + (v -> acc)
        i = i+1
      }
    }
    
//    val outputs = (for (opat <- nwa.outputPattern) yield {
//      val outChan = targetMap(PortRef(None,opat.portId))
//      var i = 0
//      for (e <- opat.exps) yield {
//        val renamedExp = IdReplacer.visitExpr(e)(replacements)
//        val id = Id(outChan)
//        id.typ = ChanType(e.typ)
//        val acc = IndexAccessor(id,IntLiteral(i))
//        acc.typ = e.typ
//        val cond = Eq(acc,renamedExp)
//        i = i+1
//        cond.pos = e.pos
//        cond
//      }
//    }).flatten
    val outputs = (for (opat <- nwa.outputPattern) yield {
      val outChan = targetMap(PortRef(None,opat.portId))
      var i = 0
      (for (e <- opat.exps) yield {
        val renamedExp = IdReplacer.visitExpr(e)(replacements)
        val id = Id(outChan)
        id.typ = ChanType(e.typ)
        val acc = IndexAccessor(id,IntLiteral(i))
        acc.typ = e.typ
        
        val stmts =
          if (e.isInstanceOf[Id] && nwa.variables.exists { x => x.id == e.asInstanceOf[Id].id }) {
            // If this is an action variable it will be used as a placeholder
            val v = transExpr(e)(renamings)
            List(Boogie.Assign(v,transExpr(acc)(renamings)))
          }
          else {
            val name = prefix+opat.portId+Sep+i
            procVars += bLocal(name,type2BType(e.typ))
            val v = VarExpr(name)
            List(Boogie.Assign(v,transExpr(acc)(renamings)),
            bAssert(v ==@ transExpr(renamedExp)(renamings),e.pos,
              "Network output might not conform to the specified action output"))    
          }
        i = i+1
        stmts
      }).flatten
    }).flatten
    
    val nwPre = for (p <- nwa.requires) yield 
      bAssume(transExpr(IdReplacer.visitExpr(p)(replacements))(renamings))
    val nwPost = for (q <- nwa.ensures) yield 
      (q.pos,transExpr(IdReplacer.visitExpr(q)(replacements))(renamings))

    // Network action entry
    val initStmt = 
      procVars.toList :::
      cInitAssumes :::
      readAssumes :::
      nwPre:::
      List(bAssume(VarExpr("C#init") ==@ VarExpr("C"))) :::
      (for ((_,nwi) <- nwInvs) yield bAssume(nwi)) :::
      (for ((chi,bChi) <- chInvs) yield {
        val baseMsg = "Channel invariant might not hold on action entry"
        val msg = if (chi.generated) baseMsg + " (generated " + GeneratedInvariantCount.next + ")" else baseMsg
        bAssert(bChi,chi.pos,msg)
      })
    val initProc = Boogie.Proc(Uniquifier.get(prefix+nwa.fullName+"#entry"),Nil,Nil,Modifies,Nil,initStmt)
    
    // Sub-actor executions
    val childActionProcs = new ListBuffer[Boogie.Proc]()
    val actorVars = new ListBuffer[Declaration]()
    val firingRules = new ListBuffer[Boogie.Expr]()
    for (inst <- entities) {
      val actor = inst.actor
      for (d <- actor.members) d match {
        case d: Declaration => actorVars += d
        case _ =>
      }
      for (m <- actor.members) m match {
        case ca@Action(_,false,_,_,_,_,_,_,_) => { // Ignore init actions for now
          val procName = prefix+nwa.fullName+Sep+actor.fullName+Sep+ca.fullName
          val (subActStmt,newVarDecls,firingRule) = 
            transSubActionExecution(
                inst, ca, networkRenamings, cInitAssumes, chInvs, actorVars.toList, sourceMap, targetMap)
          val stmt = 
            newVarDecls :::
            subActStmt
          childActionProcs += Boogie.Proc(Uniquifier.get(procName),Nil,Nil,Modifies,Nil,stmt)
          firingRules += firingRule
        }
        case _ => 
      }
    }
    
    // Network action exit
    val firingNeg = Boogie.UnaryExpr("!",firingRules.reduceLeft((a,b) => a || b)) 
    val exitStmt =
      procVars.toList:::
      cInitAssumes:::
      (for ((_,chi) <- chInvs) yield bAssume(chi)):::
      List(bAssume(firingNeg)):::
      (for (c <- connections) yield {
       if (!(delayedChannels contains c.id)) {
         c.to match {
           case PortRef(None,p) => {
             List(bAssert(bCredit(networkRenamings(c.id)) ==@ bInt(nwa.portOutputCount(p)),nwa.pos,
                 "The network might not produce the specified number of tokens on output " + p))
           }
           case PortRef(_,_) => 
             List(bAssert(bCredit(networkRenamings(c.id)) ==@ bInt(0),nwa.pos,
                 "The network might leave unread tokens on channel " + c.id))
         }
       }
       else Nil
      }).flatten:::
      outputs:::
      (nwPost.map { case (pos,q) => bAssert(q,pos,"Postcondition might not hold") }) :::
      (for (c <- connections) yield {
        c.to match {
          case pf@PortRef(None,port) => {
            val name = targetMap(pf)
            List(
                Boogie.Assign(
                    bRead(Boogie.VarExpr(name)),
                    bRead(Boogie.VarExpr(name)) + bCredit(Boogie.VarExpr(name))),
                Boogie.Assign(bCredit(Boogie.VarExpr(name)),Boogie.IntLiteral(0))
              )
          }
          case _ => Nil
        }
      }).flatten:::
      (for ((nwi,bNwi) <- nwInvs) yield 
          bAssert(bNwi,nwi.pos,"The network might not preserve the network invariant")) 
    val exitProc = Boogie.Proc(Uniquifier.get(prefix+nwa.fullName+"#exit"),Nil,Nil,Modifies,Nil,exitStmt)
    
    // The complete list of Boogie procedure generated for this network
    constDecl:::initProc::childActionProcs.toList:::List(exitProc)
  }
  
  val nextState = "St#next"
  
  def transSubActionExecution(
      instance: Instance, 
      action: Action, 
      networkRenamings: Map[String,String], // Channels and entities
      cInits: List[Boogie.Assume],
      chInvs: List[(ChannelInvariant,Boogie.Expr)],
      actorVars: List[Declaration], 
      sourceMap: Map[PortRef,List[String]], 
      targetMap: Map[PortRef,String]): (List[Boogie.Stmt],List[Boogie.LocalVar],Boogie.Expr) = {
    
    val actor = instance.actor
    val asgn = new ListBuffer[Boogie.Stmt]()
    val newVars = new ListBuffer[Boogie.LocalVar]()
    var renameMap = Map[Id,Id]()
    
    val parameterNames = instance.actor.parameters.map(p => Id(p.id))
    
    val actorParams = instance.actor.parameters.map(p => {
      val newName = "ActorParam"+Sep+p.id
      newVars += bLocal(newName,type2BType(p.typ))
      (Id(p.id),Id(newName))
    }).toMap
    
    renameMap = renameMap ++ actorParams
    for ((name,value) <- (parameterNames zip instance.arguments)) {
      // Add assumptions about the values of the actor parameters
      asgn += bAssume(transExpr(
            IdToIdReplacer.visitExpr(name)(renameMap)
          )(networkRenamings) ==@ transExpr(value)(networkRenamings))
    }
    
    asgn ++= cInits // Assumptions about initial state of channels
    asgn ++= (for ((_,chi) <- chInvs) yield bAssume(chi))  // Assume channel invariants
    
    for (av <- actorVars) {  // Add actor variables to variable declarations and renaming scheme
      val newName = "ActorVar"+Sep+av.id
      newVars += bLocal(newName,type2BType(av.typ))
      val declId = Id(av.id); declId.typ = av.typ
      renameMap = renameMap + (declId -> Id(newName))
    }
    for (av <- action.variables) {
      val newName = "ActionVar"+Sep+av.id
      newVars += bLocal(newName,type2BType(av.typ))
      val declId = Id(av.id); declId.typ = av.typ
      renameMap = renameMap + (declId -> Id(newName))
    }
    newVars += bLocal(nextState,BType.State)
    
    val firingConds = new ListBuffer[Boogie.Expr]() // Gather firing conditions from each pattern
    val replacements = scala.collection.mutable.HashMap.empty[Id,IndexAccessor]
    
    for (ipat <- action.inputPattern) {
      val cId = targetMap(PortRef(Some(instance.id),ipat.portId))
      val cond = Boogie.IntLiteral(ipat.numConsumed) <= bCredit(cId)
      
      val offset = ipat.vars.size-1
      for (v <- ipat.vars) yield {
        val c = ch(cId,v.typ)
        val acc = chAcc(c,Minus(rd(c),IntLiteral(offset)))
        replacements += (v -> acc)
      }
      
      firingConds += cond
    }
    
    val renamedGuard = action.guard match {
      case None =>
      case Some(g) =>
        val renamedGuard = IdReplacer.visitExpr(g)(replacements.toMap)
        val transGuard = transExpr(renamedGuard)(networkRenamings)
        asgn += bAssume(transGuard)
        firingConds += transGuard
    }
    
    
    val states = actor match {
      case ba: BasicActor => {
        ba.schedule match {
          case Some(schedule) => schedule.transitionsOnAction(action.fullName)
          case None => Nil
        }
      }
      case nw: Network => Nil
    }
    
    val stateGuards = 
      for ((f,t) <- states) yield {
        (bState(networkRenamings(instance.id)) ==@ Boogie.VarExpr(actor.id+Sep+f))
      }
    
        
    val stateInv = {
      if (!stateGuards.isEmpty) stateGuards.reduceLeft((a,b) => a || b)
      else Boogie.BoolLiteral(true)
    }
    asgn += bAssume(stateInv)
    
    firingConds ++= stateGuards
    val firingRule = {
      if (!firingConds.isEmpty) firingConds.reduceLeft((a,b) => a && b) 
      else Boogie.BoolLiteral(true)
    }
    asgn += bAssume(firingRule)
    
    for (ActorInvariant(e,_) <- actor.actorInvariants) {
      asgn += bAssume(transExpr(IdToIdReplacer.visitExpr(e)(renameMap))(networkRenamings))
    }
    
    for (ipat <- action.inputPattern) {
      val cId = targetMap(PortRef(Some(instance.id),ipat.portId))
      for (v <- ipat.vars) {
        val inVar = ipat.portId + Sep + v.id
        renameMap = renameMap + (v -> Id(inVar))
        newVars += bLocal(inVar,type2BType(v.typ))
        asgn += Boogie.Assign(Boogie.VarExpr(inVar),bChannelIdx(cId,bRead(cId)))
        asgn += Boogie.Assign(bRead(cId),bRead(cId) + Boogie.IntLiteral(1))
        asgn += Boogie.Assign(bCredit(cId),bCredit(cId) - Boogie.IntLiteral(1))
      }
    }
 
    for (pre <- action.requires) {
      val renamedPre = IdToIdReplacer.visitExpr(pre)(renameMap)
      asgn += bAssert(
          transExpr(renamedPre)(networkRenamings),pre.pos,
          "Precondition might not hold for instance at " + instance.pos)
    }
    for (post <- action.ensures) {
      val renamedPost = IdToIdReplacer.visitExpr(post)(renameMap)
      asgn += bAssume(transExpr(renamedPost)(networkRenamings))
    }
    for (opat <- action.outputPattern) {
      val cIds = sourceMap(PortRef(Some(instance.id),opat.portId))
      for (cId <- cIds) {
        for (e <- opat.exps) {
          val renamedExp = IdToIdReplacer.visitExpr(e)(renameMap)
          asgn += Boogie.Assign(bChannelIdx(cId,bRead(cId)+bCredit(cId)),transExpr(renamedExp)(networkRenamings))
          asgn += Boogie.Assign(bCredit(cId),bCredit(cId) + Boogie.IntLiteral(1))
        }
      }
    }
    
    val nextStateExp =
      for ((f,t) <- states) yield {
        (Boogie.VarExpr(nextState) ==@ Boogie.VarExpr(actor.id+Sep+t))
      }
    if (!nextStateExp.isEmpty) {
      asgn += bAssume(nextStateExp.reduceLeft((a,b) => a || b))
      asgn += Boogie.Assign(bState(networkRenamings(instance.id)), Boogie.VarExpr(nextState))
    }
    

    
    asgn ++= (for ((chi,bChi) <- chInvs) yield {
      val baseMsg = "Sub-actor action at " + action.pos + " might not preserve the channel invariant"
      val msg = if (chi.generated) baseMsg + " (generated " + GeneratedInvariantCount.next + ")" else baseMsg
      bAssert(bChi,chi.pos,msg)
    })
            
    (asgn.toList, newVars.toList, firingRule)
  }
  
  
  def transStmt(stmts: List[Stmt])(implicit renamings: Map[String,String]): List[Boogie.Stmt] = {
    val bStmts = new ListBuffer[Boogie.Stmt]()
    for (s <- stmts) {
      bStmts ++= (s match {
        case Assign(id,exp) => List(Boogie.Assign(transExpr(id),transExpr(exp)))
        case IndexAssign(id,idx,exp) => List(Boogie.AssignMap(transExpr(id),transExpr(idx),transExpr(exp)))
        case Assert(e) => List(bAssert(transExpr(e), e.pos, "Condition might not hold"))
        case Assume(e) => List(bAssume(transExpr(e)))
        case Havoc(ids) => for (i <- ids) yield { Boogie.Havoc(transExpr(i)) }
        case IfElse(ifCond,ifStmt,elseIfs,elseStmt) => {
          if (!elseIfs.isEmpty) {
            throw new RuntimeException("If-statements with else-if branches not supported yet")
          }
          List(Boogie.If(transExpr(ifCond),transStmt(ifStmt),transStmt(elseStmt)))
        }
        case While(_,_,_) =>
          throw new RuntimeException("Loops not supported yet")
          
      })
    }
    bStmts.toList
  }
  
  def transExpr(exp: Expr)(implicit renamings: Map[String,String]): Boogie.Expr = {
    exp match {
      case And(e1,e2) => transExpr(e1) && transExpr(e2)
      case Or(e1,e2) => transExpr(e1) || transExpr(e2)
      case Implies(e1,e2) => transExpr(e1) ==> transExpr(e2)
      case Iff(e1,e2) => transExpr(e1) <==> transExpr(e2)
      case Not(e) => UnaryExpr("!",transExpr(e)) 
      case Less(e1,e2) => transExpr(e1) < transExpr(e2)
      case Greater(e1,e2) => transExpr(e1) > transExpr(e2)
      case AtLeast(e1,e2) => transExpr(e1) >= transExpr(e2)
      case AtMost(e1,e2) => transExpr(e1) <= transExpr(e2)
      case Eq(e1,e2) => transExpr(e1) ==@ transExpr(e2)
      case NotEq(e1,e2) => transExpr(e1) !=@ transExpr(e2)
      case Plus(e1,e2) => transExpr(e1) + transExpr(e2)
      case Minus(e1,e2) => transExpr(e1) - transExpr(e2)
      case Times(e1,e2) => transExpr(e1) * transExpr(e2)
      case Div(e1,e2) => 
        BoogiePrelude.addComponent(DivModAbsPL)
        Boogie.FunctionApp("AT#Div",List(transExpr(e1),transExpr(e2)))
        //transExpr(e1) / transExpr(e2)
      case Mod(e1,e2) =>
        BoogiePrelude.addComponent(DivModAbsPL)
        Boogie.FunctionApp("AT#Mod",List(transExpr(e1),transExpr(e2)))
        //transExpr(e1) % transExpr(e2)
      case RShift(e1,e2) =>
        BoogiePrelude.addComponent(ShiftsPL)
        Boogie.FunctionApp("AT#RShift",List(transExpr(e1),transExpr(e2)))
      case LShift(e1,e2) =>
        BoogiePrelude.addComponent(ShiftsPL)
        Boogie.FunctionApp("AT#LShift",List(transExpr(e1),transExpr(e2)))
      case UnMinus(e) => UnaryExpr("-",transExpr(e))
      case IfThenElse(c,e1,e2) => Boogie.Ite(transExpr(c),transExpr(e1),transExpr(e2))
      case Forall(vars,e,pat) => 
        Boogie.Forall(Nil,
          for (v <- vars) yield Boogie.BVar(v.id,type2BType(v.typ)),
          pat match {
            case None => Nil
            case Some(p) => List(Boogie.Trigger(List(transExpr(p))))
          },
          transExpr(e)
        )
      case Exists(vars,e,pat) => 
        Boogie.Exists(Nil,
          for (v <- vars) yield Boogie.BVar(v.id,type2BType(v.typ)),
          pat match {
            case None => Nil
            case Some(p) => List(Boogie.Trigger(List(transExpr(p))))
          },
          transExpr(e)
        )
      case FunctionApp(name,params) => {
        name match {
          case "rd" => bRead(transExpr(params(0)))
          case "urd" => bCredit(transExpr(params(0)))
          case "tot" => bRead(transExpr(params(0)))+bCredit(transExpr(params(0)))
          case "initial" => bCredInit(transExpr(params(0)))
          case "next" => bChannelIdx(transExpr(params(0)), bRead(transExpr(params(0))))
          case "prev" => bChannelIdx(transExpr(params(0)), bRead(transExpr(params(0))) - Boogie.IntLiteral(1))
          case "tokens" => bCredit(transExpr(params(0))) ==@ transExpr(params(1))
          case "state" => {
            val actor = params(0).typ.asInstanceOf[ActorType].actor
            val id = params(1).asInstanceOf[Id].id
            bState(transExpr(params(0))) ==@ Boogie.VarExpr(actor.fullName+Sep+id)
          }
          case _ => throw new RuntimeException() // Should not happen
        }
      }
      case IndexAccessor(e,i) => {
        if (e.typ.isChannel) bChannelIdx(transExpr(e),transExpr(i))
        else transExpr(e) apply transExpr(i)
      }
      case ListLiteral(lst) => {
        var listlit: Boogie.Expr = intlst
        var i = 0
        for (e <- lst) {
          val transE = transExpr(e)
          listlit = Boogie.MapStore(listlit,Boogie.IntLiteral(i),transE)
          i = i+1
        }
        listlit
      }

      case IntLiteral(i) => Boogie.IntLiteral(i)
      case HexLiteral(x) => {
        val bigInt = x.toList.map("0123456789abcdef".indexOf(_)).map(BigInt(_)).reduceLeft(_ * 16 + _)
        Boogie.IntLiteral(bigInt.toString) // To decimal conversion
      }
      case BoolLiteral(b) => Boogie.BoolLiteral(b)
      case FloatLiteral(f) => Boogie.RealLiteral(f.toDouble)
      case Id(id) => renamings.get(id) match {
        case None => Boogie.VarExpr(id)
        case Some(newId) => Boogie.VarExpr(newId)
      } 
    }
  }
  
  object Helper {
    import Boogie.Expr
    
    def type2BType(t: Type): Boogie.BType = {
      assert(t != null)
      t match {
        case IntType(_) => BType.Int
        case BoolType => BType.Bool
        case FloatType => BType.Real
        case HalfType => BType.Real
        case UintType(_) => BType.Int
        case ChanType(contentType) => BType.Chan(type2BType(contentType))
        case ActorType(_) => BType.Actor
        case ListType(contentType,_) => BType.List(type2BType(contentType))
        case UnknownType =>
          assert(false, "Unknown types should not occur during the translation")
          null
      }
    }
    
    def bLocal(id: String, tp: Type) = new Boogie.LocalVar(id, type2BType(tp))
    def bLocal(id: String, tp: BType) = new Boogie.LocalVar(id, tp)
    def bThisDecl = bLocal(BMap.This,BType.Actor)
    
    def bBool(b: Boolean) = Boogie.BoolLiteral(b)
    def bInt(i: Int) = Boogie.IntLiteral(i)
    def bAssert(e: Expr, pos: Position, msg: String) = new Boogie.Assert(e, pos, msg)
    def bAssert(e: Expr) = new Boogie.Assert(e,null,"Condition might not hold") 
    def bAssume(e: Expr) = Boogie.Assume(e)
    def bAssert2Assume(assert: Boogie.Assert) = new Boogie.Assume(assert.e)
   
    def bCredit(connName: String) = (VarExpr(BMap.C) apply VarExpr(connName))
    def bCredit(channel: Boogie.Expr) = (VarExpr(BMap.C) apply channel)
    
    def bCredInit(connName: String) = (VarExpr(BMap.CInit) apply VarExpr(connName))
    def bCredInit(channel: Boogie.Expr) = (VarExpr(BMap.CInit) apply channel)
    
    def bRead(connName: String) = (VarExpr(BMap.R) apply VarExpr(connName))
    def bRead(channel: Boogie.Expr) = (VarExpr(BMap.R) apply channel)
    
    def bTotal(connName: String) = (bRead(connName)+bCredit(connName))
    def bTotal(channel: Boogie.Expr) = (bRead(channel)+bCredit(channel))
    
    def bChannel(connName: String): Expr = (VarExpr(BMap.M) apply VarExpr(connName))
    def bChannelIdx(connName: String, ind: Boogie.Expr): Expr = ((VarExpr(BMap.M) apply VarExpr(connName)) apply ind)
    def bChannel(channel: Boogie.Expr): Expr = (VarExpr(BMap.M) apply channel)
    def bChannelIdx(channel: Boogie.Expr, ind: Boogie.Expr): Expr = ((VarExpr(BMap.M) apply channel) apply ind)
    
    def bState(id: String) = VarExpr(BMap.St) apply VarExpr(id)
    def bState(actor: Boogie.Expr) = VarExpr(BMap.St) apply actor
    val bThis = bState(BMap.This)
    
    val intlst = VarExpr("AT#intlst");

  }
  
}

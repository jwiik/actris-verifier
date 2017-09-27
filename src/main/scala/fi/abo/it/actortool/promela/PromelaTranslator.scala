package fi.abo.it.actortool.promela

import fi.abo.it.actortool._
import scala.collection.mutable.ListBuffer
import fi.abo.it.actortool.ActorTool.CommandLineParameters
import fi.abo.it.actortool.util.FunctionCallReplacer
import fi.abo.it.actortool.util.ActionPeekAnalyzer
import fi.abo.it.actortool.util.ActionPeekAnalyzer
import fi.abo.it.actortool.util.PriorityMapBuilder
import fi.abo.it.actortool.util.ASTPrinter
import fi.abo.it.actortool.util.Analysis

case class Translation[+T<:DFActor](
    val entity: T, 
    val contract: ContractAction,
    val promelaProgram: List[Promela.Decl],
    val ltlFormula: Promela.Expr,
    val idMap: IdMap,
    val mergedActors: Map[String,BasicActor])

class BiMap[T,U] {
  private val to = collection.mutable.Map[T,U]()
  private val from = collection.mutable.Map[U,T]()
  
  def add(t: T, u: U) = {
    to(t) = u
    from(u) = t
  }
  
  def getDomain(t: T) = to(t)
  def getCodomain(u: U) = from(u)
  def containsDomain(t: T) = to.contains(t)
  def containsCodomain(u: U) = from.contains(u)
}

class IdMap {
  private var counter = 0
  private val map = new BiMap[Int,Instance]()
  
  def generateId(instance: Instance): Int = {
    if (map.containsCodomain(instance)) {
      throw new RuntimeException()
    }
    val id = counter
    map.add(id, instance)
    counter = counter+1
    return id
  }
  
  def getInstance(id: Int) = map.getDomain(id)
  
}

trait RenamingContext {
  val charMapping = Map("$" -> "__", "#" -> "__")
  def R(s: String): String
  def add(from: String, to: String): String
  def get(name: String): Option[String]
  def has(name: String): Boolean
  def getSubContext: RenamingContext
  def isUninterpreted(v: String): Boolean
  protected def rename(s: String) = charMapping.foldLeft(s)((a, b) => a.replaceAllLiterally(b._1, b._2))
}

class ChildRenamingContext(parent: RenamingContext) extends RenamingContext {
  
  private val map = collection.mutable.Map[String,String]()
  private val uninterpreted = collection.mutable.Set[String]()
  
  def has(name: String) = map.contains(name)
  def get(name: String) = {
    if (has(name)) map.get(name)
    else parent.get(name)
  }
  def addUninterpreted(v: String) { uninterpreted.add(v)  }
  def isUninterpreted(v: String) = uninterpreted.contains(v) || parent.isUninterpreted(v)
  def add(from: String, to: String) = {
    //if (has(from) || parent.has(from)) throw new IllegalArgumentException("Renaming already defined for " + from)
    map(from) = to
    to
  }
  def R(s: String) = renaming(s)
  private def renaming(s: String): String = {
    val newName = rename(s)
    return newName
  }
  def getSubContext = new ChildRenamingContext(this)
  override def toString = map.toString + " :: " + parent.toString
}

class RootRenamingContext extends RenamingContext {
  
  private val map = collection.mutable.Map[String,String]()
  private val uninterpreted = collection.mutable.Set[String]()
  
  private def renaming(s: String): String = {
    val newName = rename(s)
    return newName
  }
  
  def add(from: String, to: String): String = {
    if (map.contains(from)) throw new IllegalArgumentException("Already in map")
    map(from) = to
    to
  }
  def has(name: String) = map.contains(name)
  def get(from: String) = map.get(from)
  def R(s: String) = renaming(s)
  def getSubContext = new ChildRenamingContext(this)
  
  def addUninterpreted(v: String) { uninterpreted.add(v)  }
  def isUninterpreted(v: String) = uninterpreted.contains(v)
  
  override def toString = map.toString
}

class PromelaTranslator(params: CommandLineParameters) {

  val P = Promela
  val inputGenerator = new InputGenerator
  val funCallReplacer = new FunctionCallReplacer
  
  val rootRenamings = new RootRenamingContext
  
  
  
  def invoke(
      entity: DFActor, 
      mergedActors: Map[String,BasicActor], 
      alreadyTranslated: Map[String,P.ProcType], 
      constants: List[Declaration]): List[Translation[DFActor]] = {
    
    assert(!entity.contractActions.isEmpty, entity.fullName + " has no contracts")
    val procs = new ListBuffer[P.ProcType]
    entity match {
      case nw: Network => {
        val entities = nw.entities.get.entities
        for (e <- entities) {
          if (alreadyTranslated.contains(e.actor.id)) {
            assert(false)
            procs += alreadyTranslated(e.actor.id)
          }
          else if (mergedActors.contains(e.actor.id)) {
            val mergedActor = mergedActors(e.actor.id)
            val proc = translateActor(mergedActor, constants)
            procs += proc
          }
          else {
            assert(false)
          }
        }
        translateNetwork(nw, constants, procs.toList, mergedActors)
      }
      case ba: BasicActor => {
        if (alreadyTranslated.contains(ba.id)) {
          procs += alreadyTranslated(ba.id)
        }
        else {
          procs += translateActor(ba,constants)
        }
        translateBasicActor(ba, constants, procs.toList, mergedActors)
      }
    }
    
  }
  
  def generateEndStatePredicate(
      actor: DFActor, 
      contract: ContractAction, 
      channelMap: Map[PortRef,Connection], 
      connections: List[Connection]): P.Expr = {
    
    actor match {
      case nw: Network => 
        generateEndStatePredicate(
            nw, 
            TokensDefFinder.find(nw.contractInvariants map (_.expr)).toMap, 
            contract, 
            channelMap, 
            nw.structure.get.connections)
      case ba: BasicActor => {
        generateEndStatePredicate(
            ba, 
            Map.empty, 
            contract, 
            channelMap, 
            connections)
      }
    }
  }
  
  def generateEndStatePredicate(
      actor: DFActor, 
      delayTokens: Map[String,Expr], 
      contract: ContractAction, 
      channelMap: Map[PortRef,Connection],
      connections: List[Connection]): P.Expr = {
    
    val outputTokens = 
      actor.outports.map( p => (channelMap(PortRef(None,p.id)).id, contract.outportRate(p.id)) ).toMap
    
    val channelPredicate = {
      connections.map { c =>
        val tokenAmount =
          if (outputTokens.contains(c.id)) IntLiteral(outputTokens(c.id))
          else delayTokens.getOrElse(c.id,IntLiteral(0))
        P.BinaryExpr(P.FunCall("len",List(P.VarExp(c.id))), "==" , translateExpr(tokenAmount)(rootRenamings))
      }.reduceLeft((a,b) => P.BinaryExpr(a,"&&",b))
    }
    P.BinaryExpr(channelPredicate,"&&",P.VarExp("timeout"))
    //P.BinaryExpr(channelPredicate,"&&",P.VarExp("teerp"))
  }
  
  def translateBasicActor(
      actor: BasicActor, 
      constants: List[Declaration], 
      procs: List[P.ProcType], 
      mergedActors: Map[String,BasicActor]): List[Translation[BasicActor]] = {
    
    val idMap = new IdMap
    val decls = new ListBuffer[P.Decl]()
    val instances = ListBuffer[(String,PromelaInstance)]()
    
    
    val instance = Instance("this",actor.id,Nil)
    instance.actor = actor
    val connections = 
      actor.inports.map { p => val c = Connection(Some("ch__"+p.id),PortRef(None,p.id),PortRef(Some("this"),p.id)); c.typ = ChanType(p.portType); c } :::
      actor.outports.map { p => val c = Connection(Some("ch__"+p.id),PortRef(Some("this"),p.id),PortRef(None,p.id)); c.typ = ChanType(p.portType); c }
    val channelMapping = Util.buildConnectionMap(connections)
    
    for (c <- constants) {
      decls += P.VarDecl(rootRenamings.R(c.id), translateType(c.typ), Some(translateExpr(c.value.get)(rootRenamings)))
    }
    
    for (c <- connections) {
      decls += P.VarDecl(rootRenamings.R(c.id), P.NamedType("chan"),Some(P.ChInit(params.PromelaChanSize,translateType(c.typ.asInstanceOf[ChanType].contentType))))
    }
    
    
    
    for (e <- List(instance)) {
      val connections = {
        for (p <- e.actor.inports:::e.actor.outports) yield {
          val conn = channelMapping(PortRef(Some(e.id),p.id))
          (p.id,conn)
        }
      }.toMap
      instances += (e.id -> PromelaInstance(e.id,e.arguments,actor,idMap.generateId(e),connections))
    }
    
    val runs: List[P.Run] = {
      for ((id,instance) <- instances.toList) yield {
        val actor = instance.actor
        val chanNames = actor.inports:::actor.outports map { p => instance.connections(p.id) }
        val chanParams = chanNames map { p => P.VarExp(rootRenamings.R(p.id)) }
        val givenParams = instance.arguments map { x => translateExpr(x)(rootRenamings) }
        P.Run(actor.id, P.IntLiteral(instance.mapId)::chanParams:::givenParams, None)
      }
    }
    
    val inits = generateInitialisations(actor, runs, (channelMapping.map { case (pr,c) => (pr,c.id) }).toMap , constants)
    
    val contractTranslations = 
      for ((contract,init) <- inits) yield {
        val formula = generateEndStatePredicate(actor, contract, channelMapping, connections)
        
        val instr = Instrumentation.mkInstrumentationDef(List.empty, rootRenamings, params.ScheduleWeights, formula)
        
        val setups = List(init)
        
        val program: List[P.Decl] = decls.toList ::: List(instr) ::: procs ::: setups
        //(contract,program)
        Translation(actor,contract,program,formula,idMap,mergedActors)
      }
    contractTranslations.toList
  }
  
  def translateNetwork(nw: Network, constants: List[Declaration], procs: List[P.ProcType], mergedActors: Map[String,BasicActor]): List[Translation[Network]] = {
    val idMap = new IdMap
    val decls = ListBuffer[P.Decl]()
    val instances = ListBuffer[(String,PromelaInstance)]()
    
     val channelMapping = Util.buildConnectionMap(nw.structure.get.connections)
    
    for (c <- constants) {
      decls += P.VarDecl(rootRenamings.R(c.id), translateType(c.typ), Some(translateExpr(c.value.get)(rootRenamings)))
    }
    
    for (c <- nw.structure.get.connections) {
      decls +=  P.VarDecl(rootRenamings.R(c.id), P.NamedType("chan"),Some(P.ChInit(params.PromelaChanSize,translateType(c.typ.asInstanceOf[ChanType].contentType))))
    }
    
    decls += P.VarDecl(
        Instrumentation.MAX_SIZE_ARRAY,
        P.ArrayType(P.NamedType("int"), nw.structure.get.connections.size),
        None)
    
//    for (c <- nw.structure.get.connections) {
//      decls +=  
//        P.VarDecl(
//            "__INSTR_MAX_" + rootRenamings.R(c.id), 
//            P.NamedType("int"),
//            Some(P.IntLiteral(0)))
//    }
    
    
    val chans = nw.structure.get.connections.filter{ c => !c.isInput && !c.isOutput }
    val chansWithMax = chans.map { ch => {
      ch.to match {
        case PortRef(Some(actor),port) => {
          val unmA = nw.entities.get.entities.find { x => x.id == actor }.get
          val a = mergedActors(unmA.actorId)
          val maxRates = computeMaxRates(a,true)
          (ch, maxRates.find(_._1.id == port).get._2)

        }
        case _ => throw new RuntimeException()
      }
    }}
    
    
    
    for (e <- nw.entities.get.entities) {
      val connections = {
        for (p <- e.actor.inports:::e.actor.outports) yield {
          val conn = channelMapping(PortRef(Some(e.id),p.id))
          (p.id,conn)
        }
      }.toMap
      instances += (e.id -> PromelaInstance(e.id,e.arguments,mergedActors(e.actor.id),idMap.generateId(e),connections))
    }
    
    val runs: List[P.Run] = {
      for (((id,instance),idx) <- instances.toList.zipWithIndex) yield {
        val actor = instance.actor
        val chanNames = actor.inports:::actor.outports map { p => instance.connections(p.id) }
        val chanParams = chanNames map { p => P.VarExp(rootRenamings.R(p.id)) }
        val givenParams = instance.arguments map { x => translateExpr(x)(rootRenamings) }
        P.Run(actor.id, P.IntLiteral(instance.mapId)::chanParams:::givenParams, Some(P.IntLiteral(idx+1)))
      }
    }
    
    val inits = generateInitialisations(nw, runs, (channelMapping.map { case (pr,c) => (pr,c.id) }).toMap , constants)
    
    val contractTranslations = 
      for ((contract,init) <- inits) yield {
        val formula = generateEndStatePredicate(nw, contract, channelMapping, List.empty)
        
        val instr = Instrumentation.mkInstrumentationDef(chansWithMax, rootRenamings, params.ScheduleWeights, formula)
        
        val setups = List(init) 
        
        val program: List[P.Decl] = decls.toList ::: List(instr) ::: procs ::: setups
        //(contract,program)
        Translation(nw,contract,program,formula,idMap,mergedActors)
      }
    
    contractTranslations.toList
  }
  
  def generateInitialisations(entity: DFActor, runs: List[P.Stmt], channelMapping: Map[PortRef, String], constants: List[Declaration]): Map[ContractAction,P.Init] = {
    (for (contract <- entity.contractActions) yield {
      // Generate an input satisfying the contract
      val input = inputGenerator.generateInput(contract,constants)
      
      val initBlock = new ListBuffer[P.Stmt]
      for (pat <- contract.inputPattern) {
        // Get the correct channel id
        val chan = channelMapping(PortRef(None,pat.portId))
        for (i <- 0 to pat.rate-1) {
          val inputToken = input(pat.portId)(i)
          initBlock += P.Send(rootRenamings.R(chan), translateExpr(inputToken)(rootRenamings))
        }
      }
      
      initBlock += P.Atomic(runs)
      (contract,P.Init(initBlock.toList))
    }).toMap
  }

  case class PromelaInstance(id: String, arguments: List[Expr], actor: BasicActor, mapId: Int, connections: Map[String,Connection])
  
  def computeMaxRates(actor: DFActor, withRepeat: Boolean) = {
    val rates = actor.inports.map {
      ip => { 
        ip ->
        (actor.actorActions.filter(!_.init).map { 
          t =>
            t.portInputPattern(ip.id) match {
              case None => 0
              case Some(pat) => {
                if (!withRepeat) if (pat.repeat == 1) pat.rate else 1
                else pat.rate
              }
            }
        })
      }
    }
    val maxRates = rates.map { case (p,r) => (p, r.foldLeft(0)((a,b) => if (a < b) b else a)) }
    maxRates
  }
  
  def translateActor(a: BasicActor, constants: List[Declaration]): P.ProcType = {
    val actorRenamings = rootRenamings.getSubContext
    
    val params = new ListBuffer[P.ParamDecl]
    val decls = new ListBuffer[P.Stmt]
    val constInits = new ListBuffer[P.Stmt]
    val actions = new ListBuffer[P.Stmt]
    
    funCallReplacer.setFunctionDeclarations(a.functionDecls)
    
    params += P.ParamDecl("__uid",P.NamedType("int"))
    for (ip <- a.inports) params += P.ParamDecl(ip.id,P.NamedType("chan"))
    for (op <- a.outports) params += P.ParamDecl(op.id,P.NamedType("chan"))
    for (p <- a.parameters) params += P.ParamDecl(p.id, translateType(p.typ))
    for (v <- a.variables) {
      val uninterpreted = v.hasAnnotation("Uninterpreted")
      if (uninterpreted) {
        actorRenamings.addUninterpreted(v.id)
      }
      else {
        val (decl,constInit) = translateDeclaration(v, actorRenamings.R(v.id), actorRenamings, uninterpreted)
        decls ++= decl
        constInits ++= constInit
      }
      
//      val value = if (v.value.isDefined) Some(translateExpr(v.value.get)(actorRenamings)) else None  
//      decls += P.VarDecl(actorRenamings.R(v.id),translateType(v.typ), value)
    }
    
    val initBody: Option[P.Stmt] = {
      //val initAction = a.actorActions.find { _.init }
      a.actorActions.find { _.init } match {
        case Some(act) => {
          val initStmt = new ListBuffer[P.Stmt]
          for (v <- act.variables) {
            val value = if (v.value.isDefined) Some(translateExpr(v.value.get)(actorRenamings)) else None  
            initStmt += P.VarDecl(actorRenamings.R(v.id),translateType(v.typ),value)
          }
          initStmt ++= translateStmts(act.body)(actorRenamings)
          for (p <- act.outputPattern) {
            for (e <- p.exps) {
              initStmt += P.Send(actorRenamings.R(p.portId), translateExpr(e)(actorRenamings))
            }
          }
          if (initStmt.isEmpty) {
            None
          }
          else if (act.inputPattern.isEmpty && act.outputPattern.isEmpty) {
            Some(P.DStep(initStmt.toList))
          }
          else {
            Some(P.Atomic(initStmt.toList))
          }
        }
        case None => None
      }
    }
    
    val peekAnalyzer = new ActionPeekAnalyzer
    val priorityMap = PriorityMapBuilder.buildPriorityMap(a, false, true)
    
    val maxRates = computeMaxRates(a,false)
    
    // Create enough input variable declarations for each inport
    for ((ip,rate) <- maxRates) {
      for (i <- 0 to rate-1)
        decls += P.VarDecl(ip.id+"__"+i.toString,translateType(ip.portType),None)
    }
    
    
    val peeks = peekAnalyzer.analyze(a.actorActions.filter { !_.init }, priorityMap)
    
    for ((port,rate) <- peeks) {
      val stmt = new ListBuffer[P.Stmt]
      decls += P.VarDecl(port+"__peek",P.NamedType("bool"),Some(P.BoolLiteral(false)))
      stmt += P.Peek(port, P.VarExp(port+"__"+(rate-1).toString))
      stmt += P.Assign(P.VarExp(port+"__peek"),P.BoolLiteral(true))
      val guard1 = P.UnaryExpr("!", P.VarExp(port+"__peek"))
      val guard2 = P.BinaryExpr(P.IntLiteral(1),"<=",P.FunCall("len",List(P.VarExp(port)))) 
      val guard = P.BinaryExpr(guard1,"&&",guard2)
      actions += P.Atomic(List(P.GuardStmt(P.ExprStmt(guard),stmt.toList)))
    }
    
    val firingRules = collection.mutable.Map[AbstractAction,P.Expr]()
    val actionRenamingMap = collection.mutable.Map[AbstractAction,RenamingContext]()
    
    for (act <- a.actorActions.filter { !_.init }) {
      
      val peekings = peekAnalyzer.analyze(act, priorityMap)
      val peekGuards: Iterable[P.Expr] = {
        peekings.flatMap {
          case (p,r) => if (r > 0) List(P.VarExp(p+"__peek")) else Nil
        }
      }
      val actionRenamings = actorRenamings.getSubContext
      val inputRatePreds = 
        act.inputPattern.map { 
          ip => P.BinaryExpr(P.IntLiteral(ip.rate),"<=",P.FunCall("len",List(P.VarExp(ip.portId)))) 
        }
      val inputPat = 
        if (inputRatePreds.isEmpty) P.BoolLiteral(true)
        else inputRatePreds.reduceLeft((a,b) => P.BinaryExpr(a,"&&",b))

      act.inputPattern flatMap { ip =>
        ip.vars.zipWithIndex map { case (v,i) => actionRenamings.add(v.id,ip.portId+"__"+i.toString) }
      }
      
      val firingRule = {
        val pureFiringRule =
          if (act.guards.isEmpty) inputPat
          else {
            val andedGuards = act.guards.reduceLeft((a,b) => { val and = And(a,b); and.typ = BoolType; and } )
            P.BinaryExpr(inputPat,"&&",translateExpr(andedGuards)(actionRenamings) )
          }
        
        if (!peekGuards.isEmpty) {
          P.BinaryExpr(peekGuards.reduceLeft((a,b) => { P.BinaryExpr(a,"&&",b) }),"&&",pureFiringRule)
        }
        else pureFiringRule
      }
      actionRenamingMap += (act -> actionRenamings)
      firingRules += (act -> firingRule)
    }
    
    for ((act,idx) <- a.actorActions.filter{ !_.init }.zipWithIndex) {
      val allFiringRules = firingRules(act) :: priorityMap(act).map { a => P.UnaryExpr("!",firingRules(a)) }
      val firingRule = allFiringRules.reduceLeft((a,b) => P.BinaryExpr(a,"&&",b))
      
      val beforeInputRenamings = actionRenamingMap(act)
      
      val peekings = peekAnalyzer.analyze(act, priorityMap)
      
      val peekResets = 
        peekings.flatMap {
          case (p,r) => if (r > 0) List(P.Assign(P.VarExp(p+"__peek"),P.BoolLiteral(false))) else Nil
        }
      
      val stmt = new ListBuffer[P.Stmt]
      
//      stmt += 
//        P.If(List(
//          P.GuardStmt(P.ExprStmt(P.VarExp("more_expensive")), List(P.Goto("term"))),
//          P.GuardStmt(P.Else, List(P.Skip))).
//          map { g => P.OptionStmt(List(g)) })
      
      stmt += P.PrintStmtValue("<action id='%d' actor='"+rootRenamings.R(a.fullName)+ "' action='" + rootRenamings.R(act.fullName) + "' />\\n",List(P.VarExp("__uid")))
      val actionRenamings = beforeInputRenamings.getSubContext
      for (p <- act.inputPattern) {
        if (p.repeat > 1) {
          val v = p.vars(0)
          val name = p.portId+"__List"
          actionRenamings.add(v.id, name)
          stmt += P.VarDecl(name,P.ArrayType(translateType(p.typ),p.repeat), None)
          for (i <- 0 until p.repeat) {
            stmt += P.Receive(rootRenamings.R(p.portId), translateExpr(v)(beforeInputRenamings))
            stmt += P.Assign(P.IndexAccessor(P.VarExp(name),P.IntLiteral(i)), translateExpr(v)(beforeInputRenamings))
          }
        }
        else {
          for (v <- p.vars) {
            stmt += P.Receive(rootRenamings.R(p.portId), translateExpr(v)(actionRenamings))
          }
        }
      }
      
      act.refinedContract match {
        // No refined contract (unmerged basic actor without contract)
        case None => {
          for (v <- act.variables) {
            val uninterpreted = v.hasAnnotation("Uninterpreted")
            val (decls, inits) = translateDeclaration(v, rootRenamings.R(v.id), actionRenamings, uninterpreted)
            stmt ++= decls
            stmt ++= inits
          }
          
          val body = translateStmts(act.body)(actionRenamings)
          if (!body.isEmpty) {
            stmt += P.DStep(body)
          }
          
          for (p <- act.outputPattern) {
            if (p.repeat > 1) {
              val e = translateExpr(p.exps(0))(actionRenamings)
              for (i <- 0 until p.repeat) {
                stmt += P.Send(rootRenamings.R(p.portId), P.IndexAccessor(e,P.IntLiteral(i)))
              }
            }
            else {
              for (e <- p.exps) {
                stmt += P.Send(rootRenamings.R(p.portId), translateExpr(e)(actionRenamings))
              }
            }
          }
        }
        // Use contract abstraction
        case Some(contract) => {
          val data = inputGenerator.generateInput(contract, constants)
          for (p <- contract.outputPattern) {
            for (i <- 0 until p.rate) {
              stmt += P.Send(rootRenamings.R(p.portId), translateExpr(data(p.portId)(i))(actionRenamings))
            }
          }
        }
      }
      
      
      stmt += Instrumentation.mkInstrumentationCall(P.VarExp("__uid"), P.IntLiteral(idx))
      //stmt += P.CCode( InstrumentationCall(a.id,"__uid",idx.toString) )
      stmt ++= peekResets
      actions += P.Atomic(P.Comment("Action: " + act.fullName)::List(P.GuardStmt(P.ExprStmt(firingRule), stmt.toList)))
    }
    
    val constInitBlock = if (!constInits.isEmpty) List(P.DStep(constInits.toList)) else Nil  
    
    val opts = actions.toList map { a => P.OptionStmt(List(a)) }
    P.ProcType(a.id, params.toList, Nil, decls.toList ::: constInitBlock ::: initBody.toList ::: List(P.Iteration(opts)))
  }
  
  def translateDeclaration(
      d: Declaration, 
      newName: String, 
      renamings: RenamingContext, 
      uninterpreted: Boolean): (List[P.Stmt],List[P.Stmt]) = {
    
    val stmt = new ListBuffer[P.Stmt]
    val constInits = new ListBuffer[P.Stmt]
    
    if (uninterpreted) {
      return (List.empty,List.empty)
    }
    
    if (d.constant) {
      d.value match {
        case Some(value) => {
          value match {
            case ListLiteral(lst) => {
              
              stmt += P.VarDecl(newName,translateType(d.typ), None)
              
              val init = for ((l,i) <- lst.zipWithIndex) yield {
                P.Assign(P.IndexAccessor(P.VarExp(newName),P.IntLiteral(i)) , translateExpr(l)(renamings))
              }
              
              constInits ++= init
              
              //stmt ++= handleCollectionLiteralDecl(lst, newName, P.VarExp(newName), d.typ)
            }
            case MapLiteral(_,lst) => {
              
              stmt += P.VarDecl(newName,translateType(d.typ), None)
              val init = for ((l,i) <- lst.zipWithIndex) yield {
                P.Assign(P.IndexAccessor(P.VarExp(newName),P.IntLiteral(i)) , translateExpr(l)(renamings))
              }
              
              constInits ++= init
              
              //stmt ++= handleCollectionLiteralDecl(lst, newName, P.VarExp(newName), d.typ)
            }
            case x => stmt += P.VarDecl(newName,translateType(d.typ), None)
            constInits += P.Assign(P.VarExp(newName),translateExpr(x)(renamings))
          }
        }
        case None => stmt += P.VarDecl(newName,translateType(d.typ), None)
      }
    }
    else {
      stmt += P.VarDecl(newName,translateType(d.typ), None)
    }
    
    (stmt.toList, constInits.toList)
  }
  
  def handleCollectionLiteralDecl(lst: List[Expr], newName: String, assignArray: P.Expr, tp: Type, renamings: RenamingContext): List[P.Stmt] = {
    val stmt = new ListBuffer[P.Stmt]
    stmt += P.VarDecl(newName,translateType(tp), None)
//    if (Analysis.allEqual(lst)) {
//      val iterVar = "__idx__"+newName
//      stmt += P.VarDecl(iterVar,P.NamedType("int"),None)
//      val asgn = P.Assign(P.IndexAccessor(assignArray,P.VarExp(iterVar)) , translateExpr(lst(0))(renamings))
//      stmt += P.For(P.VarExp(iterVar), P.IntLiteral(0), P.IntLiteral(lst.size-1),List(asgn))
//    }
//    else {
      for ((l,i) <- lst.zipWithIndex) {
        stmt += P.Assign(P.IndexAccessor(assignArray,P.IntLiteral(i)) , translateExpr(l)(renamings))
      }
//    }
    stmt.toList
  }
  
  def translateStmts(stmt: List[Stmt])(implicit renamings: RenamingContext): List[P.Stmt] = {
    stmt map { s => translateStmt(s) }
  }
  
  def translateStmt(stmt: Stmt)(implicit renamings: RenamingContext): P.Stmt = {
    stmt match {
      case Assign(id,e) => {
        if (renamings.isUninterpreted(id.id)) {
          P.Skip
        }
        //val (newE,info) = ListLiteralReplacer.findAndReplace(e)
        else if (id.typ.isMap) {
          e match {
            case IfThenElse(cond,thn,els) => {
              val newIfStmt = {
                val (newThn,info) = ListLiteralReplacer.findAndReplace(thn)
                if (!info.isEmpty) {
                  val sequence = new ListBuffer[P.Stmt]
                  for ((s,lit) <- info) {
                    sequence ++= handleCollectionLiteralDecl(lit.elements, s, translateExpr(id), lit.typ, renamings)
                  }
                  //sequence += P.Assign(translateExpr(id),translateExpr(newThn))
                  P.Sequence(sequence.toList)
                }
                else P.Assign(translateExpr(id),translateExpr(newThn))
              }
              val ifPart = P.GuardStmt(P.ExprStmt(translateExpr(cond)), List(newIfStmt))
               
              
              val newElsStmt = {
                val (newEls,info) = ListLiteralReplacer.findAndReplace(els)
                if (!info.isEmpty) {
                  val sequence = new ListBuffer[P.Stmt]
                  for ((s,lit) <- info) {
                    
                    sequence ++= handleCollectionLiteralDecl(lit.elements, s, translateExpr(id), lit.typ, renamings)
                    
//                    sequence += P.VarDecl(s,translateType(lit.typ),None)
//                    for ((l,i) <- lit.elements.zipWithIndex) {
//                      sequence += P.Assign(P.IndexAccessor(translateExpr(id),P.IntLiteral(i)) , translateExpr(l)(renamings))
//                    }
                  }
                  //sequence += P.Assign(translateExpr(i),translateExpr(newEls))
                  P.Sequence(sequence.toList)
                }
                else P.Assign(translateExpr(id),translateExpr(newEls))
              }
              val elsPart = P.GuardStmt(P.Else, List(newElsStmt))
              
              P.If(List(P.OptionStmt(List(ifPart)),P.OptionStmt(List(elsPart))))
            }
            case ListLiteral(lst) => {
              val (_,info) = ListLiteralReplacer.findAndReplace(e)
              val sequence = new ListBuffer[P.Stmt]
              for ((s,lit) <- info) {
                sequence ++= handleCollectionLiteralDecl(lit.elements, s, translateExpr(id), lit.typ, renamings)
              }
              P.Sequence(sequence.toList)
            }
            case MapLiteral(_,lst) => {
              val (_,info) = ListLiteralReplacer.findAndReplace(e)
              val sequence = new ListBuffer[P.Stmt]
              for ((s,lit) <- info) {
                sequence ++= handleCollectionLiteralDecl(lit.elements, s, translateExpr(id), lit.typ, renamings)
              }
              P.Sequence(sequence.toList)
            }
            case x => throw new RuntimeException("Cannot assign directly to array in Promela: " + ASTPrinter.get.printExpr(x))
          }
          
        }
        else {
          
          P.Assign(translateExpr(id),translateExpr(e))
        }
      }
      case MapAssign(i,e) => {
        val uninterpreted = i match {
          case IndexAccessor(Id(v),_) => renamings.isUninterpreted(v)
          case _ => false
        }
        if (uninterpreted) P.Skip else P.Assign(translateExpr(i),translateExpr(e))
      }
      case IfElse(cond,thn,elifs,els) => {
        val grds =
          (List(P.GuardStmt(P.ExprStmt(translateExpr(cond)),translateStmts(thn))):::
          (elifs map { elif => P.GuardStmt(P.ExprStmt(translateExpr(elif.cond)),translateStmts(elif.stmt)) }) :::
          List(P.GuardStmt(P.Else, if (!els.isEmpty) translateStmts(els) else List(P.Skip) )))
        P.If( grds map { g => P.OptionStmt(List(g)) } )
      }
      case _ => throw new RuntimeException("Unsupported statement in Promela backend: " + stmt)
    }
  }
  
  object ListLiteralReplacer extends ASTReplacingVisitor[ListBuffer[(String,EnumLiteral)]] {
    
    var count = 0
    
    def findAndReplace(expr: Expr): (Expr,List[(String,EnumLiteral)]) = {
      val buffer = new ListBuffer[(String,EnumLiteral)]
      count = 0
      val e = visitExpr(expr)(buffer)
      (e, buffer.toList)
    }
    
    override def visitExpr(expr: Expr)(implicit map: ListBuffer[(String,EnumLiteral)]) = {
      expr match {
        case ll: ListLiteral => {
          val name = "__replaced_lstlit__"+count
          count = count+1
          map += (name -> ll)
          Id(name).withType(ll.typ)
        }
        case ml: MapLiteral => {
          val name = "__replaced_lstlit__"+count
          count = count+1
          map += (name -> ml)
          Id(name).withType(ml.typ)
        }
        case _ => super.visitExpr(expr)
      }
    }
  }
  
  def translateExpr(e: Expr)(implicit renamings: RenamingContext): P.Expr = {
    e match {
      case And(l,r) => P.BinaryExpr(translateExpr(l),"&&",translateExpr(r))
      case Or(l,r) => P.BinaryExpr(translateExpr(l),"||",translateExpr(r))
      case Not(e) => P.UnaryExpr("!",translateExpr(e))
      case Plus(l,r) => P.BinaryExpr(translateExpr(l),"+",translateExpr(r))
      case Minus(l,r) => P.BinaryExpr(translateExpr(l),"-",translateExpr(r))
      case Times(l,r) => P.BinaryExpr(translateExpr(l),"*",translateExpr(r))
      case Div(l,r) => P.BinaryExpr(translateExpr(l),"/",translateExpr(r))
      case UnMinus(e) => P.UnaryExpr("-",translateExpr(e))
      case Eq(l,r) => P.BinaryExpr(translateExpr(l),"==",translateExpr(r))
      case NotEq(l,r) => P.BinaryExpr(translateExpr(l),"!=",translateExpr(r))
      case Greater(l,r) => P.BinaryExpr(translateExpr(l),">",translateExpr(r))
      case Less(l,r) => P.BinaryExpr(translateExpr(l),"<",translateExpr(r))
      case AtLeast(l,r) => P.BinaryExpr(translateExpr(l),">=",translateExpr(r))
      case AtMost(l,r) => P.BinaryExpr(translateExpr(l),"<=",translateExpr(r))
      case BwAnd(l,r) => P.BinaryExpr(translateExpr(l),"&",translateExpr(r))
      case BwOr(l,r) => P.BinaryExpr(translateExpr(l),"|",translateExpr(r))
      case BwXor(l,r) => P.BinaryExpr(translateExpr(l),"^",translateExpr(r))
      case LShift(l,r) => P.BinaryExpr(translateExpr(l),"<<",translateExpr(r))
      case RShift(l,r) => P.BinaryExpr(translateExpr(l),">>",translateExpr(r))
      case IfThenElse(c,thn,els) => P.ConditionalExpr(translateExpr(c),translateExpr(thn),translateExpr(els))
      case ia@IndexAccessor(id,idx) => {
        id match {
          case Id(name) => {
            if (renamings.isUninterpreted(name)) {
              getDefaultValue(ia.typ)
            }
            else {
              P.IndexAccessor(translateExpr(id),translateExpr(idx))
            }
          }
          case _ => P.IndexAccessor(translateExpr(id),translateExpr(idx))
        }
        
      }
      case FunctionApp("int2bv",List(num,size)) => translateExpr(num)
      case FunctionApp("int",List(num,size)) => translateExpr(num)
      case FunctionApp("bvresize",List(num,size)) => {
        val arg = translateExpr(num)
        val inSize = num.typ.asInstanceOf[BvType].size
        val outSize = size.asInstanceOf[IntLiteral].value
        if (outSize < 32) 
          P.BinaryExpr(arg,"&",P.VarExp("MASK"+outSize)) 
        else 
          arg
      }
      case FunctionApp("abs",List(arg)) => {
        val pArg = translateExpr(arg)
        P.ConditionalExpr(
          P.BinaryExpr(pArg,"<",P.IntLiteral(0)),
          P.UnaryExpr("-",pArg),
          pArg)
      }
      case fa@FunctionApp(name,_) => {
        val replaced = funCallReplacer.replaceFunctionCalls(fa)
        replaced match {
          case FunctionApp(newName,_) =>
            if (name == newName) throw new RuntimeException("Unhandled function " + name)
          case _ =>
        }
        translateExpr(replaced)
      }
      case ll@ListLiteral(lst) => throw new RuntimeException("Encountered list literal in Promela translation at " + ll.pos + ": " + ll)
      case cmpr: Comprehension => throw new RuntimeException("Encountered comprehension in Promela translation at " + cmpr.pos + ": " + cmpr)
      case Id(i) => {
        if (renamings.isUninterpreted(i)) {
          println("mamma")
        }
        P.VarExp(renamings.get(i).getOrElse(renamings.R(i)))
      }
      case HexLiteral(h) => {
        val bigInt = Integer.parseInt(h, 16)
        P.IntLiteral(bigInt)
      }
      case IntLiteral(i) => P.IntLiteral(i)
      case BoolLiteral(b) => P.BoolLiteral(b)
    }
  }
  
  def translateType(tp: Type): P.Type = {
    tp match {
      case IntType => P.NamedType("int")
      case BvType(_,_) => P.NamedType("int")
      case StateType(_,_) => P.NamedType("int")
      case BoolType => P.NamedType("bool")
      case MapType(_,r,s) => P.ArrayType(translateType(r),s)
      //case ListType(c,s) => P.ArrayType(translateType(c),s)
      case x => throw new RuntimeException("Unsupported type in Promela backend: " + tp.id)
    }
  }
  
  def getDefaultValue(tp: Type) = {
    tp match {
      case IntType(_) => P.IntLiteral(0)
      case BvType(_,_) => P.IntLiteral(0)
      case BoolType => P.BoolLiteral(false)
      case _ => throw new RuntimeException("No default value for type " + tp.id)
    }
  }
  
  
}
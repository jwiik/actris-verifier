package fi.abo.it.actortool.promela

import fi.abo.it.actortool._
import scala.collection.mutable.ListBuffer
import fi.abo.it.actortool.ActorTool.CommandLineParameters
import fi.abo.it.actortool.util.FunctionCallReplacer
import fi.abo.it.actortool.util.ActionPeekAnalyzer
import fi.abo.it.actortool.util.ActionPeekAnalyzer
import fi.abo.it.actortool.util.PriorityMapBuilder
import fi.abo.it.actortool.util.ASTPrinter

case class Translation[+T<:DFActor](
    val entity: T, 
    val promelaPrograms: Map[ContractAction,List[Promela.Decl]],
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

class PromelaTranslator(params: CommandLineParameters) {

  val P = Promela
  val inputGenerator = new InputGenerator
  val funCallReplacer = new FunctionCallReplacer
  
  val renamings = new RootRenamingContext
  
  trait RenamingContext {
    val charMapping = Map("$" -> "__", "#" -> "__")
    def R(s: String): String
    def add(from: String, to: String): String
    def get(name: String): Option[String]
    def has(name: String): Boolean
    def getSubContext: RenamingContext
    protected def rename(s: String) = charMapping.foldLeft(s)((a, b) => a.replaceAllLiterally(b._1, b._2))
  }
  
  class ChildRenamingContext(parent: RenamingContext) extends RenamingContext {
    private val map = collection.mutable.Map[String,String]()
    def has(name: String) = map.contains(name)
    def get(name: String) = {
      if (has(name)) map.get(name)
      else parent.get(name)
    }
    def add(from: String, to: String) = {
      if (has(from) || parent.has(from)) throw new IllegalArgumentException("Renaming already defined for " + from)
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
    override def toString = map.toString
  }
  
  def invoke(entity: DFActor, mergedActors: Map[String,BasicActor], alreadyTranslated: Map[String,P.ProcType], constants: List[Declaration]): Translation[DFActor] = {
    assert(!entity.contractActions.isEmpty)
    var procs: Map[String,P.ProcType] = Map.empty
    
    entity match {
      case nw: Network => {
        val entities = nw.entities.get.entities
        for (e <- entities) {
          if (alreadyTranslated.contains(e.actor.id)) {
            procs += (e.actor.id -> alreadyTranslated(e.actor.id))
          }
          else if (mergedActors.contains(e.actor.id)) {
            val mergedActor = mergedActors(e.actor.id)
            val proc = translateActor(mergedActor)
            procs += (e.actor.id -> proc)
          }
          else {
            assert(false)
          }
        }
        translateNetwork(nw, constants, procs, mergedActors)
      }
      case ba: BasicActor => {
        if (alreadyTranslated.contains(ba.id)) {
          procs += (ba.id -> alreadyTranslated(ba.id))
        }
        else {
          procs += (ba.id -> translateActor(ba))
        }
        translateBasicActor(ba, constants, procs, mergedActors)
      }
    }
    
//    entity match {
//      case nw: Network =>
//    }
    
//    val decls = programCtx.program
//    val topNwName = params.Promela.get
//    var translation: List[Translation] = Nil
//    var constants: List[Declaration] = Nil
//    var procs: Map[String,P.ProcType] = Map.empty
//    
//    for (d <- decls.collect{ case du: DataUnit => du }) {
//      constants = constants ++ d.constants
//    }
//    
//    for (a <- decls.collect{ case ba: BasicActor => ba }) {
//      procs = procs + (a.id -> translateActor(a))
//    }
//    
//    for (n <- decls.collect{ case n: Network => n }) {
//      translation = translateTopNetwork(n,constants,procs) :: translation
//    }
//    
//    translation 
  }
  
  def translateBasicActor(
      actor: BasicActor, 
      constants: List[Declaration], 
      procs: Map[String,P.ProcType], 
      mergedActors: Map[String,BasicActor]): Translation[BasicActor] = {
    
    val idMap = new IdMap
    val decls = collection.mutable.Map[String,P.VarDecl]()
    val instances = collection.mutable.Map[String,PromelaInstance]()
    
    
    val instance = Instance("this",actor.id,Nil,Nil)
    instance.actor = actor
    val connections = 
      actor.inports.map { p => val c = Connection(Some("ch__"+p.id),PortRef(None,p.id),PortRef(Some("this"),p.id),Nil); c.typ = ChanType(p.portType); c } :::
      actor.outports.map { p => val c = Connection(Some("ch__"+p.id),PortRef(Some("this"),p.id),PortRef(None,p.id),Nil); c.typ = ChanType(p.portType); c }
    val channelMapping = Util.buildConnectionMap(connections)
    
    for (c <- constants) {
      decls(c.id) = P.VarDecl(renamings.R(c.id), translateType(c.typ), Some(translateExpr(c.value.get)(renamings)))
    }
    
    for (c <- connections) {
      decls += 
        c.id -> P.VarDecl(renamings.R(c.id), P.NamedType("chan"),Some(P.ChInit(100,translateType(c.typ.asInstanceOf[ChanType].contentType))))
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
        val chanParams = chanNames map { p => P.VarExp(renamings.R(p.id)) }
        val givenParams = instance.arguments map { x => translateExpr(x)(renamings) }
        P.Run(actor.id, P.IntLiteral(instance.mapId)::chanParams:::givenParams)
      }
    }
    
    val inits = generateInitialisations(actor, runs, (channelMapping.map { case (pr,c) => (pr,c.id) }).toMap , constants)
    
    val contractTranslations = 
      for ((contract,init) <- inits) yield {
        val program: List[P.Decl] = decls.values.toList ::: procs.values.toList ::: List(init)
        (contract,program)
      }
    Translation(actor,contractTranslations,idMap,mergedActors)
  }
  
  
  def translateNetwork(nw: Network, constants: List[Declaration], procs: Map[String,P.ProcType], mergedActors: Map[String,BasicActor]): Translation[Network] = {
    val idMap = new IdMap
    val decls = collection.mutable.Map[String,P.VarDecl]()
    val instances = collection.mutable.Map[String,PromelaInstance]()
    
    val channelMapping = Util.buildConnectionMap(nw.structure.get.connections)
    
    for (c <- constants) {
      decls(c.id) = P.VarDecl(renamings.R(c.id), translateType(c.typ), Some(translateExpr(c.value.get)(renamings)))
    }
    
    for (c <- nw.structure.get.connections) {
      decls += 
        c.id -> P.VarDecl(renamings.R(c.id), P.NamedType("chan"),Some(P.ChInit(100,translateType(c.typ.asInstanceOf[ChanType].contentType))))
    }
    
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
      for ((id,instance) <- instances.toList) yield {
        val actor = instance.actor
        val chanNames = actor.inports:::actor.outports map { p => instance.connections(p.id) }
        val chanParams = chanNames map { p => P.VarExp(renamings.R(p.id)) }
        val givenParams = instance.arguments map { x => translateExpr(x)(renamings) }
        P.Run(actor.id, P.IntLiteral(instance.mapId)::chanParams:::givenParams)
      }
    }
    
    val inits = generateInitialisations(nw, runs, (channelMapping.map { case (pr,c) => (pr,c.id) }).toMap , constants)
    
    val contractTranslations = 
      for ((contract,init) <- inits) yield {
        val program: List[P.Decl] = decls.values.toList ::: procs.values.toList ::: List(init)
        (contract,program)
      }
    
    Translation(nw,contractTranslations,idMap,mergedActors)
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
          initBlock += P.Send(renamings.R(chan), translateExpr(inputToken)(renamings))
        }
      }
      
      initBlock += P.Atomic(runs)
      (contract,P.Init(initBlock.toList))
    }).toMap
  }
  
  
  
  case class PromelaInstance(id: String, arguments: List[Expr], actor: BasicActor, mapId: Int, connections: Map[String,Connection])
  
//  def translateSubNetwork(nw: Network, prefix: String, ioConnections: Map[String,Connection], idMap: IdMap): (List[PromelaInstance],List[(String,P.VarDecl)]) = {
//    val decls = new ListBuffer[(String,P.VarDecl)]
//    val instances = new ListBuffer[PromelaInstance]
//    
//    val channelMapping = Util.buildConnectionMap(nw.structure.get.connections)
//    
//    for (c <- nw.structure.get.connections) {
//      (c.from,c.to) match {
//        case (PortRef(Some(x),_),PortRef(Some(y),_)) => 
//          val id = prefix+"__"+renamings.R(c.id)
//          decls += id -> P.VarDecl(id, P.NamedType("chan"), Some(P.ChInit(100,translateType(c.typ.asInstanceOf[ChanType].contentType))))
//        case (_,_) =>
//      }
//    }
//    for (e <- nw.entities.get.entities) {
//      val connections = {
//        for (p <- e.actor.inports:::e.actor.outports) yield {
//          val conn = channelMapping(PortRef(Some(e.id),p.id))
//          val mappedConn =
//            if (conn.isInput) {
//              ioConnections(conn.from.name)
//              //assert(false,parentConn)
//            }
//            else if (conn.isOutput) {
//              ioConnections(conn.to.name)
//              //assert(false,parentConn)
//            }
//            else {
//              Connection(Some(prefix+"__"+conn.id),conn.from,conn.to,conn.annotations)
//            }
//          (p.id,mappedConn)
//        }
//      }.toMap
//      instances += PromelaInstance(prefix+"__"+e.id,e,idMap.generateId(e),connections)
//    }
//    for (e <- nw.entities.get.entities) {
//      e.actor match {
//        case actor: BasicActor => 
//        case subnw: Network => {
//          val ioConns = (for (p <- e.actor.inports:::e.actor.outports) yield (p.id,channelMapping(PortRef(Some(e.id),p.id)))).toMap
//          val (instance,subDecls) = translateSubNetwork(subnw,prefix+"__"+e.id,ioConns,idMap)
//          instances ++= instance
//          decls ++= subDecls
//        }
//      }
//    }
//    (instances.toList,decls.toList)
//  }
  
  def translateActor(a: BasicActor): P.ProcType = {
    
    val actorRenamings = renamings.getSubContext
    
    val params = new ListBuffer[P.ParamDecl]
    val decls = new ListBuffer[P.VarDecl]
    val actions = new ListBuffer[P.Stmt]
    
    funCallReplacer.setFunctionDeclarations(a.functionDecls)
    
    params += P.ParamDecl("__uid",P.NamedType("int"))
    for (ip <- a.inports) params += P.ParamDecl(ip.id,P.NamedType("chan"))
    for (op <- a.outports) params += P.ParamDecl(op.id,P.NamedType("chan"))
    for (p <- a.parameters) params += P.ParamDecl(p.id, translateType(p.typ))
    for (v <- a.variables) {
      val value = if (v.value.isDefined) Some(translateExpr(v.value.get)(actorRenamings)) else None  
      decls += P.VarDecl(actorRenamings.R(v.id),translateType(v.typ), value)
    }
    
    val initBody: List[P.Stmt] =
      a.actorActions.find { _.init } match {
        case Some(act) => {
          val initStmt = new ListBuffer[P.Stmt]
          initStmt ++= translateStmts(act.body)(actorRenamings)
          for (p <- act.outputPattern) {
            for (e <- p.exps) {
              initStmt += P.Send(actorRenamings.R(p.portId), translateExpr(e)(actorRenamings))
            }
          }
          initStmt.toList
        }
        case None => Nil
      }
    
    val peekAnalyzer = new ActionPeekAnalyzer
    val priorityMap = PriorityMapBuilder.buildPriorityMap(a, false)
    
    // Get the most tokens consumed on each port by any action
    val maxRates = 
      a.inports.map {
        ip => (ip -> (a.actorActions.filter(!_.init).map { t => t.inportRate(ip.id) }).foldLeft(0)((a,b) => if (a < b) b else a))
      }
    
    // Create enough input variable declarations for each inport
    for ((ip,rate) <- maxRates) {
      for (i <- 0 to rate-1)
        decls += P.VarDecl(ip.id+"__"+i.toString,translateType(ip.portType),None)
    }
    
    
    val peeks = peekAnalyzer.analyze(a.actorActions.filter { !_.init })
    
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
      
      val peekings = peekAnalyzer.analyze(act)
      val peekGuards: Iterable[P.Expr] = 
        peekings.flatMap {
          case (p,r) => if (r > 0) List(P.VarExp(p+"__peek")) else Nil
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
    
    for (act <- a.actorActions.filter { !_.init }) {
      
      //println(act.fullName + ": " +(priorityMap(act).map { a => a.fullName }).mkString(",") )
      
      val allFiringRules = firingRules(act) :: priorityMap(act).map { a => P.UnaryExpr("!",firingRules(a)) }
      val firingRule = allFiringRules.reduceLeft((a,b) => P.BinaryExpr(a,"&&",b))
      
      val actionRenamings = actionRenamingMap(act)
      
      
      //val peeking = peekAnalyzer.analyze(act)
      
      val peekings = peekAnalyzer.analyze(act)
//      val peekGuards: Iterable[P.Expr] = 
//        peekings.flatMap {
//          case (p,r) => if (r > 0) List(P.VarExp(p+"__peek")) else Nil
//        }
      val peekResets = 
        peekings.flatMap {
          case (p,r) => if (r > 0) List(P.Assign(P.VarExp(p+"__peek"),P.BoolLiteral(false))) else Nil
        }
      
      val stmt = new ListBuffer[P.Stmt]
      
      val actionParams = 
        act.variables map { v => 
          P.VarDecl(renamings.R(v.id),translateType(v.typ),if (v.value.isDefined) Some(translateExpr(v.value.get)(actionRenamings)) else None) 
        }
        
      stmt += P.PrintStmtValue("<action id='%d' actor='"+renamings.R(a.fullName)+ "' action='" + renamings.R(act.fullName) + "' />\\n",List(P.VarExp("__uid")))
      
      for (p <- act.inputPattern) {
        if (p.repeat > 1) {
          if (p.vars.size > 1) throw new RuntimeException("Unsupported pattern with repeat")
        }
        else {
          for (v <- p.vars) {
            stmt += P.Receive(renamings.R(p.portId), translateExpr(v)(actionRenamings))
          }
        }
      }
      
      stmt ++= translateStmts(act.body)(actionRenamings)
      
      for (p <- act.outputPattern) {
        for (e <- p.exps) {
          stmt += P.Send(renamings.R(p.portId), translateExpr(e)(actionRenamings))
        }
      }
      stmt ++= peekResets
      actions += P.Atomic(actionParams :::  List(P.GuardStmt(P.ExprStmt(firingRule), stmt.toList)))
    }
    

    
    val opts = actions.toList map { a => P.OptionStmt(List(a)) }
    P.ProcType(a.id, params.toList,decls.toList,initBody ::: List(P.Iteration(opts)))
  }
  
  def translateStmts(stmt: List[Stmt])(implicit renamings: RenamingContext): List[P.Stmt] = {
    stmt map { s => translateStmt(s) }
  }
  
  def translateStmt(stmt: Stmt)(implicit renamings: RenamingContext): P.Stmt = {
    stmt match {
      case Assign(i,e) => P.Assign(translateExpr(i),translateExpr(e))
      case MapAssign(i,e) => P.Assign(translateExpr(i),translateExpr(e))
      case IfElse(cond,thn,elifs,els) => {
        val grds =
          (List(P.GuardStmt(P.ExprStmt(translateExpr(cond)),translateStmts(thn))):::
          (elifs map { elif => P.GuardStmt(P.ExprStmt(translateExpr(elif.cond)),translateStmts(elif.stmt)) }) :::
          List(P.GuardStmt(P.Else,translateStmts(els))))
        P.If( grds map { g => P.OptionStmt(List(g)) } )
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
      case IndexAccessor(id,idx) => P.IndexAccessor(translateExpr(id),translateExpr(idx))
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
      case Id(i) => 
        P.VarExp(renamings.get(i).getOrElse(renamings.R(i)))
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
    }
  }
  
  
  
}
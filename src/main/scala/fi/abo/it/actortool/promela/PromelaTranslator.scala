package fi.abo.it.actortool.promela

import fi.abo.it.actortool._
import scala.collection.mutable.ListBuffer
import fi.abo.it.actortool.ActorTool.CommandLineParameters
import fi.abo.it.actortool.util.FunctionCallReplacer
import fi.abo.it.actortool.util.ActionPeekAnalyzer
import fi.abo.it.actortool.util.ActionPeekAnalyzer
import fi.abo.it.actortool.util.PriorityMapBuilder

class PromelaTranslator(params: CommandLineParameters) extends Translator[Map[ContractAction,List[Promela.Decl]]] {

  val P = Promela
  val inputGenerator = new InputGenerator
  val funCallReplacer = new FunctionCallReplacer
  
  
  val idMap = new IdMap
  val renamings = new Renamings
  
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
  
  class Renamings {
    
    private val charMapping = Map("$" -> "__", "#" -> "__") 
    private val map = new BiMap[String,String]
    
    def renaming(s: String): String = {
      val newName = rename(s)
      map.add(s, rename(s))
      return newName
    }
    
    def R(s: String) = renaming(s)
        
    private def rename(s: String) = charMapping.foldLeft(s)((a, b) => a.replaceAllLiterally(b._1, b._2))
    
  }
  
  def translateProgram(decls: List[TopDecl], typeCtx: Resolver.Context) = {
    
    val topNwName = params.Promela.get
    var program: Option[Map[ContractAction,List[P.Decl]]] = None
    var constants: List[Declaration] = Nil
    var procs: Map[String,P.ProcType] = Map.empty
    
    for (d <- decls.collect{ case du: DataUnit => du }) {
      constants = constants ++ d.constants
    }
    
    for (a <- decls.collect{ case ba: BasicActor => ba }) {
      procs = procs + (a.id -> translateActor(a))
    }
    
    for (n <- decls.collect{ case n: Network => n }) {
      if (n.id == topNwName) { 
        program = Some(translateTopNetwork(n,constants,procs))
      }
      else {
        // ..
      }
    }
    
    
    program match {
      case Some(p) => p
      case None => throw new RuntimeException("Top-level network " + topNwName + " not found")
    }
  }
  
  def translateTopNetwork(nw: Network, constants: List[Declaration], procs: Map[String,P.ProcType]): Map[ContractAction,List[P.Decl]] = {
    val decls = collection.mutable.Map[String,P.VarDecl]()
    val instances = collection.mutable.Map[String,PromelaInstance]()
    
    val channelMapping = Util.buildConnectionMap(nw.structure.get.connections)
    
    for (c <- constants) {
      decls(c.id) = P.VarDecl(renamings.R(c.id), translateType(c.typ), Some(translateExpr(c.value.get)))
    }
    
    for (c <- nw.structure.get.connections) {
      decls += 
        c.id -> P.VarDecl(renamings.R(c.id), P.NamedType("chan"),Some(P.ChInit(100,translateType(c.typ.asInstanceOf[ChanType].contentType))))
    }
    
    for (e <- nw.entities.get.entities) {
      e.actor match {
        case actor: BasicActor => 
          val connections = {
            for (p <- e.actor.inports:::e.actor.outports) yield {
              val conn = channelMapping(PortRef(Some(e.id),p.id))
              (p.id,conn)
            }
          }.toMap
          instances += (e.id -> PromelaInstance(e.id,e,idMap.generateId(e),connections))
        case subnw: Network => {
          
          // Build port to channel map
          val ioConns = (for (p <- e.actor.inports:::e.actor.outports) yield (p.id,channelMapping(PortRef(Some(e.id),p.id)))).toMap
          
          val (subInstances,subDecls) = translateSubNetwork(subnw,e.id,ioConns)
          for (si <- subInstances) {
            instances += (si.id -> si)
          }
          for ((id,decl) <- subDecls) {
            decls += (id -> decl)
          }
        }
      }
    }
    
    val runs: List[P.Run] = {
      for ((id,instance) <- instances.toList) yield {
        val actor = instance.instance.actor
        val chanNames = actor.inports:::actor.outports map { p => instance.connections(p.id) }
        val chanParams = chanNames map { p => P.VarExp(renamings.R(p.id)) }
        val givenParams = instance.instance.arguments map translateExpr 
        P.Run(actor.id, P.IntLiteral(instance.mapId)::chanParams:::givenParams)
      }
    }
    
    (for (contract <- nw.contractActions) yield {
      // Generate an input satisfying the contract
      val input = inputGenerator.generateInput(contract,constants)
      
      val initBlock = new ListBuffer[P.Stmt]
      for (pat <- contract.inputPattern) {
        // Get the correct channel id
        val chan = channelMapping(PortRef(None,pat.portId))
        for (i <- 0 to pat.rate-1) {
          val inputToken = input((pat.portId,i))
          initBlock += P.Send(renamings.R(chan.id), translateExpr(inputToken))
        }
      }
      
      initBlock += P.Atomic(runs)
      
      val init = P.Init(initBlock.toList)
      
      val program: List[P.Decl] = decls.values.toList ::: procs.values.toList ::: List(init)
      (contract,program)
    }).toMap
  }
  
  case class PromelaInstance(id: String, instance: Instance, mapId: Int, connections: Map[String,Connection])
  
  def translateSubNetwork(nw: Network, prefix: String, ioConnections: Map[String,Connection]): (List[PromelaInstance],List[(String,P.VarDecl)]) = {
    val decls = new ListBuffer[(String,P.VarDecl)]
    val instances = new ListBuffer[PromelaInstance]
    
    val channelMapping = Util.buildConnectionMap(nw.structure.get.connections)
    
    for (c <- nw.structure.get.connections) {
      (c.from,c.to) match {
        case (PortRef(Some(x),_),PortRef(Some(y),_)) => 
          val id = prefix+"__"+renamings.R(c.id)
          decls += id -> P.VarDecl(id, P.NamedType("chan"), Some(P.ChInit(100,translateType(c.typ.asInstanceOf[ChanType].contentType))))
        case (_,_) =>
      }
    }
    for (e <- nw.entities.get.entities) {
      val connections = {
        for (p <- e.actor.inports:::e.actor.outports) yield {
          val conn = channelMapping(PortRef(Some(e.id),p.id))
          val mappedConn =
            if (conn.isInput) {
              ioConnections(conn.from.name)
              //assert(false,parentConn)
            }
            else if (conn.isOutput) {
              ioConnections(conn.to.name)
              //assert(false,parentConn)
            }
            else {
              Connection(Some(prefix+"__"+conn.id),conn.from,conn.to,conn.annotations)
            }
          (p.id,mappedConn)
        }
      }.toMap
      instances += PromelaInstance(prefix+"__"+e.id,e,idMap.generateId(e),connections)
    }
    for (e <- nw.entities.get.entities) {
      e.actor match {
        case actor: BasicActor => 
        case subnw: Network => {
          val ioConns = (for (p <- e.actor.inports:::e.actor.outports) yield (p.id,channelMapping(PortRef(Some(e.id),p.id)))).toMap
          val (instance,subDecls) = translateSubNetwork(subnw,prefix+"__"+e.id,ioConns)
          instances ++= instance
          decls ++= subDecls
        }
      }
    }
    (instances.toList,decls.toList)
  }
  
  def translateActor(a: BasicActor): P.ProcType = {
    
//    val actionPatternOrderer = new ActionPatternOrderAnalyzer(a.inports,a.actorActions.filter { !_.init })
//    val actionOrder = actionPatternOrderer.buildOrder
//    println(actionOrder.toList map { a => a.fullName })
    
    val params = new ListBuffer[P.ParamDecl]
    val decls = new ListBuffer[P.VarDecl]
    val actions = new ListBuffer[P.Stmt]
    
    funCallReplacer.setFunctionDeclarations(a.functionDecls)
    
    params += P.ParamDecl("__uid",P.NamedType("int"))
    for (ip <- a.inports) params += P.ParamDecl(ip.id,P.NamedType("chan"))
    for (op <- a.outports) params += P.ParamDecl(op.id,P.NamedType("chan"))
    for (p <- a.parameters) params += P.ParamDecl(p.id, translateType(p.typ))
    for (v <- a.variables) decls += P.VarDecl(renamings.R(v.id),translateType(v.typ),None)
    
    val initBody: List[P.Stmt] =
      a.actorActions.find { _.init } match {
        case Some(act) => {
          val initStmt = new ListBuffer[P.Stmt]
          initStmt ++= translateStmts(act.body)
          for (p <- act.outputPattern) {
            for (e <- p.exps) {
              initStmt += P.Send(renamings.R(p.portId), translateExpr(e))
            }
          }
          initStmt.toList
        }
        case None => Nil
      }
    
    val peekAnalyzer = new ActionPeekAnalyzer
    val priorityMap = PriorityMapBuilder.buildPriorityMap(a, false)
    
    for (act <- a.actorActions.filter { !_.init }) {
      println(act.fullName + ": " +(priorityMap(act).map { a => a.fullName }).mkString(",") )
          
      val peeking = peekAnalyzer.analyze(act)
      
      val stmt = new ListBuffer[P.Stmt]
      
      val inputRatePreds = 
        act.inputPattern.map { 
          ip => {
            P.BinaryExpr(P.IntLiteral(ip.rate),"<=",P.FunCall("len",List(P.VarExp(ip.portId)))) 
          }
        }
      val inputPat = inputRatePreds.foldLeft(P.BoolLiteral(true): P.Expr)((a,b) => P.BinaryExpr(a,"&&",b))
      
      val firingRule = 
        if (act.guards.isEmpty) inputPat
        else P.BinaryExpr(inputPat,"&&",translateExpr(act.guards.reduceLeft((a,b) => And(a,b))) )
      
      val actionPatParams = 
        act.inputPattern flatMap { ip =>
          ip.vars map { v => P.VarDecl(renamings.R(v.id),translateType(v.typ),None) }
        }
      
      val actionParams = 
        act.variables map { v => 
          P.VarDecl(renamings.R(v.id),translateType(v.typ),if (v.value.isDefined) Some(translateExpr(v.value.get)) else None) 
        }
        
      stmt += P.PrintStmtValue("<action id='%d' actor='"+renamings.R(a.fullName)+ "' action='" + renamings.R(act.fullName) + "'>\\n",List(P.VarExp("__uid")))
      
      for (p <- act.inputPattern) {
        if (p.repeat > 1) {
          if (p.vars.size > 1) throw new RuntimeException("Unsupported pattern with repeat")
        }
        else {
          for (v <- p.vars) {
            stmt += P.Receive(renamings.R(p.portId), translateExpr(v))
          }
        }
      }
      
      stmt ++= translateStmts(act.body)
      
      for (p <- act.outputPattern) {
        for (e <- p.exps) {
          stmt += P.Send(renamings.R(p.portId), translateExpr(e))
        }
      }
      
      actions += P.Atomic(actionPatParams ::: actionParams :::  List(P.GuardStmt(P.ExprStmt(firingRule), stmt.toList)))
    }
    

    
    val opts = actions.toList map { a => P.OptionStmt(List(a)) }
    P.ProcType(a.id, params.toList,decls.toList,initBody ::: List(P.Iteration(opts)))
  }
  
  def translateStmts(stmt: List[Stmt]): List[P.Stmt] = {
    stmt map { s => translateStmt(s) }
  }
  
  def translateStmt(stmt: Stmt): P.Stmt = {
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
  
  def translateExpr(e: Expr): P.Expr = {
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
      case FunctionApp("bvresize",List(num,size)) => translateExpr(num)
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
      case Id(i) => P.VarExp(renamings.R(i))
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
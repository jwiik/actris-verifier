package fi.abo.it.actortool.merging

import fi.abo.it.actortool._
import fi.abo.it.actortool.schedule._
import fi.abo.it.actortool.util.ASTPrinter
import fi.abo.it.actortool.util.ConnectionMap
import collection.mutable.ListBuffer
import scala.util.parsing.input.Position

object Constants {
  val Sep = "__"
}

trait MergingOutcome
case class Success(actor: BasicActor) extends MergingOutcome
case class Failure(actor: BasicActor, errors: List[(Position,String)]) extends MergingOutcome

/**
 * This class implements merging of networks and actors into composite actors. The composite
 * actor will have a (concrete) action for each contract.
 */
class ActorMerger(constants: List[Declaration]) extends GeneralBackend[ScheduleContext,MergingOutcome] {
  
  val Sep = Constants.Sep
  
  def invoke(scheduleCtx: ScheduleContext): MergingOutcome = {
    val entity = scheduleCtx.entity
    val schedules = scheduleCtx.schedules
    val members: List[Member] =
      entity match {
        case nw: Network => {
          val members = new ListBuffer[Member]
          val tokens = TokensDefFinder.find(nw.contractInvariants.map(_.expr))
          val tokenAmounts = tokens.collect { case (ch,IntLiteral(i)) => (ch,i) }
          val connections = nw.structure.get.connections
          
          var actorVariablesMap: Map[Instance,Map[String,Expr]] = Map.empty
          
          
          for ((ch,amount) <- tokenAmounts) {
            if (amount > 0) {
              val conn = connections.find { c => c.id == ch }.get
              members += Declaration(Sep+"del"+Sep+ch,MapType(IntType,conn.typ.asInstanceOf[ChanType].contentType,amount),false,None)
            }
          }
          
          for (e <- scheduleCtx.entities) yield {
            var actorVariables: Map[String,Expr] = Map.empty
            val actor = scheduleCtx.mergedActors.getOrElse(e.actorId,e.actor)
            for (v <- actor.variables)  {
              val name = e.id+Sep+v.id
              members += {
                val newVal = v.value.map { v => replaceStr(v, actorVariables) }
                Declaration(name,v.typ,v.constant, newVal)
              }
              
              actorVariables += v.id -> Id(name).withType(v.typ)
            }
            for ((param,arg) <- actor.parameters.zip(e.arguments)) {
              actorVariables += param.id -> arg
            }
            
            for (f <- actor.functionDecls) {
              val name = e.id+Sep+f.name
              val newVars = f.variables.map {
                d => Declaration(d.id,d.typ,d.constant,Some(replaceStr(d.value.get,actorVariables)))
              }
              members += FunctionDecl(name,f.inputs,f.output,newVars,replaceStr(f.expr, actorVariables))
              actorVariables += f.name -> Id(name)
            }
            actorVariablesMap += e -> actorVariables
          }
          
          val initSequence = scheduleCtx.entities.map { e => 
            val actor = scheduleCtx.mergedActors.getOrElse(e.actorId,e.actor); 
            (e, actor.actorActions.find(_.init).get) 
          }
          
          
          
          val schedData = for (s <- schedules) yield createActionForNetworkContract(nw, s, tokenAmounts, actorVariablesMap)
          val (actions,sizes) = schedData.unzip
          
          val maxSizes = (for (c <- connections.filter(!_.isInput)) yield {
            var maxSize = 0
            for (s <- sizes) {
              val sz = s.getOrElse(c.id, 0)
              if (sz > maxSize) maxSize = sz
            }
            (c.id, maxSize)
          }).toMap

          for (c <- connections.filter { !_.isInput }) {
            if (maxSizes(c.id) > 0) {
              members += Declaration(c.id,MapType(IntType,c.typ.asInstanceOf[ChanType].contentType,maxSizes(c.id)),false,None)
            }
          }
          
          members += createInitActionForNetwork(nw, initSequence, actorVariablesMap, tokenAmounts)
          
          members.toList:::actions
        }
        case ba: BasicActor => {
          val members = new ListBuffer[Member]
          var actorVariables: Map[String,Expr] = Map.empty
          val variables = ba.variables
          for (v <- ba.variables)  {
            assert(v.typ != null, v)
            val name = ba.id+Sep+v.id
            members += {
              val newVal = v.value.map { v => replaceStr(v, actorVariables) }
              Declaration(name,v.typ,v.constant,newVal)
            }
            
            actorVariables += v.id -> Id(name).withType(v.typ)
            
          }
          for (f <- ba.functionDecls) {
            val name = ba.id+Sep+f.name
            val newVars = f.variables.map {
              d => Declaration(d.id,d.typ,d.constant,Some(replaceStr(d.value.get,actorVariables)))
            }
            members += FunctionDecl(name,f.inputs,f.output,newVars,replaceStr(f.expr, actorVariables))
            actorVariables += f.name -> Id(name)
          }
          val initActions = {
            for (a <- ba.actorActions.find(_.init).toList) yield {
              ActorAction(
                  a.label,
                  a.init,
                  a.inputPattern,
                  a.outputPattern,
                  a.guards,
                  Nil,
                  Nil,
                  a.variables,
                  replaceStr(a.body,actorVariables))
            }
          }
          members ++= initActions
          val actions = for (s <- schedules) yield createActionForActorContract(ba, s, actorVariables)
          members.toList:::actions
        }
      }
    
    val actor = BasicActor(
        entity.id+Sep+"Merged",
        entity.parameters,
        entity.inports,
        entity.outports,
        members).withAnnotationsFrom(entity)
    println(ASTPrinter.get.print(actor))
    Resolver.resolve(List(actor),constants) match {
      case Resolver.Errors(errs) => {
        val nerrs = errs.map { case (p,s) => p -> ("[" + actor.fullName  + "] " + s) }
        Failure(actor,nerrs)
      }
      case Resolver.Success(ctx) => Success(actor)
    }
    
  }
  
  def createActionForNetworkContract(
      nw: Network, 
      schedule: ContractSchedule, 
      tokenAmounts: List[(String,Int)], 
      actorVariables: Map[Instance,Map[String,Expr]]): (ActorAction,Map[String,Int]) = {
    
    val contract = schedule.contract
    val connections = nw.structure.get.connections
    val stmt = new ListBuffer[Stmt]
    val connectionMap = ConnectionMap.build(connections,Map.empty)
    
    var usedVariableNames = Set.empty[String]
    val variables = new collection.mutable.ListBuffer[Declaration]()
    
    var consumeCount = connections.map( c => (c.id,0) ).toMap
    var produceCount = connections.map( c => (c.id,0) ).toMap
    
    val inputPatterns = {
      contract.inputPattern.map {
        pat => {
          val conn = connectionMap.getIn(pat.portId)
          val newpat = InputPattern(pat.portId,List(Id(conn)),pat.rate)
          val count = produceCount(conn)
          produceCount = produceCount + (conn ->  (count+pat.rate))
          newpat
//          InputPattern(pat.portId, ((0 to pat.rate-1).toList.map { 
//            i => {
//              val count = produceCount(conn)
//              produceCount = produceCount + (conn ->  (count+1))
//              Id(conn+Sep+count) 
//            }
//          }),1)
        }
      }
    }
    
    for ((ch,amount) <- tokenAmounts) {
      for (i <- 0 until amount) {
        //stmt += Assign(Id(ch+Sep+i),Id(Sep+"del"+Sep+ch+Sep+i))
        stmt += MapAssign(IndexAccessor(Id(ch),IntLiteral(i)), IndexAccessor(Id(Sep+"del"+Sep+ch),IntLiteral(i)) )
      }
    }
    
    for (firing <- schedule.sequence) {
      val a = firing.action
      val e = firing.instance
      val (subStmt,subVars,newConsCount,newProdCount,usedVariables) = 
        handleActionExecution(
          a, Some(e), Some(connectionMap), nw, actorVariables(e), usedVariableNames, consumeCount, produceCount)
      stmt ++= subStmt
      variables ++= subVars
      consumeCount = newConsCount
      produceCount = newProdCount
      usedVariableNames = usedVariables
    }
    
    for ((ch,amount) <- tokenAmounts) {
      for (i <- 0 until amount) {
        //stmt += Assign(Id(Sep+"del"+Sep+ch+Sep+i),Id(ch+Sep+(consumeCount(ch)-1+i)))
        stmt += MapAssign(IndexAccessor(Id(Sep+"del"+Sep+ch),IntLiteral(i)), IndexAccessor(Id(ch),IntLiteral( consumeCount(ch)-1+i )))
      }
    }
    
    val outputPatterns = {
      contract.outputPattern.map {
        pat => {
          val conn = connectionMap.getOut(pat.portId)
          
          //val conn = connectionMap.getIn(pat.portId)
//          val newpat = OutputPattern(pat.portId,List(Id(conn)),pat.rate)
//          val count = consumeCount(conn)
//          consumeCount = consumeCount + (conn ->  (count+1))
//          newpat
          
          if (pat.rate > 1) {
            val newpat = OutputPattern(pat.portId,List(Id(conn)),pat.rate)
            //variables += Declaration(conn+Sep, MapType(IntType,pat.typ,pat.rate), false, None)
            newpat
          }
          else {
            val newpat = OutputPattern(pat.portId,List(IndexAccessor(Id(conn),IntLiteral(0))),pat.rate)
            //variables += Declaration(conn+Sep, MapType(IntType,pat.typ,pat.rate), false, None)
            newpat
          }
          
          
//          OutputPattern(pat.portId, ((0 to pat.rate-1).toList.map { 
//            i => {
//              val count = consumeCount(conn)
//              consumeCount = consumeCount + (conn ->  (count+1))
//              Id(conn+Sep+count) 
//            }
//          }),1)
        }
      }
    }
//    
//    for (c <- connections.filter { !_.isInput }) {
//      if (produceCount(c.id) > 0) {
//        variables += Declaration(c.id,MapType(IntType,c.typ.asInstanceOf[ChanType].contentType,produceCount(c.id)),false,None)
//        usedVariableNames += c.id
//      }
//    }
    
    val action = ActorAction(
        contract.label,
        false,
        inputPatterns,
        outputPatterns,
        contract.guards.map { g => translateGuardToExecutableFormat(g,inputPatterns) } ,
        contract.requires,
        contract.ensures,
        variables.toList,
        stmt.toList)
    //println(ASTPrinter.printMember(action))
    action.refinedContract = Some(contract)
    (action,produceCount)
  }
  
  def createActionForActorContract(ba: BasicActor, schedule: ContractSchedule, actorVariables: Map[String,Expr]): ActorAction = {
    val contract = schedule.contract
    val stmt = new ListBuffer[Stmt]
    
    val variables = new ListBuffer[Declaration]()
    var usedVariableNames = Set.empty[String]
    
    val ports = ba.inports ::: ba.outports
    var consumeCount = ports.map( c => (c.id,0) ).toMap
    var produceCount = ports.map( c => (c.id,0) ).toMap
    
    val inputPatterns = 
      contract.inputPattern.map {
        pat => {
          val conn = pat.portId
          val newpat = InputPattern(pat.portId,List(Id(conn+Sep)),pat.rate)
          val count = produceCount(conn)
          produceCount = produceCount + (conn ->  (count+pat.rate))
          newpat
//          InputPattern(pat.portId, ((0 to pat.rate-1).toList.map { 
//            i => {
//              val count = produceCount(pat.portId)
//              produceCount = produceCount + (pat.portId ->  (count+1))
//              Id(pat.portId+Sep+count) 
//            }
//          }),1)
        }
      }
    for (firing <- schedule.sequence) {
      val a = firing.action
      val (subStmt,subVars,newConsCount,newProdCount,usedVariables) = 
        handleActionExecution(a, None, None, ba, actorVariables, usedVariableNames, consumeCount, produceCount)
      stmt ++= subStmt
      variables ++= subVars
      consumeCount = newConsCount
      produceCount = newProdCount
      usedVariableNames = usedVariables
    }
    
    val outputPatterns = {
      contract.outputPattern.map {
        pat => {
          val conn = pat.portId
          
          //val conn = connectionMap.getIn(pat.portId)
          val count = consumeCount(conn)
          consumeCount = consumeCount + (conn ->  (count+pat.rate))
          usedVariableNames += conn+Sep
          if (pat.rate > 1) {
            val newpat = OutputPattern(pat.portId,List(Id(conn+Sep)),pat.rate)
            variables += Declaration(conn+Sep, MapType(IntType,pat.typ,pat.rate), false, None)
            newpat
          }
          else {
            val newpat = OutputPattern(pat.portId,List(IndexAccessor(Id(conn+Sep),IntLiteral(0))),pat.rate)
            variables += Declaration(conn+Sep, MapType(IntType,pat.typ,pat.rate), false, None)
            newpat
          }
          
        }
      }
    }
    
    
    
    val action = ActorAction(
        contract.label,
        false,
        inputPatterns,
        outputPatterns,
        contract.guards.map { g => translateGuardToExecutableFormat(g,inputPatterns) } ,
        contract.requires,
        contract.ensures,
        variables.toList,
        stmt.toList)
    action.refinedContract = Some(contract)
    action
  }
  
  def handleActionExecution(
      a: ActorAction, 
      eOpt: Option[Instance], 
      connMapOpt: Option[ConnectionMap],
      actor: DFActor, 
      actorVariables: Map[String,Expr],
      usedVariableNames1: Set[String],
      startConsumeCount: Map[String,Int],
      startProduceCount: Map[String,Int]): (List[Stmt],List[Declaration],Map[String,Int],Map[String,Int],Set[String]) = {
    
    val stmt = new ListBuffer[Stmt]
    val variables = new ListBuffer[Declaration]
    var allUsedVariableNames = usedVariableNames1
    var consumeCount = startConsumeCount
    var produceCount = startProduceCount
    
    val actionVarDecls = a.variables.map(d => (d.id,d)).toMap
    val actionRenames = eOpt match {
      case Some(e) => getActionReplacements(e, a)
      case None => getReplacements(actor, a)
    }
    val renames = actorVariables ++ actionRenames
    
    val actionVariables = a.inputPattern.flatMap(_.vars) ::: a.variables.map(d => {val id = Id(d.id); id.typ = d.typ; id})
    val actionVariableInits = new ListBuffer[Stmt]()
    
    for (from <- actionVariables) {
      val to = actionRenames(from.id)
      assert(from.typ != null, from)
      val varDecl = actionVarDecls.get(from.id)
      varDecl match {
        case Some(vd) => 
          vd.value match {
            case None => None
            case Some(v) => actionVariableInits += Assign(to, v)
          }
          if (!allUsedVariableNames.contains(to.id)) {
            variables += Declaration(to.id,vd.typ,false,None)
            allUsedVariableNames += to.id
          }
        case None =>
          // Input pattern variable
          if (!allUsedVariableNames.contains(to.id)) {
            variables += Declaration(to.id,from.typ,false,None)
            allUsedVariableNames += to.id
          }
      }
    }
    
    
    for (pat <- a.inputPattern) {
      for (v <- pat.vars) {
        
        connMapOpt match {
          case Some(connectionMap) => {
            // Network
            val connections = connectionMap.connections
            val conn = connectionMap.getDst(eOpt.get.id,pat.portId)

            
            assert(pat.typ != null)
            
            for (i <- 0 until pat.repeat) {
              var count = consumeCount(conn)
              consumeCount = consumeCount + (conn ->  (count+1))
              //val name = conn+Sep+count
              val name = conn
              
//              val c = connections.find { _.id == conn }
//              if (c.get.from.actor.isDefined) {
//                // This avoids adding variables that are part of the input pattern
//                // to action variables
//                if (!allUsedVariableNames.contains(name)) {
//                  variables += Declaration(name,pat.typ,false,None)
//                  allUsedVariableNames += name
//                }
//              }
              val c = connections.find { _.id == conn }
              
              val acc =
                if (!c.get.from.actor.isDefined) {
                  // This is an input, if we only read one token on this input, it will not be a map
                  if (produceCount(conn) <= 1) Id(conn)
                  else IndexAccessor(Id(conn),IntLiteral(count))
                }
                else IndexAccessor(Id(conn),IntLiteral(count))
                
              if (pat.repeat > 1) {
                //stmt += MapAssign(IndexAccessor(replaceStr(v,renames),IntLiteral(i)) ,Id(conn+Sep+count))
                stmt += MapAssign(IndexAccessor(replaceStr(v,renames),IntLiteral(i)) ,  acc)
              }
              else {
                //stmt += Assign(replaceStr(v,renames).asInstanceOf[Id],Id(conn+Sep+count))
                stmt += Assign(replaceStr(v,renames).asInstanceOf[Id], acc)
              }
              
            }
            
          }
          case None => {
            // Basic actor
            for (i <- 0 until pat.repeat) {
              val count = consumeCount(pat.portId)
              consumeCount = consumeCount + (pat.portId ->  (count+1))
              
              val acc =
                if (produceCount(pat.portId) <= 1) Id(pat.portId+Sep)
                else IndexAccessor(Id(pat.portId+Sep),IntLiteral(count))

              
              assert(pat.typ != null)
              if (pat.repeat > 1) {
                //stmt += MapAssign(IndexAccessor(replaceStr(v,renames),IntLiteral(i)) ,Id(pat.portId+Sep+count))
                stmt += MapAssign(IndexAccessor(replaceStr(v,renames),IntLiteral(i)) ,acc)
              }
              else {
                //stmt += Assign(replaceStr(v,renames).asInstanceOf[Id],Id(pat.portId+Sep+count))
                stmt += Assign(replaceStr(v,renames).asInstanceOf[Id],acc)
              }
            }
          }
        }
        
      }
    }
    stmt ++= replaceStr(actionVariableInits.toList,renames)
    stmt ++= replaceStr(a.body,renames)
    for (pat <- a.outputPattern) {
      for (exp <- pat.exps) {
        
        connMapOpt match {
          case Some(connectionMap) => {
            // Network
            val conn = connectionMap.getSrc(eOpt.get.id,pat.portId)
            for (i <- 0 until pat.repeat) {
              val count = produceCount(conn)
              produceCount = produceCount + (conn ->  (count+1))
              //val name = conn+Sep+count
              val name = conn
//              assert(pat.typ != null)
//              if (!allUsedVariableNames.contains(name)) {
//                variables += Declaration(name,pat.typ,false,None)
//                allUsedVariableNames += name
//              }
              if (pat.repeat > 1) {
                //assert(false)
                //stmt += Assign(replaceStr(Id(name),renames).asInstanceOf[Id],IndexAccessor(replaceStr(exp,renames),IntLiteral(i)))
                stmt += MapAssign(IndexAccessor(replaceStr(Id(name),renames), IntLiteral(count)) ,IndexAccessor(replaceStr(exp,renames),IntLiteral(i)))
              }
              else {
                //stmt += Assign(replaceStr(Id(name),renames).asInstanceOf[Id],replaceStr(exp,renames))
                stmt += MapAssign(IndexAccessor(replaceStr(Id(name),renames), IntLiteral(count)) ,replaceStr(exp,renames))
              }
            }
          }
          case None => {
            for (i <- 0 until pat.repeat) {
              val count = produceCount(pat.portId)
              produceCount = produceCount + (pat.portId -> (count+1))
              //val name = pat.portId+Sep+count
              val name = pat.portId+Sep
              assert(pat.typ != null)
//              if (!allUsedVariableNames.contains(name)) {
//                variables += Declaration(name,pat.typ,false,None)
//                allUsedVariableNames += name
//              }
              if (pat.repeat > 1) {
                //assert(false)
                //stmt += Assign(replaceStr(Id(name),renames).asInstanceOf[Id],IndexAccessor(replaceStr(exp,renames),IntLiteral(i)) )
                stmt += MapAssign(IndexAccessor(replaceStr(Id(name),renames), IntLiteral(count)) ,IndexAccessor(replaceStr(exp,renames),IntLiteral(i)) )
              }
              else {
                stmt += MapAssign(IndexAccessor(replaceStr(Id(name),renames), IntLiteral(count)) ,replaceStr(exp,renames))
              }
            }
          }
        }
        
      }
    }
    
    (stmt.toList,variables.toList,consumeCount,produceCount,allUsedVariableNames)
    
  }
  
  def createInitActionForNetwork(nw: Network, initSequence: List[(Instance,ActorAction)], actorVariables: Map[Instance,Map[String,Expr]], tokenAmounts: List[(String,Int)]) = {
    val connections = nw.structure.get.connections
    val stmt = new ListBuffer[Stmt]
    val connectionMap = ConnectionMap.build(connections,Map.empty)
    var usedVariableNames = Set.empty[String]
    val variables = new collection.mutable.ListBuffer[Declaration]()
    var consumeCount = connections.map( c => (c.id,0) ).toMap
    var produceCount = connections.map( c => (c.id,0) ).toMap
    
    for ((e,a) <- initSequence) {
      val (subStmt,subVars,newConsCount,newProdCount,usedVariables) = 
        handleActionExecution(a, Some(e), Some(connectionMap), nw, actorVariables(e), usedVariableNames, consumeCount, produceCount)
      stmt ++= subStmt
      variables ++= subVars
      consumeCount = newConsCount
      produceCount = newProdCount
      usedVariableNames = usedVariables
    }
    
    for ((ch,amount) <- tokenAmounts) {
      for (i <- 0 until amount) {
        //stmt += Assign(Id(Sep+"del"+Sep+ch+Sep+i),Id(ch+Sep+i))
        stmt += MapAssign( IndexAccessor(Id(Sep+"del"+Sep+ch),IntLiteral(i)),  IndexAccessor(Id(ch), IntLiteral(i)) )
      }
    }
    
//    for (c <- connections.filter { !_.isInput }) {
//      if (produceCount(c.id) > 0) {
//        variables += Declaration(c.id,MapType(IntType,c.typ.asInstanceOf[ChanType].contentType,produceCount(c.id)),false,None)
//        usedVariableNames += c.id
//      }
//    }
    
    
    val action = ActorAction(
        Some("Init__"),
        true,
        Nil,
        Nil,
        Nil,
        Nil,
        Nil,
        variables.toList,
        stmt.toList)
    action
  }
  
  
  def replace(e: Expr, renamings: Map[Id,Id]) = IdToIdReplacer.visitExpr(e)(renamings)
  def replace(e: Stmt, renamings: Map[Id,Id]) = IdToIdReplacer.visitStmt(e)(renamings)
  def replace(id: Id, renamings: Map[Id,Id]) = IdToIdReplacer.visitId(id)(renamings)
  def replace(e: List[Stmt], renamings: Map[Id,Id]) = IdToIdReplacer.visitStmt(e)(renamings)
  
  def replaceStr(e: Expr, renamings: Map[String,Expr]) = IdReplacerString.visitExpr(e)(renamings)
  def replaceStrAll(exps: List[Expr], renamings: Map[String,Expr]) = exps map {e => IdReplacerString.visitExpr(e)(renamings)}
  def replaceStrAssertsAll(exps: List[Assertion], renamings: Map[String,Expr]) = exps map {e => Assertion(IdReplacerString.visitExpr(e.expr)(renamings),e.free,e.msg)}
  def replaceStr(e: Stmt, renamings: Map[String,Expr]) = IdReplacerString.visitStmt(e)(renamings)
  //def replaceStr(id: Id, renamings: Map[String,Expr]) = IdReplacerString.visitId(id)(renamings)
  def replaceStr(e: List[Stmt], renamings: Map[String,Expr]) = IdReplacerString.visitStmt(e)(renamings)
  
  def getActionReplacements(e: Instance, a: ActorAction) = {
    (//e.actor.variables.map { v => { val id = Id(v.id); id.typ = v.typ; id -> Id(e.id+Sep+v.id) } } :::
    a.variables.map { v => { v.id -> Id(replaceChars(e.id+Sep+v.id)) } } :::
    a.inputPattern.flatMap(pat => pat.vars).map { v => (v.id -> Id(replaceChars(e.id+Sep+v.id))) })
    .toMap
  }
  
  def getReplacements(ba: DFActor, a: ActorAction) = {
    (//ba.variables.map { v => { val id = Id(v.id); id.typ = v.typ; id -> Id(v.id) } } :::
    a.variables.map { v => { v.id -> Id(replaceChars(ba.id+Sep+a.fullName+Sep+v.id)) } } :::
    a.inputPattern.flatMap(pat => pat.vars).map { v => (v.id -> Id(replaceChars(ba.id+Sep+a.fullName+Sep+v.id))) })
    .toMap
  }
  
  def replaceChars(str: String) = str.replace(".", "_")
  
  def translateGuardToExecutableFormat(guard: Expr, inputPatterns: List[InputPattern]): Expr = {
    val map =
      (inputPatterns.flatMap {
        pat => pat.vars.zipWithIndex.map { 
          case (v,i) => {
            if (pat.repeat > 1) {
              ((pat.portId,i) -> IndexAccessor(v,IntLiteral(i)))
            }
            else{
              ((pat.portId,i) -> v)
            }
          }
        }
      }).toMap
    ContractGuardToActorGuardTranslator.visitExpr(guard)(map)
  }
  
}
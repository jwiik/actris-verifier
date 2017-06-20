package fi.abo.it.actortool.merging

import fi.abo.it.actortool._
import fi.abo.it.actortool.schedule._
import fi.abo.it.actortool.util.ASTPrinter
import fi.abo.it.actortool.util.ConnectionMap
import collection.mutable.ListBuffer

object Constants {
  val Sep = "__"
}

/**
 * This class implements merging of networks and actors into composite actors. The composite
 * actors should have a (concrete) action for each contract.
 */
class ActorMerger(constants: List[Declaration]) extends GeneralBackend[ScheduleContext,Option[BasicActor]] {
  
  val Sep = Constants.Sep
  
  def invoke(scheduleCtx: ScheduleContext): Option[BasicActor] = {
    val entity = scheduleCtx.entity
    val schedules = scheduleCtx.schedules
    val members: List[Member] =
      entity match {
        case nw: Network => {
          val members = new ListBuffer[Member]
          val tokens = TokensDefFinder.find(nw.actorInvariants.map(_.expr))
          val tokenAmounts = tokens.collect { case (ch,IntLiteral(i)) => (ch,i) }
          var actorVariables: Map[Id,Id] = Map.empty
          
          for ((ch,amount) <- tokenAmounts) {
            val conn = nw.structure.get.connections.find { c => c.id == ch }.get
            for (i <- 0 until amount) {
              members += Declaration(Sep+"del"+Sep+ch+Sep+i,conn.typ.asInstanceOf[ChanType].contentType,false,None)
            }
          }
          
          for (e <- scheduleCtx.entities) yield {
            val actor = scheduleCtx.mergedActors.getOrElse(e.actorId,e.actor)
            for (v <- actor.variables)  {
              val name = e.id+Sep+v.id
              members += Declaration(name,v.typ,v.constant,v.value)
              
              actorVariables += {
                val fromId = Id(v.id)
                val toId = Id(name)
                fromId.typ = v.typ;
                toId.typ = v.typ;
                Id(v.id) -> Id(name)
              }
            }
            for (f <- actor.functionDecls) {
              val name = e.id+Sep+f.name
              members += FunctionDecl(name,f.inputs,f.output,replace(f.expr, actorVariables))
              actorVariables += Id(f.name) -> Id(name)
            }
          }
          val actions = for (s <- schedules) yield createActionForNetworkContract(nw, s, tokenAmounts, actorVariables)
          members.toList:::actions
        }
        case ba: BasicActor => {
          val members = new ListBuffer[Member]
          var actorVariables: Map[Id,Id] = Map.empty
          val variables = ba.variables
          for (v <- ba.variables)  {
            assert(v.typ != null, v)
            val name = ba.id+Sep+v.id
            members += Declaration(name,v.typ,v.constant,v.value)
            
            actorVariables += {
              val fromId = Id(v.id)
              val toId = Id(name)
              fromId.typ = v.typ;
              toId.typ = v.typ;
              Id(v.id) -> Id(name)
            }
          }
          for (f <- ba.functionDecls) {
            val name = ba.id+Sep+f.name
            members += FunctionDecl(name,f.inputs,f.output,replace(f.expr, actorVariables))
            actorVariables += Id(f.name) -> Id(name)
          }
          val initActions = {
            for (a <- ba.actorActions.find(_.init).toList) yield {
              ActorAction(
                  a.label,a.init,a.inputPattern,a.outputPattern,a.guards,a.requires,a.ensures,
                  a.variables,IdToIdReplacer.visitStmt(a.body)(actorVariables))
            }
          }
          members ++= initActions
          val actions = for (s <- schedules) yield createActionForActorContract(ba, s, actorVariables)
          members.toList:::actions
        }
      }
    
    val actor = BasicActor(
        entity.annotations,
        entity.id+Sep+"Merged",
        entity.parameters,
        entity.inports,
        entity.outports,
        members)
    //println(ASTPrinter.print(actor))
    Resolver.resolve(List(actor),constants) match {
      case Resolver.Errors(errs) => println(errs); None
      case Resolver.Success(ctx) => Some(actor)
    }
    
  }
  
  def createActionForNetworkContract(
      nw: Network, 
      schedule: ContractSchedule, 
      tokenAmounts: List[(String,Int)], 
      actorVariables: Map[Id,Id]): ActorAction = {
    val contract = schedule.contract
    val connections = nw.structure.get.connections
    val stmt = new ListBuffer[Stmt]
    val connectionMap = ConnectionMap.build(connections,Map.empty)
    
    val variables = collection.mutable.Map[String,Declaration]()
    
    var consumeCount = connections.map( c => (c.id,0) ).toMap
    var produceCount = connections.map( c => (c.id,0) ).toMap
    
    val inputPatterns = {
      contract.inputPattern.map {
        pat => {
          val conn = connectionMap.getIn(pat.portId)
          InputPattern(pat.portId, ((0 to pat.rate-1).toList.map { 
            i => {
              val count = produceCount(conn)
              produceCount = produceCount + (conn ->  (count+1))
              Id(conn+Sep+count) 
            }
          }),1)
        }
      }
    }
//    if (!tokens.isEmpty) {
//      val delIdxDecl = Declaration(Sep+"del"+Sep+"idx",IntType,false,Some(IntLiteral(0)))
//      val delIdxId = Id(delIdxDecl.id)
//      val delIdxIncr = Assign(delIdxId,Plus(delIdxId,IntLiteral(1)))
//      for ((ch,del) <- tokens) {
//        val stmt =
//          List(
//              MapAssign(IndexAccessor(Id(ch),delIdxId),IndexAccessor(Id(Sep+del+Sep+ch),delIdxId)),
//              delIdxIncr)
//        While(Less(delIdxId,del),Nil,stmt)
//      }
//    }
    
    
    
    for ((ch,amount) <- tokenAmounts) {
      for (i <- 0 until amount) {
        stmt += Assign(Id(ch+Sep+i),Id(Sep+"del"+Sep+ch+Sep+i))
      }
    }
    
    for ((e,a) <- schedule.sequence) {
      //val actor = schedule.mergedActors.getOrElse(e.actorId,e.actor)
      val actionRenames = getActionReplacements(e, a)
      for ((from,to) <- actionRenames) {
        assert(from.typ != null, from)
        variables += to.id -> Declaration(to.id,from.typ,false,None)
      }
      val renames = actorVariables ++ actionRenames
      
      for (pat <- a.inputPattern) {
        for (v <- pat.vars) {
          val conn = connectionMap.getDst(e.id,pat.portId)
          val count = consumeCount(conn)
          consumeCount = consumeCount + (conn ->  (count+1))
          val name = conn+Sep+count
          assert(pat.typ != null)
          
          val c = connections.find { _.id == conn }
          if (c.get.from.actor.isDefined) {
            // This avoids adding variables that are part of the input pattern
            // to action variables
            variables += name-> Declaration(name,pat.typ,false,None)
          }
          
          stmt += Assign(replace(v,renames),Id(conn+Sep+count))
        }
      }
      stmt ++= replace(a.body,renames)
      for (pat <- a.outputPattern) {
        for (exp <- pat.exps) {
          val conn = connectionMap.getSrc(e.id,pat.portId)
          val count = produceCount(conn)
          produceCount = produceCount + (conn ->  (count+1))
          val name = conn+Sep+count
          assert(pat.typ != null)
          variables += name-> Declaration(name,pat.typ,false,None)
          stmt += Assign(Id(name),replace(exp,renames))
        }
      }
    }
    
    for ((ch,amount) <- tokenAmounts) {
      for (i <- 0 until amount) {
        stmt += Assign(Id(Sep+"del"+Sep+ch+Sep+i),Id(ch+Sep+(consumeCount(ch)-1+i)))
      }
    }
    
    val outputPatterns = 
      contract.outputPattern.map {
        pat => {
          val conn = connectionMap.getOut(pat.portId)
          OutputPattern(pat.portId, ((0 to pat.rate-1).toList.map { 
            i => {
              val count = consumeCount(conn)
              consumeCount = consumeCount + (conn ->  (count+1))
              Id(conn+Sep+count) 
            }
          }),1)
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
        variables.values.toList,
        stmt.toList)
    //println(ASTPrinter.printMember(action))
    action.refinedContract = Some(contract)
    action
  }
  
  def createActionForActorContract(ba: BasicActor, schedule: ContractSchedule, actorVariables: Map[Id,Id]): ActorAction = {
    val contract = schedule.contract
    val stmt = new ListBuffer[Stmt]
    
    val variables = collection.mutable.Map[String,Declaration]()
    
    val ports = ba.inports ::: ba.outports
    var consumeCount = ports.map( c => (c.id,0) ).toMap
    var produceCount = ports.map( c => (c.id,0) ).toMap
    
    val inputPatterns = 
      contract.inputPattern.map {
        pat => {
          InputPattern(pat.portId, ((0 to pat.rate-1).toList.map { 
            i => {
              val count = produceCount(pat.portId)
              produceCount = produceCount + (pat.portId ->  (count+1))
              Id(pat.portId+Sep+count) 
            }
          }),1)
        }
      }
    for ((_,a) <- schedule.sequence) {
      val actionRenames = getReplacements(ba, a)
      for ((from,to) <- actionRenames) {
        assert(from.typ != null, from)
        variables += to.id -> Declaration(to.id,from.typ,false,None)
      }
      val renames = actorVariables ++ actionRenames
      for (pat <- a.inputPattern) {
        for (v <- pat.vars) {
          val count = consumeCount(pat.portId)
          consumeCount = consumeCount + (pat.portId ->  (count+1))
          val name = pat.portId+Sep+count
          assert(pat.typ != null)
          
          stmt += Assign(replace(v,renames),Id(pat.portId+Sep+count))
        }
      }
      stmt ++= replace(a.body,renames)
      for (pat <- a.outputPattern) {
        for (exp <- pat.exps) {
          val count = produceCount(pat.portId)
          produceCount = produceCount + (pat.portId -> (count+1))
          val name = pat.portId+Sep+count
          assert(pat.typ != null)
          variables += name-> Declaration(name,pat.typ,false,None)
          stmt += Assign(Id(name),replace(exp,renames))
        }
      }
    }
    
    val outputPatterns = 
      contract.outputPattern.map {
        pat => {
          OutputPattern(pat.portId, ((0 to pat.rate-1).toList.map { 
            i => {
              val count = consumeCount(pat.portId)
              consumeCount = consumeCount + (pat.portId ->  (count+1))
              Id(pat.portId+Sep+count) 
            }
          }),1)
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
        variables.values.toList,
        stmt.toList)
    action.refinedContract = Some(contract)
    action
  }
  
  def createInitActionForNetwork(nw: Network) = {
    val entities = nw.entities.get.entities
    val initActions = entities.flatMap { e => e.actor.actorActions.filter(_.init) }
  }
  
  def replace(e: Expr, renamings: Map[Id,Id]) = IdToIdReplacer.visitExpr(e)(renamings)
  def replace(e: Stmt, renamings: Map[Id,Id]) = IdToIdReplacer.visitStmt(e)(renamings)
  def replace(id: Id, renamings: Map[Id,Id]) = IdToIdReplacer.visitId(id)(renamings)
  def replace(e: List[Stmt], renamings: Map[Id,Id]) = IdToIdReplacer.visitStmt(e)(renamings)
  
  def getActionReplacements(e: Instance, a: ActorAction) = {
    (//e.actor.variables.map { v => { val id = Id(v.id); id.typ = v.typ; id -> Id(e.id+Sep+v.id) } } :::
    a.variables.map { v => { val id = Id(v.id); id.typ = v.typ; id -> Id(replaceChars(e.id+Sep+v.id)) } } :::
    a.inputPattern.flatMap(pat => pat.vars).map { v => (v -> Id(replaceChars(e.id+Sep+v.id))) })
    .toMap
  }
  
  def getReplacements(ba: BasicActor, a: ActorAction) = {
    (//ba.variables.map { v => { val id = Id(v.id); id.typ = v.typ; id -> Id(v.id) } } :::
    a.variables.map { v => { val id = Id(v.id); id.typ = v.typ; id -> Id(replaceChars(ba.id+Sep+a.fullName+Sep+v.id)) } } :::
    a.inputPattern.flatMap(pat => pat.vars).map { v => (v -> Id(replaceChars(ba.id+Sep+a.fullName+Sep+v.id))) })
    .toMap
  }
  
  def replaceChars(str: String) = str.replace(".", "_")
  
  def translateGuardToExecutableFormat(guard: Expr, inputPatterns: List[InputPattern]): Expr = {
    val map =
      (inputPatterns.flatMap {
        pat => pat.vars.zipWithIndex.map { case (v,i) => ((pat.portId,i) -> v) }
      }).toMap
    ContractGuardToActorGuardTranslator.visitExpr(guard)(map)
  }
  
}
package fi.abo.it.actortool.boogie

import fi.abo.it.actortool._
import fi.abo.it.actortool.schedule._

class BoogieScheduleCheckTranslator(mergedActions: Boolean) extends EntityTranslator[ScheduleContext] with GeneralBackend[ScheduleContext,List[Boogie.Decl]] {

  
  def invoke(scheduleCtx: ScheduleContext) = translateEntity(scheduleCtx)
  
  def translateEntity(scheduleCtx: ScheduleContext): List[Boogie.Decl] = {
    
    
    val constDecls =
      (scheduleCtx.program.collect{ 
        case u: DataUnit => {
          u.constants flatMap { d =>
            val (axiom,_) = stmtTranslator.transExpr(d.value.get,Map.empty,false)
            List(Boogie.Const(d.id,false,B.type2BType(d.typ)),Boogie.Axiom(Boogie.VarExpr(d.id) ==@ axiom))
          }
        }
      }).flatten
    
    val decls = scheduleCtx.entity match {
      case nw: Network => {
        val verStructBuilder = new NetworkVerificationStructureBuilder(stmtTranslator,new Resolver.EmptyContext(true),mergedActions)
        val nwvs = verStructBuilder.buildStructure(nw)
        scheduleCtx.schedules.flatMap(s => translateNetworkSchedule(scheduleCtx, s, nwvs))
      }
      case ba: BasicActor => {
        val verStructBuilder = new ActorVerificationStructureBuilder(stmtTranslator,new Resolver.EmptyContext(true),mergedActions)
        val avs = verStructBuilder.buildStructure(ba)
        translateFunctionDecl(avs) ::: scheduleCtx.schedules.flatMap(s => translateActorSchedule(scheduleCtx,s,avs))
      }
    }
      
    constDecls ::: decls
  }
  
  def translateActorSchedule(scheduleCtx: ScheduleContext, schedule: ContractSchedule, avs: ActorVerificationStructure) = {
    val decls = new collection.mutable.ListBuffer[Boogie.Stmt]
    val stmts = new collection.mutable.ListBuffer[Boogie.Stmt]
    val alreadyDeclared = collection.mutable.Set[String]()
    decls ++= avs.actorVarDecls map { _.decl }
    decls ++= avs.actorParamDecls map { _.decl }
    stmts += B.Assume(avs.uniquenessCondition)
    stmts ++= avs.basicAssumes
    stmts += B.Assume(B.Mode(B.This) ==@ Boogie.VarExpr(schedule.contract.fullName))
    stmts += B.Assume(Boogie.VarExpr(BMap.R) ==@ Boogie.VarExpr(BMap.I))
    stmts += B.Assume(Boogie.VarExpr(BMap.C) ==@ Boogie.VarExpr(BMap.R))
    for (inv <- avs.invariants) stmts += BAssume(inv, avs.renamings)
    
    for (ipat <- schedule.contract.inputPattern) {
      stmts += Boogie.Assign(
          B.C(transExpr(ipat.portId,ipat.typ)(avs.renamings)), 
          B.C(transExpr(ipat.portId,ipat.typ)(avs.renamings)) + B.Int(ipat.rate))
    }
    
    stmts ++= schedule.contract.guards.map { g => B.Assume(transExpr(g)(avs.renamings)) }
    stmts ++= schedule.contract.requires.map { r => B.Assume(transExpr(r.expr)(avs.renamings)) }
    
    val renamingsBuffer = collection.mutable.Map[ActorAction,Map[String,Id]]()
    for (action <- schedule.entity.actorActions) {
      val prefix = action.fullName
      val actionRenamings = collection.mutable.Map[String,Id]()
      for (v <- action.variables) {
        val name = prefix+B.Sep+v.id
        decls += B.Local(name,B.type2BType(v.typ))
        val id = Id(name)
        id.typ = v.typ
        actionRenamings += (v.id -> id)
      }
      for (p <- action.inputPattern) {
        for (v <- p.vars) {
          val name = prefix+B.Sep+v.id
          decls += B.Local(name,B.type2BType(v.typ))
          val id = Id(name)
          id.typ = v.typ
          actionRenamings += (v.id -> id)
        }
      }
      renamingsBuffer += (action -> actionRenamings.toMap)
    }
    
    val renamings = renamingsBuffer.toMap
    
    for (firing <- schedule.sequence) {
      val action = firing.action
      val actionRenamings = avs.renamings ++ renamings(action)
      val actionData = avs.actionData(action)
      
      for (ipat <- action.inputPattern) {
        val id = ipat.portId
        stmts += B.Assert(B.Int(ipat.rate) <= B.Urd(id),ipat.pos,"Input pattern might not be satisfied for action '" + action.fullName + "'")
        for (v <- ipat.vars) {
          stmts += Boogie.Assign(transExpr(v.id,v.typ)(actionRenamings),B.ChannelIdx(id,v.typ,B.R(id)))
          stmts += Boogie.Assign(B.R(id), B.R(id) + B.Int(1))
        }
      }
      stmts ++= action.guards.map { g => B.Assert(transExpr(g)(actionRenamings),g.pos,"Guard might not be satisfied for action '" + action.fullName + "'" ) }
      stmts ++= action.requires.filter(!_.free).map { r => B.Assert(transExpr(r.expr)(actionRenamings),r.pos,"Precondition might not hold for action '" + action.fullName + "'" ) }
      stmts ++= transStmt(action.body)(actionRenamings)
      
      for (opat <- action.outputPattern) {
        val id = opat.portId
        for (e <- opat.exps) {
          stmts += Boogie.Assign(B.ChannelIdx(id,e.typ,B.C(id)),transExpr(e)(actionRenamings))
          stmts += Boogie.Assign(B.C(id), B.C(id) + B.Int(1))
        }

      }
      for (q <- action.ensures) stmts += B.Assume(transExpr(q.expr)(actionRenamings))
      for (inv <- avs.invariants) stmts += BAssume(inv, avs.renamings)
    }
    
    for (opat <- schedule.contract.outputPattern) {
      stmts += B.Assert(
          B.Urd(transExpr(opat.portId,opat.typ)(avs.renamings)) ==@ B.Int(opat.rate),
          opat.pos,
          "The correct amount of tokens might not be produced on output " + opat.portId)
    }
    
    List(B.createProc(schedule.entity.id+B.Sep+schedule.contract.fullName, decls.toList:::stmts.toList, false))
  }
  
  def translateNetworkSchedule(scheduleCtx: ScheduleContext, schedule: ContractSchedule, nwvs: NetworkVerificationStructure) = {
    val decls = new collection.mutable.ListBuffer[Boogie.Stmt]
    val stmts = new collection.mutable.ListBuffer[Boogie.Stmt]
    val alreadyDeclared = collection.mutable.Set[String]()
    
    decls ++= (nwvs.entityDecls map { _.decl })
    decls ++= nwvs.subactorVarDecls map { _.decl }
    
    stmts ++= nwvs.uniquenessConditions map { B.Assume(_) }
    stmts ++= nwvs.basicAssumes
    stmts += B.Assume(B.Mode(B.This) ==@ Boogie.VarExpr(schedule.contract.fullName))
    stmts += B.Assume(Boogie.VarExpr(BMap.R) ==@ Boogie.VarExpr(BMap.I))
    for (nwi <- nwvs.nwInvariants) stmts += BAssume(nwi, nwvs.renamings)
    for (chi <- nwvs.chInvariants) stmts += BAssume(chi, nwvs.renamings)
    
    for (e <- scheduleCtx.entities) {
      val renamings = nwvs.instanceRenamings(e)
      for (inv <- e.actor.streamInvariants) stmts += B.Assume(transExpr(inv.expr)(renamings))
    }
    
    for (ipat <- schedule.contract.inputPattern) {
      stmts += Boogie.Assign(
          B.C(transExpr(ipat.portId,ipat.typ)(nwvs.renamings)), 
          B.C(transExpr(ipat.portId,ipat.typ)(nwvs.renamings)) + B.Int(ipat.rate))
    }
    for (guard <- schedule.contract.guards) {
      stmts += B.Assume(transExpr(guard)(nwvs.renamings))
    }
    for (pre <- schedule.contract.requires) {
      stmts += B.Assume(transExpr(pre.expr)(nwvs.renamings))
    }
    
    

    
    for (firing <- schedule.sequence) {
      val a1 = firing.action
      val e = firing.instance
      val action = a1.refinedContract.getOrElse(a1)
      //decls+ ++= nwvs.getEntityActionData(e, action).declarations  map { _.decl }
      
      stmts += Boogie.Comment("Instance: " + e.id + ", Action: " + action.fullName)
      val renamings = nwvs.subActionRenamings(e, action)
      for (d <- nwvs.getEntityActionData(e, action).declarations) {
        if (!alreadyDeclared.contains(d.name)) {
          decls += d.decl
          alreadyDeclared += d.name
        }
      }
      
      for (ip <- e.actor.inports) {
        val cId = nwvs.connectionMap.getDst(PortRef(Some(e.id),ip.id))
        stmts += Boogie.Assign(B.Isub(cId), B.R(cId))
      }
      
      for (op <- e.actor.outports) {
        val cId = nwvs.connectionMap.getSrc(PortRef(Some(e.id),op.id))
        stmts += Boogie.Assign(B.Isub(cId), B.C(cId))
      }
      
      for (d <- nwvs.getEntityActionData(e, action).oldDeclarations) {
        val renamed = renamings(d.id).asInstanceOf[Id].id
        stmts += Boogie.Assign(Boogie.VarExpr(renamed+B.Sep+"old"),transExpr(d)(renamings))
      }
      
      val firingRules = getFiringRules(e, nwvs)
      //println(firingRules.keys map (_.fullName))
      stmts += B.Assert(firingRules(action),action.pos,schedule.contract.fullName + ": Firing rule might not be satisfied for action '" + action.fullName + "' of instance '" + e.id +"'")
      
      for (pat <- action.inputPattern) {
        val id = nwvs.connectionMap.getDst(PortRef(Some(e.id),pat.portId))
        pat match {
          case InputPattern(_,vars,1) => {
            for (v <- vars) {
              stmts += Boogie.Assign(transExpr(v.id,v.typ)(renamings),B.ChannelIdx(id,v.typ,B.R(id)))
              stmts += Boogie.Assign(B.R(id), B.R(id) plus B.Int(1))
            }
          }
          case InputPattern(_,List(v),repeat) => {
            for (i <- 0 until repeat) {
              stmts += Boogie.Assign(transExpr(v)(renamings), B.Fun("Map#Store",transExpr(v)(renamings) , B.Int(i) , B.ChannelIdx(id, v.typ, B.R(id)) )  )
              stmts += Boogie.Assign(B.R(id), B.R(id) plus B.Int(1))
            }
          }
          case npat: NwPattern => {
            stmts += Boogie.Assign(B.R(id), B.R(id) plus B.Int(npat.rate))
          }
          case _ => assert(false)
        }
      }
      
      for (pre <- action.requires) {
        if (!pre.free) {
          stmts += B.Assert(transExprPrecondCheck(pre.expr)(renamings),pre.pos,"Precondition might not hold")
        }
      }
      
      stmts ++= generateHavoc(nwvs.getEntityActionData(e, action).assignedVariables, renamings)
      
      for (pat <- action.outputPattern) {
        val id = nwvs.connectionMap.getSrc(PortRef(Some(e.id),pat.portId))
        pat match {
          case OutputPattern(_,exps,1) => {
            for (e <- exps) {
              stmts += Boogie.Assign(B.ChannelIdx(id,e.typ,B.C(id)),transExpr(e)(renamings))
              stmts += Boogie.Assign(B.C(id),B.C(id) plus B.Int(1))
            }
          }
          case OutputPattern(_,List(e),repeat) => {
            for (i <- 0 until repeat) {
              stmts += Boogie.Assign(B.ChannelIdx(id, e.typ, B.C(id)), B.Fun("Map#Select",transExpr(e)(renamings), B.Int(i)))
              stmts += Boogie.Assign(B.C(id), B.C(id) plus B.Int(1))
            }
          }
          case npat: NwPattern => {
            stmts += Boogie.Assign(B.C(id),B.C(id) plus B.Int(npat.rate))
          }
          case _ => assert(false)
        }
        
      }
      
      for (post <- action.ensures) {
        stmts += B.Assume(transExprPrecondCheck(post.expr)(renamings))
      }
      
      for (inv <- e.actor.streamInvariants) stmts += B.Assume(transExpr(inv.expr)(renamings))
      
    }
    
    for (opat <- schedule.contract.outputPattern) {
      stmts += B.Assert(
          B.Urd(transExpr(opat.portId,opat.typ)(nwvs.renamings)) ==@ B.Int(opat.rate),
          opat.pos,
          "The correct amount of tokens might not be produced on output " + opat.portId)
    }
    
    List(B.createProc(nwvs.entity.id+B.Sep+schedule.contract.fullName, decls.toList:::stmts.toList, false))
  }
  
  def getFiringRules(instance: Instance, nwvs: NetworkVerificationStructure) = {
    ///val actor = nwvs.mergedActors(instance.actorId)
    // This list includes contract actions if the entity has such, otherwise basic actions
    val priorityList = nwvs.entityData(instance).priorities
    (priorityList.keys map { ca => (ca, transSubActionFiringRules(instance, ca, nwvs)) }).toMap
  }
  
}
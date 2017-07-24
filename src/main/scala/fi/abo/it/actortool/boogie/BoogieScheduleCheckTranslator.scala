package fi.abo.it.actortool.boogie

import fi.abo.it.actortool._
import fi.abo.it.actortool.schedule._

class BoogieScheduleCheckTranslator(
    mergedActions: Boolean, 
    actionTranslator: BasicActorTranslator) 
    extends EntityTranslator[ScheduleContext] 
    with GeneralBackend[ScheduleContext,List[Boogie.Decl]] {

  
  def invoke(scheduleCtx: ScheduleContext) = translateEntity(scheduleCtx)
  
  def translateEntity(scheduleCtx: ScheduleContext): List[Boogie.Decl] = {
    
    val constDecls =
      (scheduleCtx.program.collect{ 
        case u: DataUnit => {
          u.constants flatMap { d =>
            val axiom = stmtTranslator.transExpr(d.value.get,false)
            List(Boogie.Const(d.id,false,B.type2BType(d.typ)),Boogie.Axiom(Boogie.VarExpr(d.id) ==@ axiom))
          }
        }
      }).flatten
    
      
    val decls = {
      scheduleCtx.entity match {
        case ba: BasicActor => {
          val vs = VerStruct(ba,mergedActions)
            
          translateFunctionDecl(vs) ++ 
          //actionChecks ++ 
          scheduleCtx.schedules.flatMap { s => translateActorSchedule(scheduleCtx,s,vs) }
        }
        case nw: Network => {
          val vs = VerStruct(nw,mergedActions)
          scheduleCtx.schedules.flatMap {
            s => translateNetworkSchedule(scheduleCtx, s, vs)
          }
        }
      }
    }
    
    constDecls ++ decls
  }
  
  def translateActorSchedule(scheduleCtx: ScheduleContext, schedule: ContractSchedule, avs: RootVerStruct[BasicActor]) = {
    val decls = new collection.mutable.ListBuffer[Boogie.Stmt]
    val stmts = new collection.mutable.ListBuffer[Boogie.Stmt]
    val alreadyDeclared = collection.mutable.Set[String]()
    
    decls ++= avs.declarations.map(_.decl)
    alreadyDeclared ++= avs.declarations.map(_.name)
    stmts ++= avs.assumes
    
    stmts += B.Assume(B.Mode(B.This) ==@ Boogie.VarExpr(schedule.contract.fullName))
    stmts += B.Assume(Boogie.VarExpr(BMap.R) ==@ Boogie.VarExpr(BMap.I))
    stmts += B.Assume(Boogie.VarExpr(BMap.C) ==@ Boogie.VarExpr(BMap.R))
    
    for (inv <- avs.entity.actorInvariants) stmts += BAssume(inv, avs)
    
    for (ipat <- schedule.contract.inputPattern) {
      stmts += Boogie.Assign(
          B.C(transExpr(ipat.portId,ipat.typ,avs)), 
          B.C(transExpr(ipat.portId,ipat.typ,avs)) + B.Int(ipat.rate))
    }
    
    stmts ++= schedule.contract.guards.map { g => B.Assume(transExpr(g,avs)) }
    stmts ++= schedule.contract.requires.map { r => B.Assume(transExpr(r.expr,avs)) }
    
    
    for (firing <- schedule.sequence) {
      val action = firing.action

      val gt = translateActorGuards(action, avs)
      
      val tvs = VerStruct(avs,action,gt,true)
      
      for (d <- tvs.declarations) {
        if (!alreadyDeclared.contains(d.name)) {
          decls += d.decl
          alreadyDeclared += d.name
        }
      }
      
      for (ipat <- action.inputPattern) {
        val id = ipat.portId
        stmts += B.Assert(
            B.Int(ipat.rate) <= B.Urd(id),
            ipat.pos,
            "Input pattern might not be satisfied for action '" + action.fullName + "'")
        
        ipat match {
          case InputPattern(_,vars,1) => {
            for (v <- vars) {
              stmts += Boogie.Assign(transExpr(v.id,v.typ,tvs),B.ChannelIdx(id,v.typ,B.R(id)))
              stmts += Boogie.Assign(B.R(id), B.R(id) + B.Int(1))
            }
          }
          case InputPattern(_,List(v),repeat) => {
            for (i <- 0 until repeat) {
              stmts += Boogie.Assign(
                  transExpr(v,tvs), 
                  B.Fun("Map#Store",transExpr(v,tvs) , B.Int(i) , B.ChannelIdx(id, v.typ, B.R(id)) )  )
              stmts += Boogie.Assign(B.R(id), B.R(id) plus B.Int(1))
            }
          }
          
        }
        
      }
      
      stmts ++= action.guards.map { 
        g => B.Assert(
            transExpr(g,tvs),
            g.pos,
            "Guard might not be satisfied for action '" + action.fullName + "'" ) 
      }
      
      stmts ++= action.requires.filter(!_.free).map { 
        r => B.Assert(
            transExpr(r.expr,tvs),
            r.pos,
            "Precondition might not hold for action '" + action.fullName + "'" ) 
      }
      
      stmts ++= generateHavoc(tvs.assignedVariables,tvs)
      
      for (opat <- action.outputPattern) {
        val id = opat.portId
        
        opat match {
          case OutputPattern(_,exps,1) => {
            for (e <- exps) {
              stmts += Boogie.Assign(B.ChannelIdx(id,e.typ,B.C(id)),transExpr(e,tvs))
              stmts += Boogie.Assign(B.C(id), B.C(id) + B.Int(1))
            }
          }
          case OutputPattern(_,List(e),repeat) => {
            for (i <- 0 until repeat) {
              stmts += Boogie.Assign(B.ChannelIdx(id, e.typ, B.C(id)), B.Fun("Map#Select",transExpr(e,tvs), B.Int(i)))
              stmts += Boogie.Assign(B.C(id), B.C(id) plus B.Int(1))
            }
          }
        }

      }
      for (q <- action.ensures) stmts += B.Assume(transExpr(q.expr,tvs))
      for (inv <- avs.entity.actorInvariants) stmts += BAssume(inv,avs)
    }
    
    for (opat <- schedule.contract.outputPattern) {
      stmts += B.Assert(
          B.Urd(transExpr(opat.portId,opat.typ,avs)) ==@ B.Int(opat.rate),
          opat.pos,
          "The correct amount of tokens might not be produced on output " + opat.portId)
    }
    
    List(B.createProc(schedule.entity.id+B.Sep+schedule.contract.fullName, decls.toList:::stmts.toList, false))
  }
  
  def translateNetworkSchedule(
      scheduleCtx: ScheduleContext, 
      schedule: ContractSchedule, 
      nwvs: RootVerStruct[Network]) = {
    
    val decls = new collection.mutable.ListBuffer[Boogie.Stmt]
    val stmts = new collection.mutable.ListBuffer[Boogie.Stmt]
    val alreadyDeclared = collection.mutable.Set[String]()
    
    decls ++= nwvs.declarations.map(_.decl)
    alreadyDeclared ++= nwvs.declarations.map(_.name)
    
    stmts ++= nwvs.assumes
    
    stmts += B.Assume(B.Mode(B.This) ==@ Boogie.VarExpr(schedule.contract.fullName))
    stmts += B.Assume(Boogie.VarExpr(BMap.R) ==@ Boogie.VarExpr(BMap.I))
    for (nwi <- nwvs.nwInvariants) stmts += BAssume(nwi, nwvs)
    for (chi <- nwvs.chInvariants) stmts += BAssume(chi, nwvs)
    
    for (ioi <- nwvs.translatedIoInvariants(stmtTranslator)) stmts += B.Assume(ioi)
    
    for (ipat <- schedule.contract.inputPattern) {
      stmts += Boogie.Assign(
          B.C(transExpr(ipat.portId,ipat.typ,nwvs)), 
          B.C(transExpr(ipat.portId,ipat.typ,nwvs)) + B.Int(ipat.rate))
    }
    for (guard <- schedule.contract.guards) {
      stmts += B.Assume(transExpr(guard,nwvs))
    }
    for (pre <- schedule.contract.requires) {
      stmts += B.Assume(transExpr(pre.expr,nwvs))
    }
    
    for (firing <- schedule.sequence) {
      val a1 = firing.action
      val e = firing.instance
      val action = a1.refinedContract.getOrElse(a1)
      
      val acvs = VerStruct(VerStruct(nwvs, e), action)
      
      for (d <- acvs.declarations) {
        if (!alreadyDeclared.contains(d.name)) {
          decls += d.decl
          alreadyDeclared += d.name
        }
      }
      
      stmts += Boogie.Comment("Instance: " + e.id + ", Action: " + action.fullName)
      
      for (ip <- e.actor.inports) {
        val cId = nwvs.connectionMap.getDst(PortRef(Some(e.id),ip.id))
        stmts += Boogie.Assign(B.Isub(cId), B.R(cId))
      }
      
      for (op <- e.actor.outports) {
        val cId = nwvs.connectionMap.getSrc(PortRef(Some(e.id),op.id))
        stmts += Boogie.Assign(B.Isub(cId), B.C(cId))
      }
      
      val firingRules = getFiringRules(e, acvs)
      
      stmts += B.Assert(
          firingRules(action),
          action.pos,
          schedule.contract.fullName + ": Firing rule might not be satisfied for action '" + action.fullName + "' of instance '" + e.id +"'")
      
      for (pat <- action.inputPattern) {
        val id = nwvs.connectionMap.getDst(PortRef(Some(e.id),pat.portId))
        pat match {
          case InputPattern(_,vars,1) => {
            for (v <- vars) {
              stmts += Boogie.Assign(transExpr(v.id,v.typ,acvs),B.ChannelIdx(id,v.typ,B.R(id)))
              stmts += Boogie.Assign(B.R(id), B.R(id) plus B.Int(1))
            }
          }
          case InputPattern(_,List(v),repeat) => {
            for (i <- 0 until repeat) {
              stmts += Boogie.Assign(transExpr(v,acvs), B.Fun("Map#Store",transExpr(v,acvs) , B.Int(i) , B.ChannelIdx(id, v.typ, B.R(id)) )  )
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
          stmts += B.Assert(transExprPrecondCheck(pre.expr,acvs),pre.pos,"Precondition might not hold")
        }
      }
      
      stmts ++= generateHavoc(acvs.assignedVariables, acvs)
      
      for (pat <- action.outputPattern) {
        val id = nwvs.connectionMap.getSrc(PortRef(Some(e.id),pat.portId))
        pat match {
          case OutputPattern(_,exps,1) => {
            for (e <- exps) {
              stmts += Boogie.Assign(B.ChannelIdx(id,e.typ,B.C(id)),transExpr(e,acvs))
              stmts += Boogie.Assign(B.C(id),B.C(id) plus B.Int(1))
            }
          }
          case OutputPattern(_,List(e),repeat) => {
            for (i <- 0 until repeat) {
              stmts += Boogie.Assign(B.ChannelIdx(id, e.typ, B.C(id)), B.Fun("Map#Select",transExpr(e,acvs), B.Int(i)))
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
        stmts += B.Assume(transExprPrecondCheck(post.expr,acvs))
      }
      
      for (inv <- e.actor.streamInvariants) stmts += B.Assume(transExpr(inv.expr,acvs))
      
    }
    
    for (opat <- schedule.contract.outputPattern) {
      stmts += B.Assert(
          B.Urd(transExpr(opat.portId,opat.typ,nwvs)) ==@ B.Int(opat.rate),
          opat.pos,
          "The correct amount of tokens might not be produced on output " + opat.portId)
    }
    
    List(B.createProc(nwvs.entity.id+B.Sep+schedule.contract.fullName, decls.toList:::stmts.toList, false))
  }
  
  def getFiringRules(instance: Instance, ivs: SubActionVerStruct) = {
    ///val actor = nwvs.mergedActors(instance.actorId)
    // This list includes contract actions if the entity has such, otherwise basic actions
    val priorityList = ivs.priorities(mergedActions)
    (priorityList.keys map { ca => (ca, transSubActionFiringRules(instance, ca, ivs)) }).toMap
  }
  
}
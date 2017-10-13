package fi.abo.it.actortool.boogie

import fi.abo.it.actortool._
import fi.abo.it.actortool.schedule._

class BoogieScheduleCheckTranslator(
    val mergedActions: Boolean, 
    val contractsToVerify: List[(String,String)]
    //val smokeTest: Boolean,
    //val skipMutualExclusiveness: Boolean
    ) 
    extends EntityTranslator[ScheduleContext,ContractSchedule] 
    with GeneralBackend[ScheduleContext,Seq[BoogieTranslation[ContractSchedule]]] {

  
  def invoke(scheduleCtx: ScheduleContext) = {
    
    translateEntity(scheduleCtx)
  }
  
  def translateEntity(scheduleCtx: ScheduleContext): Seq[BoogieTranslation[ContractSchedule]] = {
    
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
          val vs = VerStruct.forActor(ba,false)
          //translateFunctionDecl(vs) ++ 
          //actionChecks ++ 
          scheduleCtx.schedules.map { s => 
            BoogieTranslation(s, constDecls ++ translateFunctionDecl(vs) ++ translateActorSchedule(scheduleCtx,s,vs))
          }
        }
        case nw: Network => {
          val vs = VerStruct.forNetwork(nw,mergedActions)
          scheduleCtx.schedules.map {
            s => BoogieTranslation(s, constDecls ++ translateNetworkSchedule(scheduleCtx, s, vs))
          }
        }
      }
    }
    
    decls
    //List(constDecls ++ decls)
  }
  
  def translateActorSchedule(
      scheduleCtx: ScheduleContext, 
      schedule: ContractSchedule, 
      avs: RootVerStruct[BasicActor]): List[Boogie.Proc] = {
    
    
    if (!contractsToVerify.isEmpty && !contractsToVerify.contains(avs.entity.id -> schedule.contract.fullName)) {
      return List.empty
    }
    
    val stateVarsInGuards = avs.guardStateVariables
    val stateChannels = avs.stateChannelNames.filter{ case (id,_) => stateVarsInGuards.contains(id) }
    
    val vs = VerStruct.forSchedule(avs, schedule, stateChannels.unzip._2.toSeq)
    
    val decls = new collection.mutable.ListBuffer[Boogie.Stmt]
    val stmts = new collection.mutable.ListBuffer[Boogie.Stmt]
    val alreadyDeclared = collection.mutable.Set[String]()
    
    decls ++= vs.declarations.map(_.decl)
    alreadyDeclared ++= vs.declarations.map(_.name)
    stmts ++= vs.assumes
    
    stmts += B.Assume(B.Mode(B.This) ==@ Boogie.VarExpr(schedule.contract.fullName))
    stmts += B.Assume(Boogie.VarExpr(BMap.R) ==@ Boogie.VarExpr(BMap.I))
    //stmts += B.Assume(Boogie.VarExpr(BMap.C) ==@ Boogie.VarExpr(BMap.R))
    
    for (inv <- avs.entity.contractInvariants) stmts += BAssume(inv, vs)
    for (inv <- avs.entity.actionInvariants) stmts += BAssume(inv, vs)
    
    for (ipat <- schedule.contract.inputPattern) {
      stmts += Boogie.Assign(
          B.C(transExpr(ipat.portId,ipat.typ,vs)), 
          B.C(transExpr(ipat.portId,ipat.typ,vs)) + B.Int(ipat.rate))
    }
    
    stmts ++= schedule.contract.guards.map { g => B.Assume(transExpr(g,vs)) }
    stmts ++= schedule.contract.requires.map { r => B.Assume(transExpr(r.expr,vs)) }
    
//    stmts ++= 
//      stateChannels.map { case (id,ch) => B.Assume(B.C(transExpr(ch,vs)) ==@ B.R(transExpr(ch,vs)) + B.Int(1)) }
    
    for ((firing,idx) <- schedule.sequence.zipWithIndex) {
      
      val action = firing.action
      
      stmts += Boogie.Comment("Action: " + action.fullName + ", Step: " + idx)

      val gt = translateActorGuards(action, avs)
      
      val tvs = VerStruct.forActorAction(avs,action,gt,true)
      
      for (d <- tvs.declarations) {
        if (!alreadyDeclared.contains(d.name)) {
          decls += d.decl
          alreadyDeclared += d.name
        }
      }
      
      //stmts ++= tvs.assumes
      
//      for ((id,ch) <- stateChannels ) {
//        //stmts += B.Assume(B.ChannelIdx(transExpr(ch,tvs),B.R(transExpr(ch,tvs))) ==@ transExpr(Id(id).withType(ch.typ),tvs))
//        stmts += Boogie.Assign(B.R(transExpr(ch,tvs)),B.R(transExpr(ch,tvs)) + B.Int(1))
//      }
      
      for ((id,ch) <- stateChannels ) {
        stmts += B.Assume(B.C(transExpr(ch,tvs)) ==@ B.R(transExpr(ch,tvs)) + B.Int(1))
        stmts += B.Assume(B.ChannelIdx(transExpr(ch,tvs),B.R(transExpr(ch,tvs))) ==@ transExpr(Id(id).withType(ch.typ),tvs))
      }
      
      for ((id,ch) <- stateChannels) {
        stmts += Boogie.Assign(B.R(transExpr(ch,tvs)),B.R(transExpr(ch,tvs)) + B.Int(1))
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
      
      for ((id,ch) <- stateChannels) {
        stmts += Boogie.Assign(B.ChannelIdx(transExpr(ch,tvs),B.C(transExpr(ch,tvs))), transExpr(Id(id).withType(ch.typ),tvs) )
        stmts += Boogie.Assign(B.C(transExpr(ch,tvs)),B.C(transExpr(ch,tvs)) + B.Int(1))
      }
      
      for (q <- action.ensures) stmts += B.Assume(transExpr(q.expr,tvs))

      for (inv <- avs.entity.actionInvariants) stmts += BAssume(inv,avs)
    }
    
    for (opat <- schedule.contract.outputPattern) {
      stmts += B.Assert(
          B.Urd(transExpr(opat.portId,opat.typ,vs)) ==@ B.Int(opat.rate),
          opat.pos,
          "The correct amount of tokens might not be produced on output " + opat.portId)
    }
    
    for (q <- schedule.contract.ensures) {
      stmts += B.Assert(
          transExpr(q.expr,vs),
          q.expr.pos,
          "The contract postcondition might not hold")
    }
    
    for (inv <- avs.entity.contractInvariants) stmts += BAssert(inv, "Contract invariant might not be preserved", vs)
    
    return List(B.createProc(schedule.entity.id+B.Sep+schedule.contract.fullName, decls.toList:::stmts.toList, false))
  }
  
  def translateNetworkSchedule(
      scheduleCtx: ScheduleContext, 
      schedule: ContractSchedule, 
      nwvs: RootVerStruct[Network]): List[Boogie.Proc] = {
    
    if (!contractsToVerify.isEmpty && !contractsToVerify.contains(nwvs.entity.id -> schedule.contract.fullName)) {
      return List.empty
    }
    
    val decls = new collection.mutable.ListBuffer[Boogie.Stmt]
    val stmts = new collection.mutable.ListBuffer[Boogie.Stmt]
    val alreadyDeclared = collection.mutable.Set[String]()
    
    val allStateChannels = new collection.mutable.ListBuffer[Id]()
    
    for (e <- nwvs.entity.entities.get.entities) {
      val ivs = VerStruct.forInstance(nwvs, e, mergedActions)
      val stateVarsInGuards = ivs.guardStateVariables
      val stateChannels = ivs.stateChannelNames.filter{ case (id,_) => stateVarsInGuards.contains(id) }
      allStateChannels ++= stateChannels.unzip._2
      
      for (d <- ivs.declarations) {
        if (!alreadyDeclared.contains(d.name)) {
          decls += d.decl
          alreadyDeclared += d.name
        }
      }
      
    }
    
    val svs = VerStruct.forSchedule(nwvs, schedule, allStateChannels)
    
    for (d <- svs.declarations) {
      if (!alreadyDeclared.contains(d.name)) {
        decls += d.decl
        alreadyDeclared += d.name
      }
    }
    
    
    stmts ++= svs.assumes
    
    stmts += B.Assume(B.Mode(B.This) ==@ Boogie.VarExpr(schedule.contract.fullName))
    stmts += B.Assume(Boogie.VarExpr(BMap.R) ==@ Boogie.VarExpr(BMap.I))
    for (nwi <- svs.contractInvariants) stmts += BAssume(nwi, svs)
    for (chi <- svs.actionInvariants) stmts += BAssume(chi, svs)
    
    for (ioi <- svs.translatedIoInvariants(stmtTranslator)) stmts += B.Assume(ioi)
    
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
    
    for ((firing,idx) <- schedule.sequence.zipWithIndex) {
      val a1 = firing.action
      val e = firing.instance
      val action = a1.refinedContract.getOrElse(a1)
      
      val ivs = VerStruct.forInstance(nwvs, e, mergedActions)
      val acvs = VerStruct.forSubAction(ivs, action)
      
      val stateVarsInGuards = ivs.guardStateVariables
      val stateChannels = ivs.stateChannelNames.filter{ case (id,_) => stateVarsInGuards.contains(id) }
      
      for (d <- acvs.declarations) {
        if (!alreadyDeclared.contains(d.name)) {
          decls += d.decl
          alreadyDeclared += d.name
        }
      }
      
      stmts += Boogie.Comment("Instance: " + e.id + ", Action: " + action.fullName + ", Step: " + idx)
      
      for (ip <- e.actor.inports) {
        val cId = nwvs.connectionMap.getDst(PortRef(Some(e.id),ip.id))
        stmts += Boogie.Assign(B.Isub(cId), B.R(cId))
      }
      
      for (op <- e.actor.outports) {
        val cId = nwvs.connectionMap.getSrc(PortRef(Some(e.id),op.id))
        stmts += Boogie.Assign(B.Isub(cId), B.C(cId))
      }
      
      val firingRules = getFiringRules(e, acvs)
      
      for ((id,ch) <- stateChannels ) {
        stmts += B.Assume(B.C(transExpr(ch,ivs)) ==@ B.R(transExpr(ch,ivs)) + B.Int(1))
        stmts += B.Assume(B.ChannelIdx(transExpr(ch,ivs),B.R(transExpr(ch,ivs))) ==@ transExpr(Id(id).withType(ch.typ),ivs))
      }
      
      stmts += B.Assert(
          firingRules(action),
          action.pos,
          schedule.contract.fullName + ": Firing rule might not be satisfied for action '" + action.fullName + "' of instance '" + e.id +"'")
      
      for ((id,ch) <- stateChannels) {
        stmts += Boogie.Assign(B.R(transExpr(ch,ivs)),B.R(transExpr(ch,ivs)) + B.Int(1))
      } 
          
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
              stmts += Boogie.Assign(
                  transExpr(v,acvs), 
                  B.Fun("Map#Store" , transExpr(v,acvs) , B.Int(i) , B.ChannelIdx(id, v.typ, B.R(id)) )  )
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
      
      for ((id,ch) <- stateChannels) {
        stmts += Boogie.Assign(B.ChannelIdx(transExpr(ch,ivs),B.C(transExpr(ch,ivs))), transExpr(Id(id).withType(ch.typ),ivs) )
        stmts += Boogie.Assign(B.C(transExpr(ch,ivs)),B.C(transExpr(ch,ivs)) + B.Int(1))
      }
      
      for (post <- action.ensures) {
        stmts += B.Assume(transExprPrecondCheck(post.expr,acvs))
      }
      
      for (inv <- e.actor.streamInvariants(nwvs.useContracts)) stmts += B.Assume(transExpr(inv.expr,acvs))
      
    }
    
    for (opat <- schedule.contract.outputPattern) {
      stmts += B.Assert(
          B.Urd(transExpr(opat.portId,opat.typ,nwvs)) ==@ B.Int(opat.rate),
          opat.pos,
          "The correct amount of tokens might not be produced on output " + opat.portId)
    }
    
    for (q <- schedule.contract.ensures) {
      B.Assert(
          transExpr(q.expr,nwvs),
          q.pos,
          "The contract postcondition might not hold")
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
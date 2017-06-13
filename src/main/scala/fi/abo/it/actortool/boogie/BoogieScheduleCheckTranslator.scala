package fi.abo.it.actortool.boogie

import fi.abo.it.actortool._
import fi.abo.it.actortool.schedule._

class BoogieScheduleCheckTranslator extends EntityTranslator[ContractSchedule] with GeneralBackend[ScheduleContext,List[Boogie.Decl]] {
  
  val verificationStructureBuilder = new NetworkVerificationStructureBuilder(stmtTranslator,Resolver.EmptyContext)
  
  def invoke(scheduleCtx: ScheduleContext) = {
    
    scheduleCtx.schedules.flatMap {
      schedule => translateEntity(schedule)
    }
  }
  
  def translateEntity(schedule: ContractSchedule): List[Boogie.Decl] = {
    val decls = new collection.mutable.ListBuffer[Boogie.Stmt]
    val stmts = new collection.mutable.ListBuffer[Boogie.Stmt]
    val alreadyDeclared = collection.mutable.Set[String]()
    
    val nwvs = schedule.entity match {
      case nw: Network => verificationStructureBuilder.buildStructure(nw)
      case ba: BasicActor => throw new RuntimeException("Boogie schedule checker does not support basic actors yet")
    }
    
    for (inst <- nwvs.entities) {
      val actor = inst.actor
      
      /// This list includes contract actions if the entity has such, otherwise basic actions
      val priorityList = nwvs.entityData(inst).priorities
      
      val firingRules = (priorityList.keys map { ca => (ca, transSubActionFiringRules(inst, ca, nwvs)) }).toMap
    }
    
    decls ++= (nwvs.entityDecls map { _.decl })
    decls ++= nwvs.subactorVarDecls map { _.decl }
    
    stmts ++= nwvs.uniquenessConditions map { B.Assume(_) }
    stmts ++= nwvs.basicAssumes
    stmts += B.Assume(Boogie.VarExpr(BMap.R) ==@ Boogie.VarExpr(BMap.I))
    for (nwi <- nwvs.nwInvariants) stmts += BAssume(nwi, nwvs.renamings)
    for (chi <- nwvs.chInvariants) stmts += BAssume(chi, nwvs.renamings)
    
    for (ipat <- schedule.contract.inputPattern) {
      stmts += Boogie.Assign(
          B.C(transExpr(ipat.portId,ipat.typ)(nwvs.renamings)), 
          B.C(transExpr(ipat.portId,ipat.typ)(nwvs.renamings)) + B.Int(ipat.rate))
    }
    for (guard <- schedule.contract.guards) {
      stmts += B.Assume(transExpr(guard)(nwvs.renamings))
    }
    for (pre <- schedule.contract.requires) {
      stmts += B.Assume(transExpr(pre)(nwvs.renamings))
    }
    
    for ((e,a) <- schedule.sequence) {
      stmts += Boogie.Comment("Instance: " + e.id)
      
      val renamings = nwvs.subActionRenamings(e, a)
      for (d <- nwvs.getEntityActionData(e, a).declarations) {
        if (!alreadyDeclared.contains(d.name)) {
          decls += d.decl
          alreadyDeclared += d.name
        }
      }
      
      val firingRules = getFiringRules(e, nwvs)
      
      stmts += B.Assert(firingRules(a),a.pos,"Firing rule might not be satisfied for action '" + a.fullName + "' of instance '" + e.id +"'")
      
      for (ipat <- a.inputPattern) {
        val id = nwvs.connectionMap.getDst(PortRef(Some(e.id),ipat.portId))
        for (v <- ipat.vars) {
          stmts += Boogie.Assign(transExpr(v.id,v.typ)(renamings),B.ChannelIdx(id,v.typ,B.R(id)))
          stmts += Boogie.Assign(B.R(id), B.R(id) + B.Int(ipat.rate))
        }
      }
      for (opat <- a.outputPattern) {
        val id = nwvs.connectionMap.getSrc(PortRef(Some(e.id),opat.portId))
        for (e <- opat.exps) {
          stmts += Boogie.Assign(B.ChannelIdx(id,e.typ,B.C(id)),transExpr(e)(renamings))
          stmts += Boogie.Assign(B.C(id), B.C(id) + B.Int(opat.rate))
        }
      }
      
    }
    
    List(B.createProc(nwvs.entity.id+B.Sep+schedule.contract.fullName, decls.toList:::stmts.toList, false))
    
  }
  
  def getFiringRules(instance: Instance, nwvs: NetworkVerificationStructure) = {
    val actor = instance.actor
    // This list includes contract actions if the entity has such, otherwise basic actions
    val priorityList = nwvs.entityData(instance).priorities
    (priorityList.keys map { ca => (ca, transSubActionFiringRules(instance, ca, nwvs)) }).toMap
  }
  
}
package fi.abo.it.actortool.boogie

import fi.abo.it.actortool._
import fi.abo.it.actortool.schedule._

class BoogieScheduleCheckTranslator extends EntityTranslator[ScheduleContext] with GeneralBackend[ScheduleContext,List[Boogie.Decl]] {

  
  def invoke(scheduleCtx: ScheduleContext) = translateEntity(scheduleCtx)
  
  def translateEntity(scheduleCtx: ScheduleContext): List[Boogie.Decl] = {
    val verStructBuilder = new NetworkVerificationStructureBuilder(stmtTranslator,Resolver.EmptyContext)
    scheduleCtx.schedules.flatMap {
      schedule => translateSchedule(schedule,verStructBuilder)
    }
  }
  
  def translateSchedule(schedule: ContractSchedule, verStructBuilder: NetworkVerificationStructureBuilder) = {
    val decls = new collection.mutable.ListBuffer[Boogie.Stmt]
    val stmts = new collection.mutable.ListBuffer[Boogie.Stmt]
    val alreadyDeclared = collection.mutable.Set[String]()
    
    val nwvs = schedule.entity match {
      case nw: Network => verStructBuilder.buildStructure(nw)
      case ba: BasicActor => throw new RuntimeException("Boogie schedule checker does not support basic actors yet")
    }
    
//    for (inst <- nwvs.entities) {
//      
//      /// This list includes contract actions if the entity has such, otherwise basic actions
//      val priorityList = nwvs.entityData(inst).priorities
//      
//      val firingRules = (priorityList.keys map { ca => (ca, transSubActionFiringRules(inst, ca, nwvs)) }).toMap
//    }
    
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
    
    for ((e,a1) <- schedule.sequence) {
      
      val action = a1.refinedContract.getOrElse(a1)
      //decls+ ++= nwvs.getEntityActionData(e, action).declarations  map { _.decl }
      
      stmts += Boogie.Comment("Instance: " + e.id)
      val renamings = nwvs.subActionRenamings(e, action)
      for (d <- nwvs.getEntityActionData(e, action).declarations) {
        if (!alreadyDeclared.contains(d.name)) {
          decls += d.decl
          alreadyDeclared += d.name
        }
      }
      
      val firingRules = getFiringRules(e, nwvs)
      stmts += B.Assert(firingRules(action),action.pos,"Firing rule might not be satisfied for action '" + action.fullName + "' of instance '" + e.id +"'")
      
      for (pat <- action.inputPattern) {
        val id = nwvs.connectionMap.getDst(PortRef(Some(e.id),pat.portId))
        pat match {
          case ipat: InputPattern => {
            for (v <- ipat.vars) {
              stmts += Boogie.Assign(transExpr(v.id,v.typ)(renamings),B.ChannelIdx(id,v.typ,B.R(id)))
              stmts += Boogie.Assign(B.R(id), B.R(id) + B.Int(ipat.rate))
            }
          }
          case npat: NwPattern => {
            stmts += Boogie.Assign(B.R(id), B.R(id) plus B.Int(npat.rate))
          }
          case _ => assert(false)
        }
      }
      for (pat <- action.outputPattern) {
        val id = nwvs.connectionMap.getSrc(PortRef(Some(e.id),pat.portId))
        pat match {
          case opat: OutputPattern => {
            for (e <- opat.exps) {
              stmts += Boogie.Assign(B.ChannelIdx(id,e.typ,B.C(id)),transExpr(e)(renamings))
              stmts += Boogie.Assign(B.C(id), B.C(id) + B.Int(opat.rate))
            }
          }
          case npat: NwPattern => {
            stmts += Boogie.Assign(B.C(id),B.C(id) plus B.Int(npat.rate))
          }
          case _ => assert(false)
        }
        
      }
      
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
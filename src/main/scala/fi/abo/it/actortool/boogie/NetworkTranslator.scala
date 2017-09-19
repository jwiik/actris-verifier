package fi.abo.it.actortool.boogie

import fi.abo.it.actortool._
import scala.collection.mutable.ListBuffer
import fi.abo.it.actortool.ActorTool.TranslationException

class NetworkTranslator(
    val smokeTest: Boolean,
    val skipMutualExclusivenessCheck: Boolean,
    val typeCtx: Resolver.Context,
    val useContracts: Boolean) extends EntityTranslator[Network,Network] {

  
  def translateEntity(network: Network): Seq[BoogieTranslation[Network]] = {
    val nwvs = VerStruct.forNetwork(network,false)
    Seq(BoogieTranslation(network, translateNetwork(nwvs)))
  }
  
  def translateNetwork(nwvs: RootVerStruct[Network]): List[Boogie.Decl] = {
    val decls = new ListBuffer[Boogie.Decl]()

    decls ++= translateNetworkInit(nwvs)
    
    val (subActorProcs, subActorFiringRules) = translateSubActorExecutions(nwvs)
    decls ++= subActorProcs
    
    for (c <- nwvs.contracts) {
      decls ++= translateNetworkAction(c,nwvs,subActorFiringRules)
    }
  
    val contractActionFiringRules = new ListBuffer[(AbstractAction,Boogie.Expr)]
    for (a <- nwvs.contracts) {
      val firingRule = new ListBuffer[Boogie.Expr]
      for (p <- a.inputPattern) {
        firingRule += B.Int(p.rate) <= B.Urd(transExpr(nwvs.renamings(p.portId),nwvs))
      }
      firingRule ++= a.guards map { p => transExpr(p,nwvs) }
      
      contractActionFiringRules += (( a, firingRule.foldLeft(B.Bool(true): Boogie.Expr)((a,b) => a && b) ))
    }
    
    if (!skipMutualExclusivenessCheck) {
      createMutualExclusivenessCheck(nwvs,contractActionFiringRules.toList,Set.empty) match {
        case Some(proc) => decls += proc
        case None =>
      }
    }
    
    decls.toList
  }
  
  def createMutualExclusivenessCheck(
      nwvs: RootVerStruct[Network], guards: List[(AbstractAction,Boogie.Expr)], inpatDecls: Set[BDecl]): Option[Boogie.Proc] = {
    
    if (guards.size <= 1) return None
    
    val asgn = new ListBuffer[Boogie.Stmt]
    
    asgn ++= nwvs.declarations map { _.decl }
    asgn ++= nwvs.assumes
      
    asgn ++= createMEAssertionsRec(nwvs.entity,guards)
    return Some(B.createProc(Uniquifier.get(nwvs.namePrefix+B.Sep+"GuardWD"), asgn.toList, smokeTest))
    
  }
  
  def translateNetworkInit(nwvs: RootVerStruct[Network]): List[Boogie.Decl] = {
    
    val asgn = new ListBuffer[Boogie.Stmt]
    val connections = nwvs.entity.structure.get.connections
    val entities = nwvs.entity.entities.get.entities
//    asgn ++= (nwvs.entityDecls map { _.decl })
//    asgn ++= nwvs.subactorVarDecls map { _.decl }
//    asgn ++= nwvs.uniquenessConditions map {B.Assume(_)}
//    asgn ++= nwvs.basicAssumes
    asgn ++= nwvs.declarations map { _.decl }
    asgn ++= nwvs.assumes
    
    for (c <- connections) {
      asgn += B.Assume(B.C(transExpr(c.id,c.typ,nwvs)) ==@ B.Int(0))
      asgn += B.Assume(B.R(transExpr(c.id,c.typ,nwvs)) ==@ B.Int(0))
    }
    
    for (inst <- entities) {
      val ivs = VerStruct.forInstance(nwvs, inst, useContracts)
      
      val actor = inst.actor
      
      val parameterNames = actor.parameters map {x => val id = Id(x.id); id.typ = x.typ; id}
      for ((name,value) <- (parameterNames zip inst.arguments)) {
        // Add assumptions about the values of the actor parameters
        asgn += B.Assume(transExpr(name,ivs) ==@ transExpr(value,ivs))
      }
      
      val actions = if (actor.contractActions.isEmpty) actor.actorActions else actor.contractActions
      
      for (ca <- actions.filter(_.init)) {
        for (opat <- ca.outputPattern) {
          val cId = nwvs.connectionMap.getSrc(inst.id,opat.portId)
          for (e <- opat.asInstanceOf[OutputPattern].exps) {
            asgn += Boogie.Assign(B.ChannelIdx(cId,e.typ,B.C(cId)),transExpr(e,ivs))
            asgn += Boogie.Assign(B.C(cId),B.C(cId) plus B.Int(1))
          }
        }
      }

    }
    
    for (chi <- nwvs.actionInvariants) {
      if (!chi.assertion.free)
        asgn += BAssert(chi, "Initialization of network '" + nwvs.entity.id + "' might not establish the channel invariant", nwvs)
    }
    
    asgn += Boogie.Assign(Boogie.VarExpr(BMap.I), Boogie.VarExpr(BMap.R))
    for (nwi <- nwvs.contractInvariants) {
      if (!nwi.assertion.free) {
        asgn += BAssert(nwi,"Initialization of network '" + nwvs.entity.id + "' might not establish the network invariant",nwvs)
      }
    }
    
    val stmt = asgn.toList
    List(B.createProc(Uniquifier.get(nwvs.namePrefix+"init"),stmt,smokeTest))
  }
  
  def translateSubActorExecutions(nwvs: RootVerStruct[Network]) = {
    
    val boogieProcs = new ListBuffer[Boogie.Proc]()
    val nwFiringRules = new ListBuffer[Boogie.Expr]()
    
    for (inst <- nwvs.entities) {
      val ivs = VerStruct.forInstance(nwvs, inst, useContracts)
      val actor = inst.actor
      
      /// This list includes contract actions if the entity has such, otherwise basic actions
      val priorityList = ivs.priorities(useContracts)
      
      val firingRules = (priorityList.keys map { 
        ca => 
          val acvs = VerStruct.forSubAction(ivs, ca)
          (ca, transSubActionFiringRules(inst, ca, acvs)) 
      }).toMap
      
      for ((ca,higherPrioActions) <- priorityList) {
        if (!ca.init) {
          val procName = nwvs.namePrefix+B.Sep+actor.id+B.Sep+ca.fullName
          
          val higherPrioFiringRules = higherPrioActions map {a => firingRules(a) }
          
          val acvs = VerStruct.forSubAction(ivs, ca)
          val subActorStmt = transSubActionExecution(inst, ca, acvs, firingRules(ca))
          boogieProcs += B.createProc(Uniquifier.get(procName),subActorStmt,smokeTest)
        }
      }
      nwFiringRules ++= firingRules.values
    }
    
    (boogieProcs.toList, nwFiringRules.toList)
  }
  
  def transSubActionExecution(
      instance: Instance, 
      action: AbstractAction, 
      acvs: SubActionVerStruct,
      firingRule: Boogie.Expr): List[Boogie.Stmt] = {
    
    val actor = instance.actor
    
    val asgn = new ListBuffer[Boogie.Stmt]()
    
//    asgn ++= nwvs.entityDecls map { _.decl }
//    asgn ++= nwvs.subactorVarDecls  map { _.decl }
//    asgn ++= nwvs.uniquenessConditions map {B.Assume(_)}
//    asgn ++= nwvs.getEntityActionData(instance, action).declarations  map { _.decl }
//    
//    asgn ++= nwvs.basicAssumes
//    
    asgn ++= acvs.declarations.map { _.decl }
    asgn ++= acvs.assumes
    
    
    for (ip <- instance.actor.inports) {
      val cId = acvs.connectionMap.getDst(PortRef(Some(instance.id),ip.id))
      asgn += Boogie.Assign(B.Isub(cId), B.R(cId))
    }
    
    for (op <- instance.actor.outports) {
      val cId = acvs.connectionMap.getSrc(PortRef(Some(instance.id),op.id))
      asgn += Boogie.Assign(B.Isub(cId), B.C(cId))
    }
    
    asgn ++= (for (chi <- acvs.actionInvariants) yield BAssume(chi,acvs))  // Assume channel invariants
    
    asgn ++= acvs.parent.parent.translatedIoInvariants(stmtTranslator) map B.Assume
    
//    for ((pinv,renames) <- nwvs.publicSubInvariants) {
//      asgn += BAssume(pinv, renames)
//    }
    
//    val renamings = nwvs.subActionRenamings(instance, action)
//    
//    val replacementMap = nwvs.getEntityActionData(instance, action).replacements
//    
    asgn += B.Assume(firingRule)
    
    for (ipat <- action.inputPattern) {
      val cId = acvs.connectionMap.getDst(PortRef(Some(instance.id),ipat.portId))
      if (action.isContractAction) {
        asgn += Boogie.Assign(B.R(cId), B.R(cId) plus B.Int(ipat.rate))
      }
      else {
        val inputPat = ipat.asInstanceOf[InputPattern]
        if (inputPat.repeat == 1) {
          for (v <- inputPat.vars) {
            asgn += Boogie.Assign(transExpr(v.id,v.typ,acvs),B.ChannelIdx(cId,v.typ,B.R(cId)))
            asgn += Boogie.Assign(B.R(cId), B.R(cId) plus B.Int(1))
          }
        }
        else {
          val v = inputPat.vars(0)
          for (i <- 0 until inputPat.repeat) {
            asgn += Boogie.Assign(transExpr(v,acvs), B.Fun("Map#Store",transExpr(v,acvs) , B.Int(i) , B.ChannelIdx(cId, v.typ, B.R(cId)) )  )
            asgn += Boogie.Assign(B.R(cId), B.R(cId) plus B.Int(1))
          }
        }
      }
    }
    
    for (pre <- action.requires) {
      if (!pre.free) {
        asgn += B.Assert(transExprPrecondCheck(pre.expr,acvs),pre.pos,"Precondition might not hold for instance at " + instance.pos)
      }
    }
    
    asgn ++= generateHavoc(acvs.assignedVariables, acvs)
    
    for (opat <- action.outputPattern) {
      val cId = acvs.connectionMap.getSrc(PortRef(Some(instance.id),opat.portId))
      if (action.isContractAction) {
        asgn += Boogie.Assign(B.C(cId),B.C(cId) plus B.Int(opat.rate))
      }
      else {
        val outputPat = opat.asInstanceOf[OutputPattern]
        if (opat.repeat == 1) {
          for (e <- outputPat.exps) {
            asgn += Boogie.Assign(B.ChannelIdx(cId,e.typ,B.C(cId)),transExpr(e,acvs))
            asgn += Boogie.Assign(B.C(cId),B.C(cId) plus B.Int(1))
          }
        }
        else {
          val v = outputPat.exps(0)
          for (i <- 0 until opat.repeat) {
            asgn += Boogie.Assign(B.ChannelIdx(cId, v.typ, B.C(cId)), B.Fun("Map#Select",transExpr(v,acvs), B.Int(i)))
            asgn += Boogie.Assign(B.C(cId), B.C(cId) plus B.Int(1))
          }
        }
      }
    }
    
    for (post <- action.ensures) {
      asgn += B.Assume(transExprPrecondCheck(post.expr,acvs))
    }
    
    for (chi <- acvs.actionInvariants) {
      if (!chi.assertion.free) {
        val msg = 
            "Action at " + action.pos + " ('" + action.fullName + "') for actor instance '" + 
            instance.id + "' might not preserve the channel invariant"
        asgn += BAssert(chi, msg, acvs)
      }
    }
    
    asgn.toList
  }
  
  // Contract checking
  
  def translateNetworkAction(
    nwa: ContractAction, nwvs: RootVerStruct[Network], subactorFiringRules: List[Boogie.Expr]): List[Boogie.Decl] = {
  
    val boogieProcs = new ListBuffer[Boogie.Proc]()
    
    for (ipat <- nwa.inputPattern) {
      val stmt = translateNetworkInput(nwa, ipat, nwvs)
      boogieProcs += B.createProc(Uniquifier.get(nwvs.namePrefix+nwa.fullName+B.Sep+"input"+B.Sep+ipat.portId),stmt,smokeTest)
    }
    
    boogieProcs += transNetworkExit(nwa, nwvs, subactorFiringRules)
    
    boogieProcs.toList
  }
  
  def translateNetworkInput(action: ContractAction, pattern: NwPattern, nwvs: RootVerStruct[Network]) = {
    
    val asgn = new ListBuffer[Boogie.Stmt]()
    
    asgn ++= nwvs.declarations.map { _.decl }
    asgn ++= nwvs.assumes
    
//    asgn ++= (nwvs.entityDecls map { _.decl })
//    asgn ++= nwvs.subactorVarDecls  map { _.decl }
//    asgn ++= (nwvs.uniquenessConditions map { B.Assume(_) })
//    asgn ++= nwvs.basicAssumes
   // asgn += B.Assume(nwvs.actionRatePredicates(action))
    //asgn += B.Local("x", B.type2BType(IntType(-1)))
    
    asgn += B.Assume(B.Mode(B.This) ==@ Boogie.VarExpr(action.fullName))
    
    val portType = nwvs.entity.getInport(pattern.portId).get.portType
    
    asgn += 
      B.Assume(
          (B.C(transExpr(pattern.portId,ChanType(portType),nwvs)) - 
            B.I(transExpr(pattern.portId,ChanType(portType),nwvs))) < 
              B.Int(pattern.rate))
     
    for (chi <- nwvs.actionInvariants) {
      asgn += BAssume(chi, nwvs)
    }
    
    asgn ++= nwvs.translatedIoInvariants(stmtTranslator) map B.Assume
    
    asgn += Boogie.Assign(
        B.C(transExpr(pattern.portId,ChanType(portType),nwvs)),
        B.C(transExpr(pattern.portId,ChanType(portType),nwvs)) + B.Int(1))
    
    for (g <- action.guards) {
      asgn += B.Assume(transExpr(g,nwvs))
    }
    for (r <- action.requires) {
      asgn += B.Assume(transExpr(r.expr,nwvs))
    }
    
    
    for (chi <- nwvs.actionInvariants) {
      if (!chi.assertion.free) {
        asgn += BAssert(chi, "Channel invariant might be falsified by network input on port '" + pattern.portId + "' for contract '" + action.fullName + "'"  , nwvs)
      }
    }

    asgn.toList
  }
  
  def transNetworkExit(nwa: ContractAction, nwvs: RootVerStruct[Network], subactorFiringRules: List[Boogie.Expr]) = {
    // Network action exit
    
    val inputBounds = 
      nwvs.entity.inports.map { 
        p =>
          B.Assume(B.C(transExpr(p.id,p.portType,nwvs)) - B.I(transExpr(p.id,p.portType,nwvs)) ==@ B.Int(nwa.inportRate(p.id)))
      }
    
    val outputBounds = 
      nwvs.entity.outports.map { 
        p =>
          B.Assert(
              B.C(transExpr(p.id,p.portType,nwvs)) - B.I(transExpr(p.id,p.portType,nwvs)) ==@ B.Int(nwa.outportRate(p.id)),
              nwa.pos,
              "The correct number of tokens might not be produced on output '" + p.id +  "' for contract '" + nwa.fullName + "'" 
              )
      }
    
    val firingNegAssumes = subactorFiringRules map { fr => B.Assume(Boogie.UnaryExpr("!",fr)) }
    
    val asgn = new ListBuffer[Boogie.Stmt]
    
    asgn ++= nwvs.declarations.map { _.decl }
    asgn ++= nwvs.assumes
    
//    asgn ++= (nwvs.entityDecls map { _.decl })
//    asgn ++= (nwvs.subactorVarDecls  map { _.decl })
//    asgn ++= (nwvs.uniquenessConditions map {B.Assume(_)})
//    asgn ++= nwvs.basicAssumes
    asgn += B.Assume(B.Mode(B.This) ==@ Boogie.VarExpr(nwa.fullName))
//    asgn += B.Assume(nwvs.actionRatePredicates(nwa))
    
    for (chi <- nwvs.actionInvariants) {
      asgn += BAssume(chi,nwvs)
    }
    
    asgn ++= nwvs.translatedIoInvariants(stmtTranslator) map B.Assume
    
    asgn ++= inputBounds
    
    for (r <- nwa.requires) {
      asgn += B.Assume(transExpr(r.expr,nwvs))
    }
    
    asgn ++= firingNegAssumes
    asgn ++= outputBounds
    
    for (q <- nwa.ensures) {
      if (!q.free) {
        asgn += B.Assert(transExpr(q.expr,nwvs),q.pos,"Network action postcondition might not hold")
      }
    }
    
    for (c <- nwvs.connections) {
      c.to match {
        // Match network output channels
        case pf@PortRef(None,port) => {
          val name = nwvs.connectionMap.getDst(pf)
          asgn += Boogie.Assign(B.R(Boogie.VarExpr(name)), B.R(Boogie.VarExpr(name)) +  (B.Int(nwa.outportRate(port))))
        }
        case _ =>
      }
    }
    asgn += Boogie.Assign(Boogie.VarExpr(BMap.I), Boogie.VarExpr(BMap.R))
    for (chi <- nwvs.actionInvariants) {
      if (!chi.assertion.free) {
        asgn += BAssert(chi,"The network might not preserve the channel invariant for contract '" + nwa.fullName + "'" ,nwvs)
      }
    }
    
    for (nwi <- nwvs.contractInvariants) {
      if (!nwi.assertion.free) {
        asgn += BAssert(nwi,"The network might not preserve the network invariant for contract '" + nwa.fullName + "'",nwvs)
      }
    }
    
    B.createProc(Uniquifier.get(nwvs.namePrefix+nwa.fullName+"#exit"),asgn.toList,smokeTest)
  }
  
}

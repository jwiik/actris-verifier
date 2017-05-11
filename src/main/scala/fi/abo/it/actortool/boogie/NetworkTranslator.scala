package fi.abo.it.actortool.boogie

import fi.abo.it.actortool._
import scala.collection.mutable.ListBuffer
import fi.abo.it.actortool.ActorTool.TranslationException

class NetworkTranslator(
    val smokeTest: Boolean,
    val skipMutualExclusivenessCheck: Boolean,
    val typeCtx: Resolver.Context) extends EntityTranslator[Network] {
  
  val nwVerStructBuilder = new NetworkVerificationStructureBuilder(stmtTranslator,typeCtx)
  
  def translateEntity(network: Network): List[Boogie.Decl] = {
    val nwvs = nwVerStructBuilder.buildStructure(network)
    translateNetwork(nwvs)
  }
  
  def translateNetwork(nwvs: NetworkVerificationStructure): List[Boogie.Decl] = {
    val decls = new ListBuffer[Boogie.Decl]()

    decls ++= translateNetworkInit(nwvs)
    
    val (subActorProcs, subActorFiringRules) = translateSubActorExecutions(nwvs)
    decls ++= subActorProcs
    for (a <- nwvs.actions) {
      decls ++= translateNetworkAction(a,nwvs,subActorFiringRules)
    }

    decls.toList
  }
  
  def translateNetworkInit(nwvs: NetworkVerificationStructure): List[Boogie.Decl] = {
    
    val asgn = new ListBuffer[Boogie.Stmt]
    
    asgn ++= (nwvs.entityDecls map { _.decl })
    asgn ++= nwvs.subactorVarDecls map { _.decl }
    asgn ++= nwvs.uniquenessConditions map {B.Assume(_)}
    asgn ++= nwvs.basicAssumes
    
    for (c <- nwvs.connections) {
      asgn += B.Assume(B.C(transExpr(c.id,c.typ)(nwvs.nwRenamings)) ==@ B.Int(0))
      asgn += B.Assume(B.R(transExpr(c.id,c.typ)(nwvs.nwRenamings)) ==@ B.Int(0))
    }
    
    for (inst <- nwvs.entities) {
      
      val actor = inst.actor
      
      val renamings = nwvs.instanceRenamings(inst)
      
      val parameterNames = actor.parameters map {x => val id = Id(x.id); id.typ = x.typ; id}
      for ((name,value) <- (parameterNames zip inst.arguments)) {
        // Add assumptions about the values of the actor parameters
        asgn += B.Assume(transExpr(name)(renamings) ==@ transExpr(value)(renamings))
      }
      
      val actions = if (actor.contractActions.isEmpty) actor.actorActions else actor.contractActions
      
      for (ca <- actions.filter(_.init)) {
        for (opat <- ca.outputPattern) {
          val cId = nwvs.sourceMap(PortRef(Some(inst.id),opat.portId))
          for (e <- opat.asInstanceOf[OutputPattern].exps) {
            asgn += Boogie.Assign(B.ChannelIdx(cId,e.typ,B.C(cId)),transExpr(e)(renamings))
            asgn += Boogie.Assign(B.C(cId),B.C(cId) plus B.Int(1))
          }
        }
      }

    }
    
    for (chi <- nwvs.chInvariants) {
      if (!chi.assertion.free)
        asgn += BAssert(chi, "Initialization of network '" + nwvs.entity.id + "' might not establish the channel invariant", nwvs.nwRenamings)
    }
    
    asgn += Boogie.Assign(Boogie.VarExpr(BMap.I), Boogie.VarExpr(BMap.R))
    for (nwi <- nwvs.nwInvariants) {
      if (!nwi.assertion.free) 
        asgn += BAssert(nwi,"Initialization of network '" + nwvs.entity.id + "' might not establish the network invariant",nwvs.nwRenamings)
    }
    
    val stmt = asgn.toList
    List(B.createProc(Uniquifier.get(nwvs.namePrefix+"init"),stmt,smokeTest))
  }
  
  def translateSubActorExecutions(nwvs: NetworkVerificationStructure) = {
    
    val boogieProcs = new ListBuffer[Boogie.Proc]()
    val nwFiringRules = new ListBuffer[Boogie.Expr]()
    
    for (inst <- nwvs.entities) {
      val actor = inst.actor
      
      /// This list includes contract actions if the entity has such, otherwise basic actions
      val priorityList = nwvs.entityData(inst).priorities
      
      val firingRules = (priorityList.keys map { ca => (ca, transSubActionFiringRules(inst, ca, nwvs)) }).toMap
      
      for ((ca,higherPrioActions) <- priorityList) {
        if (!ca.init) {
          val procName = nwvs.namePrefix+B.Sep+actor.id+B.Sep+ca.fullName
          
          val higherPrioFiringRules = higherPrioActions map {a => firingRules(a) }
          
          val subActorStmt = transSubActionExecution(inst, ca, nwvs, firingRules(ca), higherPrioFiringRules)
          boogieProcs += B.createProc(Uniquifier.get(procName),subActorStmt,smokeTest)
        }
      }
      nwFiringRules ++= firingRules.values
    }
    
    (boogieProcs.toList, nwFiringRules.toList)
  }
  
  def translateNetworkAction(
      nwa: ContractAction, nwvs: NetworkVerificationStructure, subactorFiringRules: List[Boogie.Expr]): List[Boogie.Decl] = {
    
    val boogieProcs = new ListBuffer[Boogie.Proc]()
    
    for (ipat <- nwa.inputPattern) {
      val stmt = translateNetworkInput(nwa, ipat, nwvs)
      boogieProcs += B.createProc(Uniquifier.get(nwvs.namePrefix+nwa.fullName+B.Sep+"input"+B.Sep+ipat.portId),stmt,smokeTest)
    }
    
    boogieProcs += transNetworkExit(nwa, nwvs, subactorFiringRules)
    
    boogieProcs.toList
  }
  
  
  def transNetworkExit(nwa: ContractAction, nwvs: NetworkVerificationStructure, subactorFiringRules: List[Boogie.Expr]) = {
    // Network action exit
    
    val inputBounds = 
      nwvs.entity.inports.map { 
        p =>
          B.Assume(B.C(transExpr(p.id,p.portType)(nwvs.nwRenamings)) - B.I(transExpr(p.id,p.portType)(nwvs.nwRenamings)) ==@ B.Int(nwa.inportRate(p.id)))
      }
    
    val outputBounds = 
      nwvs.entity.outports.map { 
        p =>
          B.Assert(
              B.C(transExpr(p.id,p.portType)(nwvs.nwRenamings)) - B.I(transExpr(p.id,p.portType)(nwvs.nwRenamings)) ==@ B.Int(nwa.outportRate(p.id)),
              nwa.pos,
              "The correct number of tokens might not be produced on output '" + p.id +  "'"
              )
      }
    
    val firingNegAssumes = subactorFiringRules map { fr => B.Assume(Boogie.UnaryExpr("!",fr)) }
    
    val asgn = new ListBuffer[Boogie.Stmt]
    
    asgn ++= (nwvs.entityDecls map { _.decl })
    asgn ++= (nwvs.subactorVarDecls  map { _.decl })
    asgn ++= (nwvs.uniquenessConditions map {B.Assume(_)})
    asgn ++= nwvs.basicAssumes
    asgn += B.Assume(nwvs.actionRatePredicates(nwa))
    for (chi <- nwvs.chInvariants) {
      asgn += BAssume(chi,nwvs.nwRenamings)
    }
    for ((pinv,renames) <- nwvs.publicSubInvariants) {
      asgn += BAssume(pinv, renames)
    }
    asgn ++= inputBounds
    asgn ++= (nwa.requires.map { r => B.Assume(transExpr(r)(nwvs.nwRenamings)) })
    asgn ++= firingNegAssumes
    asgn ++= outputBounds
    asgn ++= (nwa.ensures.map { q => B.Assert(transExpr(q)(nwvs.nwRenamings),q.pos,"Network action postcondition might not hold") })
    for (c <- nwvs.connections) {
      c.to match {
        // Match network output channels
        case pf@PortRef(None,port) => {
          val name = nwvs.targetMap(pf)
          asgn += Boogie.Assign(B.R(Boogie.VarExpr(name)), B.R(Boogie.VarExpr(name)) +  (B.Int(nwa.outportRate(port))))
        }
        case _ =>
      }
    }
    asgn += Boogie.Assign(Boogie.VarExpr(BMap.I), Boogie.VarExpr(BMap.R))
    for (chi <- nwvs.chInvariants) {
      if (!chi.assertion.free) {
        asgn += BAssert(chi,"The network might not preserve the channel invariant",nwvs.nwRenamings)
      }
    }
    
    for (nwi <- nwvs.nwInvariants) {
      if (!nwi.assertion.free) {
        asgn += BAssert(nwi,"The network might not preserve the network invariant",nwvs.nwRenamings)
      }
    }
    
    B.createProc(Uniquifier.get(nwvs.namePrefix+nwa.fullName+"#exit"),asgn.toList,smokeTest)
  }
  
  def transSubActionFiringRules(
      instance: Instance, 
      action: AbstractAction, 
      nwvs: NetworkVerificationStructure) = {
    
    val firingCondsBuffer = new ListBuffer[Boogie.Expr]() // Gather firing conditions from each pattern
    val renamings = nwvs.subActionRenamings(instance, action)
    val replacementMap = nwvs.getEntityActionData(instance,action).replacements
    
    for (ipat <- action.inputPattern) {
      val cId = nwvs.targetMap(PortRef(Some(instance.id),ipat.portId))
      firingCondsBuffer += B.Int(ipat.rate) <= B.Urd(cId)
    }
    
    for (g <- action.guard) {
      val renamedGuard = IdReplacer.visitExpr(g)(replacementMap)
      val transGuard = transExpr(renamedGuard)(renamings)
      firingCondsBuffer += transGuard
    }
    
    firingCondsBuffer.reduceLeft((a,b) => a && b)
  }
  
  def transSubActionExecution(
      instance: Instance, 
      action: AbstractAction, 
      nwvs: NetworkVerificationStructure,
      firingRule: Boogie.Expr,
      higherPriorityGuards: List[Boogie.Expr]): List[Boogie.Stmt] = {
    
    val actor = instance.actor
    val asgn = new ListBuffer[Boogie.Stmt]()
    
    asgn ++= nwvs.entityDecls map { _.decl }
    asgn ++= nwvs.subactorVarDecls  map { _.decl }
    asgn ++= nwvs.uniquenessConditions map {B.Assume(_)}
    asgn ++= nwvs.getEntityActionData(instance, action).declarations  map { _.decl }
    
    asgn ++= nwvs.basicAssumes
    
    for (ip <- instance.actor.inports) {
      val cId = nwvs.targetMap(PortRef(Some(instance.id),ip.id))
      asgn += Boogie.Assign(B.Isub(cId), B.R(cId))
    }
    
    for (op <- instance.actor.outports) {
      val cId = nwvs.sourceMap(PortRef(Some(instance.id),op.id))
      asgn += Boogie.Assign(B.Isub(cId), B.C(cId))
    }
    
    asgn ++= (for (chi <- nwvs.chInvariants) yield BAssume(chi,nwvs.nwRenamings))  // Assume channel invariants
    
    for ((pinv,renames) <- nwvs.publicSubInvariants) {
      asgn += BAssume(pinv, renames)
    }
    
    val renamings = nwvs.subActionRenamings(instance, action)
    
    val replacementMap = nwvs.getEntityActionData(instance, action).replacements
    
    asgn += B.Assume(firingRule)
    
    for (ipat <- action.inputPattern) {
      var repeats = 0
      while (repeats < ipat.repeat) {
        val cId = nwvs.targetMap(PortRef(Some(instance.id),ipat.portId))
        if (action.isContractAction) {
          asgn += Boogie.Assign(B.R(cId), B.R(cId) plus B.Int(ipat.rate))
        }
        else {
          val inputPat = ipat.asInstanceOf[InputPattern]
          for (v <- inputPat.vars) {
            asgn += Boogie.Assign(transExpr(v.id,v.typ)(renamings),B.ChannelIdx(cId,v.typ,B.R(cId)))
            asgn += Boogie.Assign(B.R(cId), B.R(cId) plus B.Int(1))
          }
        }
        repeats = repeats+1
      }
    }
    
    for (pre <- action.requires) {
      asgn += B.Assert(
          transExprPrecondCheck(pre)(renamings),pre.pos,
          "Precondition might not hold for instance at " + instance.pos)
    }
    
    for (ev <- nwvs.getEntityActionData(instance, action).assignedVariables) {
      
      val hVar = Boogie.VarExpr(BMap.H)
      val qF = Boogie.VarExpr("f$")
      val qR = Boogie.VarExpr("r$")
      val qVars =
          List(Boogie.BVar("r$", BType.Ref),Boogie.BVar("f$", BType.ParamField("a")))
      val qExp1 = 
        hVar.apply(qR).apply(qF) ==@ Boogie.Old(hVar).apply(qR).apply(qF)
      
      ev match {
        case fa@FieldAccessor(r,f) => {
          val fieldName = B.FieldName(r.typ.asInstanceOf[RefType].name, f);
          val qExp2 = ((qR ==@ transExpr(r)(renamings)) && (qF ==@ Boogie.VarExpr(fieldName)))
          val frameCond = Boogie.Forall(List(Boogie.TVar("a")),qVars,Nil, (qExp1 || qExp2) )
          asgn += Boogie.Havoc(hVar)
          asgn += B.Assume(frameCond)
        }
        case id: Id => {
          if (id.typ.isRef) {
            val qExp2 = qR ==@ transExpr(id)(renamings)
            val frameCond = Boogie.Forall(List(Boogie.TVar("a")),qVars,Nil,qExp1 || qExp2)
            asgn += Boogie.Havoc(hVar)
            asgn += B.Assume(frameCond)
          }
          else {
            asgn += Boogie.Havoc(transExpr(ev)(renamings)) 
          }
        }
        case IndexAccessor(_,_) => throw new TranslationException(ev.pos, "")
      }
    }
    
    for (opat <- action.outputPattern) {
      val cId = nwvs.sourceMap(PortRef(Some(instance.id),opat.portId))
      var repeats = 0
      while (repeats < opat.repeat) {
        if (action.isContractAction) {
          asgn += Boogie.Assign(B.C(cId),B.C(cId) plus B.Int(opat.rate))
        }
        else {
          val outputPat = opat.asInstanceOf[OutputPattern]
          for (e <- outputPat.exps) {
            asgn += Boogie.Assign(B.ChannelIdx(cId,e.typ,B.C(cId)),transExpr(e)(renamings))
            asgn += Boogie.Assign(B.C(cId),B.C(cId) plus B.Int(1))
          }
        }
        repeats = repeats+1
      }
    }
    
    for (post <- action.ensures) {
      asgn += B.Assume(transExprPrecondCheck(post)(renamings))
    }
    
    for (chi <- nwvs.chInvariants) {
      if (!chi.assertion.free) {
        val msg = 
            "Action at " + action.pos + " ('" + action.fullName + "') for actor instance '" + 
            instance.id + "' might not preserve the channel invariant"
        asgn += BAssert(chi, msg, nwvs.nwRenamings)
      }
    }
    
    asgn.toList
  }
  
  
  def translateNetworkInput(action: ContractAction, pattern: NwPattern, nwvs: NetworkVerificationStructure) = {
    
    val asgn = new ListBuffer[Boogie.Stmt]()
    asgn ++= (nwvs.entityDecls map { _.decl })
    asgn ++= nwvs.subactorVarDecls  map { _.decl }
    asgn ++= (nwvs.uniquenessConditions map { B.Assume(_) })
    asgn ++= nwvs.basicAssumes
    asgn += B.Assume(nwvs.actionRatePredicates(action))
    //asgn += B.Local("x", B.type2BType(IntType(-1)))
    
    val portType = nwvs.entity.getInport(pattern.portId).get.portType
    
    asgn += 
      B.Assume(B.C(transExpr(pattern.portId,ChanType(portType))(nwvs.nwRenamings)) - B.I(transExpr(pattern.portId,ChanType(portType))(nwvs.nwRenamings)) < B.Int(pattern.rate))
     
    for (chi <- nwvs.chInvariants) {
      asgn += BAssume(chi, nwvs.nwRenamings)
    }
    
    for ((pinv,renames) <- nwvs.publicSubInvariants) {
      asgn += BAssume(pinv, renames)
    }
    asgn += Boogie.Assign(
        B.C(transExpr(pattern.portId,ChanType(portType))(nwvs.nwRenamings)),
        B.C(transExpr(pattern.portId,ChanType(portType))(nwvs.nwRenamings)) + B.Int(1))
        
    for (r <- action.requires) {
      asgn += B.Assume(transExpr(r)(nwvs.nwRenamings))
    }
    
    for (chi <- nwvs.chInvariants) {
      if (!chi.assertion.free) {
        asgn += BAssert(chi, "Channel invariant might be falsified by network input", nwvs.nwRenamings)
      }
    }

    asgn.toList
  }
}
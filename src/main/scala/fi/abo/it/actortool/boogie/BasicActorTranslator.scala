package fi.abo.it.actortool.boogie

import fi.abo.it.actortool._
import scala.collection.mutable.ListBuffer

class BasicActorTranslator(
    val smokeTest: Boolean,
    val skipMutualExclusivenessCheck: Boolean,
    val typeCtx: Resolver.Context) extends EntityTranslator[BasicActor] {

  val actorVerStructBuilder = new ActorVerificationStructureBuilder(stmtTranslator,typeCtx,true)
  
  def translateEntity(actor: BasicActor): List[Boogie.Decl] = {
    val avs = actorVerStructBuilder.buildStructure(actor)
    translateActor(avs)
  }
  
  def translateActor(avs: ActorVerificationStructure): List[Boogie.Decl] = {    
    val decls = new ListBuffer[Boogie.Decl]()
    val actionFiringRules = collection.mutable.Map[AbstractAction,(Boogie.Expr,Boogie.Expr)]()
    val nonLocalActionFiringRules = collection.mutable.Map[AbstractAction,(Boogie.Expr,Boogie.Expr)]()
    val actionInpatDecls = collection.mutable.Map[AbstractAction,List[BDecl]]()
    val actionRenamings = collection.mutable.Map[AbstractAction,Map[String,Id]]()
    var allInpatDecls = Set.empty[BDecl]
    
    val bFunDecls = translateFunctionDecl(avs)
    decls ++= bFunDecls
    
    decls += translateActorInit(avs)
    
    for (a <- avs.actorActions) {
      if (!a.init) {
        val (patterns,guards,nonLocalGuards,inpatDecls,renamings) = translateActorGuards(a, avs)
        allInpatDecls = allInpatDecls ++ inpatDecls
        actionFiringRules += (a -> (patterns,guards))
        nonLocalActionFiringRules += (a -> (patterns,nonLocalGuards))
        actionInpatDecls += (a -> inpatDecls)
        actionRenamings += (a -> renamings)
      }
    }
    
    for (a <- avs.actorActions) {
      if (!a.init) {
        val higherPrioActions = avs.priorityMap(a)
        val higherPrioGuards = higherPrioActions map { h => actionFiringRules(h) }
        decls ++= translateActorAction(a, avs, allInpatDecls.toList, avs.renamings ++ actionRenamings(a), actionFiringRules(a), higherPrioGuards)
      }
    }
    
    val allGuards = new ListBuffer[(AbstractAction,Boogie.Expr)]()
    //val supersetTests = new ListBuffer[Boogie.Expr]()
    
    for ((action,higherPrioActions) <- avs.priorityMap) {
      val (ownPattern,ownGuard) = nonLocalActionFiringRules(action)
      val negHigherPrioGuards = higherPrioActions map { a => { val (p,g) = nonLocalActionFiringRules(a); Boogie.UnaryExpr("!",p && g) } }

      val andedGuard = ownPattern && ownGuard
      
      val completeGuard = negHigherPrioGuards.foldLeft(B.Bool(true): Boogie.Expr)((g1,g2) => g1 && g2 ) && andedGuard
      allGuards += ((action,completeGuard))
    }
    
    if (!skipMutualExclusivenessCheck) {
      createMutualExclusivenessCheck(avs,allGuards.toList,allInpatDecls) match {
        case Some(proc) => decls += proc
        case None =>
      }
    }
    
    val contractActionFiringRules = new ListBuffer[(AbstractAction,Boogie.Expr)]
    for (a <- avs.contractActions) {
      val firingRule = new ListBuffer[Boogie.Expr]
      for (p <- a.inputPattern) {
        firingRule += B.Int(p.rate) <= B.Urd(p.portId)
        decls += translateContractActionInput(avs, p, a)
      }
      firingRule ++= a.guards map { p => transExpr(p)(avs.renamings) }
      decls ++= translateContractActionExit(avs, a, allGuards.toList)
      
      contractActionFiringRules += (( a, firingRule.foldLeft(B.Bool(true): Boogie.Expr)((a,b) => a && b) ))
    }
    
    if (!skipMutualExclusivenessCheck) {
      createMutualExclusivenessCheck(avs,contractActionFiringRules.toList,Set.empty) match {
        case Some(proc) => decls += proc
        case None =>
      }
    }
    
    decls.toList
  }
  
  def createMutualExclusivenessCheck(
      avs: ActorVerificationStructure, guards: List[(AbstractAction,Boogie.Expr)], inpatDecls: Set[BDecl]): Option[Boogie.Proc] = {
    
    val nonInitActions = (avs.actorActions.filter { a => !a.init }).size
    
    if (nonInitActions > 1) {      
      val decls = 
        (avs.actorVarDecls map { _.decl }) ::: 
        (inpatDecls map { _.decl }).toList ::: 
        List(B.Assume(avs.uniquenessCondition)) :::
        avs.basicAssumes :::
        avs.invariants.map { inv => B.Assume(transExpr(inv.expr)(avs.renamings)) } 
      
      val stmt = decls ::: createMEAssertionsRec(avs.entity,guards)
      Some(B.createProc(Uniquifier.get(avs.namePrefix+B.Sep+"GuardWD"), stmt, smokeTest))
    }
    else {
      None
    }
  }
  
  def translateActorInit(avs: ActorVerificationStructure) = {
    val asgn = new ListBuffer[Boogie.Stmt]
    //asgn ++= avs.channelDecls map { _.decl }
    asgn ++= avs.actorVarDecls map { _.decl }
    asgn ++= avs.actorParamDecls map { _.decl }
    asgn += B.Assume(avs.uniquenessCondition)
    asgn ++= avs.initAssumes
    
    val initAction = avs.actorActions.find { x => x.init } 
    initAction match {
      case Some(a) => {
        asgn ++= transStmt( a.body )(avs.renamings)
        for (q <- a.ensures) {
          if (!q.free) {
            asgn += B.Assert(transExpr(q.expr)(avs.renamings), q.pos, "Action postcondition might not hold")
          }
        }
        for (opat <- a.outputPattern) {
          val cId = opat.portId
          for (v <- opat.exps) {
            asgn += Boogie.Assign(B.ChannelIdx(cId, v.typ, B.C(cId)), transExpr(v)(avs.renamings))
            asgn += Boogie.Assign(B.C(cId), B.C(cId) plus B.Int(1))
          }
        }
      }
      case None =>
    }
    
    for (inv <- avs.invariants) {
      if (!inv.assertion.free) 
        asgn += B.Assert(transExpr(inv.expr)(avs.renamings),inv.expr.pos, "Initialization might not establish the invariant")
    }
    
    B.createProc(Uniquifier.get(avs.namePrefix+"init"),asgn.toList,smokeTest)
  }
  
  
  
  def translateActorAction(
      a: ActorAction, 
      avs: ActorVerificationStructure,
      inpatDecls: List[BDecl],
      renamings: Map[String,Id], 
      guard1: (Boogie.Expr,Boogie.Expr),
      higherPrioGuards: List[(Boogie.Expr,Boogie.Expr)]): List[Boogie.Decl] = {
     
    val asgn = new ListBuffer[Boogie.Stmt]
    val actionData = avs.actionData(a)
    
    //asgn ++= avs.channelDecls map { _.decl }
    asgn ++= avs.actorVarDecls map { _.decl }
    asgn ++= avs.actorParamDecls map { _.decl }
    asgn ++= inpatDecls map { _.decl }
    asgn ++= actionData.declarations map { _.decl }
    asgn += B.Assume(avs.uniquenessCondition)
    
    if (a.init) asgn ++= avs.initAssumes
    else asgn ++= avs.basicAssumes
     
    if (!a.init) {
      // Assume invariants
      asgn ++= (for (i <- avs.invariants) yield B.Assume(transExpr(i.expr)(avs.renamings)))
    }

    // Assume input pattern
    asgn ++= ( guard1 match { case (pat,_) => List(B.Assume(pat)) } )
     
    for (ipat <- a.inputPattern) {
      val cId = ipat.portId
      if (ipat.repeat == 1) {
        for (v <- ipat.vars) {
          asgn += Boogie.Assign(transExpr(v)(renamings), B.ChannelIdx(cId, v.typ, B.R(cId)))
          asgn += Boogie.Assign(B.R(cId), B.R(cId) plus B.Int(1))
        }
      }
      else {
        val v = ipat.vars(0)
        for (i <- 0 until ipat.repeat) {
          asgn += Boogie.Assign(transExpr(v)(renamings), B.Fun("Map#Store",transExpr(v)(renamings) , B.Int(i) , B.ChannelIdx(cId, v.typ, B.R(cId)) )  )
          asgn += Boogie.Assign(B.R(cId), B.R(cId) plus B.Int(1))
        }
      }
    }
    
    for (p <- a.requires) {
      asgn += B.Assume(transExpr(p.expr)(renamings))
    }

    asgn ++= higherPrioGuards map { case (pat,guard) => B.Assume(Boogie.UnaryExpr("!", /*pat &&*/ guard)) }
    
    asgn ++= ( guard1 match { case (_,guard) => List(B.Assume(guard)) } )
    asgn ++= actionData.variableInitialValues map { a => B.Assume(transExpr(a)(renamings) ) }
    asgn ++= transStmt( a.body )(renamings)
    
    for (q <- a.ensures) {
      if (!q.free) {
        asgn += B.Assert(transExpr(q.expr)(renamings), q.pos, "Action postcondition might not hold")
      }
    }
     
    for (opat <- a.outputPattern) {
      val cId = opat.portId
      if (opat.repeat == 1) {
        for (v <- opat.exps) {
          asgn += Boogie.Assign(B.ChannelIdx(cId, v.typ, B.C(cId)), transExpr(v)(renamings))
          asgn += Boogie.Assign(B.C(cId), B.C(cId) plus B.Int(1))
        }
      }
      else {
        val v = opat.exps(0)
        for (i <- 0 until opat.repeat) {
          asgn += Boogie.Assign(B.ChannelIdx(cId, v.typ, B.C(cId)), B.Fun("Map#Select",transExpr(v)(renamings), B.Int(i)))
          asgn += Boogie.Assign(B.C(cId), B.C(cId) plus B.Int(1))
        }
      }
    }
     
    for (inv <- avs.invariants) {
      if (!inv.assertion.free) 
        asgn += B.Assert(transExpr(inv.expr)(avs.renamings),inv.expr.pos, "Action '" + a.fullName +  "' at " + a.pos + " might not preserve the invariant")
    }
     
    val proc = B.createProc(Uniquifier.get(avs.namePrefix+a.fullName),asgn.toList,smokeTest)
     
    List(proc)
  }
  
  
  
  def generateCommonContractProcedureHeader(avs: ActorVerificationStructure, action: ContractAction) = {
    val asgn = new ListBuffer[Boogie.Stmt]
    
    //asgn ++= avs.channelDecls map { _.decl }
    asgn ++= avs.actorVarDecls map { _.decl }
    asgn ++= avs.actorParamDecls map { _.decl }
    asgn += B.Assume(avs.uniquenessCondition)
    asgn ++= avs.basicAssumes
    asgn += B.Assume(B.Mode(B.This) ==@ Boogie.VarExpr(action.fullName))
    
    for (op <- avs.entity.outports) {
      asgn += B.Assume(B.R(op.id) ==@ B.I(op.id))
    }
    
    asgn ++= { for (i <- avs.invariants) yield B.Assume(transExpr(i.expr)(avs.renamings)) }
    
    asgn.toList
  }
  
  
  def translateContractActionInput(avs: ActorVerificationStructure, pattern: NwPattern,  action: ContractAction) = {
    val asgn = new ListBuffer[Boogie.Stmt]
    asgn ++= generateCommonContractProcedureHeader(avs, action)
    
    val portType = avs.entity.getInport(pattern.portId).get.portType
    val portVar = transExpr(pattern.portId,ChanType(portType))(avs.renamings)
    asgn += B.Assume(B.C(portVar) - B.I(portVar) < B.Int(pattern.rate))
    
    asgn += Boogie.Assign(B.C(portVar), B.C(portVar) + B.Int(1))
        
    for (r <- action.requires) {
      asgn += B.Assume(transExpr(r.expr)(avs.renamings))
    }
    for (r <- action.guards) {
      asgn += B.Assume(transExpr(r)(avs.renamings))
    }
    
    for (chi <- avs.invariants) {
      if (!chi.assertion.free) {
        asgn += BAssert(chi, "Invariant might be falsified by actor input", avs.renamings)
      }
    }
    B.createProc(Uniquifier.get(avs.namePrefix+"contract"+B.Sep+action.fullName+B.Sep+"input"), asgn.toList, smokeTest)
  }
  
  
  def translateContractActionExit(avs: ActorVerificationStructure, action: ContractAction, guards: List[(AbstractAction, Boogie.Expr)]) = {
    val asgn = new ListBuffer[Boogie.Stmt]
    asgn ++= generateCommonContractProcedureHeader(avs, action)
    
    for (ip <- avs.entity.inports) {
      val rate = action.inportRate(ip.id)
      asgn += B.Assume(B.C(ip.id) - B.I(ip.id) ==@ B.Int(rate))
    }
      
    for (p <- action.requires) {
      asgn += B.Assume(transExpr(p.expr)(avs.renamings))
    }
    
    for ((_,g) <- guards) {
      asgn += B.Assume(Boogie.UnaryExpr("!",g))
    }
    
    for (op <- avs.entity.outports) {
      val rate = action.outportRate(op.id)
      asgn += B.Assert(B.C(op.id) - B.I(op.id) ==@ B.Int(rate),action.pos,
          "The correct number of tokens might not be produced on output '" + op.id + "' with contract '" + action.fullName + "'")
    }
    
    for (q <- action.ensures) {
      if (!q.free) {
        asgn += B.Assert(transExpr(q.expr)(avs.renamings),q.pos,"Contract action postcondition might not hold")
      }
    }
    
    for (op <- avs.entity.outports) {
      asgn += Boogie.Assign(B.R(Boogie.VarExpr(op.id)), B.R(Boogie.VarExpr(op.id)) +  (B.Int(action.outportRate(op.id))))
    }
    asgn += Boogie.Assign(Boogie.VarExpr(BMap.I), Boogie.VarExpr(BMap.R))
    
    for (inv <- avs.invariants) {
      if (!inv.assertion.free) {
        asgn += BAssert(inv,"The actor might not preserve the invariant with contract '" + action.fullName + "' at " + action.pos, avs.renamings)
      }
    }
    
    List(B.createProc(Uniquifier.get(avs.namePrefix+"contract"+B.Sep+action.fullName+B.Sep+"exit"), asgn.toList, smokeTest))
    
  }
  
  
}

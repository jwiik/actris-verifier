package fi.abo.it.actortool.boogie

import fi.abo.it.actortool._
import scala.collection.mutable.ListBuffer

class BasicActorTranslator(
    val smokeTest: Boolean,
    val skipMutualExclusivenessCheck: Boolean,
    val typeCtx: Resolver.Context,
    val checkContractActions: Boolean) extends EntityTranslator[BasicActor] {
  
  def translateEntity(actor: BasicActor): List[Boogie.Decl] = {
    val avs = VerStruct(actor, checkContractActions)
    translateActor(avs)
  }
  
  def translateActor(avs: ActorVerStruct): List[Boogie.Decl] = {    
    val decls = new ListBuffer[Boogie.Decl]()
    val actionFiringRules = collection.mutable.Map[AbstractAction,(Boogie.Expr,Boogie.Expr)]()
    val nonLocalActionFiringRules = collection.mutable.Map[AbstractAction,(Boogie.Expr,Boogie.Expr)]()
    val actionInpatDecls = collection.mutable.Map[AbstractAction,List[BDecl]]()
    val actionRenamings = collection.mutable.Map[AbstractAction,Map[String,Id]]()
    val gts = collection.mutable.Map[AbstractAction,GuardTranslation]()
    
    var allInpatDecls = Set.empty[BDecl]
    
    if (checkContractActions) {
      // Ugly hack
      decls ++= translateFunctionDecl(avs)
    }
    
    decls += translateActorInit(avs)
    
    for (a <- avs.entity.actorActions) {
      if (!a.init) {
        val gt = translateActorGuards(a, avs)
        gts += (a -> gt)
        allInpatDecls = allInpatDecls ++ gt.declarations
        actionFiringRules += (a -> (gt.pattern,gt.localGuard))
        nonLocalActionFiringRules += (a -> (gt.pattern,gt.localGuard))
        actionInpatDecls += (a -> gt.declarations.toList)
        actionRenamings += (a -> gt.renamings)
      }
    }
    
    for (a <- avs.entity.actorActions) {
      if (!a.init) {
        val higherPrioActions = avs.priorities(checkContractActions)(a)
        val higherPrioGuards = higherPrioActions map { h => actionFiringRules(h) }
        val vs = VerStruct(avs,a,gts(a))
        decls ++= translateActorAction(a, vs, higherPrioGuards)
      }
    }
    
    val allGuards = new ListBuffer[(AbstractAction,Boogie.Expr)]()
    //val supersetTests = new ListBuffer[Boogie.Expr]()
    
    for ((action,higherPrioActions) <- avs.priorities(checkContractActions)) {
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
    
    if (checkContractActions) {
      val contractActionFiringRules = new ListBuffer[(AbstractAction,Boogie.Expr)]
      for (a <- avs.contracts) {
        val firingRule = new ListBuffer[Boogie.Expr]
        for (p <- a.inputPattern) {
          firingRule += B.Int(p.rate) <= B.Urd(p.portId)
          decls += translateContractActionInput(avs, p, a)
        }
        firingRule ++= a.guards map { p => transExpr(p,avs) }
        decls ++= translateContractActionExit(avs, a, allGuards.toList)
        
        contractActionFiringRules += (( a, firingRule.foldLeft(B.Bool(true): Boogie.Expr)((a,b) => a && b) ))
      }
      
      if (!skipMutualExclusivenessCheck) {
        createMutualExclusivenessCheck(avs,contractActionFiringRules.toList,Set.empty) match {
          case Some(proc) => decls += proc
          case None =>
        }
      }
    }
    
    decls.toList
  }
  
  def createMutualExclusivenessCheck(
      avs: ActorVerStruct, guards: List[(AbstractAction,Boogie.Expr)], inpatDecls: Set[BDecl]): Option[Boogie.Proc] = {
    
    val nonInitActions = (avs.entity.actorActions.filter { a => !a.init }).size
    
    if (nonInitActions > 1) {      
      val decls: List[Boogie.Stmt] = 
        (avs.declarations map { _.decl }) ++ 
        (inpatDecls map { _.decl }).toList ++
        avs.assumes ++ 
        avs.entity.actorInvariants.map { inv => B.Assume(transExpr(inv.expr,avs)) } 
      
      val stmt = decls ::: createMEAssertionsRec(avs.entity,guards)
      Some(B.createProc(Uniquifier.get(avs.namePrefix+B.Sep+"GuardWD"), stmt, smokeTest))
    }
    else {
      None
    }
  }
  
  def translateActorInit(avs1: ActorVerStruct) = {
    //val renamings = avs.renamings
    
    val initAction = avs1.entity.actorActions.find( x => x.init ).get
    
    val vs = VerStruct(
        avs1,
        initAction,
        GuardTranslation(initAction,Seq.empty,Map.empty,B.Bool(true),B.Bool(true),B.Bool(true)))
    
    val asgn = new ListBuffer[Boogie.Stmt]
    
    asgn ++= vs.declarations map { _.decl }
    
    asgn ++= vs.assumes
    
    asgn ++= stmtTranslator.transStmt(initAction.body, TranslatorContext(vs.renamings,false,vs.stateChannelNames))
    
    //asgn ++= transStmt( a.body )(avs.renamings)
    for (q <- initAction.ensures) {
      if (!q.free) {
        asgn += B.Assert(transExpr(q.expr,vs), q.pos, "Action postcondition might not hold")
      }
    }
    for (opat <- initAction.outputPattern) {
      val cId = opat.portId
      for (v <- opat.exps) {
        asgn += Boogie.Assign(B.ChannelIdx(cId, v.typ, B.C(cId)), transExpr(v,vs))
        asgn += Boogie.Assign(B.C(cId), B.C(cId) plus B.Int(1))
      }
    }
    
    for ((id,ch) <- vs.stateChannelNames) {
      asgn += Boogie.Assign(
          B.ChannelIdx(transExpr(ch,vs),B.C(transExpr(ch,vs))), 
          transExpr(Id(id).withType(ch.typ),vs) )
      asgn += Boogie.Assign(B.C(transExpr(ch,vs)),B.C(transExpr(ch,vs)) + B.Int(1))
    }
    
    for (inv <- vs.parent.entity.actorInvariants) {
      if (!inv.assertion.free) 
        asgn += B.Assert(transExpr(inv.expr,vs),inv.expr.pos, "Initialization might not establish the invariant")
    }
    
    B.createProc(Uniquifier.get(vs.namePrefix+B.Sep+"init"),asgn.toList,smokeTest)
  }
  
  
  
  def translateActorAction(
      a: ActorAction, 
      vs: ActionVerStruct,
      higherPrioGuards: List[(Boogie.Expr,Boogie.Expr)]): List[Boogie.Decl] = {
     
    val asgn = new ListBuffer[Boogie.Stmt]
    
    val invariants = vs.parent.entity.actorInvariants

    asgn ++= vs.declarations map { _.decl }
    //asgn ++= vs.de map { _.decl }
    asgn ++= vs.assumes

//    if (a.init) asgn ++= avs.initAssumes
//    else asgn ++= avs.basicAssumes
     
    if (!a.init) {
      // Assume invariants
      asgn ++= (for (i <- invariants) yield B.Assume(transExpr(i.expr,vs.parent)))
    }

    for ((id,ch) <- vs.stateChannelNames) {
      asgn += B.Assume(B.ChannelIdx(transExpr(ch,vs),B.R(transExpr(ch,vs))) ==@ transExpr(Id(id).withType(ch.typ),vs))
      asgn += Boogie.Assign(B.R(transExpr(ch,vs)),B.R(transExpr(ch,vs)) + B.Int(1))
    }
    
    // Assume input pattern
    asgn += B.Assume(vs.guard.pattern)
    
    for (ipat <- a.inputPattern) {
      val cId = ipat.portId
      if (ipat.repeat == 1) {
        for (v <- ipat.vars) {
          asgn += Boogie.Assign(transExpr(v,vs), B.ChannelIdx(cId, v.typ, B.R(cId)))
          asgn += Boogie.Assign(B.R(cId), B.R(cId) plus B.Int(1))
        }
      }
      else {
        val v = ipat.vars(0)
        for (i <- 0 until ipat.repeat) {
          asgn += Boogie.Assign(transExpr(v,vs), B.Fun("Map#Store",transExpr(v,vs) , B.Int(i) , B.ChannelIdx(cId, v.typ, B.R(cId)) )  )
          asgn += Boogie.Assign(B.R(cId), B.R(cId) plus B.Int(1))
        }
      }
    }
    
    for (p <- a.requires) {
      asgn += B.Assume(transExpr(p.expr,vs))
    }

    asgn ++= higherPrioGuards map { case (pat,guard) => B.Assume(Boogie.UnaryExpr("!", /*pat &&*/ guard)) }
    
    asgn += B.Assume(vs.guard.localGuard)
    asgn ++= vs.actionVariableInits map { a => B.Assume(transExpr(a,vs) ) }
    
    asgn ++= transStmt(a.body, vs)
    
    for (q <- a.ensures) {
      if (!q.free) {
        asgn += B.Assert(transExpr(q.expr, vs), q.pos, "Action postcondition might not hold")
      }
    }
     
    for (opat <- a.outputPattern) {
      val cId = opat.portId
      if (opat.repeat == 1) {
        for (v <- opat.exps) {
          asgn += Boogie.Assign(B.ChannelIdx(cId, v.typ, B.C(cId)), transExpr(v,vs))
          asgn += Boogie.Assign(B.C(cId), B.C(cId) plus B.Int(1))
        }
      }
      else {
        val v = opat.exps(0)
        for (i <- 0 until opat.repeat) {
          asgn += Boogie.Assign(B.ChannelIdx(cId, v.typ, B.C(cId)), B.Fun("Map#Select",transExpr(v,vs), B.Int(i)))
          asgn += Boogie.Assign(B.C(cId), B.C(cId) plus B.Int(1))
        }
      }
    }
    
    for ((id,ch) <- vs.stateChannelNames) {
      asgn += Boogie.Assign(B.ChannelIdx(transExpr(ch,vs),B.C(transExpr(ch,vs))), transExpr(Id(id).withType(ch.typ),vs) )
      asgn += Boogie.Assign(B.C(transExpr(ch,vs)),B.C(transExpr(ch,vs)) + B.Int(1))
    }
     
    for (inv <- invariants) {
      if (!inv.assertion.free) 
        asgn += B.Assert(transExpr(inv.expr,vs.parent),inv.expr.pos, "Action '" + a.fullName +  "' at " + a.pos + " might not preserve the invariant")
    }
     
    val proc = B.createProc(Uniquifier.get(vs.namePrefix),asgn.toList,smokeTest)
     
    List(proc)
  }
  
  
  
  def generateCommonContractProcedureHeader(avs: VerStruct[BasicActor], action: ContractAction) = {
    val asgn = new ListBuffer[Boogie.Stmt]
    
    //asgn ++= avs.channelDecls map { _.decl }
    asgn ++= avs.declarations.map(_.decl)
    asgn ++= avs.assumes
    asgn += B.Assume(B.Mode(B.This) ==@ Boogie.VarExpr(action.fullName))
    
    for (op <- avs.entity.outports) {
      asgn += B.Assume(B.R(op.id) ==@ B.I(op.id))
    }
    
    asgn ++= { for (i <- avs.entity.actorInvariants) yield B.Assume(transExpr(i.expr,avs)) }
    
    asgn.toList
  }
  
  
  def translateContractActionInput(avs: VerStruct[BasicActor], pattern: NwPattern,  action: ContractAction) = {
    val asgn = new ListBuffer[Boogie.Stmt]
    asgn ++= generateCommonContractProcedureHeader(avs, action)
    
    val portType = avs.entity.getInport(pattern.portId).get.portType
    val portVar = transExpr(pattern.portId,ChanType(portType),avs)
    asgn += B.Assume(B.C(portVar) - B.I(portVar) < B.Int(pattern.rate))
    
    asgn += Boogie.Assign(B.C(portVar), B.C(portVar) + B.Int(1))
        
    for (r <- action.requires) {
      asgn += B.Assume(transExpr(r.expr,avs))
    }
    
    for (r <- action.guards) {
      asgn += B.Assume(transExpr(r,avs))
    }
    
    for (chi <- avs.entity.actorInvariants) {
      if (!chi.assertion.free) {
        asgn += BAssert(chi, "Invariant might be falsified by actor input", avs)
      }
    }
    B.createProc(Uniquifier.get(avs.namePrefix+"contract"+B.Sep+action.fullName+B.Sep+"input"), asgn.toList, smokeTest)
  }
  
  
  def translateContractActionExit(avs: VerStruct[BasicActor], action: ContractAction, guards: List[(AbstractAction, Boogie.Expr)]) = {
    val asgn = new ListBuffer[Boogie.Stmt]
    asgn ++= generateCommonContractProcedureHeader(avs, action)
    
    for (ip <- avs.entity.inports) {
      val rate = action.inportRate(ip.id)
      asgn += B.Assume(B.C(ip.id) - B.I(ip.id) ==@ B.Int(rate))
    }
      
    for (p <- action.requires) {
      asgn += B.Assume(transExpr(p.expr,avs))
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
        asgn += B.Assert(transExpr(q.expr,avs),q.pos,"Contract action postcondition might not hold")
      }
    }
    
    for (op <- avs.entity.outports) {
      asgn += Boogie.Assign(B.R(Boogie.VarExpr(op.id)), B.R(Boogie.VarExpr(op.id)) +  (B.Int(action.outportRate(op.id))))
    }
    asgn += Boogie.Assign(Boogie.VarExpr(BMap.I), Boogie.VarExpr(BMap.R))
    
    for (inv <- avs.entity.actorInvariants) {
      if (!inv.assertion.free) {
        asgn += BAssert(inv,"The actor might not preserve the invariant with contract '" + action.fullName + "' at " + action.pos,avs)
      }
    }
    
    List(B.createProc(Uniquifier.get(avs.namePrefix+"contract"+B.Sep+action.fullName+B.Sep+"exit"), asgn.toList, smokeTest))
    
  }
  
  
}

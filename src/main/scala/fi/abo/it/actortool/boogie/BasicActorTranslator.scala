package fi.abo.it.actortool.boogie

import fi.abo.it.actortool._
import scala.collection.mutable.ListBuffer

class BasicActorTranslator(
    val smokeTest: Boolean,
    val skipMutualExclusivenessCheck: Boolean,
    val typeCtx: Resolver.Context) extends EntityTranslator[BasicActor] {

  val actorVerStructBuilder = new ActorVerificationStructureBuilder(stmtTranslator,typeCtx)
  
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
        val (patterns,guards,nonLocalGuards,inpatDecls,renamings) = translateGuards(a, avs)
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
        asgn ++= (for (q <- a.ensures) yield {
          B.Assert(transExpr(q)(avs.renamings), q.pos, "Action postcondition might not hold")
        })
     
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
  
  def translateGuards(a: ActorAction, avs: ActorVerificationStructure): (Boogie.Expr,Boogie.Expr,Boogie.Expr,List[BDecl],Map[String,Id]) = {
    val renamingsBuffer = new ListBuffer[(String,Id)]
    
    val replacementBuffer = new ListBuffer[(String,Expr)]
    
    val inpatDeclBuffer = new ListBuffer[BDecl]
    val patterns = new ListBuffer[Boogie.Expr]
    for (ipat <- a.inputPattern) {
      for ((v,i) <- ipat.vars.zipWithIndex) {
        val name = ipat.portId+B.Sep+i.toString
        renamingsBuffer += ((v.id, {val id = Id(name); id.typ = v.typ; id} ))
        replacementBuffer += (( 
            v.id, 
            { 
              val e = Elements.chAcc(Elements.ch(ipat.portId,v.typ), Elements.next(ipat.portId, ChanType(v.typ), i)); 
              e.typ = v.typ; e 
            } 
        ))
        val lVar = B.Local(name, v.typ)
        inpatDeclBuffer += BDecl(name,lVar)
      }
      patterns += B.Int(ipat.vars.size) <= B.C(ipat.portId)-B.R(ipat.portId)
    }
    
    val renamings = avs.renamings ++ renamingsBuffer.toMap

    val guards =
       a.guards map { e => transExpr(e)(avs.renamings ++ renamingsBuffer.toMap) }
    // This version does not use variables local to the actions (input pattern variables)
    // It is used (at least) as assumptions in contract action checking
    val nonLocalGuards =
       a.guards map { e => transExpr(e)(avs.renamings ++ replacementBuffer.toMap) }
    
    val pattern = if (patterns.isEmpty) B.Bool(true) else patterns.reduceLeft((a,b) => a && b)
    val guard = if (guards.isEmpty) B.Bool(true) else guards.reduceLeft((a,b) => a && b)
    val nonLocalGuard = if (nonLocalGuards.isEmpty) B.Bool(true) else nonLocalGuards.reduceLeft((a,b) => a && b)
    (pattern, guard, nonLocalGuard, inpatDeclBuffer.toList, renamings)
  }
  
  def translateActorAction(
      a: ActorAction, 
      avs: ActorVerificationStructure,
      inpatDecls: List[BDecl],
      renamings: Map[String,Id], 
      guard1: (Boogie.Expr,Boogie.Expr),
      higherPrioGuards: List[(Boogie.Expr,Boogie.Expr)]): List[Boogie.Decl] = {
     
    val asgn = new ListBuffer[Boogie.Stmt]
    val (actionVars,actionVarAssumes) = avs.actionData(a)
    
    //asgn ++= avs.channelDecls map { _.decl }
    asgn ++= avs.actorVarDecls map { _.decl }
    asgn ++= avs.actorParamDecls map { _.decl }
    asgn ++= inpatDecls map { _.decl }
    asgn ++= actionVars map { _.decl }
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
       
      for (v <- ipat.vars) {
        asgn += Boogie.Assign(transExpr(v)(renamings), B.ChannelIdx(cId, v.typ, B.R(cId)))
        asgn += Boogie.Assign(B.R(cId), B.R(cId) plus B.Int(1))
      }
    }
     
    asgn ++= (for (p <- a.requires) yield {B.Assume(transExpr(p)(renamings)) })

    asgn ++= higherPrioGuards map { case (pat,guard) => B.Assume(Boogie.UnaryExpr("!", /*pat &&*/ guard)) }
    
    asgn ++= ( guard1 match { case (_,guard) => List(B.Assume(guard)) } )
    asgn ++= actionVarAssumes map { a => B.Assume(transExpr(a)(renamings) ) }
    asgn ++= transStmt( a.body )(renamings)
     
    asgn ++= (for (q <- a.ensures) yield {
      B.Assert(transExpr(q)(renamings), q.pos, "Action postcondition might not hold")
    })
     
    for (opat <- a.outputPattern) {
      val cId = opat.portId
      for (v <- opat.exps) {
        asgn += Boogie.Assign(B.ChannelIdx(cId, v.typ, B.C(cId)), transExpr(v)(renamings))
        asgn += Boogie.Assign(B.C(cId), B.C(cId) plus B.Int(1))
      }
    }
     
    for (inv <- avs.invariants) {
      if (!inv.assertion.free) 
        asgn += B.Assert(transExpr(inv.expr)(avs.renamings),inv.expr.pos, "Action '" + a.fullName +  "' at " + a.pos + " might not preserve the invariant")
    }
     
    val proc = B.createProc(Uniquifier.get(avs.namePrefix+a.fullName),asgn.toList,smokeTest)
     
    List(proc)
  }
  
  def translateFunctionDecl(avs: ActorVerificationStructure): List[Boogie.Function] = {
    avs.functionDecls map {
      fd => {
        Boogie.Function(
            avs.renamings(fd.name).id,
            fd.inputs map { i => Boogie.BVar(i.id, B.type2BType(i.typ)) },
            Boogie.BVar("out", B.type2BType(fd.output)))
      }
    }
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
      asgn += B.Assume(transExpr(r)(avs.renamings))
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
      asgn += B.Assume(transExpr(p)(avs.renamings))
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
      asgn += B.Assert(transExpr(q)(avs.renamings),q.pos,"Contract action postcondition might not hold")
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
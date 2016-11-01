package fi.abo.it.actortool.boogie

import scala.util.parsing.input.Position
import scala.collection.mutable.ListBuffer
import fi.abo.it.actortool.boogie.Boogie.DeclComment
import fi.abo.it.actortool.boogie.Boogie.VarExpr
import fi.abo.it.actortool.boogie.Boogie.MapSelect
import fi.abo.it.actortool.boogie.Boogie.BType
import fi.abo.it.actortool.boogie.Boogie.NamedType
import fi.abo.it.actortool.boogie.Boogie.LocalVar
import fi.abo.it.actortool.boogie.Boogie.UnaryExpr
import fi.abo.it.actortool.ActorTool.TranslationException
import fi.abo.it.actortool._ 

class Translator(
    val fixedBaseLength: Int, 
    val ftMode: Boolean, 
    val smokeTest: Boolean,
    val skipMutualExclusivenessCheck: Boolean,
    implicit val bvMode: Boolean) {  
  
  val stmtTranslator = new StmtExpTranslator(ftMode, bvMode); 
  val Inhalator = new Inhalator(stmtTranslator)
  val Exhalator = new Exhalator(stmtTranslator)
  
  final val Modifies = List(BMap.C, BMap.R, BMap.M, BMap.I):::
    (if (!ftMode) Nil else List(BMap.SqnCh, BMap.SqnActor))
  
  object Annot {
    final val Error = "error"
  }
  
  object Uniquifier {
    private var i = -1
    def get(id: String) = { i = i+1; id+B.Sep+(i.toString) }
  }
  
  def translateProgram(decls: List[TopDecl]): List[Boogie.Decl] = {
    val nwVerStructBuilder = new NetworkVerificationStructureBuilder()
    val actorVerStructBuilder = new ActorVerificationStructureBuilder()
    
    if (ftMode) BoogiePrelude.addComponent(SeqNumberingPL)
        
    val bProgram = decls flatMap {
      case a: BasicActor => {
        val avs = actorVerStructBuilder.buildStructure(a)
        translateActor(avs)
      }
      case n: Network => {
        val nwvs = nwVerStructBuilder.buildStructure(n)
        translateNetwork(nwvs)
      }
      case u: DataUnit => Nil
    }
    
    return bProgram
    
  }
  
  def translateActor(avs: ActorVerificationStructure): List[Boogie.Decl] = {    
    val decls = new ListBuffer[Boogie.Decl]()
    val actionGuards = collection.mutable.Map[Action,List[Boogie.Expr]]()
    val actionInpatDecls = collection.mutable.Map[Action,List[BDecl]]()
    val actionRenamings = collection.mutable.Map[Action,Map[String,Id]]()
    var allInpatDecls = Set.empty[BDecl]
    
    decls += translateActorInit(avs)
    
    for (a <- avs.actions) {
      if (!a.init) {
        val (guards,inpatDecls,renamings) = translateGuards(a, avs)
        allInpatDecls = allInpatDecls ++ inpatDecls
        actionGuards += (a -> guards)
        actionInpatDecls += (a -> inpatDecls)
        actionRenamings += (a -> renamings)
      }
    }
    
    for (a <- avs.actions) {
      if (!a.init) {
        val higherPrioGuards = avs.priorityMap(a) flatMap { h => actionGuards(h) }
        decls ++= translateActorAction(a, avs, actionInpatDecls(a), actionRenamings(a), actionGuards(a), higherPrioGuards)
      }
    }
    
    val allGuards = new ListBuffer[Boogie.Expr]()
    
    for ((action,higherPrioActions) <- avs.priorityMap) {
      val ownGuards = actionGuards(action)
      val higherPrioGuards = higherPrioActions flatMap { a => actionGuards(a) }
      
      val andedGuard =
        if (!ownGuards.isEmpty) ownGuards.reduceLeft((a,b) => (a && b))
        else B.Bool(true)
      
      val completeGuard = 
        if (!higherPrioGuards.isEmpty) 
          Boogie.UnaryExpr("!",higherPrioGuards.reduceLeft((a,b) => (a && b))) && andedGuard 
        else andedGuard
      allGuards += completeGuard
    }
    
    if (!skipMutualExclusivenessCheck) {
      createMutualExclusivenessCheck(avs,allGuards.toList,allInpatDecls) match {
        case Some(proc) => decls += proc
        case None =>
      }
    }
    
    decls.toList
  }
  
  def createMutualExclusivenessCheck(
      avs: ActorVerificationStructure, guards: List[Boogie.Expr], inpatDecls: Set[BDecl]): Option[Boogie.Proc] = {
    
    val nonInitActions = avs.actions.filter { a => !a.init }
    if (nonInitActions.size > 1) {
      
      val decls = 
        (avs.channelDecls map { _.decl }) ::: 
        (avs.actorVarDecls map { _.decl }) ::: 
        (inpatDecls map { _.decl }).toList ::: 
        List(B.Assume(avs.uniquenessCondition))
        
      val stmt = decls :::createMEAssertionsRec(avs.entity,guards)
      Some(createBoogieProc(Uniquifier.get(avs.namePrefix+B.Sep+"GuardWD"), stmt))
    }
    else None
  }
  
  def createMEAssertionsRec(a: DFActor, guards: List[Boogie.Expr]): List[Boogie.Assert] = {
    guards match {
      case first::rest => {
        val asserts = for (g <- rest) yield {
          B.Assert(
              Boogie.UnaryExpr("!", first && g) , a.pos, 
              "The actions of actor '" + a.id + "' might not have mutually exclusive guards")
        }
        asserts:::createMEAssertionsRec(a,rest)
      }
      case Nil => Nil
    }
  }
  
  def translateActorInit(avs: ActorVerificationStructure) = {
    val asgn = new ListBuffer[Boogie.Stmt]
    asgn ++= avs.channelDecls map { _.decl }
    asgn ++= avs.actorVarDecls map { _.decl }
    asgn ++= avs.actorParamDecls map { _.decl }
    asgn += B.Assume(avs.uniquenessCondition)
    asgn ++= avs.initAssumes
    
    val initAction = avs.actions.find { x => x.init } 
    initAction match {
      case Some(a) => {
        asgn ++= transStmt( a.body )(Map.empty)
        asgn ++= (for (q <- a.ensures) yield {
          B.Assert(transExpr(q)(Map.empty), q.pos, "Action postcondition might not hold")
        })
     
        for (opat <- a.outputPattern) {
          val cId = opat.portId
          for (v <- opat.exps) {
            asgn += Boogie.Assign(B.ChannelIdx(cId, B.C(cId)), transExpr(v)(Map.empty))
            asgn += Boogie.Assign(B.C(cId), B.C(cId) plus B.Int(1))
          }
        }
      }
      case None =>
    }
    

    
    for (inv <- avs.invariants) {
      if (!inv.assertion.free) 
        asgn += B.Assert(transExpr(inv.expr)(Map.empty),inv.expr.pos, "Initialization might not establish the invariant")
    }
    
    createBoogieProc(Uniquifier.get(avs.namePrefix+"init"),asgn.toList)
  }
  
  def translateGuards(a: Action, avs: ActorVerificationStructure): (List[Boogie.Expr],List[BDecl],Map[String,Id]) = {
    val renamingsBuffer = new ListBuffer[(String,Id)]
    val inpatDeclBuffer = new ListBuffer[BDecl]
    val readTokensRules = new ListBuffer[Boogie.Expr]
    for (ipat <- a.inputPattern) {
      for ((v,i) <- ipat.vars.zipWithIndex) {
        val name = ipat.portId+B.Sep+i.toString
        renamingsBuffer += ((v.id, Id(name)))
        val lVar = B.Local(name, v.typ)
        inpatDeclBuffer += BDecl(name,lVar)
      }
      readTokensRules += B.Int(ipat.vars.size) <= B.C(ipat.portId)-B.R(ipat.portId)
    }
    val renamings = renamingsBuffer.toMap
    val guards =
       (a.guard match {
         case None => Nil
         case Some(e) => List(transExpr(e)(renamings))
       })
    (readTokensRules.toList:::guards, inpatDeclBuffer.toList, renamings)
  }
  
  def translateActorAction(
      a: Action, 
      avs: ActorVerificationStructure,
      inpatDecls: List[BDecl],
      renamings: Map[String,Id], 
      guards: List[Boogie.Expr],
      higherPrioGuards: List[Boogie.Expr]): List[Boogie.Decl] = {
     
    val asgn = new ListBuffer[Boogie.Stmt]
    
    asgn ++= avs.channelDecls map { _.decl }
    asgn ++= avs.actorVarDecls map { _.decl }
    asgn ++= avs.actorParamDecls map { _.decl }
    asgn ++= inpatDecls map { _.decl }
    asgn += B.Assume(avs.uniquenessCondition)
    
    if (a.init) asgn ++= avs.initAssumes
    else asgn ++= avs.basicAssumes
     
     if (!a.init) {
       // Assume invariants
       asgn ++= (for (i <- avs.invariants) yield B.Assume(transExpr(i.expr)(Map.empty)))
     }
     
     val guards =
       (a.guard match {
         case None => Nil
         case Some(e) => List(transExpr(e)(renamings))
       })
     
     for (ipat <- a.inputPattern) {
       val cId = ipat.portId
       for (v <- ipat.vars) {
         asgn += Boogie.Assign(transExpr(v)(renamings), B.ChannelIdx(cId, B.R(cId)))
         asgn += Boogie.Assign(B.R(cId), B.R(cId) plus B.Int(1))
       }
     }
     
     asgn ++= (for (p <- a.requires) yield {B.Assume(transExpr(p)(renamings)) })
     
     asgn ++= higherPrioGuards map { g => B.Assume(Boogie.UnaryExpr("!",g)) }
     
     asgn ++= guards map {g => B.Assume(g)}
     
     asgn ++= transStmt( a.body )(renamings)
     
     asgn ++= (for (q <- a.ensures) yield {
       B.Assert(transExpr(q)(renamings), q.pos, "Action postcondition might not hold")
     })
     
     for (opat <- a.outputPattern) {
       val cId = opat.portId
       for (v <- opat.exps) {
         asgn += Boogie.Assign(B.ChannelIdx(cId, B.C(cId)), transExpr(v)(renamings))
         asgn += Boogie.Assign(B.C(cId), B.C(cId) plus B.Int(1))
       }
     }
     for (inv <- avs.invariants) {
       if (!inv.assertion.free) 
         asgn += B.Assert(transExpr(inv.expr)(Map.empty),inv.expr.pos, "Action at " + a.pos + " might not preserve invariant")
     }
     
     val proc = createBoogieProc(Uniquifier.get(avs.namePrefix+a.fullName),asgn.toList)
     
     List(proc)
   }
  

      
  def translateNetwork(nwvs: NetworkVerificationStructure): List[Boogie.Decl] = {
    val decls = new ListBuffer[Boogie.Decl]()

    decls ++= translateNetworkInit(nwvs)
    
    val (subActorProcs, subActorFiringRules) = translateSubActorExecutions(nwvs)
    decls ++= subActorProcs
    decls += translateNetworkEntry(nwvs, subActorFiringRules)
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
      asgn += B.Assume(B.C(transExpr(c.id)(nwvs.nwRenamings)) ==@ B.Int(0))
      asgn += B.Assume(B.R(transExpr(c.id)(nwvs.nwRenamings)) ==@ B.Int(0))
    }
    
    if (ftMode) {
      for (e <- nwvs.entities) {
        asgn += B.Assume(B.SqnAct(transExpr(e.id)(nwvs.nwRenamings)) ==@ B.Int(0))
      }
    }
    
    for (inst <- nwvs.entities) {
      
      val actor = inst.actor
      
      val renamings = nwvs.instanceRenamings(inst)
      
      val parameterNames = actor.parameters map {x => Id(x.id)}
      for ((name,value) <- (parameterNames zip inst.arguments)) {
        // Add assumptions about the values of the actor parameters
        asgn += B.Assume(transExpr(name)(renamings) ==@ transExpr(value)(renamings))
      }
      
      for (ca <- actor.actions filter(_.init)) {
        for (opat <- ca.outputPattern) {
          val cId = nwvs.sourceMap(PortRef(Some(inst.id),opat.portId))
          for (e <- opat.exps) {
            asgn += Boogie.Assign(B.ChannelIdx(cId,B.C(cId)),transExpr(e)(renamings))
            asgn += Boogie.Assign(B.C(cId),B.C(cId) plus B.Int(1))
          }
        }
      }
      
      for (inv <- actor.publicActorInvariants) {
        asgn += B.Assume(transExpr(inv.expr)(renamings))
      }

    }
    
    for (chi <- nwvs.chInvariants) {
      asgn += BAssert(chi, "Initialization of network '" + nwvs.entity.id + "' might not establish the channel invariant", nwvs.nwRenamings)
    }
    
    asgn += Boogie.Assign(Boogie.VarExpr(BMap.I), Boogie.VarExpr(BMap.R))
    for (nwi <- nwvs.nwInvariants) {
      asgn ++= Exhalator.visit(
          nwi, "Network initialization might not establish the network invariant", nwvs.nwRenamings)
    }
    
    val emptyChans = (for (c <- nwvs.connections) yield {
      B.Assert(B.Credit(transExpr(c.id)(nwvs.nwRenamings)) ==@ B.Int(0), c.pos, 
          "The initialization might produce unspecified tokens on channel " + c.id)
    })
    
    asgn ++= emptyChans
    
    val stmt = asgn.toList
    List(createBoogieProc(Uniquifier.get(nwvs.namePrefix+"init"),stmt))
  }
  
  def translateNetworkEntry(nwvs: NetworkVerificationStructure, firingRules: List[Boogie.Expr]) = {
    val asgn = new ListBuffer[Boogie.Stmt]
    asgn ++= (nwvs.entityDecls map { _.decl })
    asgn ++= nwvs.subactorVarDecls map { _.decl }
    asgn ++= nwvs.uniquenessConditions map {B.Assume(_)}
    asgn ++= nwvs.basicAssumes
    for (c <- nwvs.connections) {
      asgn += B.Assume(B.C(transExpr(c.id)(nwvs.nwRenamings)) ==@ B.R(transExpr(c.id)(nwvs.nwRenamings)))
    }
    for (nwi <- nwvs.nwInvariants) {
      asgn ++= Inhalator.visit(nwi, "", nwvs.nwRenamings)
    }
    for (chi <- nwvs.chInvariants) {
      asgn += BAssume(chi, nwvs.nwRenamings)
    }
    for ((inv,renames) <- nwvs.publicSubInvariants) {
      asgn += BAssume(inv, renames)
    }
    for (fr <- firingRules) {
      asgn += B.Assert(
          Boogie.UnaryExpr("!",fr), nwvs.entity.pos, 
          "Sub-actors in the network might fire without network input. This is not permitted.")
    }
    createBoogieProc(nwvs.namePrefix+"entry", asgn.toList)
  }
  
  def translateSubActorExecutions(nwvs: NetworkVerificationStructure) = {
    
    val boogieProcs = new ListBuffer[Boogie.Proc]()
    val nwFiringRules = new ListBuffer[Boogie.Expr]()
    
    for (inst <- nwvs.entities) {
      val actor = inst.actor
      
      val priorityList = nwvs.entityData(inst).priorities
      val firingRules = priorityList.keys map { ca => (ca, transSubActionFiringRules(inst, ca, nwvs)) } toMap

      for ((ca,higherPrioActions) <- priorityList) {
        if (!ca.init) {
          val procName = nwvs.namePrefix+B.Sep+actor.id+B.Sep+ca.fullName
          
          val higherPrioFiringRules = higherPrioActions map {a => firingRules(a) }
          
          val subActorStmt = transSubActionExecution(inst, ca, nwvs, firingRules(ca), higherPrioFiringRules)
          boogieProcs += createBoogieProc(Uniquifier.get(procName),subActorStmt)
        }
      }
      nwFiringRules ++= firingRules.values
    }
    
    (boogieProcs.toList, nwFiringRules.toList)
  }
  
  def translateNetworkAction(
      nwa: Action, nwvs: NetworkVerificationStructure, subactorFiringRules: List[Boogie.Expr]): List[Boogie.Decl] = {
    
    val boogieProcs = new ListBuffer[Boogie.Proc]()
    
    for (ipat <- nwa.inputPattern) {
      val stmt = translateNetworkInput(nwa, ipat, nwvs)
      boogieProcs += createBoogieProc(Uniquifier.get(nwvs.namePrefix+nwa.fullName+B.Sep+"input"+B.Sep+ipat.portId),stmt)
    }
    
    boogieProcs += transNetworkExit(nwa, nwvs, subactorFiringRules)
    
    boogieProcs.toList
  }
  
  
  def transNetworkExit(nwa: Action, nwvs: NetworkVerificationStructure, subactorFiringRules: List[Boogie.Expr]) = {
    // Network action exit
    
    val inputBounds = for (c <- nwvs.connections.filter { _.isInput }) yield {
      B.Assume(B.C(transExpr(c.id)(nwvs.nwRenamings)) - B.I(transExpr(c.id)(nwvs.nwRenamings)) ==@ B.Int(nwa.portInputCount(c.from.name)) /* B.BaseL*/)
    }
    
    val nwPre = for (r <- nwa.requires) yield 
      (r.pos,transExpr(r)(nwvs.nwRenamings))
    
    val nwPost = for (q <- nwa.ensures) yield 
      (q.pos,transExpr(q)(nwvs.nwRenamings))
    
    val firingNegAssumes = subactorFiringRules map { fr => B.Assume(Boogie.UnaryExpr("!",fr)) }
    
    val asgn = new ListBuffer[Boogie.Stmt]
    
    asgn ++= (nwvs.entityDecls map { _.decl })
    asgn ++= (nwvs.subactorVarDecls  map { _.decl })
    asgn ++= (nwvs.uniquenessConditions map {B.Assume(_)})
    asgn ++= nwvs.basicAssumes
    for (chi <- nwvs.chInvariants) {
      asgn += BAssume(chi,nwvs.nwRenamings)
    }
    for ((pinv,renames) <- nwvs.publicSubInvariants) {
      asgn += BAssume(pinv, renames)
    }
    asgn ++= inputBounds
    asgn ++= (nwPre.map { case (_,r) => B.Assume(r) })
    asgn ++= firingNegAssumes
    asgn ++= (nwPost.map { case (pos,q) => B.Assert(q,pos,"Network action postcondition might not hold") })
    for (c <- nwvs.connections) {
      c.to match {
        // Match network output channels
        case pf@PortRef(None,port) => {
          val name = nwvs.targetMap(pf)
          asgn += Boogie.Assign(B.R(Boogie.VarExpr(name)), B.R(Boogie.VarExpr(name)) +  (B.Int(nwa.portOutputCount(port))))
        }
        case _ =>
      }
    }
    asgn += Boogie.Assign(Boogie.VarExpr(BMap.I), Boogie.VarExpr(BMap.R))
    for (chi <- nwvs.chInvariants) {
      if (!chi.assertion.free)
        asgn += BAssert(chi,"The network might not preserve the channel invariant"  ,nwvs.nwRenamings)
    }
    
    for (nwi <- nwvs.nwInvariants) {
      if (!nwi.assertion.free)
        asgn ++= Exhalator.visit(nwi,"The network might not preserve the network invariant",nwvs.nwRenamings)
    }
    for (c <- nwvs.connections) {
      val msg =
        if (c.isOutput) "The network might not produce the specified number of tokens on output " + c.to.name
        else "The network might leave unread tokens on channel " + c.id
      asgn += B.Assert(B.C(transExpr(c.id)(nwvs.nwRenamings)) ==@ B.R(transExpr(c.id)(nwvs.nwRenamings)),nwa.pos, msg)
    } 
    
    createBoogieProc(Uniquifier.get(nwvs.namePrefix+nwa.fullName+"#exit"),asgn.toList)
  }
  
  def transSubActionFiringRules(
      instance: Instance, 
      action: Action, 
      nwvs: NetworkVerificationStructure) = {
    
    val firingCondsBuffer = new ListBuffer[Boogie.Expr]() // Gather firing conditions from each pattern
    val renamings = nwvs.subActionRenamings(instance, action)
    val replacementMap = nwvs.entityData(instance).actionData(action).replacements
    
    for (ipat <- action.inputPattern) {
      val cId = nwvs.targetMap(PortRef(Some(instance.id),ipat.portId))
      firingCondsBuffer += B.Int(ipat.numConsumed) lte B.Credit(cId)
    }
    
    val renamedGuard = action.guard match {
      case None =>
      case Some(g) =>
        val renamedGuard = IdReplacer.visitExpr(g)(replacementMap)
        val transGuard = transExpr(renamedGuard)(renamings)
        firingCondsBuffer += transGuard
    }
    
    firingCondsBuffer.reduceLeft((a,b) => a && b)
  }
  
  def transSubActionExecution(
      instance: Instance, 
      action: Action, 
      nwvs: NetworkVerificationStructure,
      firingRule: Boogie.Expr,
      higherPriorityGuards: List[Boogie.Expr]): List[Boogie.Stmt] = {
    
    val actor = instance.actor
    val asgn = new ListBuffer[Boogie.Stmt]()
    
    asgn ++= nwvs.entityDecls map { _.decl }
    asgn ++= nwvs.subactorVarDecls  map { _.decl }
    asgn ++= nwvs.uniquenessConditions map {B.Assume(_)}
    asgn ++= nwvs.entityData(instance).actionData(action).declarations  map { _.decl }
    
    asgn ++= nwvs.basicAssumes
    asgn ++= (for (chi <- nwvs.chInvariants) yield BAssume(chi,nwvs.nwRenamings))  // Assume channel invariants
    
    for ((pinv,renames) <- nwvs.publicSubInvariants) {
      asgn += BAssume(pinv, renames)
    }
    
    val renamings = nwvs.subActionRenamings(instance, action)
    
    val replacementMap = nwvs.entityData(instance).actionData(action).replacements
    
    
    
    asgn += B.Assume(firingRule)
    
    for (ActorInvariant(e,_,_) <- actor.actorInvariants) {
      asgn += B.Assume(transExpr(e.expr)(renamings))
    }
      
    for (ipat <- action.inputPattern) {
      var repeats = 0
      while (repeats < ipat.repeat) {
        val cId = nwvs.targetMap(PortRef(Some(instance.id),ipat.portId))
        for (v <- ipat.vars) {
          asgn += Boogie.Assign(transExpr(v.id)(renamings),B.ChannelIdx(cId,B.Read(cId)))
          asgn += Boogie.Assign(B.R(cId), B.R(cId) plus B.Int(1))
        }
        repeats = repeats+1
      }
    }
    
    for (pre <- action.requires) {
      asgn += B.Assert(
          transExpr(pre)(renamings),pre.pos,
          "Precondition might not hold for instance at " + instance.pos)
    }
    
    for (ev <- nwvs.entityData(instance).actionData(action).assignedVariables) {
      asgn += Boogie.Havoc(transExpr(ev)(renamings))
    }
        
    for (opat <- action.outputPattern) {
      val cId = nwvs.sourceMap(PortRef(Some(instance.id),opat.portId))
      var repeats = 0
      while (repeats < opat.repeat) {
        for (e <- opat.exps) {
          asgn += Boogie.Assign(B.ChannelIdx(cId,B.C(cId)),transExpr(e)(renamings))
          if (ftMode) {
            asgn += Boogie.Assign(B.SqnCh(cId,B.C(cId)),B.SqnAct(transExpr(instance.id)(nwvs.nwRenamings)))
          }
          asgn += Boogie.Assign(B.C(cId),B.C(cId) plus B.Int(1))
        }
        repeats = repeats+1
      }
    }
    
    for (post <- action.ensures) {
      asgn += B.Assume(transExpr(post)(renamings))
    }
    
    if (ftMode && action.aClass != ActionClass.Recovery) {
      asgn += Boogie.Assign(B.SqnAct(transExpr(instance.id)(nwvs.nwRenamings)),B.SqnAct(transExpr(instance.id)(nwvs.nwRenamings)) plus B.Int(1))
    }
    for (ActorInvariant(e,_,_) <- actor.actorInvariants) {
      asgn += B.Assume(transExpr(e.expr)(renamings))
    }
    
    for ((pinv,renames) <- nwvs.publicSubInvariants) {
      asgn += BAssume(pinv, renames)
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
  
  
  def translateNetworkInput(action: Action, pattern: InputPattern, nwvs: NetworkVerificationStructure) = {
    
    val asgn = new ListBuffer[Boogie.Stmt]()
    asgn ++= (nwvs.entityDecls map { _.decl })
    asgn ++= nwvs.subactorVarDecls  map { _.decl }
    asgn ++= (nwvs.uniquenessConditions map { B.Assume(_) })
    asgn ++= nwvs.basicAssumes
    asgn += B.Local("x", B.type2BType(IntType(32)))
    
    //asgn += B.Assume(B.C(transExpr(pattern.portId)(nwvs.nwRenamings)) < B.Int(pattern.vars.size))
     
    for (chi <- nwvs.chInvariants) {
      asgn += BAssume(chi, nwvs.nwRenamings)
    }
    
    for ((pinv,renames) <- nwvs.publicSubInvariants) {
      asgn += BAssume(pinv, renames)
    }
    asgn += B.Assume(B.Int(0) <= Boogie.VarExpr("x"))
    asgn += Boogie.Assign(
        B.C(transExpr(pattern.portId)(nwvs.nwRenamings)),
        B.C(transExpr(pattern.portId)(nwvs.nwRenamings)) + Boogie.VarExpr("x"))
        
    for (r <- action.requires) {
      asgn += B.Assume(transExpr(r)(nwvs.nwRenamings))
    }
    
    for (chi <- nwvs.chInvariants) {
      asgn += BAssert(chi, "Channel invariant might be falsified by network input", nwvs.nwRenamings)
    }

    asgn.toList
  }
  
  def createBoogieProc(name: String, stmt: List[Boogie.Stmt]) = {
    val body =
      if (smokeTest) stmt:::List(B.Assert(Boogie.BoolLiteral(false),"[smoke]"+ name))
      else stmt
    Boogie.Proc(name,Nil,Nil,Modifies,Nil,body)
  }
  
  def BAssume(chi: Invariant, renamings: Map[String,Expr]) = B.Assume(transExpr(chi.expr)(renamings))
  
  def BAssert(chi: Invariant, msg: String, renamings: Map[String,Expr]) = 
    B.Assert(transExpr(chi.expr)(renamings), chi.expr.pos, msg)
  
  def transExpr(id: String)(implicit renamings: Map[String,Expr]): Boogie.Expr = stmtTranslator.transExpr(Id(id))
  def transExpr(exp: Expr)(implicit renamings: Map[String,Expr]): Boogie.Expr = stmtTranslator.transExpr(exp)
  
  def transStmt(stmts: List[Stmt])(implicit renamings: Map[String,Expr]): List[Boogie.Stmt] = stmtTranslator.transStmt(stmts)

}

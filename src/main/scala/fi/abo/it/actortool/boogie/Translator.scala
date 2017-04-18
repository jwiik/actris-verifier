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
    val smokeTest: Boolean,
    val skipMutualExclusivenessCheck: Boolean) {  
  
  val stmtTranslator = new StmtExpTranslator(); 
  //val Inhalator = new Inhalator(stmtTranslator)
  //val Exhalator = new Exhalator(stmtTranslator)
  
  final val Modifies = List(BMap.C, BMap.R, BMap.M, BMap.I, BMap.H)//:::
//    (if (!ftMode) Nil else List(BMap.SqnCh, BMap.SqnActor)) 
  
  object Annot {
    final val Error = "error"
  }
  
  object Uniquifier {
    private var i = -1
    def get(id: String) = { i = i+1; id+B.Sep+(i.toString) }
  }
  
  def translateProgram(decls: List[TopDecl], typeCtx: Resolver.Context): List[Boogie.Decl] = {
    assert(typeCtx.getErrors.isEmpty)
    val nwVerStructBuilder = new NetworkVerificationStructureBuilder(typeCtx)
    val actorVerStructBuilder = new ActorVerificationStructureBuilder(typeCtx)
    
    //var userTypes = Map.empty[String,NamedType]
        
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
      case td: TypeDecl => {
        //userTypes += (td.tp.id -> NamedType(td.tp.id))
        for (f <- td.fields) yield {
          Boogie.Const(td.tp.id+"."+f.id,true,BType.Field(B.type2BType(f.typ)))
        }
      }
    }
    
    return bProgram
    
  }
  
  def translateActor(avs: ActorVerificationStructure): List[Boogie.Decl] = {    
    val decls = new ListBuffer[Boogie.Decl]()
    val actionFiringRules = collection.mutable.Map[AbstractAction,(Boogie.Expr,Boogie.Expr)]()
    val actionInpatDecls = collection.mutable.Map[AbstractAction,List[BDecl]]()
    val actionRenamings = collection.mutable.Map[AbstractAction,Map[String,Id]]()
    var allInpatDecls = Set.empty[BDecl]
    
    val bFunDecls = translateFunctionDecl(avs.functionDecls,avs.namePrefix)
    decls ++= bFunDecls
    
    decls += translateActorInit(avs)
    
    for (a <- avs.actorActions) {
      if (!a.init) {
        val (patterns,guards,inpatDecls,renamings) = translateGuards(a, avs)
        allInpatDecls = allInpatDecls ++ inpatDecls
        actionFiringRules += (a -> (patterns,guards))
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
      val (ownPattern,ownGuard) = actionFiringRules(action)
      val negHigherPrioGuards = higherPrioActions map { a => { val (p,g) = actionFiringRules(a); Boogie.UnaryExpr("!",p && g) } }

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
    
    decls.toList
  }
  
  def createMutualExclusivenessCheck(
      avs: ActorVerificationStructure, guards: List[(AbstractAction,Boogie.Expr)], inpatDecls: Set[BDecl]): Option[Boogie.Proc] = {
    
    val nonInitActions = (avs.actorActions.filter { a => !a.init }).size
    
    if (nonInitActions > 1) {      
      val decls = 
        (avs.channelDecls map { _.decl }) ::: 
        (avs.actorVarDecls map { _.decl }) ::: 
        (inpatDecls map { _.decl }).toList ::: 
        List(B.Assume(avs.uniquenessCondition))
      
      val stmt = decls ::: createMEAssertionsRec(avs.entity,guards)
      Some(createBoogieProc(Uniquifier.get(avs.namePrefix+B.Sep+"GuardWD"), stmt))
    }
    else {
      None
    }
  }
  
  def createMEAssertionsRec(a: DFActor, guards: List[(AbstractAction,Boogie.Expr)]): List[Boogie.Assert] = {
    guards match {
      case (action1,first)::rest => {
        val asserts = for ((action2,guard) <- rest) yield {
          B.Assert(
              Boogie.UnaryExpr("!", first && guard) , a.pos, 
              "The actions '" + action1.fullName + "' and '" + action2.fullName + "' of actor '" + a.id + "' might not have mutually exclusive guards")
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
    
//    if (ftMode) {
//      asgn += Boogie.Assign(B.SqnAct(B.This),B.Int(0))
//    }
    
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
    
    createBoogieProc(Uniquifier.get(avs.namePrefix+"init"),asgn.toList)
  }
  
  def translateGuards(a: ActorAction, avs: ActorVerificationStructure): (Boogie.Expr,Boogie.Expr,List[BDecl],Map[String,Id]) = {
    val renamingsBuffer = new ListBuffer[(String,Id)]
    val inpatDeclBuffer = new ListBuffer[BDecl]
    val patterns = new ListBuffer[Boogie.Expr]
    for (ipat <- a.inputPattern) {
      for ((v,i) <- ipat.vars.zipWithIndex) {
        val name = ipat.portId+B.Sep+i.toString
        renamingsBuffer += ((v.id, {val id = Id(name); id.typ = v.typ; id} ))
        val lVar = B.Local(name, v.typ)
        inpatDeclBuffer += BDecl(name,lVar)
      }
      patterns += B.Int(ipat.vars.size) <= B.C(ipat.portId)-B.R(ipat.portId)
    }
    val renamings = avs.renamings ++ renamingsBuffer.toMap
    val guards =
       (a.guard match {
         case None => Nil
         case Some(e) => List(transExpr(e)(renamings))
       })
    val pattern = if (patterns.isEmpty) B.Bool(true) else patterns.reduceLeft((a,b) => a && b)
    val guard = if (guards.isEmpty) B.Bool(true) else guards.reduceLeft((a,b) => a && b)
    (pattern, guard, inpatDeclBuffer.toList, renamings)
  }
  
  def translateActorAction(
      a: ActorAction, 
      avs: ActorVerificationStructure,
      inpatDecls: List[BDecl],
      renamings: Map[String,Id], 
      guards: (Boogie.Expr,Boogie.Expr),
      higherPrioGuards: List[(Boogie.Expr,Boogie.Expr)]): List[Boogie.Decl] = {
     
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
       asgn ++= (for (i <- avs.invariants) yield B.Assume(transExpr(i.expr)(avs.renamings)))
     }
     
     val guards =
       (a.guard match {
         case None => Nil
         case Some(e) => List(transExpr(e)(renamings))
       })
     
     for (ipat <- a.inputPattern) {
       val cId = ipat.portId
       
       for (v <- ipat.vars) {
         asgn += Boogie.Assign(transExpr(v)(renamings), B.ChannelIdx(cId, v.typ, B.R(cId)))
//         if (ftMode) asgn += Boogie.Assign(transExpr(v.id+"#sqn")(renamings), B.SqnCh(cId, B.R(cId)))
         asgn += Boogie.Assign(B.R(cId), B.R(cId) plus B.Int(1))
       }
     }
     
     asgn ++= (for (p <- a.requires) yield {B.Assume(transExpr(p)(renamings)) })
     
     asgn ++= higherPrioGuards map { case (pat,guard) => B.Assume(Boogie.UnaryExpr("!", pat && guard)) }
     
     asgn ++= guards map {g => B.Assume(g)}
     
     asgn ++= transStmt( a.body )(renamings)
     
     asgn ++= (for (q <- a.ensures) yield {
       B.Assert(transExpr(q)(renamings), q.pos, "Action postcondition might not hold")
     })
     
     for (opat <- a.outputPattern) {
       val cId = opat.portId
       for (v <- opat.exps) {
         asgn += Boogie.Assign(B.ChannelIdx(cId, v.typ, B.C(cId)), transExpr(v)(renamings))
//         if (ftMode) {
//           asgn += Boogie.Assign(B.SqnCh(cId, B.C(cId)), B.SqnAct(B.This))
//         }
         asgn += Boogie.Assign(B.C(cId), B.C(cId) plus B.Int(1))
         
       }
     }
     
//    if (ftMode) {
//      asgn += Boogie.Assign(B.SqnAct(B.This), B.SqnAct(B.This) plus B.Int(1))
//    }
     
     for (inv <- avs.invariants) {
       if (!inv.assertion.free) 
         asgn += B.Assert(transExpr(inv.expr)(avs.renamings),inv.expr.pos, "Action at " + a.pos + " might not preserve invariant")
     }
     
     val proc = createBoogieProc(Uniquifier.get(avs.namePrefix+a.fullName),asgn.toList)
     
     List(proc)
   }
  
  def translateFunctionDecl(funDecls: List[FunctionDecl], prefix: String): List[Boogie.Function] = {
    funDecls map {
      fd => {
        Boogie.Function(
            prefix+fd.name,
            fd.inputs map { i => Boogie.BVar(i.id, B.type2BType(i.typ)) },
            Boogie.BVar("out", B.type2BType(fd.output)))
      }
    }
  }

      
  def translateNetwork(nwvs: NetworkVerificationStructure): List[Boogie.Decl] = {
    val decls = new ListBuffer[Boogie.Decl]()

    decls ++= translateNetworkInit(nwvs)
    
    val (subActorProcs, subActorFiringRules) = translateSubActorExecutions(nwvs)
    decls ++= subActorProcs
//    decls += translateNetworkEntry(nwvs, subActorFiringRules)
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
    
//    if (ftMode) {
//      for (e <- nwvs.entities) {
//        asgn += B.Assume(B.SqnAct(transExpr(e.id)(nwvs.nwRenamings)) ==@ B.Int(0))
//      }
//    }
    
    for (inst <- nwvs.entities) {
      
      val actor = inst.actor
      
      val renamings = nwvs.instanceRenamings(inst)
      
      val parameterNames = actor.parameters map {x => val id = Id(x.id); id.typ = x.typ; id}
      for ((name,value) <- (parameterNames zip inst.arguments)) {
        // Add assumptions about the values of the actor parameters
        asgn += B.Assume(transExpr(name)(renamings) ==@ transExpr(value)(renamings))
      }
      
      for (ca <- actor.actions filter(_.init)) {
        for (opat <- ca.outputPattern) {
          val cId = nwvs.sourceMap(PortRef(Some(inst.id),opat.portId))
          for (e <- opat.asInstanceOf[OutputPattern].exps) {
            asgn += Boogie.Assign(B.ChannelIdx(cId,e.typ,B.C(cId)),transExpr(e)(renamings))
            asgn += Boogie.Assign(B.C(cId),B.C(cId) plus B.Int(1))
          }
        }
      }
      
//      for (inv <- actor.publicActorInvariants) {
//        //asgn += B.Assume(transExpr(inv.expr)(renamings))
//        val (_,stmt) = Inhalator.visit(inv.expr, "", renamings)
//        asgn ++= stmt
//      }

    }
    
    for (chi <- nwvs.chInvariants) {
      if (!chi.assertion.free)
        asgn += BAssert(chi, "Initialization of network '" + nwvs.entity.id + "' might not establish the channel invariant", nwvs.nwRenamings)
    }
    
    //val tokenChs = new scala.collection.mutable.HashSet[String]
    asgn += Boogie.Assign(Boogie.VarExpr(BMap.I), Boogie.VarExpr(BMap.R))
    for (nwi <- nwvs.nwInvariants) {
      //val (chs,asserts) = Exhalator.visit(nwi, "Network initialization might not establish the network invariant", nwvs.nwRenamings)
      if (!nwi.assertion.free) 
        asgn += BAssert(nwi,"Initialization of network '" + nwvs.entity.id + "' might not establish the network invariant",nwvs.nwRenamings)
      //tokenChs ++= chs
    }
    
//    for (c <- nwvs.connections.filter(c => !tokenChs.contains(c.id))) {
//      asgn += B.Assert(B.Urd(transExpr(c.id)(nwvs.nwRenamings)) ==@ B.Int(0), 
//          c.pos, "The initialization might produce unspecified tokens on channel " + c.id)
//    }
    
    val stmt = asgn.toList
    List(createBoogieProc(Uniquifier.get(nwvs.namePrefix+"init"),stmt))
  }
  
//  def translateNetworkEntry(nwvs: NetworkVerificationStructure, firingRules: List[Boogie.Expr]) = {
//    val asgn = new ListBuffer[Boogie.Stmt]
//    asgn ++= (nwvs.entityDecls map { _.decl })
//    asgn ++= nwvs.subactorVarDecls map { _.decl }
//    asgn ++= nwvs.uniquenessConditions map {B.Assume(_)}
//    asgn ++= nwvs.basicAssumes
//    for (c <- nwvs.connections) {
//      asgn += B.Assume(B.C(transExpr(c.id)(nwvs.nwRenamings)) ==@ B.R(transExpr(c.id)(nwvs.nwRenamings)))
//    }
//    for (nwi <- nwvs.nwInvariants) {
//      val (chs,asserts) = Inhalator.visit(nwi, "", nwvs.nwRenamings)
//      asgn ++= asserts
//    }
//    for (chi <- nwvs.chInvariants) {
//      asgn += BAssume(chi, nwvs.nwRenamings)
//    }
//    for ((inv,renames) <- nwvs.publicSubInvariants) {
//      val (_,stmt) = Inhalator.visit(inv.expr, "", renames)
//      asgn ++= stmt
//    }
//    for (fr <- firingRules) {
//      asgn += B.Assert(
//          Boogie.UnaryExpr("!",fr), nwvs.entity.pos, 
//          "Sub-actors in the network might fire without network input. This is not permitted.")
//    }
//    createBoogieProc(nwvs.namePrefix+"entry", asgn.toList)
//  }
  
  def translateSubActorExecutions(nwvs: NetworkVerificationStructure) = {
    
    val boogieProcs = new ListBuffer[Boogie.Proc]()
    val nwFiringRules = new ListBuffer[Boogie.Expr]()
    
    for (inst <- nwvs.entities) {
      val actor = inst.actor
      
      val priorityList = nwvs.entityData(inst).priorities
      val firingRules = (priorityList.keys map { ca => (ca, transSubActionFiringRules(inst, ca, nwvs)) }).toMap
      
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
      nwa: ContractAction, nwvs: NetworkVerificationStructure, subactorFiringRules: List[Boogie.Expr]): List[Boogie.Decl] = {
    
    val boogieProcs = new ListBuffer[Boogie.Proc]()
    
    for (ipat <- nwa.inputPattern) {
      val stmt = translateNetworkInput(nwa, ipat, nwvs)
      boogieProcs += createBoogieProc(Uniquifier.get(nwvs.namePrefix+nwa.fullName+B.Sep+"input"+B.Sep+ipat.portId),stmt)
    }
    
    boogieProcs += transNetworkExit(nwa, nwvs, subactorFiringRules)
    
    boogieProcs.toList
  }
  
  
  def transNetworkExit(nwa: ContractAction, nwvs: NetworkVerificationStructure, subactorFiringRules: List[Boogie.Expr]) = {
    // Network action exit
    
    val inputBounds = for (c <- nwvs.connections.filter { _.isInput }) yield {
      if (nwa.inportRate(c.from.name) > 0)
        B.Assume(
            B.C(transExpr(c.id,c.typ)(nwvs.nwRenamings)) - B.I(transExpr(c.id,c.typ)(nwvs.nwRenamings)) 
            ==@ B.Int(nwa.inportRate(c.from.name)))
      else B.Assume(B.Bool(true))
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
    asgn += B.Assume(nwvs.actionRatePredicates(nwa))
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
          asgn += Boogie.Assign(B.R(Boogie.VarExpr(name)), B.R(Boogie.VarExpr(name)) +  (B.Int(nwa.outportRate(port))))
        }
        case _ =>
      }
    }
    asgn += Boogie.Assign(Boogie.VarExpr(BMap.I), Boogie.VarExpr(BMap.R))
    for (chi <- nwvs.chInvariants) {
      if (!chi.assertion.free)
        asgn += BAssert(chi,"The network might not preserve the channel invariant"  ,nwvs.nwRenamings)
    }
    
    //val tokenChs = new scala.collection.mutable.HashSet[String]
    for (nwi <- nwvs.nwInvariants) {
      if (!nwi.assertion.free) {
        asgn += BAssert(nwi,"The network might not preserve the network invariant",nwvs.nwRenamings)
        //tokenChs ++= chs
      }
    }
//    for (c <- nwvs.connections.filter(c => !tokenChs.contains(c.id))) {
//      val msg =
//        if (c.isOutput) "The network might not produce the specified number of tokens on output " + c.to.name
//        else "The network might leave unread tokens on channel " + c.id
//      asgn += B.Assert(B.Urd(transExpr(c.id)(nwvs.nwRenamings)) ==@ B.Int(0),nwa.pos, msg)
//    } 
    
    createBoogieProc(Uniquifier.get(nwvs.namePrefix+nwa.fullName+"#exit"),asgn.toList)
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
    //nwvs.chInvariants foreach { chi => chi.expr.typ != null }
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
          transExpr(pre)(renamings),pre.pos,
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
      asgn += B.Assume(transExpr(post)(renamings))
    }
    
//    if (ftMode && action.aClass != ActionClass.Recovery) {
//      asgn += Boogie.Assign(B.SqnAct(transExpr(instance.id)(nwvs.nwRenamings)),B.SqnAct(transExpr(instance.id)(nwvs.nwRenamings)) plus B.Int(1))
//    }
    
//    for (ActorInvariant(e,_,_) <- actor.actorInvariants) {
//      val (_,stmt) = Inhalator.visit(e.expr, "", renamings)
//      asgn ++= stmt
//    }
    
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
    //asgn += B.Assume(B.Int(0) <= B.Int(1))
    asgn += Boogie.Assign(
        B.C(transExpr(pattern.portId,ChanType(portType))(nwvs.nwRenamings)),
        B.C(transExpr(pattern.portId,ChanType(portType))(nwvs.nwRenamings)) + B.Int(1))
        
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
  
  def BAssert(chi: Invariant, msg: String, renamings: Map[String,Expr]) = {
    val completeMsg = chi.assertion.msg match {
      case None => msg
      case Some(m) => msg + ": " + m
    }
    B.Assert(transExpr(chi.expr)(renamings), chi.expr.pos, completeMsg)
  }
  
  def transExpr(id: String, t: Type)(implicit renamings: Map[String,Expr]): Boogie.Expr = {
    val i = Id(id)
    i.typ = t
    transExpr(i)
  }
  def transExpr(exp: Expr)(implicit renamings: Map[String,Expr]): Boogie.Expr = {
    val (expr,ctx) = stmtTranslator.transExpr(exp)
    expr
  }
  
  def transStmt(stmts: List[Stmt])(implicit renamings: Map[String,Expr]): List[Boogie.Stmt] = {
    val (bStmt,ctx) = stmtTranslator.transStmt(stmts)
    bStmt
  }

}
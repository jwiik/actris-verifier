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
  //val Inhalator = new Inhalator(stmtTranslator)
  val Exhalator = new Exhalator(stmtTranslator)
  
  final val Modifies = List(BMap.C, BMap.R, BMap.M, BMap.I, BMap.St):::
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
    
    val buffer = new ListBuffer[TopDecl]()
    
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
    val guards = new ListBuffer[Boogie.Expr]()
    var inpatDecls = Map.empty[String,BDecl]
    
    for (a <- avs.actions) {
      val (decl,guard,renames) = translateActorAction(a, avs)
      decls ++= decl
      inpatDecls = inpatDecls ++ renames
      if (!a.init) {
        // And together the input pattern expressions and the guard expression
        if (!guard.isEmpty) {
          guards += guard.reduceLeft((a,b) => (a && b))
        }
      }
    } // end for
    
    if (!skipMutualExclusivenessCheck) {
      createMutualExclusivenessCheck(avs,guards.toList,inpatDecls.values.toList) match {
        case Some(proc) => decls += proc
        case None =>
      }
    }
    
    avs.actorBoogieStates:::decls.toList
  }
  
  def createMutualExclusivenessCheck(
      avs: ActorVerificationStructure, guards: List[Boogie.Expr], inpatDecls: List[BDecl]): Option[Boogie.Proc] = {
    
    val nonInitActions = avs.actions.filter { a => !a.init }
    if (nonInitActions.size > 1) {
      
      val decls = 
        (avs.channelDecls map { _.decl }) ::: 
        (avs.actorVarDecls map { _.decl }) ::: 
        (inpatDecls map { _.decl }) ::: 
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
  
  def translateActorAction(a: Action, avs: ActorVerificationStructure): (List[Boogie.Decl],List[Boogie.Expr],Map[String,BDecl]) = {
     
    val asgn = new ListBuffer[Boogie.Stmt]
    val renamingsBuffer = new ListBuffer[(String,String)]
    val inpatDeclBuffer = new ListBuffer[(String,BDecl)]
    val readTokensRules = new ListBuffer[Boogie.Expr]
    
    asgn ++= avs.channelDecls map { _.decl }
    asgn ++= avs.actorVarDecls map { _.decl }
    asgn ++= avs.actorParamDecls map { _.decl }
    asgn += B.Assume(avs.uniquenessCondition)

    for (ipat <- a.inputPattern) {
      for ((v,i) <- ipat.vars.zipWithIndex) {
        val name = ipat.portId+B.Sep+i.toString
        renamingsBuffer += ((v.id, name))
        val lVar = B.Local(name, v.typ)
        asgn += lVar
        inpatDeclBuffer += ((name,BDecl(name,lVar)))
      }
      readTokensRules += B.Int(ipat.vars.size) <= B.C(ipat.portId)-B.R(ipat.portId)
    }
    
    if (a.init) asgn ++= avs.initAssumes
    else asgn ++= avs.basicAssumes
     
     val renamings = renamingsBuffer.toMap
     
     if (!a.init) {
       // Assume invariants
       asgn ++= (for (i <- avs.invariants) yield B.Assume(transExpr(i.expr)(renamings)))
     }
     avs.allowedStateInv match {
       case Some(e) => asgn += B.Assume(e)
       case None =>
     }
     
     val guards =
       (a.guard match {
         case None => Nil
         case Some(e) => List(transExpr(e)(renamings))
       })
     
     val transitions = avs.schedule match {
       case Some(sched) => sched.transitionsOnAction(a.fullName)
       case None => Nil
     }
     val stateGuards = for ((f,t) <- transitions) yield {
       (B.This ==@ Boogie.VarExpr(avs.namePrefix+f)) : Boogie.Expr
     }
     val stateGuard = if (stateGuards.isEmpty) Nil else List(stateGuards.reduceLeft((a,b) => (a || b)))
     
     for (ipat <- a.inputPattern) {
       val cId = ipat.portId
       for (v <- ipat.vars) {
         asgn += Boogie.Assign(transExpr(v)(renamings), B.ChannelIdx(cId, B.R(cId)))
         asgn += Boogie.Assign(B.R(cId), B.R(cId) plus B.Int(1))
       }
     }
     
     asgn ++= (for (p <- a.requires) yield {B.Assume(transExpr(p)(renamings)) })
     asgn ++= stateGuard map {x => B.Assume(x)}
     asgn ++= guards map {g => B.Assume(g)}
     
     asgn ++= 
       (a.body match {
         case None => List(B.Assume(Boogie.BoolLiteral(true)))
         case Some(b) => transStmt( b )(renamings)
       })
     
     asgn ++= 
       (transitions match {
         case Nil => Nil
         case List((f,t)) => List(Boogie.Assign(B.This, Boogie.VarExpr(avs.namePrefix+t)))
         case _ => assert(false); Nil
       })
     
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
     asgn ++= (for (inv <- avs.invariants) yield {
       if (!inv.assertion.free) B.Assert(transExpr(inv.expr)(renamings),inv.expr.pos, "Action at " + a.pos + " might not preserve invariant")
       else B.Assume(transExpr(inv.expr)(renamings))
     })
     
     val proc = createBoogieProc(Uniquifier.get(avs.namePrefix+a.fullName),asgn.toList)
     
     (List(proc), readTokensRules.toList:::stateGuard:::guards, inpatDeclBuffer.toMap)
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
    val vars = new ListBuffer[Boogie.LocalVar]
    
    asgn ++= (nwvs.entityDecls map { _.decl })
    asgn ++= nwvs.subactorVarDecls map { _.decl }
    asgn ++= nwvs.uniquenessConditions map {B.Assume(_)}
    asgn ++= nwvs.basicAssumes
    
    for (c <- nwvs.connections) {
      asgn += B.Assume(B.C(nwvs.nwRenamings(c.id)) ==@ B.Int(0))
      asgn += B.Assume(B.R(nwvs.nwRenamings(c.id)) ==@ B.Int(0))
    }
    
    if (ftMode) {
      for (e <- nwvs.entities) {
        asgn += B.Assume(B.SqnAct(nwvs.nwRenamings(e.id)) ==@ B.Int(0))
      }
    }
    
    for (inst <- nwvs.entities) {
      
      val actor = inst.actor
      
      val renamings = nwvs.nwRenamings ++  nwvs.entityData(inst).renamings
      
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
      
      for (inv <- actor.actorInvariants) {
        asgn += B.Assume(transExpr(inv.expr)(renamings))
      }
      
      actor.members.find(_.isSchedule) match {
        case Some(s) => {
          val schedule = s.asInstanceOf[Schedule]
          asgn += B.Assume(B.State(nwvs.nwRenamings(inst.id)) ==@ Boogie.VarExpr(actor.fullName+B.Sep+schedule.initState))
        }
        case None =>
      }
    }
    for (chi <- nwvs.chInvariants) {
      asgn += BAssert(chi, "Network initialization might not establish the channel invariant", nwvs.nwRenamings)
    }
    asgn += Boogie.Assign(Boogie.VarExpr(BMap.I), Boogie.VarExpr(BMap.R))

    for (nwi <- nwvs.nwInvariants) {
      asgn ++= Exhalator.visit(
          nwi, "Network initialization might not establish the network invariant", nwvs.nwRenamings)
    }
    
    val emptyChans = (for (c <- nwvs.connections) yield {
      B.Assert(B.Credit(nwvs.nwRenamings(c.id)) ==@ B.Int(0), c.pos, 
          "The initialization might unspecified tokens on channel " + c.id)
    })
    
    asgn ++= emptyChans
    
    val stmt = vars.toList:::asgn.toList
    List(createBoogieProc(Uniquifier.get(nwvs.namePrefix+"init"),stmt))
  }
  
  def translateSubActorExecutions(nwvs: NetworkVerificationStructure) = {
    
    val boogieProcs = new ListBuffer[Boogie.Proc]()
    val nwFiringRules = new ListBuffer[Boogie.Expr]()
    for (inst <- nwvs.entities) {
      val actor = inst.actor
      
      val orderedActions = new ListBuffer[(Action,List[Action])]()
      actor.priority match {
        case Some(pr) => {
          for (name <- pr.order) {
            // Assuming valid label
            val act = actor.actions.find{ a => a.fullName == name }.get
            orderedActions += (act -> orderedActions.toList.map {_._1})
          }
        }
        case None =>
      }
      
      for (act <- actor.actions) {
        if (! (orderedActions exists {case (a,_) => a == act})) {
          orderedActions += (act -> List.empty)
        }
      }
         
      val actorFiringRulesNoPrio = collection.mutable.Map[Action,Boogie.Expr]()
      val actorFiringRulesPrio = collection.mutable.Map[Action,Boogie.Expr]()
      for ((ca,higherPrioAction) <- orderedActions) {
        if (!ca.init) {
          val procName = nwvs.namePrefix+B.Sep+actor.id+B.Sep+ca.fullName
          
          val prFiringRule = higherPrioAction map {a => actorFiringRulesNoPrio(a)}
          
          val (subActorStmt,newVarDecls,firingRulePrio,firingRuleNoPrio) = 
            transSubActionExecution(inst, ca, nwvs, prFiringRule)
          val stmt = 
            (nwvs.entityDecls map { _.decl }) :::
            (nwvs.subactorVarDecls  map { _.decl }):::
            (nwvs.uniquenessConditions map {B.Assume(_)}) :::
            newVarDecls :::
            subActorStmt
          boogieProcs += createBoogieProc(Uniquifier.get(procName),stmt)
          actorFiringRulesNoPrio += (ca -> firingRuleNoPrio)
          actorFiringRulesPrio += (ca -> firingRulePrio)
        }
      }
      nwFiringRules ++= actorFiringRulesPrio.values
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
      B.Assume(B.C(nwvs.nwRenamings(c.id)) - B.I(nwvs.nwRenamings(c.id)) ==@ B.Int(nwa.portInputCount(c.from.name)) /* B.BaseL*/)
    }
    
    val nwPre = for (r <- nwa.requires) yield 
      (r.pos,transExpr(r)(nwvs.nwRenamings))
    
    val nwPost = for (q <- nwa.ensures) yield 
      (q.pos,transExpr(q)(nwvs.nwRenamings))
    
    val firingNegAssumes = subactorFiringRules map { fr => B.Assume(Boogie.UnaryExpr("!",fr)) }
    
    val exitStmt =
      (nwvs.entityDecls map { _.decl }) :::
      (nwvs.subactorVarDecls  map { _.decl }):::
      (nwvs.uniquenessConditions map {B.Assume(_)}) :::
      nwvs.basicAssumes:::
      (for (chi <- nwvs.chInvariants) yield BAssume(chi,nwvs.nwRenamings)):::
      inputBounds:::
      (nwPre.map { case (_,r) => B.Assume(r) }) :::
      firingNegAssumes:::
      //outputs:::
      (nwPost.map { case (pos,q) => B.Assert(q,pos,"Network action postcondition might not hold") }) :::
      (for (c <- nwvs.connections) yield {
        c.to match {
          // Match network output channels
          case pf@PortRef(None,port) => {
            val name = nwvs.targetMap(pf)
            List(Boogie.Assign(B.R(Boogie.VarExpr(name)), B.R(Boogie.VarExpr(name)) +  (B.Int(nwa.portOutputCount(port)))))
          }
          case _ => Nil
        }
      }).flatten:::
      //
      List(Boogie.Assign(Boogie.VarExpr(BMap.I), Boogie.VarExpr(BMap.R))) :::
      //
      (for (chi <- nwvs.chInvariants) yield 
        BAssert(chi,"The network might not preserve the channel invariant"  ,nwvs.nwRenamings)) :::
      //
      (for (nwi <- nwvs.nwInvariants) yield 
        Exhalator.visit(nwi,"The network might not preserve the network invariant",nwvs.nwRenamings)).flatten :::
      (for (c <- nwvs.connections) yield {
        if (c.isOutput) {
          B.Assert(B.C(nwvs.nwRenamings(c.id)) ==@ B.R(nwvs.nwRenamings(c.id)),nwa.pos,"The network might not produce the specified number of tokens on output " + c.to.name)
        }
        else {
          B.Assert(B.C(nwvs.nwRenamings(c.id)) ==@ B.R(nwvs.nwRenamings(c.id)),nwa.pos,"The network might leave unread tokens on channel " + c.id)
        }
      })
    createBoogieProc(Uniquifier.get(nwvs.namePrefix+nwa.fullName+"#exit"),exitStmt)
  }
  
  val nextState = "St#next"
  
  
  
  def transSubActionExecution(
      instance: Instance, 
      action: Action, 
      nwvs: NetworkVerificationStructure,
      higherPriorityGuards: List[Boogie.Expr]): (List[Boogie.Stmt],List[Boogie.LocalVar],Boogie.Expr,Boogie.Expr) = {
    
    val actor = instance.actor
    val asgn = new ListBuffer[Boogie.Stmt]()
    val newVars = new ListBuffer[Boogie.LocalVar]()
    
    asgn ++= nwvs.basicAssumes
    asgn ++= (for (chi <- nwvs.chInvariants) yield BAssume(chi,nwvs.nwRenamings))  // Assume channel invariants
    
    newVars += B.Local(nextState,BType.State)
    
    val firingCondsBuffer = new ListBuffer[Boogie.Expr]() // Gather firing conditions from each pattern
    val replacements = scala.collection.mutable.HashMap.empty[Id,Expr]
    
    for (ipat <- action.inputPattern) {
      val cId = nwvs.targetMap(PortRef(Some(instance.id),ipat.portId))
      firingCondsBuffer += B.Int(ipat.numConsumed) lte B.Credit(cId)
      
      for ((v,ind) <- ipat.vars.zipWithIndex) {
        val c = Elements.ch(cId,v.typ)
        val index = 
          if (ind == 0) Elements.rd0(c.id) 
          else Minus(Elements.rd0(c.id),IntLiteral(ind))
        val acc = Elements.chAcc(c,index)
        replacements += (v -> acc)
      }

    }
    
    val patternVarRenamings = (for (ipat <- action.inputPattern) yield {
      for (v <- ipat.vars) yield {
        val inVar = ipat.portId + B.Sep + v.id
        newVars += B.Local(inVar,B.type2BType(v.typ))
        (v.id,inVar)
      }
    }).flatten.toMap
    
    val renamings = nwvs.nwRenamings ++ nwvs.entityData(instance).renamings ++ patternVarRenamings

    
    val replacementMap = replacements.toMap
    
    val renamedGuard = action.guard match {
      case None =>
      case Some(g) =>
        val renamedGuard = IdReplacer.visitExpr(g)(replacementMap)
        val transGuard = transExpr(renamedGuard)(renamings)
        //asgn += B.Assume(transGuard)
        firingCondsBuffer += transGuard
    }
    
    val firingCondsWithoutPrio = firingCondsBuffer.toList
    val firingCondsWithPrio = (higherPriorityGuards map { x: Boogie.Expr => Boogie.UnaryExpr("!",x) }) ::: firingCondsWithoutPrio
    
    val firingRuleWithPrio = {
      if (!firingCondsWithPrio.isEmpty) {
        firingCondsWithPrio.reduceLeft((a,b) => a && b) 
      }
      else Boogie.BoolLiteral(true)
    }
    
    val firingRuleWithoutPrio = {
      if (!firingCondsWithoutPrio.isEmpty) {
        firingCondsWithoutPrio.reduceLeft((a,b) => a && b) 
      }
      else Boogie.BoolLiteral(true)
    }
    
    asgn += B.Assume(firingRuleWithPrio)
    
    for (ActorInvariant(e,_,_) <- actor.actorInvariants) {
      asgn += B.Assume(transExpr(e.expr)(renamings))
    }
    
    val publicInvs = actor.publicActorInvariants map { a => (a.assertion.expr.pos, transExpr(a.assertion.expr)(renamings)) }
    
    for (ipat <- action.inputPattern) {
      var repeats = 0
      while (repeats < ipat.repeat) {
        val cId = nwvs.targetMap(PortRef(Some(instance.id),ipat.portId))
        for (v <- ipat.vars) {
          asgn += Boogie.Assign(Boogie.VarExpr(patternVarRenamings(v.id)),B.ChannelIdx(cId,B.Read(cId)))
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
    
    for (ev <- nwvs.entityData(instance).variables) {
      asgn += Boogie.Havoc(Boogie.VarExpr(ev))
    }
        
    for (opat <- action.outputPattern) {
      val cId = nwvs.sourceMap(PortRef(Some(instance.id),opat.portId))
      var repeats = 0
      while (repeats < opat.repeat) {
        for (e <- opat.exps) {
          asgn += Boogie.Assign(B.ChannelIdx(cId,B.C(cId)),transExpr(e)(renamings))
          if (ftMode) {
            asgn += Boogie.Assign(B.SqnCh(cId,B.C(cId)),B.SqnAct(Boogie.VarExpr( renamings(instance.id) )))
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
      asgn += Boogie.Assign(B.SqnAct(renamings(instance.id)),B.SqnAct(renamings(instance.id)) plus B.Int(1))
    }
    for (ActorInvariant(e,_,_) <- actor.actorInvariants) {
      asgn += B.Assume(transExpr(e.expr)(renamings))
    }
    asgn ++= (for (chi <- nwvs.chInvariants) yield {
      if (!chi.assertion.free) {
        val msg = 
          "Action at " + action.pos + " ('" + action.fullName + "') for actor instance '" + 
          instance.id + "' might not preserve the channel invariant"
        List(BAssert(chi, msg, nwvs.nwRenamings))
      }
      else {
        Nil
      }
    }).flatten
            
    (asgn.toList, newVars.toList, firingRuleWithPrio, firingRuleWithoutPrio)
  }
  
  
  def translateNetworkInput(action: Action, pattern: InputPattern, nwvs: NetworkVerificationStructure) = {
    
    
    val asgn = new ListBuffer[Boogie.Stmt]()
    asgn ++= (nwvs.entityDecls map { _.decl })
    asgn ++= nwvs.subactorVarDecls  map { _.decl }
    asgn ++= (nwvs.uniquenessConditions map { B.Assume(_) })
    asgn ++= nwvs.basicAssumes
    
    asgn += B.Assume(B.C(nwvs.nwRenamings(pattern.portId)) < B.Int(pattern.vars.size))

    for (chi <- nwvs.chInvariants) {
      asgn += BAssume(chi, nwvs.nwRenamings)
    }

    asgn += Boogie.Assign(
        B.C(nwvs.nwRenamings(pattern.portId)),
        B.C(nwvs.nwRenamings(pattern.portId)) + B.Int(1))
        
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
      if (smokeTest) stmt:::List(B.Assert(Boogie.BoolLiteral(false),"["+ name +"]"))
      else stmt
    Boogie.Proc(name,Nil,Nil,Modifies,Nil,body)
  }
  
  def BAssume(chi: ChannelInvariant, renamings: Map[String,String]) = B.Assume(transExpr(chi.expr)(renamings))
  
  def BAssert(chi: ChannelInvariant, msg: String, renamings: Map[String,String]) = 
    B.Assert(transExpr(chi.expr)(renamings), chi.expr.pos, msg)
  
  def transExprNoRename(exp: Expr): Boogie.Expr = transExpr(exp)(Map.empty)
  
  def transExpr(exp: Expr)(implicit renamings: Map[String,String]): Boogie.Expr = stmtTranslator.transExpr(exp)
  
  def transStmtNoRename(stmt: List[Stmt]): List[Boogie.Stmt] = transStmt(stmt)(Map.empty)
  
  def transStmt(stmts: List[Stmt])(implicit renamings: Map[String,String]): List[Boogie.Stmt] = stmtTranslator.transStmt(stmts)

}

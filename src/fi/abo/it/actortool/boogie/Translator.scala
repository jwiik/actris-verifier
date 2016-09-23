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
    implicit val bvMode: Boolean) {  
  
  val B = Helper  

  final val Modifies = List(BMap.C, BMap.R, BMap.M, BMap.I, BMap.St):::
    (if (!ftMode) Nil else List(BMap.SqnCh, BMap.SqnActor))
  
  object Annot {
    final val Error = "error"
  }
  
  object Uniquifier {
    private var i = -1
    def get(id: String) = { i = i+1; id+B.Sep+(i.toString) }
  }
  
  object GeneratedInvariantCount {
    private var i = -1
    def next = { i = i+1; "#"+(i.toString) }
  }
  
  def translateProgram(decls: List[TopDecl]): List[Boogie.Decl] = {
    
    if (ftMode) BoogiePrelude.addComponent(SeqNumberingPL)
    
    val bProgram = decls flatMap {
      case a: BasicActor => translateActor(a)
      case n: Network => translateNetwork(n)
      case u: DataUnit => Nil
    }
    
    return bProgram
      
  }
    
  def translateActor(actor: BasicActor): List[Boogie.Decl] = {
    val decls = new ListBuffer[Boogie.Decl]()
    val invariants = new ListBuffer[(ActorInvariant,Boogie.Expr)]()
    val actorVars = new ListBuffer[Boogie.LocalVar]()
    
    val prefix = actor.id+B.Sep
    
    val portChans = 
      ((for (p <- actor.inports) yield B.Local(p.id, B.type2BType(ChanType(p.portType))))
      :::
      (for (p <- actor.outports) yield B.Local(p.id, B.type2BType(ChanType(p.portType))))
      )
    
    val states = actor.schedule match {
      case Some(s) => 
        actorVars += B.ThisDecl
        s.states
      case None => Nil
    }
    
    val bActorStates = for (s <- states) yield {
      //actorVars += bLocal(currentState,BType.State)
      Boogie.Const(prefix+s,true,BType.State)
    }
    
    if (!states.isEmpty) {
      val allowedStatesInvariant = (for (s <- states) yield {
        B.This ==@ Boogie.VarExpr(prefix+s)
      }).reduceLeft((a,b) => (a || b))
      val ai = ActorInvariant(Assertion(null,false),true)
      ai.pos = actor.pos
      invariants += ((ai,allowedStatesInvariant))
    }
      
    for (m <- actor.members) {
      m match {
        case inv: ActorInvariant => invariants += ((inv,transExpr(inv.expr)(Map.empty)))
        case Declaration(id,t,_,_) => actorVars += B.Local(id,t)
        case FunctionDecl(name,ins,out,body) => {
          val func = Boogie.Function(
              actor.id+B.Sep+name, ins.map(i => Boogie.BVar(i.id,B.type2BType(i.typ))), 
              Boogie.BVar("out"+B.Sep, B.type2BType(out)))
        }
        case _ =>
      }
    }
    
    val guards = new ListBuffer[Boogie.Expr]()
    
    val localVarsMap = scala.collection.mutable.HashMap.empty[String,Boogie.LocalVar]
    
    for (a <- actor.actions) {
      val (decl,guard,localVars) = translateActorAction(a, portChans, invariants.toList,actorVars.toList,actor.schedule,prefix)
      decls ++= decl
      
      if (!a.init) {
        for (lv <- localVars) { // Add variable declarations not already present
          if (!localVarsMap.contains(lv.x.id)) {
            localVarsMap += (lv.x.id -> lv )
          }
        }
        
        // And together the input pattern expressions and the guard expression
        if (!guard.isEmpty) {
          guards += guard.reduceLeft((a,b) => (a && b))
        }
      }
    } // end for
     
    createMutualExclusivenessCheck(actor, actor.actions, guards.toList, localVarsMap.values.toList, prefix) match {
      case Some(proc) => decls += proc
      case None =>
    }

    
    bActorStates:::decls.toList
  }
  
  def createMutualExclusivenessCheck(
      actor: DFActor, actions: List[Action], guards: List[Boogie.Expr],
      localVars: List[Boogie.LocalVar], prefix: String): Option[Boogie.Proc] = {
    
    val nonInitActions = actions.filter { a => !a.init }
    if (nonInitActions.size > 1) {
      

//      val assertion = B.Assert(Boogie.UnaryExpr("!", guards.reduceLeft((a,b) => (a && b))),actor.pos,
//          "The actions of actor '" + actor.id + "' might not have mutually exclusive guards")
      val stmt = localVars:::createMEAssertionsRec(actor,guards)
      
      
      
      Some(createBoogieProc(Uniquifier.get(prefix+B.Sep+"GuardWD"), stmt))
    }
    else None
  }
  
  def createMEAssertionsRec(a: DFActor, guards: List[Boogie.Expr]): List[Boogie.Assert] = {
    guards match {
      case first::rest => {
        val asserts = for (g <- rest) yield {
          B.Assert(Boogie.UnaryExpr("!", first && g) , a.pos, "The actions of actor '" + a.id + "' might not have mutually exclusive guards (" + GeneratedInvariantCount.next + ")")
        }
        asserts:::createMEAssertionsRec(a,rest)
      }
      case Nil => Nil
    }
    
  }
  
  def translateActorAction(
       a: Action, 
       portChans: List[Boogie.LocalVar],
       invs: List[(ActorInvariant,Boogie.Expr)],
       actorVars: List[Boogie.LocalVar],
       schedule: Option[Schedule],
       prefix: String): (List[Boogie.Decl],List[Boogie.Expr],List[Boogie.LocalVar]) = {
     
     val renamings = new ListBuffer[(Id,Expr)]
     val readTokensRules = new ListBuffer[Boogie.Expr]
     
     for (inPat <- a.inputPattern) {
       for ((v,i) <- inPat.vars.zipWithIndex) {
         val id = Id(inPat.portId); id.typ = ChanType(v.typ)
         renamings += ((Id(v.id), IndexAccessor(id, IntLiteral(i))))
       }
       
       readTokensRules += B.Int(inPat.vars.size) <= B.C(inPat.portId)-B.R(inPat.portId)
     }
     
     val actionVars = for (v <- a.variables) yield {
       val name = "ActionVar"+B.Sep+v.id
       renamings += ((Id(v.id), Id(name)))
       B.Local(name,v.typ)
     }
     
     val renameMap = renamings.toMap
     
     val invAssumes = for ((pos,i) <- invs) yield B.Assume(i)
     
     val preCondAssumes = for (p <- a.requires) yield {
       B.Assume(transExprNoRename( IdReplacer.visitExpr(p)(renameMap) ))
     }
     
     val guards = a.guard match {
       case None => Nil
       case Some(e) => List(transExprNoRename( IdReplacer.visitExpr(e)(renameMap) ))
     }
     
     val guardAssume = guards map {g => B.Assume(g)}
     
     val transitions = schedule match {
       case Some(sched) => sched.transitionsOnAction(a.fullName)
       case None => Nil
     }
     
     val stateGuards = for ((f,t) <- transitions) yield {
       (B.This ==@ Boogie.VarExpr(prefix+f)) : Boogie.Expr
     }
     
     val stateGuard = if (stateGuards.isEmpty) Nil else List(stateGuards.reduceLeft((a,b) => (a || b)))
     
     val body = a.body match {
       case None => List(B.Assume(Boogie.BoolLiteral(true)))
       case Some(b) => transStmtNoRename( IdReplacer.visitStmt(b)(renameMap) )
     }
     val stateUpdates = transitions match {
       case Nil => Nil
       case List((f,t)) => List(Boogie.Assign(B.This, Boogie.VarExpr(prefix+t)))
       case _ => assert(false); Nil
     }
     
     val invAsserts = for ((aInv,bInv) <- invs) yield {
       if (!aInv.assertion.free) B.Assert(bInv,aInv.expr.pos, "Action at " + a.pos + " might not preserve invariant")
       else B.Assume(bInv)
     }
     
     val postCondAsserts = for (q <- a.ensures) yield {
       B.Assert(transExprNoRename(IdReplacer.visitExpr(q)(renameMap)), q.pos, "Action postcondition might not hold")
     }
     
     val stmt =
       portChans:::
       actorVars:::
       actionVars:::
       invAssumes:::
       preCondAssumes:::
       (stateGuard map {x => B.Assume(x)})  :::
       guardAssume:::
       body:::
       stateUpdates:::
       postCondAsserts:::
       invAsserts
     (List(createBoogieProc(Uniquifier.get(prefix+a.fullName),stmt)), readTokensRules.toList:::stateGuard:::guards, portChans:::actorVars/*:::inputVars*/)
   }
  
  def translateNetwork(network: Network): List[Boogie.Decl] = {
    val decls = new ListBuffer[Boogie.Decl]()
    val actions = network.actions
    val nwInvariants = network.actorInvariants
    val chInvariants = network.channelInvariants
    val connections = network.structure.get.connections
    val entities = network.entities.get.entities
    
    val namePrefix = network.id+B.Sep
    
    val (networkRenamings, subactorVarDecls) = {
      val buffer = new ListBuffer[(String,String)]
      val decls = new ListBuffer[Boogie.LocalVar]
      for (c <- connections) buffer += ((c.id,namePrefix+c.id))
      
      // Add input/output port names as synonyms to the connected channels
      for (ip <- network.inports) {
        val ch = network.structure.get.getInputChannel(ip.portId)
        ch match {
          case Some(c) => buffer += ((ip.portId,namePrefix+c.id))
          case None =>
        }
      }
      for (op <- network.outports) {
        val ch = network.structure.get.getOutputChannel(op.portId)
        ch match {
          case Some(c) => buffer += ((op.portId,namePrefix+c.id))
          case None =>
        }
      }
      
      for (e <- entities) {
        buffer += ((e.id,namePrefix+e.id))
        for (av <- e.actor.variables) {
          val avName = namePrefix+e.id+B.Sep+"AV"+B.Sep+av.id
          buffer += ((av.id,avName))
          decls += B.Local(avName,av.typ)
        }
      }
      (buffer.toMap,decls.toList)
    }
    
    val (sourceMap,targetMap) = {
      val source = scala.collection.mutable.HashMap.empty[PortRef,List[String]]
      val target = scala.collection.mutable.HashMap.empty[PortRef,String]
      for (c <- connections) {
        if (!(source contains c.from)) source += (c.from -> List(networkRenamings(c.id)))
        else source(c.from) = source(c.from):::List(networkRenamings(c.id))
        target(c.to) = networkRenamings(c.id)
      }
      (source.toMap,target.toMap)
    }
    
    val basicAssumes =
      (for (c <- connections) yield {
        val name = networkRenamings(c.id)
        val list1 = List(
          B.Int(0) <= B.I(name),
          B.I(name) <= B.R(name),
          B.R(name) <= B.C(name))
        val list2 = (if (c.isOutput) List(B.I(name) ==@ B.R(name)) else Nil)
        (list1 ::: list2).map(x => B.Assume(x))
      }).flatten
    
    val constDecls = new ListBuffer[Boogie.Const]
    for (e <- entities) {
      constDecls += Boogie.Const(networkRenamings(e.id),true,BType.Actor)
    }
    for (c <- connections) {
      constDecls += Boogie.Const(networkRenamings(c.id),true,BType.Chan(B.type2BType(c.typ)))
    }
    
    decls ++= translateNetworkInit(basicAssumes, nwInvariants, chInvariants, networkRenamings, 
        sourceMap, targetMap, entities, connections, network.id+B.Sep)
    
    val (subActorProcs, subActorFiringRules) = 
      translateSubActorExecutions(basicAssumes, nwInvariants, chInvariants, networkRenamings, sourceMap, 
          targetMap, entities, connections, subactorVarDecls, network.id+B.Sep)
    decls ++= subActorProcs

    for (a <- actions) {
      decls ++= translateNetworkAction(
          a, basicAssumes, nwInvariants,chInvariants,networkRenamings,sourceMap,targetMap,
          entities,connections,subactorVarDecls,subActorFiringRules,network.id+B.Sep)
    }

    constDecls.toList:::decls.toList
  }
  
  def translateNetworkInit(
       basicAssumes: List[Boogie.Assume],
       nwInvs: List[ActorInvariant],
       chInvs: List[ChannelInvariant],
       networkRenamings: Map[String,String], // Channels and entities
       sourceMap: Map[PortRef,List[String]],
       targetMap: Map[PortRef,String],
       entities: List[Instance],
       connections: List[Connection],
       prefix: String): List[Boogie.Decl] = {
    
    val asgn = new ListBuffer[Boogie.Stmt]
    val vars = new ListBuffer[Boogie.LocalVar]
    
    asgn ++= basicAssumes
    
    for (c <- connections) {
      asgn += B.Assume(B.C(networkRenamings(c.id)) ==@ B.Int(0))
      asgn += B.Assume(B.R(networkRenamings(c.id)) ==@ B.Int(0))
    }
    
    if (ftMode) {
      for (e <- entities) {
        asgn += B.Assume(B.SqnAct(networkRenamings(e.id)) ==@ B.Int(0))
      }
    }
    
    for (inst <- entities) {
      val actor = inst.actor
      val actorParams = actor.parameters.map(p => {
        val newName = "ActorParam"+B.Sep+inst.id+B.Sep+p.id
        vars += B.Local(newName,B.type2BType(p.typ))
        (Id(p.id),Id(newName))
      }).toMap
      val parameterNames = actor.parameters map {x => Id(x.id)}
      for ((name,value) <- (parameterNames zip inst.arguments)) {
        // Add assumptions about the values of the actor parameters
        asgn += B.Assume(transExpr(
              IdToIdReplacer.visitExpr(name)(actorParams)
            )(networkRenamings) ==@ transExpr(value)(networkRenamings))
      }
      
      for (ca <- actor.actions filter(_.init)) {
        for (opat <- ca.outputPattern) {
          val cIds = sourceMap(PortRef(Some(inst.id),opat.portId))
          for (cId <- cIds) {
            for (e <- opat.exps) {
              val renamedExp = IdToIdReplacer.visitExpr(e)(actorParams)
              asgn += Boogie.Assign(
                  B.ChannelIdx(cId,B.C(cId)),transExpr(renamedExp)(networkRenamings))
              asgn += Boogie.Assign(B.C(cId),B.C(cId) plus B.Int(1))
            }
          }
        }
      }
      
      actor.members.find(_.isSchedule) match {
        case Some(s) => {
          val schedule = s.asInstanceOf[Schedule]
          asgn += B.Assume(B.State(networkRenamings(inst.id)) ==@
              Boogie.VarExpr(actor.fullName+B.Sep+schedule.initState))
        }
        case None =>
      }
    }
    for (chi <- chInvs) {
      asgn ++= Exhalator.visit(
          chi, "Network initialization might not establish the channel invariant (" + GeneratedInvariantCount.next + ")", networkRenamings)
    }
    asgn += Boogie.Assign(Boogie.VarExpr(BMap.I), Boogie.VarExpr(BMap.R))

    for (nwi <- nwInvs) {
      asgn ++= Exhalator.visit(
          nwi, "Network initialization might not establish the network invariant", networkRenamings)
    }
    
    val emptyChans = (for (c <- connections) yield {
      B.Assert(B.Credit(networkRenamings(c.id)) ==@ B.Int(0), c.pos, "The initialization might unspecified tokens on channel " + c.id)
    })
    
    val stmt = vars.toList:::asgn.toList
    List(createBoogieProc(Uniquifier.get(prefix+"init"),stmt))
  }
  
  def translateSubActorExecutions(
       basicAssumes: List[Boogie.Assume],
       nwInvs: List[ActorInvariant],
       chInvs: List[ChannelInvariant],
       networkRenamings: Map[String,String], // Channels and entities
       sourceMap: Map[PortRef,List[String]],
       targetMap: Map[PortRef,String],
       entities: List[Instance],
       connections: List[Connection],
       procVars: List[Boogie.LocalVar],
       prefix: String) = {
    
    val boogieProcs = new ListBuffer[Boogie.Proc]()
    val nwFiringRules = new ListBuffer[Boogie.Expr]()
    for (inst <- entities) {
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
          val procName = prefix+B.Sep+actor.id+B.Sep+ca.fullName
          
          val prFiringRule = higherPrioAction map {a => actorFiringRulesNoPrio(a)}
          
          val (subActorStmt,newVarDecls,firingRulePrio,firingRuleNoPrio) = 
            transSubActionExecution(
                inst, ca, networkRenamings, basicAssumes, nwInvs, chInvs, sourceMap, targetMap, prFiringRule)

          val stmt = 
            procVars.toList :::
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
       nwa: Action,
       basicAssumes: List[Boogie.Assume],
       nwInvs: List[ActorInvariant],
       chInvs: List[ChannelInvariant],
       networkRenamings: Map[String,String], // Channels and entities
       sourceMap: Map[PortRef,List[String]],
       targetMap: Map[PortRef,String],
       entities: List[Instance],
       connections: List[Connection],
       subactorVarDecls: List[Boogie.LocalVar],
       subActorFiringRules: List[Boogie.Expr],
       prefix: String): List[Boogie.Decl] = {
    
    val procVars = new ListBuffer[Boogie.LocalVar]
    
    procVars ++= subactorVarDecls
    
    
    val actionRenamings = new ListBuffer[(String,String)]
    for (v <- nwa.variables) {
      val newName = "ActionVar"+B.Sep+v.id
      procVars += B.Local(newName,B.type2BType(v.typ))
      actionRenamings += ((v.id,newName))
    }

    val renamings = networkRenamings ++ actionRenamings.toMap
    
    val assumesBuffer = new ListBuffer[Boogie.Assume]
    
    for (c <- connections) {
      assumesBuffer += B.Assume(B.Credit(networkRenamings(c.id)) ==@ B.Int(0))
    }
    
    val rcAssumes = assumesBuffer.toList
    
    val boogieProcs = new ListBuffer[Boogie.Proc]()
    
    boogieProcs += transNetworkEntry(
        nwa, basicAssumes, nwInvs, chInvs, renamings, connections, procVars.toList, prefix)
    
    for (ipat <- nwa.inputPattern) {
      val stmt = translateNetworkInput(nwa, ipat, renamings, basicAssumes, sourceMap, chInvs)
      boogieProcs += createBoogieProc(Uniquifier.get(prefix+nwa.fullName+B.Sep+"input"+B.Sep+ipat.portId),stmt)
    }
    
    
    boogieProcs += transNetworkExit(
        nwa, basicAssumes, nwInvs, chInvs, sourceMap, targetMap, renamings, 
        subActorFiringRules, connections, procVars.toList, prefix)
    
    // The complete list of Boogie procedure generated for this network action
    boogieProcs.toList
  }
  
  def transNetworkEntry(
        nwa: Action,
        basicAssumes: List[Boogie.Assume],
        nwInvs: List[ActorInvariant],
        chInvs: List[ChannelInvariant],
        renamings: Map[String,String], // Channels and entities
        connections: List[Connection],
        procVars: List[Boogie.LocalVar],
        prefix: String) = {
    
    val entryStmt = 
      procVars.toList :::
      basicAssumes:::
      List(B.Assume(Boogie.VarExpr(BMap.I) ==@ Boogie.VarExpr(BMap.R))) :::
      (for (c <- connections) yield {
        B.Assume(B.R(renamings(c.id)) ==@ B.C(renamings(c.id)))
      }) :::
      (for (nwi <- nwInvs) yield 
        Inhalator.visit(nwi,"",renamings)).flatten :::
      (for (chi <- chInvs) yield 
        Inhalator.visit(chi,""  ,renamings)).flatten
        
      createBoogieProc(Uniquifier.get(prefix+nwa.fullName+"#entry"),entryStmt)
  }
  
  def transNetworkExit(
       nwa: Action,
       basicAssumes: List[Boogie.Assume],
       nwInvs: List[ActorInvariant],
       chInvs: List[ChannelInvariant],
       sourceMap: Map[PortRef,List[String]],
       targetMap: Map[PortRef,String],
       renamings: Map[String,String], // Channels and entities
       nwFiringRules: List[Boogie.Expr],
       connections: List[Connection],
       procVars: List[Boogie.LocalVar],
       prefix: String) = {
    // Network action exit
    
    val inputBounds = for (c <- connections.filter { _.isInput }) yield {
      B.Assume(B.C(renamings(c.id)) - B.I(renamings(c.id)) ==@ B.Int(nwa.portInputCount(c.from.name)) /* B.BaseL*/)
    }
    
    val nwPre = for (r <- nwa.requires) yield 
      (r.pos,transExpr(r)(renamings))
    
    val nwPost = for (q <- nwa.ensures) yield 
      (q.pos,transExpr(q)(renamings))
    
    val firingNegAssumes = nwFiringRules map { fr => B.Assume(Boogie.UnaryExpr("!",fr)) }
    
    val exitStmt =
      procVars:::
      basicAssumes:::
      (for (chi <- chInvs) yield Inhalator.visit(chi,renamings)).flatten:::
      inputBounds:::
      (nwPre.map { case (_,r) => B.Assume(r) }) :::
      firingNegAssumes:::
      //outputs:::
      (nwPost.map { case (pos,q) => B.Assert(q,pos,"Network action postcondition might not hold") }) :::
      (for (c <- connections) yield {
        c.to match {
          // Match network output channels
          case pf@PortRef(None,port) => {
            val name = targetMap(pf)
            List(Boogie.Assign(B.R(Boogie.VarExpr(name)), B.R(Boogie.VarExpr(name)) +  (B.Int(nwa.portOutputCount(port)))))
          }
          case _ => Nil
        }
      }).flatten:::
      //
      List(Boogie.Assign(Boogie.VarExpr(BMap.I), Boogie.VarExpr(BMap.R))) :::
      //
      (for (chi <- chInvs) yield 
        Exhalator.visit(chi,"The network might not preserve the channel invariant (" + GeneratedInvariantCount.next + ")"  ,renamings)).flatten :::
      //
      (for (nwi <- nwInvs) yield 
        Exhalator.visit(nwi,"The network might not preserve the network invariant",renamings)).flatten :::
      (for (c <- connections) yield {
        if (c.isOutput) {
          B.Assert(B.C(renamings(c.id)) ==@ B.R(renamings(c.id)),nwa.pos,"The network might not produce the specified number of tokens on output " + c.to.name)
        }
        else {
          B.Assert(B.C(renamings(c.id)) ==@ B.R(renamings(c.id)),nwa.pos,"The network might leave unread tokens on channel " + c.id)
        }
      })
    createBoogieProc(Uniquifier.get(prefix+nwa.fullName+"#exit"),exitStmt)
  }
  
  val nextState = "St#next"
  
  def transSubActionExecution(
      instance: Instance, 
      action: Action, 
      networkRenamings: Map[String,String], // Channels and entities
      basicAssumes: List[Boogie.Assume],
      nwInvs: List[ActorInvariant],
      chInvs: List[ChannelInvariant],
      sourceMap: Map[PortRef,List[String]], 
      targetMap: Map[PortRef,String],
      priorityGuard: List[Boogie.Expr]): (List[Boogie.Stmt],List[Boogie.LocalVar],Boogie.Expr,Boogie.Expr) = {
    
    val actor = instance.actor
    val asgn = new ListBuffer[Boogie.Stmt]()
    val newVars = new ListBuffer[Boogie.LocalVar]()
    
    asgn ++= basicAssumes
            
    val parameterNames = instance.actor.parameters.map(p => p.id)
    
    val actorParamRenames = instance.actor.parameters.map(p => {
      val newName = "ActorParam"+B.Sep+p.id
      newVars += B.Local(newName,B.type2BType(p.typ))
      (p.id,newName)
    }).toMap
    
    for ((name,value) <- (parameterNames zip instance.arguments)) {
      asgn += B.Assume(B.Var(actorParamRenames(name)) ==@ transExpr(value)(networkRenamings))
    }
    
    asgn ++= (for (chi <- chInvs) yield Inhalator.visit(chi,networkRenamings)).flatten  // Assume channel invariants
    
    val actorRenamings = networkRenamings ++ actorParamRenames //++ actorVarRenames
    
    newVars += B.Local(nextState,BType.State)
    
    val firingConds = new ListBuffer[Boogie.Expr]() // Gather firing conditions from each pattern
    val replacements = scala.collection.mutable.HashMap.empty[Id,Expr]
    
    for (ipat <- action.inputPattern) {
      val cId = targetMap(PortRef(Some(instance.id),ipat.portId))
      val cond = B.Int(ipat.numConsumed) lte B.Credit(cId)
      
      val offset = ipat.vars.size-1
      for (v <- ipat.vars) yield {
        val c = Elements.ch(cId,v.typ)
        val acc = Elements.chAcc(c,Minus(Elements.rd0(c.id),IntLiteral(offset)))
        replacements += (v -> acc)
      }
      
      firingConds += cond
    }

    
    val patternVarRenamings = (for (ipat <- action.inputPattern) yield {
      for (v <- ipat.vars) yield {
        val inVar = ipat.portId + B.Sep + v.id
        newVars += B.Local(inVar,B.type2BType(v.typ))
        (v.id,inVar)
      }
    }).flatten.toMap
    
    val outportRenames = (for (outExp <- action.outputPattern) yield {
      (outExp.portId, sourceMap(PortRef(Some(instance.id),outExp.portId))(0))
    }).toMap
    
    val actionRenamings = actorRenamings ++ patternVarRenamings ++ outportRenames ++ action.variables.map(av => {
      val newName = "ActionVar"+B.Sep+av.id
      newVars += B.Local(newName,B.type2BType(av.typ))
      (av.id,newName)
    }).toMap
    
    val replacementMap = replacements.toMap
    
    val renamedGuard = action.guard match {
      case None =>
      case Some(g) =>
        val renamedGuard = IdReplacer.visitExpr(g)(replacements.toMap)
        val transGuard = transExpr(renamedGuard)(actionRenamings)
        asgn += B.Assume(transGuard)
        firingConds += transGuard
    }
    
    val states = actor match {
      case ba: BasicActor => {
        ba.schedule match {
          case Some(schedule) => schedule.transitionsOnAction(action.fullName)
          case None => Nil
        }
      }
      case nw: Network => Nil
    }
    
    val stateGuards = 
      for ((f,t) <- states) yield {
        (B.State(networkRenamings(instance.id)) ==@ Boogie.VarExpr(actor.id+B.Sep+f))
      }
    
        
    val stateInv = {
      if (!stateGuards.isEmpty) stateGuards.reduceLeft((a,b) => a || b)
      else Boogie.BoolLiteral(true)
    }
    asgn += B.Assume(stateInv)
    
    firingConds ++= stateGuards
    val firingCondsWithoutPrio = firingConds.toList
    val firingCondsWithPrio = (priorityGuard map { x: Boogie.Expr => Boogie.UnaryExpr("!",x) }) ::: firingCondsWithoutPrio
    
    val firingRuleWithPrio = {
      if (!firingCondsWithPrio.isEmpty) firingCondsWithPrio.reduceLeft((a,b) => a && b) 
      else Boogie.BoolLiteral(true)
    }
    
    val firingRuleWithoutPrio = {
      if (!firingCondsWithoutPrio.isEmpty) firingCondsWithoutPrio.reduceLeft((a,b) => a && b) 
      else Boogie.BoolLiteral(true)
    }
    
    asgn += B.Assume(firingRuleWithPrio)
    
    for (ActorInvariant(e,_) <- actor.actorInvariants) {
      asgn += B.Assume(transExpr(e.expr)(actorRenamings))
    }
    
    for (pre <- action.requires) {
      val replacedPre = IdReplacer.visitExpr(pre)(replacementMap)
      asgn += B.Assert(
          transExpr(replacedPre)(actionRenamings),pre.pos,
          "Precondition might not hold for instance at " + instance.pos)
    }
    
    for (ipat <- action.inputPattern) {
      var repeats = 0
      while (repeats < ipat.repeat) {
        val cId = targetMap(PortRef(Some(instance.id),ipat.portId))
        for (v <- ipat.vars) {
          asgn += Boogie.Assign(Boogie.VarExpr(patternVarRenamings(v.id)),B.ChannelIdx(cId,B.Read(cId)))
          asgn += Boogie.Assign(B.R(cId), B.R(cId) plus B.Int(1))
        }
        repeats = repeats+1
      }
    }
    
    val instanceBName = actionRenamings(instance.id)
    
    for (opat <- action.outputPattern) {
      val cIds = sourceMap(PortRef(Some(instance.id),opat.portId))
      for (cId <- cIds) {
        var repeats = 0
        while (repeats < opat.repeat) {
          for (e <- opat.exps) {
            asgn += Boogie.Assign(B.ChannelIdx(cId,B.C(cId)),transExpr(e)(actionRenamings))
            if (ftMode) {
              asgn += Boogie.Assign(B.SqnCh(cId,B.C(cId)),B.SqnAct(Boogie.VarExpr( instanceBName )))
            }
            asgn += Boogie.Assign(B.C(cId),B.C(cId) plus B.Int(1))
          }
          repeats = repeats+1
        }
      }
    }
    
    for (post <- action.ensures) {
      asgn += B.Assume(transExpr(post)(actionRenamings))
    }
    
    val nextStateExp =
      for ((f,t) <- states) yield {
        (Boogie.VarExpr(nextState) ==@ Boogie.VarExpr(actor.id+B.Sep+t))
      }
    if (!nextStateExp.isEmpty) {
      asgn += B.Assume(nextStateExp.reduceLeft((a,b) => a || b))
      asgn += Boogie.Assign(B.State(networkRenamings(instance.id)), Boogie.VarExpr(nextState))
    }
    
    if (ftMode && action.aClass != ActionClass.Recovery) {
      asgn += Boogie.Assign(B.SqnAct(instanceBName),B.SqnAct(instanceBName) plus B.Int(1))
    }
    
    asgn ++= (for (chi <- chInvs) yield {
      if (!chi.assertion.free) {
        val baseMsg = 
          "Action at " + action.pos + " ('" + action.fullName + "') for actor instance '" + 
          instance.id + "' might not preserve the channel invariant"
        val msg = baseMsg + " (" + GeneratedInvariantCount.next + ")"
        Exhalator.visit(chi, msg, networkRenamings)
      }
      else {
        Nil
      }
    }).flatten
            
    (asgn.toList, newVars.toList, firingRuleWithPrio, firingRuleWithoutPrio)
  }
  
  
  def translateNetworkInput(
      /*nw: Network,*/ action: Action, pattern: InputPattern,
      nwRenamings: Map[String,String],
      basicAssumes: List[Boogie.Assume],
      /*replacements: Map[Id,IndexAccessor],*/
      sourceMap: Map[PortRef,List[String]],
      chInvs: List[ChannelInvariant]) = {
    
    
    val asgn = new ListBuffer[Boogie.Stmt]()
    asgn ++= basicAssumes
    
    asgn += B.Assume(B.C(nwRenamings(pattern.portId)) < B.Int(pattern.vars.size))
    //asgn ++= limitAssumes
    
    //asgn ++= (chInvs map { x => bAssume(transExpr(x.expr)(nwRenamings)) })
    
    for (chi <- chInvs) {
      asgn ++= Inhalator.visit(chi.expr, "Channel invariant might not hold", nwRenamings)
    }

    asgn += Boogie.Assign(
        B.C(nwRenamings(pattern.portId)),
        B.C(nwRenamings(pattern.portId)) + B.Int(1))
        
    for (r <- action.requires) {
      asgn += B.Assume(transExpr(r)(nwRenamings))
    }
    
    for (chi <- chInvs) {
      asgn ++= Exhalator.visit(chi.expr, "Channel invariant might be falsified by network input", nwRenamings)
    }

    asgn.toList
  }
  
  def createBoogieProc(name: String, stmt: List[Boogie.Stmt]) = {
    val body =
      if (smokeTest) stmt:::List(B.Assert(Boogie.BoolLiteral(false),"["+ name +"]"))
      else stmt
    Boogie.Proc(name,Nil,Nil,Modifies,Nil,body)
  }
  
  object Inhalator extends Halator(true, false)
  object Exhalator extends Halator(false, false)
  //object InhalatorSub extends Halator(true, true)
  //object ExhalatorSub extends Halator(false, true)
  
  abstract class Halator(val inhale: Boolean, val subAction: Boolean) {
    
    def visit(inv: ChannelInvariant, renamings: Map[String,String]): List[Boogie.Stmt] = 
      visit(inv, "Invariant might not hold", renamings)
    
    def visit(inv: ActorInvariant, renamings: Map[String,String]): List[Boogie.Stmt] = 
      visit(inv, "Invariant might not hold", renamings)
    
    def visit(inv: ActorInvariant, msg: String, renamings: Map[String,String]): List[Boogie.Stmt] = {
      val buffer = new ListBuffer[Boogie.Stmt]
      visit(inv.expr, inv.assertion.free)(buffer,msg,renamings);
      buffer.toList
    }
    
    def visit(inv: ChannelInvariant, msg: String, renamings: Map[String,String]): List[Boogie.Stmt] = {
      val buffer = new ListBuffer[Boogie.Stmt]
      visit(inv.expr, inv.assertion.free)(buffer,msg,renamings);
      buffer.toList
    }
    
    def visit(e: Expr, msg: String, renamings: Map[String,String]): List[Boogie.Stmt] = {
      val buffer = new ListBuffer[Boogie.Stmt]
      visit(e, false)(buffer,msg,renamings);
      buffer.toList
    }
    
    def visit(expr: Expr, free: Boolean)(
        implicit buffer: ListBuffer[Boogie.Stmt], msg: String, renamings: Map[String,String]) {
      expr match {
        case And(left,right) => visit(left, free); visit(right, free)
        case Implies(left,right) => {
          val branchBuffer = new ListBuffer[Boogie.Stmt]
          visit(right, free)(branchBuffer,msg,renamings)
          buffer += Boogie.If(transExpr(left),branchBuffer.toList,List.empty) 
        }
        case FunctionApp("delay",params) => {
          if (!subAction) {
            val chCredit = B.C(transExpr(params(0)))
            if (inhale) {
              buffer += Boogie.Assign(chCredit, chCredit + transExpr(params(1)))
            }
            else {
              buffer += Boogie.Assign(chCredit, chCredit - transExpr(params(1)))
            }
          }
        }
//        case FunctionApp("credit", params) => {
//          if (inhale) {
//            val chC = bC(transExpr(params(0)))
//            buffer += Boogie.Assign(chC, chC + transExpr(params(1)))
//          }
//          else {
//            val chR = bC(transExpr(params(0)))
//            buffer += Boogie.Assign(chR, chR + transExpr(params(1)))
//          }
//        }
        case x => {
          if (inhale) buffer += B.Assume(transExpr(x)) 
          else if (!free) {
            buffer += B.Assert(transExpr(x), x.pos, msg)
          }
        }
      }
    }
  
  }
  
  val stmtTranslator = new StmtExpTranslator(ftMode, bvMode); 
  
  def transExprNoRename(exp: Expr): Boogie.Expr = transExpr(exp)(Map.empty)
  
  def transExpr(exp: Expr)(implicit renamings: Map[String,String]): Boogie.Expr = stmtTranslator.transExpr(exp)
  
  def transStmtNoRename(stmt: List[Stmt]): List[Boogie.Stmt] = transStmt(stmt)(Map.empty)
  
  def transStmt(stmts: List[Stmt])(implicit renamings: Map[String,String]): List[Boogie.Stmt] = stmtTranslator.transStmt(stmts)

}

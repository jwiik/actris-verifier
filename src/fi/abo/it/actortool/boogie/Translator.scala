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
  
//  class OldReplacer extends ASTReplacingVisitor[FunctionApp,Id] {
//    override def visitExpr(expr: Expr)(implicit map: Map[FunctionApp,Id]): Expr = {
//      expr match {
//        case FunctionApp("old",params) => {
//          val id = params(0).asInstanceOf[Id]
//          val oldId = Id(id.id + B.Sep + "old")
//          oldId.typ = id.typ
//          oldId
//        }
//        case _ => super.visitExpr(expr)
//      }
//    }
//  }
  
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
    
    val prefix = actor.id+B.Sep
    
    val portChans = 
      ((for (p <- actor.inports) yield B.Local(p.id, B.type2BType(ChanType(p.portType))))
      :::
      (for (p <- actor.outports) yield B.Local(p.id, B.type2BType(ChanType(p.portType))))
      )
    
    val actorVars = new ListBuffer[Boogie.LocalVar]()
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
    
    for (inv <- actor.actorInvariants) {
      invariants += ((inv,transExpr(inv.expr)(Map.empty)))
    }
    
    
    //val oldAssigns = new ListBuffer[Boogie.Assign]()
    for (decl <- actor.variables) {
      val newName = decl.id
      //val oldName = decl.id+B.Sep+"old"
      actorVars  += B.Local(newName,decl.typ)
      //actorVars  += B.Local(oldName,decl.typ)
      //oldAssigns += Boogie.Assign(Boogie.VarExpr(oldName),Boogie.VarExpr(newName))
    }
    
//    for (m <- actor.members) {
//      m match {
//        case inv: ActorInvariant => {
//          invariants += ((inv,transExpr(inv.expr)(Map.empty)))
//        }
//        case Declaration(id,t,_,_) => {
//          actorVars += B.Local(id,t)
//          actorVars += B.Local(id+B.Sep+"old",t)
//        }
//        case FunctionDecl(name,ins,out,body) => {
//          val func = Boogie.Function(
//              actor.id+B.Sep+name, ins.map(i => Boogie.BVar(i.id,B.type2BType(i.typ))), 
//              Boogie.BVar("out"+B.Sep, B.type2BType(out)))
//        }
//        case _ =>
//      }
//    }
    
    val basicAssumes = {
      (for (p <- actor.inports ::: actor.outports) yield {
        val name = p.id
        val list = List(
          //B.Int(0) <= B.I(name),
          //B.I(name) <= B.R(name),
          B.Int(0) <= B.R(name),
          B.R(name) <= B.C(name))
        list.map {x => B.Assume(x)}
      }).flatten
    }
    
    val guards = new ListBuffer[Boogie.Expr]()
    
    val localVarsMap = scala.collection.mutable.HashMap.empty[String,Boogie.LocalVar]
    
    for (a <- actor.actions) {
      val assumes = {
        if (a.init) {
          (for (p <- actor.inports ::: actor.outports) yield {
            val name = p.id
            val list = List(
              B.R(name) ==@ B.Int(0),
              B.C(name) ==@ B.Int(0))
            list.map {x => B.Assume(x)}
          }).flatten
        }
        else basicAssumes
      }
      val (decl,guard) = 
        translateActorAction(a, portChans, assumes, invariants.toList ,actorVars.toList, actor.schedule, prefix)
      decls ++= decl
      
      if (!a.init) {
        for (lv <- portChans ::: actorVars.toList) { // Add variable declarations not already present
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
    
    if (!skipMutualExclusivenessCheck) {
      createMutualExclusivenessCheck(actor, actor.actions, guards.toList, localVarsMap.values.toList, prefix) match {
        case Some(proc) => decls += proc
        case None =>
      }
    }
    
    bActorStates:::decls.toList
  }
  
  def createMutualExclusivenessCheck(
      actor: DFActor, actions: List[Action], guards: List[Boogie.Expr],
      localVars: List[Boogie.LocalVar], prefix: String): Option[Boogie.Proc] = {
    
    val nonInitActions = actions.filter { a => !a.init }
    if (nonInitActions.size > 1) {
      val stmt = localVars:::createMEAssertionsRec(actor,guards)
      Some(createBoogieProc(Uniquifier.get(prefix+B.Sep+"GuardWD"), stmt))
    }
    else None
  }
  
  def createMEAssertionsRec(a: DFActor, guards: List[Boogie.Expr]): List[Boogie.Assert] = {
    guards match {
      case first::rest => {
        val asserts = for (g <- rest) yield {
          B.Assert(Boogie.UnaryExpr("!", first && g) , a.pos, "The actions of actor '" + a.id + "' might not have mutually exclusive guards")
        }
        asserts:::createMEAssertionsRec(a,rest)
      }
      case Nil => Nil
    }
    
  }
  
  def translateActorAction(
       a: Action, 
       portChansBDecls: List[Boogie.LocalVar],
       basicAssumes: List[Boogie.Assume],
       invs: List[(ActorInvariant,Boogie.Expr)],
       actorVarBDecls: List[Boogie.LocalVar],
       schedule: Option[Schedule],
       prefix: String): (List[Boogie.Decl],List[Boogie.Expr]) = {
     
    val asgn = new ListBuffer[Boogie.Stmt]
    val renamings = new ListBuffer[(Id,Expr)]
    val readTokensRules = new ListBuffer[Boogie.Expr]
     
    for (inPat <- a.inputPattern) {
      for ((v,i) <- inPat.vars.zipWithIndex) {
        val id = Id(inPat.portId); id.typ = ChanType(v.typ)
        renamings += ((Id(v.id), IndexAccessor(id, IntLiteral(i))))
      }
      readTokensRules += B.Int(inPat.vars.size) <= B.C(inPat.portId)-B.R(inPat.portId)
    }
    
    asgn ++= portChansBDecls
    asgn ++= actorVarBDecls
    asgn ++= basicAssumes
    
    asgn ++= // Action variable
      (for (v <- a.variables) yield {
        val name = "ActionVar"+B.Sep+v.id
        renamings += ((Id(v.id), Id(name)))
        B.Local(name,v.typ)
      })
     
     val renameMap = renamings.toMap
     
     if (!a.init) {
       // Assume invariants
       asgn ++= (for ((pos,i) <- invs) yield B.Assume(i))
     }
     asgn ++= // Assume preconditions
       (for (p <- a.requires) yield {
         B.Assume(transExprNoRename( IdReplacer.visitExpr(p)(renameMap) ))
       })

     val guards =
       (a.guard match {
         case None => Nil
         case Some(e) => List(transExprNoRename( IdReplacer.visitExpr(e)(renameMap) ))
       })
     
       
     val transitions = schedule match {
       case Some(sched) => sched.transitionsOnAction(a.fullName)
       case None => Nil
     }
     val stateGuards = for ((f,t) <- transitions) yield {
       (B.This ==@ Boogie.VarExpr(prefix+f)) : Boogie.Expr
     }
     val stateGuard = if (stateGuards.isEmpty) Nil else List(stateGuards.reduceLeft((a,b) => (a || b)))
     
     asgn ++= stateGuard map {x => B.Assume(x)}
     asgn ++= guards map {g => B.Assume(g)}
     
     for (ipat <- a.inputPattern) {
       val cId = ipat.portId
       for (v <- ipat.vars) {
         asgn += Boogie.Assign(B.R(cId), B.R(cId) plus B.Int(1))
       }
     }
     
     asgn ++= 
       (a.body match {
         case None => List(B.Assume(Boogie.BoolLiteral(true)))
         case Some(b) => transStmtNoRename( IdReplacer.visitStmt(b)(renameMap) )
       })
     
    for (opat <- a.outputPattern) {
       val cId = opat.portId
       for (v <- opat.exps) {
         asgn += Boogie.Assign(B.C(cId), B.C(cId) plus B.Int(1))
       }
     }
       
     asgn ++= 
       (transitions match {
         case Nil => Nil
         case List((f,t)) => List(Boogie.Assign(B.This, Boogie.VarExpr(prefix+t)))
         case _ => assert(false); Nil
       })
     
     asgn ++= (for (q <- a.ensures) yield {
       B.Assert(transExprNoRename(IdReplacer.visitExpr(q)(renameMap)), q.pos, "Action postcondition might not hold")
     })
     asgn ++= (for ((aInv,bInv) <- invs) yield {
       if (!aInv.assertion.free) B.Assert(bInv,aInv.expr.pos, "Action at " + a.pos + " might not preserve invariant")
       else B.Assume(bInv)
     })
     
     val proc = createBoogieProc(Uniquifier.get(prefix+a.fullName),asgn.toList)
     
     (List(proc), readTokensRules.toList:::stateGuard:::guards)
   }
  
  class NetworkVerificationStructure(
      val actions: List[Action],
      val nwInvariants: List[ActorInvariant],
      val chInvariants: List[ChannelInvariant],
      val connections: List[Connection],
      val entities: List[Instance],
      val sourceMap: Map[PortRef,String],
      val targetMap: Map[PortRef,String],
      val nwRenamings: Map[String,String],
      val entityRenamings: Map[Instance, Map[String, String]],
      val entityVariables: Map[Instance, List[String]],
      val subactorVarDecls: List[Boogie.LocalVar],
      val basicAssumes: List[Boogie.Assume],
      val namePrefix: String)
      
  def translateNetwork(network: Network): List[Boogie.Decl] = {
    val decls = new ListBuffer[Boogie.Decl]()
    val constDecls = new ListBuffer[Boogie.Const]
    
    val nwvs = buildNetworkVerificationStructure(network)
    
    for (e <- nwvs.entities) {
      constDecls += Boogie.Const(nwvs.nwRenamings(e.id),true,BType.Actor)
    }
    for (c <- nwvs.connections) {
      constDecls += Boogie.Const(nwvs.nwRenamings(c.id),true,BType.Chan(B.type2BType(c.typ)))
    }
    
    decls ++= translateNetworkInit(nwvs)
    
    val (subActorProcs, subActorFiringRules) = translateSubActorExecutions(nwvs)
    decls ++= subActorProcs

    for (a <- nwvs.actions) {
      decls ++= translateNetworkAction(a,nwvs,subActorFiringRules)
    }

    constDecls.toList:::decls.toList
  }
  
  def buildNetworkVerificationStructure(network: Network): NetworkVerificationStructure = {
    val actions = network.actions
    val nwInvariants = network.actorInvariants
    val chInvariants = network.channelInvariants
    val connections = network.structure.get.connections
    val entities = network.entities.get.entities
    
    val namePrefix = network.id+B.Sep
    
    val buffer = new ListBuffer[(String,String)]
    for (c <- connections) buffer += ((c.id,namePrefix+c.id))
    
    // Add input/output port names as synonyms to the connected channels
    for (ip <- network.inports) {
      val ch = network.structure.get.getInputChannel(ip.id)
      ch match {
        case Some(c) => buffer += ((ip.id,namePrefix+c.id))
        case None =>
      }
    }
    for (op <- network.outports) {
      val ch = network.structure.get.getOutputChannel(op.id)
      ch match {
        case Some(c) => buffer += ((op.id,namePrefix+c.id))
        case None =>
      }
    }
    
    val (sourceMap,targetMap) = {
      val tempRenamings = buffer.toMap
      val source = scala.collection.mutable.HashMap.empty[PortRef,String]
      val target = scala.collection.mutable.HashMap.empty[PortRef,String]
      for (c <- connections) {
        source(c.from) = tempRenamings(c.id)
        target(c.to) = tempRenamings(c.id)
      }
      (source.toMap,target.toMap)
    }
    
    val entitySpecificRenames = new ListBuffer[(Instance,Map[String,String])]
    val entitySpecificVariables = new ListBuffer[(Instance,List[String])]
    val subactorVarDecls = new ListBuffer[Boogie.LocalVar]

    val renameBuffer = new ListBuffer[(String,String)]()
    
    for (e <- entities) {
      val variables = new ListBuffer[String]()
      val actor = e.actor
      
      buffer += ((e.id,namePrefix+e.id))
     
      for (p <- actor.inports) {
        val newName = targetMap(PortRef(Some(e.id),p.id))
        renameBuffer += ((p.id,newName))
      }
      
      for (p <- actor.outports) {
        val newName = sourceMap(PortRef(Some(e.id),p.id))
        renameBuffer += ((p.id,newName))
      }
      
      for (p <- actor.parameters) {
        val newName = "AP"+B.Sep+e.id+B.Sep+p.id
        subactorVarDecls += B.Local(newName,B.type2BType(p.typ))
        renameBuffer += ((p.id,newName))
      }
      
      for (v <- actor.variables) {
        val newName = "AV"+B.Sep+e.id+B.Sep+v.id
        subactorVarDecls += B.Local(newName,B.type2BType(v.typ))
        variables += newName
        renameBuffer += ((v.id,newName))
      }
      
      entitySpecificVariables += ((e,variables.toList))
      entitySpecificRenames += ((e,renameBuffer.toMap))
      
    }
    
    val networkRenamings = buffer.toMap
    val entityRenamings = entitySpecificRenames.toMap
    val entityVariables = entitySpecificVariables.toMap
    
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
      
      
    new NetworkVerificationStructure(
        actions, nwInvariants, chInvariants, connections, entities, sourceMap, targetMap, 
        networkRenamings, entityRenamings, entityVariables, subactorVarDecls.toList, basicAssumes, namePrefix)
  }
  
  
  def translateNetworkInit(nwvs: NetworkVerificationStructure): List[Boogie.Decl] = {
    
    val asgn = new ListBuffer[Boogie.Stmt]
    val vars = new ListBuffer[Boogie.LocalVar]
    
    asgn ++= nwvs.subactorVarDecls
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
      
      val renamings = nwvs.nwRenamings ++  nwvs.entityRenamings(inst)
      
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
      asgn ++= Exhalator.visit(chi, "Network initialization might not establish the channel invariant", nwvs.nwRenamings)
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
            nwvs.subactorVarDecls:::
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
    
//    boogieProcs += transNetworkEntry(
//        nwa, basicAssumes, nwInvs, chInvs, renamings, connections, procVars.toList, prefix)
    
    for (ipat <- nwa.inputPattern) {
      val stmt = translateNetworkInput(nwa, ipat, nwvs)
      boogieProcs += createBoogieProc(Uniquifier.get(nwvs.namePrefix+nwa.fullName+B.Sep+"input"+B.Sep+ipat.portId),stmt)
    }
    
    boogieProcs += transNetworkExit(nwa, nwvs, subactorFiringRules)
    
    // The complete list of Boogie procedure generated for this network action
    boogieProcs.toList
  }
  
//  def transNetworkEntry(
//        nwa: Action,
//        basicAssumes: List[Boogie.Assume],
//        nwInvs: List[ActorInvariant],
//        chInvs: List[ChannelInvariant],
//        renamings: Map[String,String], // Channels and entities
//        connections: List[Connection],
//        procVars: List[Boogie.LocalVar],
//        prefix: String) = {
//    
//    val entryStmt = 
//      procVars.toList :::
//      basicAssumes:::
//      List(B.Assume(Boogie.VarExpr(BMap.I) ==@ Boogie.VarExpr(BMap.R))) :::
//      (for (c <- connections) yield {
//        B.Assume(B.R(renamings(c.id)) ==@ B.C(renamings(c.id)))
//      }) :::
//      (for (nwi <- nwInvs) yield 
//        Inhalator.visit(nwi,"",renamings)).flatten :::
//      (for (chi <- chInvs) yield 
//        Inhalator.visit(chi,""  ,renamings)).flatten
//        
//      createBoogieProc(Uniquifier.get(prefix+nwa.fullName+"#entry"),entryStmt)
//  }
  
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
      nwvs.subactorVarDecls:::
      nwvs.basicAssumes:::
      (for (chi <- nwvs.chInvariants) yield Inhalator.visit(chi,nwvs.nwRenamings)).flatten:::
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
        Exhalator.visit(chi,"The network might not preserve the channel invariant"  ,nwvs.nwRenamings)).flatten :::
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
      priorityGuard: List[Boogie.Expr]): (List[Boogie.Stmt],List[Boogie.LocalVar],Boogie.Expr,Boogie.Expr) = {
    
    val actor = instance.actor
    val asgn = new ListBuffer[Boogie.Stmt]()
    val newVars = new ListBuffer[Boogie.LocalVar]()
        
    asgn ++= nwvs.basicAssumes
            
    
    asgn ++= (for (chi <- nwvs.chInvariants) yield Inhalator.visit(chi,nwvs.nwRenamings)).flatten  // Assume channel invariants
    
    newVars += B.Local(nextState,BType.State)
    
    val firingConds = new ListBuffer[Boogie.Expr]() // Gather firing conditions from each pattern
    val replacements = scala.collection.mutable.HashMap.empty[Id,Expr]
    
    for (ipat <- action.inputPattern) {
      val cId = nwvs.targetMap(PortRef(Some(instance.id),ipat.portId))
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
    
    val renamings = nwvs.nwRenamings ++ nwvs.entityRenamings(instance) ++ patternVarRenamings

    
    val replacementMap = replacements.toMap
    
    val renamedGuard = action.guard match {
      case None =>
      case Some(g) =>
        val renamedGuard = IdReplacer.visitExpr(g)(replacements.toMap)
        val transGuard = transExpr(renamedGuard)(renamings)
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
        (B.State(renamings(instance.id)) ==@ Boogie.VarExpr(actor.id+B.Sep+f))
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
      asgn += B.Assume(transExpr(e.expr)(renamings))
    }
    
    for (pre <- action.requires) {
      val replacedPre = IdReplacer.visitExpr(pre)(replacementMap)
      asgn += B.Assert(
          transExpr(replacedPre)(renamings),pre.pos,
          "Precondition might not hold for instance at " + instance.pos)
    }
    
    
    
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
    
    for (ev <- nwvs.entityVariables(instance)) {
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
    
    val nextStateExp =
      for ((f,t) <- states) yield {
        (Boogie.VarExpr(nextState) ==@ Boogie.VarExpr(actor.id+B.Sep+t))
      }
    if (!nextStateExp.isEmpty) {
      asgn += B.Assume(nextStateExp.reduceLeft((a,b) => a || b))
      asgn += Boogie.Assign(B.State(renamings(instance.id)), Boogie.VarExpr(nextState))
    }
    
    if (ftMode && action.aClass != ActionClass.Recovery) {
      asgn += Boogie.Assign(B.SqnAct(renamings(instance.id)),B.SqnAct(renamings(instance.id)) plus B.Int(1))
    }
    for (ActorInvariant(e,_) <- actor.actorInvariants) {
      asgn += B.Assume(transExpr(e.expr)(renamings))
    }
    asgn ++= (for (chi <- nwvs.chInvariants) yield {
      if (!chi.assertion.free) {
        val msg = 
          "Action at " + action.pos + " ('" + action.fullName + "') for actor instance '" + 
          instance.id + "' might not preserve the channel invariant"
        Exhalator.visit(chi, msg, nwvs.nwRenamings)
      }
      else {
        Nil
      }
    }).flatten
            
    (asgn.toList, newVars.toList, firingRuleWithPrio, firingRuleWithoutPrio)
  }
  
  
  def translateNetworkInput(action: Action, pattern: InputPattern, nwvs: NetworkVerificationStructure) = {
    
    
    val asgn = new ListBuffer[Boogie.Stmt]()
    asgn ++= nwvs.subactorVarDecls
    asgn ++= nwvs.basicAssumes
    
    asgn += B.Assume(B.C(nwvs.nwRenamings(pattern.portId)) < B.Int(pattern.vars.size))

    for (chi <- nwvs.chInvariants) {
      asgn ++= Inhalator.visit(chi.expr, "Channel invariant might not hold", nwvs.nwRenamings)
    }

    asgn += Boogie.Assign(
        B.C(nwvs.nwRenamings(pattern.portId)),
        B.C(nwvs.nwRenamings(pattern.portId)) + B.Int(1))
        
    for (r <- action.requires) {
      asgn += B.Assume(transExpr(r)(nwvs.nwRenamings))
    }
    
    for (chi <- nwvs.chInvariants) {
      asgn ++= Exhalator.visit(chi.expr, "Channel invariant might be falsified by network input", nwvs.nwRenamings)
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

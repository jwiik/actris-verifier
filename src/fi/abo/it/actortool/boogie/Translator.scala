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


class Translator(val fixedBaseLength: Int, val ftMode: Boolean, implicit val bvMode: Boolean) {  
  
  import Helper._
  import AstElement._
  
  
  
  final val Modifies = List(BMap.C, BMap.R, BMap.M, BMap.I, BMap.St):::
    (if (!ftMode) Nil else List(BMap.SqnCh, BMap.SqnActor))
  
  object Annot {
    final val Error = "error"
  }
  
  object Uniquifier {
    private var i = -1
    def get(id: String) = { i = i+1; id+Sep+(i.toString) }
  }
  
  object GeneratedInvariantCount {
    private var i = -1
    def next = { i = i+1; "#"+(i.toString) }
  }
  
  object AstElement {
    def ch(name: String, carriedType: Type) = {
      val i = Id(name)
      i.typ = ChanType(carriedType)
      i
    }
    def rd(ch: Id) = {
      val fa = FunctionApp("rd",List(ch))
      fa.typ = IntType(32)
      fa
    }
    def urd(ch: Id) = {
      val fa = FunctionApp("urd",List(ch))
      fa.typ = IntType(32)
      fa
    }
    def chAcc(ch: Id, idx: Expr) = {
      val t = ch.typ.asInstanceOf[ChanType].contentType
      val ia = IndexAccessor(ch,idx)
      ia.typ = t
      ia
    }
  }
  
  
  
  def translateProgram(decls: List[TopDecl]): List[Boogie.Decl] = {
    
    if (ftMode) BoogiePrelude.addComponent(SeqNumberingPL)
    
    // Add axioms and assumptions
    val initDecls =
      if (fixedBaseLength > 0) List(Boogie.Axiom(bBaseL ==@ bInt(fixedBaseLength)))
      else Nil
      
    val bProgram = decls flatMap {
      case a: BasicActor => translateActor(a)
      case n: Network => translateNetwork(n)
      case u: DataUnit => Nil
    }
    
    return initDecls:::bProgram
      
  }
    
  def translateActor(actor: BasicActor): List[Boogie.Decl] = {
    val decls = new ListBuffer[Boogie.Decl]()
    val actions = new ListBuffer[Action]()
    val invariants = new ListBuffer[(ActorInvariant,Boogie.Expr)]()
    val actorVars = new ListBuffer[Boogie.LocalVar]()
    
    val prefix = actor.id+Sep
    
    val portChans = 
      ((for (p <- actor.inports) yield bLocal(p.id, type2BType(ChanType(p.portType))))
      :::
      (for (p <- actor.outports) yield bLocal(p.id, type2BType(ChanType(p.portType))))
      )
    
    val states = actor.schedule match {
      case Some(s) => 
        actorVars += bThisDecl
        s.states
      case None => Nil
    }
    
    val bActorStates = for (s <- states) yield {
      //actorVars += bLocal(currentState,BType.State)
      Boogie.Const(prefix+s,true,BType.State)
    }
    
    if (!states.isEmpty) {
      val allowedStatesInvariant = (for (s <- states) yield {
        bThis ==@ Boogie.VarExpr(prefix+s)
      }).reduceLeft((a,b) => (a || b))
      val ai = ActorInvariant(Assertion(null,false),true)
      ai.pos = actor.pos
      invariants += ((ai,allowedStatesInvariant))
    }
      
    for (m <- actor.members) {
      m match {
        case inv: ActorInvariant => invariants += ((inv,transExpr(inv.expr)(Map.empty)))
        case a: Action => actions += a
        case Declaration(id,t,_,_) => actorVars += bLocal(id, t)
        case FunctionDecl(name,ins,out,body) => {
          val func = Boogie.Function(
              actor.id+Sep+name, ins.map(i => Boogie.BVar(i.id,type2BType(i.typ))), 
              Boogie.BVar("out"+Sep, type2BType(out)))
          
        }
        case _ =>
      }
    }
    
    val guards = new ListBuffer[Boogie.Expr]()
    
    val localVarsMap = scala.collection.mutable.HashMap.empty[String,Boogie.LocalVar]
    
    for (a <- actions) {
      val (decl,guard,localVars) = translateActorAction(a, portChans, invariants.toList,actorVars.toList,actor.schedule,prefix)
      decls ++= decl
      
      if (!a.init) {
        for (lv <- localVars) { // Add variable declarations not already present
          if (!localVarsMap.contains(lv.x.id)) {
            localVarsMap += (lv.x.id -> lv)
          }
        }
        
        val inputPatExp = for (ip <- a.inputPattern) yield { // Build input pattern expressions
          bInt(ip.numConsumed) <= Boogie.VarExpr(ip.portId+Sep+"NumRead")
        }
        
        // And together the input pattern expressions and the guard expression
        if (!(inputPatExp.isEmpty && guard.isEmpty)) {
          guards += (inputPatExp:::guard).reduceLeft((a,b) => (a && b))
        }
      }
    } // end for
    
//    val nonInitActions = actions.filter { a => !a.init }
//    if (nonInitActions.size > 1) {
//      val localVarDecls = localVarsMap.values.toList
//      val assertion = bAssert(Boogie.UnaryExpr("!", guards.reduceLeft((a,b) => (a && b))),actor.pos,
//          "The actions might not have mutually exclusive guards")
//      val stmt = localVarDecls:::portTokenVars:::List(assertion)
//      
//      decls += Boogie.Proc(Uniquifier.get(prefix+Sep+"GuardWD"),Nil,Nil,Modifies,Nil,stmt)
//    }
    
    bActorStates:::decls.toList
  }
  
   def translateActorAction(
       a: Action, 
       portChans: List[Boogie.LocalVar],
       invs: List[(ActorInvariant,Boogie.Expr)],
       actorVars: List[Boogie.LocalVar],
       schedule: Option[Schedule],
       prefix: String): (List[Boogie.Decl],List[Boogie.Expr],List[Boogie.LocalVar]) = {
     
     val renamings = new ListBuffer[(Id,Expr)]
     
     for (inPat <- a.inputPattern) {
       for ((v,i) <- inPat.vars.zipWithIndex) {
         //val name = "IV"+Sep+(inPat.portId)+Sep+i
         val id = Id(inPat.portId); id.typ = ChanType(v.typ)
         renamings += ((Id(v.id), IndexAccessor(id, IntLiteral(i))))
         //bLocal(name,v.typ)
       }
     }
     
     val actionVars = for (v <- a.variables) yield {
       val name = "ActionVar"+Sep+v.id
       renamings += ((Id(v.id), Id(name)))
       bLocal(name,v.typ)
     }
     
     val renameMap = renamings.toMap
     
     val invAssumes = for ((pos,i) <- invs) yield Helper.bAssume(i)
     val preCondAssumes = for (p <- a.requires) yield {
       Helper.bAssume(transExprNoRename( IdReplacer.visitExpr(p)(renameMap) ))
     }
     
     val guards = a.guard match {
       case None => Nil
       case Some(e) => List(transExprNoRename( IdReplacer.visitExpr(e)(renameMap) ))
     }
     
     val guardAssume = guards map {g => bAssume(g)}
     
     
     val transitions = schedule match {
       case Some(sched) => sched.transitionsOnAction(a.fullName)
       case None => Nil
     }
     
     val stateGuards = for ((f,t) <- transitions) yield {
       (bThis ==@ Boogie.VarExpr(prefix+f))
     }
     
     val stateGuard = if (stateGuards.isEmpty) bBool(true) else stateGuards.reduceLeft((a,b) => (a || b))
     val stateGuardAssume = List(bAssume(stateGuard))
     
     val body = a.body match {
       case None => List(bAssume(Boogie.BoolLiteral(true)))
       case Some(b) => transStmtNoRename( IdReplacer.visitStmt(b)(renameMap) )
     }
     val stateUpdates = transitions match {
       case Nil => Nil
       case List((f,t)) => List(Boogie.Assign(bThis, Boogie.VarExpr(prefix+t)))
       case _ => assert(false); Nil
     }
     val invAsserts = for ((aInv,bInv) <- invs) yield {
       if (aInv.assertion.free) bAssert(bInv,aInv.expr.pos, "Action at " + a.pos + " might not preserve invariant")
       else bAssume(bInv)
     }
     val postCondAsserts = for (q <- a.ensures) yield {
       bAssert(transExprNoRename(IdReplacer.visitExpr(q)(renameMap)), q.pos, "Action postcondition might not hold")
     }
     val stmt =
       portChans:::
       actorVars:::
       //inputVars:::
       actionVars:::
       invAssumes:::
       preCondAssumes:::
       stateGuardAssume:::
       guardAssume:::
       body:::
       stateUpdates:::
       postCondAsserts:::
       invAsserts
     (List(Boogie.Proc(Uniquifier.get(prefix+a.fullName),Nil,Nil,Modifies,Nil,stmt)),stateGuard::guards,actorVars/*:::inputVars*/)
   }
  
  def translateNetwork(network: Network): List[Boogie.Decl] = {
    val decls = new ListBuffer[Boogie.Decl]()
    val actions = network.actions
    val nwInvariants = network.actorInvariants
    val chInvariants = network.channelInvariants
    val connections = network.structure.get.connections
    val entities = network.entities.get.entities
    
    val namePrefix = network.id+Sep
    
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
          val avName = namePrefix+e.id+Sep+"AV"+Sep+av.id
          buffer += ((av.id,avName))
          decls += bLocal(avName,av.typ)
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
          bInt(0) <= bI(name),
          bI(name) <= bR(name),
          bR(name) <= bC(name))
        val list2 = (
        c.to match {
          case PortRef(None,x) => List(bI(name) ==@ bR(name))
          case _ => Nil
        })
        (list1 ::: list2).map(x => bAssume(x))
      }).flatten
    
    decls ++= translateNetworkInit(basicAssumes, nwInvariants, chInvariants, networkRenamings, 
        sourceMap, targetMap, entities, connections, network.id+Sep)

    for (a <- actions) {
      decls ++= translateNetworkAction(
          a, basicAssumes, nwInvariants,chInvariants,networkRenamings,sourceMap,targetMap,
          entities,connections,subactorVarDecls,network.id+Sep)
    }

    decls.toList
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
      asgn += bAssume(bC(networkRenamings(c.id)) ==@ bInt(0))
      asgn += bAssume(bR(networkRenamings(c.id)) ==@ bInt(0))
    }
    
    if (ftMode) {
      for (e <- entities) {
        asgn += bAssume(bSqnAct(networkRenamings(e.id)) ==@ bInt(0))
      }
    }
    
    
    for (inst <- entities) {
      val actor = inst.actor
      val actorParams = actor.parameters.map(p => {
        val newName = "ActorParam"+Sep+inst.id+Sep+p.id
        vars += bLocal(newName,type2BType(p.typ))
        (Id(p.id),Id(newName))
      }).toMap
      val parameterNames = actor.parameters map {x => Id(x.id)}
      for ((name,value) <- (parameterNames zip inst.arguments)) {
        // Add assumptions about the values of the actor parameters
        asgn += bAssume(transExpr(
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
                  bChannelIdx(cId,bC(cId)),transExpr(renamedExp)(networkRenamings))
              asgn += Boogie.Assign(bC(cId),bC(cId) plus bInt(1))
            }
          }
        }
      }
      
      actor.members.find(_.isSchedule) match {
        case Some(s) => {
          val schedule = s.asInstanceOf[Schedule]
          asgn += bAssume(bState(networkRenamings(inst.id)) ==@
              Boogie.VarExpr(actor.fullName+Sep+schedule.initState))
        }
        case None =>
      }
    }
    for (chi <- chInvs) {
      asgn ++= Exhalator.visit(
          chi, "Network initialization might not establish the channel invariant (" + GeneratedInvariantCount.next + ")", networkRenamings)
    }
    for (nwi <- nwInvs) {
      asgn ++= Exhalator.visit(
          nwi, "Network initialization might not establish the network invariant", networkRenamings)
    }
    val stmt = vars.toList:::asgn.toList
    List(Boogie.Proc(Uniquifier.get(prefix+"init"),Nil,Nil,Modifies,Nil,stmt))
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
       prefix: String): List[Boogie.Decl] = {
    
    val constDecls = new ListBuffer[Boogie.Const]
    val procVars = new ListBuffer[Boogie.LocalVar]
    
    procVars ++= subactorVarDecls
    
    val actionRenamings = new ListBuffer[(String,String)]
    for (v <- nwa.variables) {
      val newName = "ActionVar"+Sep+v.id
      procVars += bLocal(newName,type2BType(v.typ))
      actionRenamings += ((v.id,newName))
    }
    

    
    val renamings = networkRenamings ++ actionRenamings.toMap
    
    val limitAssumesBuffer = new ListBuffer[Boogie.Assume]
    val limitLoopCondBuffer = new ListBuffer[Boogie.Expr]
    val assumesBuffer = new ListBuffer[Boogie.Assume]
    
    for (e <- entities) {
      constDecls += Boogie.Const(networkRenamings(e.id),true,BType.Actor)
    }
    for (c <- connections) {
      constDecls += Boogie.Const(networkRenamings(c.id),true,BType.Chan(type2BType(c.typ)))
      c.from match {
        case PortRef(None,p) =>
          limitAssumesBuffer += bAssume(bLimit(networkRenamings(c.id)) ==@ bInt(nwa.portInputCount(p))*bBaseL)
          limitAssumesBuffer += bAssume(bR(networkRenamings(c.id)) - bI(networkRenamings(c.id)) <= bLimit(networkRenamings(c.id)))
          limitLoopCondBuffer += bR(networkRenamings(c.id)) - bI(networkRenamings(c.id)) < bLimit(networkRenamings(c.id))
        case _ =>
      }
//      c.to match {
//        case PortRef(None,p) =>
//          limitAssumesBuffer += bAssume(bLimit(networkRenamings(c.id)) ==@ bInt(nwa.portOutputCount(p))*bBaseL)
//        case _ =>
//      }
      assumesBuffer += bAssume(bCredit(networkRenamings(c.id)) ==@ bInt(0))
    }
    
    val constDecl = constDecls.toList
    val limitAssumes = limitAssumesBuffer.toList
    val rcAssumes = assumesBuffer.toList
    val limitLoopConds = limitLoopCondBuffer.toList
    
    var replacements = Map[Id,IndexAccessor]()
    
    for (ipat <- nwa.inputPattern) {
      assert(sourceMap(PortRef(None,ipat.portId)).size == 1)
      val inChan = Id(sourceMap(PortRef(None,ipat.portId))(0))
      var i = 0
      for (v <- ipat.vars) {
        inChan.typ = ChanType(v.typ)
        val acc = IndexAccessor(inChan,IntLiteral(i))
        Resolver.resolveExpr(acc)
        replacements = replacements + (v -> acc)
        i = i+1
      }
    }
    
    for ((decl,portId,index) <- nwa.placeHolderVars) {
      val outChan = Id(targetMap(PortRef(None,portId))); outChan.typ = ChanType(decl.typ)
      val acc = IndexAccessor(outChan,IntLiteral(index))
      Resolver.resolveExpr(acc)
      replacements = replacements + (Id(decl.id) -> acc)      
    }

    val outputs = (for (opat <- nwa.outputPattern) yield {
      val outChan = targetMap(PortRef(None,opat.portId))
      var i = 0
      (for (e <- opat.exps) yield {
        val renamedExp = IdReplacer.visitExpr(e)(replacements)
        val id = Id(outChan)
        id.typ = ChanType(e.typ)
        val acc = if (0 < i) IndexAccessor(id,IntLiteral(i)) else IndexAccessor(id,IntLiteral(i))
        Resolver.resolveExpr(acc)
        
        val stmts =
          if (e.isInstanceOf[Id] && (nwa.placeHolderVars exists {case (d,p,i) => d.id == e.asInstanceOf[Id].id  })) {
            Nil
          }
          else {
            List(bAssert(transExpr(acc)(renamings) ==@ transExpr(renamedExp)(renamings),
                e.pos,"Network output might not conform to the specified action output"))    
          }
        i = i+1
        stmts
      }).flatten
    }).flatten
    

    
    val nwPre = for (p <- nwa.requires) yield 
      bAssume(transExpr(IdReplacer.visitExpr(p)(replacements))(renamings))
    val nwPost = for (q <- nwa.ensures) yield 
      (q.pos,transExpr(IdReplacer.visitExpr(q)(replacements))(renamings))

      
    // Network action entry
    val entryStmt = 
      procVars.toList :::
      basicAssumes:::
      //actorSqnAssumes :::
      limitAssumes :::
      rcAssumes :::
      List(bAssume(Boogie.VarExpr(BMap.I) ==@ Boogie.VarExpr(BMap.R))) :::
      (for (nwi <- nwInvs) yield Inhalator.visit(nwi, networkRenamings)).flatten :::
      (for (chi <- chInvs) yield Inhalator.visit(chi, networkRenamings)).flatten :::
      nwPre:::
      (for (chi <- chInvs) yield {
        if (!chi.assertion.free) {
          val baseMsg = "Channel invariant might not hold on action entry"
          val msg = baseMsg + " (" + GeneratedInvariantCount.next + ")"
          Exhalator.visit(chi,msg,renamings)
        }
        else Nil
      }).flatten
    val initProc = Boogie.Proc(Uniquifier.get(prefix+nwa.fullName+"#entry"),Nil,Nil,Modifies,Nil,entryStmt)
    
    // Sub-actor executions
    val childActionProcs = new ListBuffer[Boogie.Proc]()
    //val actorVars = new ListBuffer[Declaration]()
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
          val procName = prefix+nwa.fullName+Sep+actor.id+Sep+ca.fullName
          
          val prFiringRule = higherPrioAction map {a => actorFiringRulesNoPrio(a)}
          
          val (subActorStmt,newVarDecls,firingRulePrio,firingRuleNoPrio) = 
            transSubActionExecution(
                inst, ca, networkRenamings, basicAssumes, limitAssumes, chInvs, sourceMap, 
                targetMap, prFiringRule)

          val stmt = 
            procVars.toList :::
            newVarDecls :::
            subActorStmt
          childActionProcs += Boogie.Proc(Uniquifier.get(procName),Nil,Nil,Modifies,Nil,stmt)
          actorFiringRulesNoPrio += (ca -> firingRuleNoPrio)
          actorFiringRulesPrio += (ca -> firingRulePrio)
        }
      }
      nwFiringRules ++= actorFiringRulesPrio.values
    }
    val nwFiringRuleList = nwFiringRules.toList
    
    
    // Network action exit
    //val firingNeg = Boogie.UnaryExpr("!", nwFiringRules.reduceLeft((a,b) => a || b))
    val firingNegAssumes = nwFiringRuleList map { fr => bAssume(Boogie.UnaryExpr("!",fr)) }
    val limitNegAssumes = limitLoopConds map { c => bAssume(Boogie.UnaryExpr("!",c)) } 
    
    val exitStmt =
      procVars.toList:::
      basicAssumes:::
      limitAssumes:::
      (for (chi <- chInvs) yield Inhalator.visit(chi,renamings)).flatten:::
      limitNegAssumes:::
      firingNegAssumes:::
      outputs:::
      (nwPost.map { case (pos,q) => bAssert(q,pos,"Network action postcondition might not hold") }) :::
      (for (c <- connections) yield {
        c.to match {
          // Match network output channels
          case pf@PortRef(None,port) => {
            val name = targetMap(pf)
            List(
                Boogie.Assign(
//                    bC(Boogie.VarExpr(name)), bC(Boogie.VarExpr(name)) -  (bInt(nwa.portOutputCount(port))*bBaseL)
                    bR(Boogie.VarExpr(name)), bR(Boogie.VarExpr(name)) +  (bInt(nwa.portOutputCount(port))*bBaseL)
                  )
              )
          }
          case _ => Nil
        }
      }).flatten:::
      //
      List(Boogie.Assign(Boogie.VarExpr(BMap.I), Boogie.VarExpr(BMap.R))) :::
      //
      (for (chi <- chInvs) yield 
        Exhalator.visit(chi,"The network might not preserve the channel invariant (" + GeneratedInvariantCount.next + ")"  ,networkRenamings)).flatten :::
      //
      (for (nwi <- nwInvs) yield 
        Exhalator.visit(nwi,"The network might not preserve the network invariant",networkRenamings)).flatten :::
      (for (c <- connections) yield {
        c.to match {
          case PortRef(None,p) =>
            bAssert(bCredit(networkRenamings(c.id)) ==@ bInt(0),nwa.pos,"The network might not produce the specified number of tokens on output " + p)
          case PortRef(_,_) => {
            
            bAssert(bCredit(networkRenamings(c.id)) ==@ bInt(0),nwa.pos,"The network might leave unread tokens on channel " + c.id)
          }
       }
      })
    val exitProc = Boogie.Proc(Uniquifier.get(prefix+nwa.fullName+"#exit"),Nil,Nil,Modifies,Nil,exitStmt)
    
    // The complete list of Boogie procedure generated for this network
    constDecl:::initProc::childActionProcs.toList:::List(exitProc)
  }
  
  val nextState = "St#next"
  
  def transSubActionExecution(
      instance: Instance, 
      action: Action, 
      networkRenamings: Map[String,String], // Channels and entities
      basicAssumes: List[Boogie.Assume],
      cInits: List[Boogie.Assume],
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
      val newName = "ActorParam"+Sep+p.id
      newVars += bLocal(newName,type2BType(p.typ))
      (p.id,newName)
    }).toMap
    
    //renameMap = renameMap ++ actorParams
    for ((name,value) <- (parameterNames zip instance.arguments)) {
      // Add assumptions about the values of the actor parameters
      asgn += bAssume(bVar(actorParamRenames(name)) ==@ transExpr(value)(networkRenamings))
    }
    
    asgn ++= cInits // Assumptions about initial state of channels
    asgn ++= (for (chi <- chInvs) yield Inhalator.visit(chi,networkRenamings)).flatten  // Assume channel invariants
    
    
    val actorRenamings = networkRenamings ++ actorParamRenames //++ actorVarRenames
    
    newVars += bLocal(nextState,BType.State)
    
    val firingConds = new ListBuffer[Boogie.Expr]() // Gather firing conditions from each pattern
    val replacements = scala.collection.mutable.HashMap.empty[Id,Expr]
    
    for (ipat <- action.inputPattern) {
      val cId = targetMap(PortRef(Some(instance.id),ipat.portId))
      val cond = bInt(ipat.numConsumed) lte bCredit(cId)
      
      val offset = ipat.vars.size-1
      for (v <- ipat.vars) yield {
        val c = ch(cId,v.typ)
        val acc = chAcc(c,Minus(rd(c),IntLiteral(offset)))
        replacements += (v -> acc)
      }
      
      firingConds += cond
    }

    
    val patternVarRenamings = (for (ipat <- action.inputPattern) yield {
      for (v <- ipat.vars) yield {
        val inVar = ipat.portId + Sep + v.id
        newVars += bLocal(inVar,type2BType(v.typ))
        (v.id,inVar)
      }
    }).flatten.toMap
    
    val actionRenamings = actorRenamings ++ patternVarRenamings ++ action.variables.map(av => {
      val newName = "ActionVar"+Sep+av.id
      newVars += bLocal(newName,type2BType(av.typ))
      (av.id,newName)
    }).toMap
    
    val replacementMap = replacements.toMap
    
    val renamedGuard = action.guard match {
      case None =>
      case Some(g) =>
        val renamedGuard = IdReplacer.visitExpr(g)(replacements.toMap)
        val transGuard = transExpr(renamedGuard)(actionRenamings)
        asgn += bAssume(transGuard)
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
        (bState(networkRenamings(instance.id)) ==@ Boogie.VarExpr(actor.id+Sep+f))
      }
    
        
    val stateInv = {
      if (!stateGuards.isEmpty) stateGuards.reduceLeft((a,b) => a || b)
      else Boogie.BoolLiteral(true)
    }
    asgn += bAssume(stateInv)
    
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
    
    asgn += bAssume(firingRuleWithPrio)
    
    for (ActorInvariant(e,_) <- actor.actorInvariants) {
      asgn += bAssume(transExpr(e.expr)(actorRenamings))
    }
    
    for (pre <- action.requires) {
      val replacedPre = IdReplacer.visitExpr(pre)(replacementMap)
      asgn += bAssert(
          transExpr(replacedPre)(actionRenamings),pre.pos,
          "Precondition might not hold for instance at " + instance.pos)
    }
    
    for (ipat <- action.inputPattern) {
      val cId = targetMap(PortRef(Some(instance.id),ipat.portId))
      for (v <- ipat.vars) {
        asgn += Boogie.Assign(Boogie.VarExpr(patternVarRenamings(v.id)),bChannelIdx(cId,/*bStep(cId)+*/bRead(cId)))
        //asgn += Boogie.Assign(bRead(cId),bRead(cId) plus bInt(1))
        //asgn += Boogie.Assign(bCredit(cId),bCredit(cId) minus bInt(1))
        asgn += Boogie.Assign(bR(cId), bR(cId) plus bInt(1))
      }
    }
 
    
    for (post <- action.ensures) {
      asgn += bAssume(transExpr(post)(actionRenamings))
    }
    
    val instanceBName = actionRenamings(instance.id)
    
    for (opat <- action.outputPattern) {
      val cIds = sourceMap(PortRef(Some(instance.id),opat.portId))
      for (cId <- cIds) {
        for (e <- opat.exps) {
          //val renamedExp = IdToIdReplacer.visitExpr(e)(renameMap)
          //asgn += Boogie.Assign(bChannelIdx(cId,bRead(cId) plus bCredit(cId)),transExpr(e)(actionRenamings))
          asgn += Boogie.Assign(bChannelIdx(cId,bC(cId)),transExpr(e)(actionRenamings))
          if (ftMode) {
            //asgn += Boogie.Assign(bSqnCh(cId,bRead(cId) plus bCredit(cId)),bSqnAct(Boogie.VarExpr( instanceBName )))
            asgn += Boogie.Assign(bSqnCh(cId,bC(cId)),bSqnAct(Boogie.VarExpr( instanceBName )))
          }
          //asgn += Boogie.Assign(bCredit(cId),bCredit(cId) plus bInt(1))
          asgn += Boogie.Assign(bC(cId),bC(cId) plus bInt(1))
        }
      }
    }
    
    val nextStateExp =
      for ((f,t) <- states) yield {
        (Boogie.VarExpr(nextState) ==@ Boogie.VarExpr(actor.id+Sep+t))
      }
    if (!nextStateExp.isEmpty) {
      asgn += bAssume(nextStateExp.reduceLeft((a,b) => a || b))
      asgn += Boogie.Assign(bState(networkRenamings(instance.id)), Boogie.VarExpr(nextState))
    }
    
    if (ftMode && action.aClass != ActionClass.Recovery) {
      asgn += Boogie.Assign(bSqnAct(instanceBName),bSqnAct(instanceBName) plus bInt(1))
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
  

  
  object Inhalator extends Halator(true)
  object Exhalator extends Halator(false)
  
  abstract class Halator(val inhale: Boolean) {
    import Helper._
    
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
    
    def visit(expr: Expr, free: Boolean)(implicit buffer: ListBuffer[Boogie.Stmt], msg: String, renamings: Map[String,String]) {
      expr match {
        case And(left,right) => visit(left, free); visit(right, free)
        case Implies(left,right) => {
          val branchBuffer = new ListBuffer[Boogie.Stmt]
          visit(right, free)(branchBuffer,msg,renamings)
          buffer += Boogie.If(transExpr(left),branchBuffer.toList,List.empty) 
        }
        case FunctionApp("tokens",params) => {
          val chCredit = bC(transExpr(params(0)))
          if (inhale) {
            buffer += Boogie.Assign(chCredit, chCredit + transExpr(params(1)))
          }
          else {
            buffer += Boogie.Assign(chCredit, chCredit - transExpr(params(1)))
          }
        }
        case FunctionApp("credit", params) => {
          if (inhale) {
            val chC = bC(transExpr(params(0)))
            buffer += Boogie.Assign(chC, chC + transExpr(params(1)))
          }
          else {
            val chR = bC(transExpr(params(0)))
            buffer += Boogie.Assign(chR, chR + transExpr(params(1)))
          }
        }
        case x => {
          if (inhale) buffer += bAssume(transExpr(x)) 
          else if (!free) {
            buffer += bAssert(transExpr(x), x.pos, msg)
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

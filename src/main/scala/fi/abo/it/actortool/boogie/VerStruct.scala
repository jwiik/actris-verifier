package fi.abo.it.actortool.boogie

import fi.abo.it.actortool._
import fi.abo.it.actortool.schedule._
import fi.abo.it.actortool.util.ConnectionMap
import fi.abo.it.actortool.util.PriorityMapBuilder
import collection.mutable.ListBuffer
import fi.abo.it.actortool.util.GuardStateAnalyzer

trait VerStruct[T] {
  def entity: T
  def namePrefix: String
  def renamings: Map[String,Expr] = Map.empty
  def declarations: Seq[BDecl] = Seq.empty
  def assumes = Seq.empty[Boogie.Assume]
  def stateChannelNames: Map[String,Id] = Map.empty
  def entities: Seq[Instance] = Seq.empty
  def connections: Seq[Connection] = Seq.empty
  def contractInvariants: Seq[Invariant] = Seq.empty
  def actionInvariants: Seq[Invariant] = Seq.empty
  def connectionMap: ConnectionMap = ConnectionMap.empty
  def translatedIoInvariants(t: StmtExpTranslator): Seq[Boogie.Expr] = Seq.empty
  def guardStateVariables: Set[String] = Set.empty
  def useContracts: Boolean
}


trait RootVerStruct[T<:DFActor] extends VerStruct[T] {
  def contracts: Seq[ContractAction]
  def priorities = PriorityMapBuilder.buildPriorityMap(entity, false, useContracts)
  override def guardStateVariables = {
    if (useContracts) GuardStateAnalyzer.analyze(entity.contractActions, entity.variables.filter(!_.constant))
    else GuardStateAnalyzer.analyze(entity.actorActions, entity.variables.filter(!_.constant))
  }
}

trait ChildVerStruct[T,P] extends VerStruct[T] {
  def parent: VerStruct[P]
  override def renamings = parent.renamings
  override def declarations = parent.declarations
  override def assumes = parent.assumes
  override def stateChannelNames = parent.stateChannelNames
  override def connections: Seq[Connection] = parent.connections
  override def contractInvariants: Seq[Invariant] = parent.contractInvariants
  override def actionInvariants: Seq[Invariant] = parent.actionInvariants
  override def connectionMap: ConnectionMap = parent.connectionMap
  
  override def translatedIoInvariants(t: StmtExpTranslator): Seq[Boogie.Expr] = 
    parent.translatedIoInvariants(t)
    
  override def guardStateVariables = parent.guardStateVariables
  override def useContracts = parent.useContracts
}

trait ActionExecVerStruct[T,P] extends ChildVerStruct[T,P] {
  def assignedVariables: Set[Id]
}

class ActorVerStruct(
    override val entity: BasicActor,
    override val declarations: List[BDecl],
    override val assumes: List[Boogie.Assume],
    override val useContracts: Boolean,
    val functionNames: Map[String,Id],
    override val stateChannelNames: Map[String,Id]
    ) extends RootVerStruct[BasicActor] {
  
  override def contracts = entity.contractActions
  override def namePrefix = entity.id
  override def renamings = functionNames
  
}

class NetworkVerStruct(
    override val entity: Network,
    override val declarations: List[BDecl],
    override val assumes: List[Boogie.Assume],
    override val stateChannelNames: Map[String,Id],
    override val renamings: Map[String,Id],
    val ioInvariants: List[(Instance,List[Invariant])],
    override val useContracts: Boolean
    ) extends RootVerStruct[Network] {
  
  override def contracts = entity.contractActions
  override def namePrefix = entity.id
  override def connectionMap = ConnectionMap.build(entity.structure.get.connections, renamings)
  
  override def entities = entity.entities.get.entities
  override def connections = entity.structure.get.connections
  override def contractInvariants = entity.contractInvariants
  override def actionInvariants = entity.actionInvariants
  
  override def translatedIoInvariants(translator: StmtExpTranslator) = {
    (for ((e,invs) <- ioInvariants) yield {
      val ivs = VerStruct.forInstance(this, e, useContracts)
      val ctx = TranslatorContext(ivs.renamings,false)
      for (i <- invs) yield {
        translator.transExpr(i.expr,ctx)
      }
    }) flatten
  }
  
}

class ActionVerStruct(
    override val parent: RootVerStruct[BasicActor],
    override val entity: ActorAction,
    val actionDeclarations: List[BDecl],
    val actionAssumes: List[Boogie.Assume],
    val actionVariableInits: List[Expr],
    val guard: GuardTranslation
    ) extends ActionExecVerStruct[ActorAction,BasicActor] {
  
  override def namePrefix = parent.namePrefix + B.Sep + entity.fullName
  override def declarations = parent.declarations ++ actionDeclarations
  override def assumes = parent.assumes ++ actionAssumes
  override def assignedVariables = AssignedVarsFinder.find(entity.body)
  override def renamings = parent.renamings ++ guard.renamings
  
}

class ScheduleVerStruct[P<:DFActor](
    override val parent: VerStruct[P],
    override val entity: ContractSchedule,
    val actionDeclarations: Seq[BDecl],
    val actionAssumes: Seq[Boogie.Assume],
    val actionVariableInits: Seq[Expr],
    val guard: GuardTranslation
    ) extends ActionExecVerStruct[ContractSchedule,P] {
  
  override def namePrefix = parent.namePrefix + B.Sep + entity.contract.fullName
  override def declarations = parent.declarations ++ actionDeclarations
  override def assumes = parent.assumes ++ actionAssumes
  override def assignedVariables = Set.empty
  override def renamings = parent.renamings //++ guard.renamings
  
}

class InstanceVerStruct(
    override val parent: VerStruct[Network],
    override val entity: Instance,
    override val useContracts: Boolean,
    val instanceDecls: Seq[BDecl],
    val paramRenamings: Map[String,Expr],
    override val guardStateVariables: Set[String],
    override val stateChannelNames: Map[String,Id]) extends ChildVerStruct[Instance,Network] {
  
  override def namePrefix = parent.namePrefix + B.Sep + entity.id
  
  def priorities(useContracts: Boolean) = 
    PriorityMapBuilder.buildPriorityMap(entity.actor, true, useContracts)
  
  override def renamings = parent.renamings ++ paramRenamings
  override def declarations = parent.declarations ++ instanceDecls
  
}

class SubActionVerStruct(
    override val parent: InstanceVerStruct,
    override val entity: AbstractAction,
    val actionDecls: List[BDecl],
    val replacements: Map[Id,Expr],
    val subactionRenamings: Map[String,Id],
    override val assignedVariables: Set[Id]) extends ActionExecVerStruct[AbstractAction,Instance] {
  
  override def namePrefix = parent.namePrefix + B.Sep + entity.fullName
  override def connectionMap = parent.connectionMap
  
  def priorities(useContracts: Boolean) = {
    parent.priorities(useContracts)
  }
  
  override def renamings = parent.renamings ++ subactionRenamings
  override def declarations = parent.declarations ++ actionDecls
  
}

object VerStruct {
  
  def forActor(actor: BasicActor, useContracts: Boolean) = {
    val stmtTranslator = new StmtExpTranslator
    val decls = new ListBuffer[BDecl]
    val assumes = new ListBuffer[Boogie.Assume]
    //val stateChannelNames = collection.mutable.Map[String,Id]()
    
    
    // Declaration of ports
    for (p <- actor.inports ::: actor.outports) {
      decls += BDecl(p.id, ChanType(p.portType)) 
    }
    
    for (p <- actor.parameters) {
      decls += BDecl(p.id,p.typ)
    }
    
    val (stateDcls,stateChannelNames) = getStateChannels(actor)
    
    decls ++= stateDcls
    
    assumes += B.Assume(createUniquenessCondition(decls.toList))
    
    val contractRates = actor.contractActions.map {
      c => {
        c ->
        (actor.inports.map {
          p => B.B(p.id) ==@ B.Int(c.inportRate(p.id))
        } ++
        actor.outports.map {
          p => B.B(p.id) ==@ B.Int(c.outportRate(p.id))
        })
        .reduceLeft((a,b) => a && b)
      }
    }
    
    if (!contractRates.isEmpty) {
      assumes += B.Assume(contractRates.unzip._2.reduceLeft((a,b) => a || b))
    }
    
    assumes ++=
      actor.inports:::actor.outports map { 
        p => B.Assume(B.Int(0) <= B.I(p.id) && B.I(p.id) <= B.R(p.id) && B.R(p.id) <= B.C(p.id)) 
      }
//    assumes ++=
//      stateChannelNames.values map { 
//        k => B.Assume(B.Int(0) <= B.I(k.id) && B.I(k.id) <= B.R(k.id) && B.R(k.id) <= B.C(k.id)) 
//      }
    
    val (contractModeDecls, contractModeAssumes) = createContractModeDeclsAndAssumes(actor)
    decls ++= contractModeDecls
    assumes ++= contractModeAssumes
    
    val (variableDecls, variableAssumes) = 
      createVarAndConstDecls(stmtTranslator, actor.variables, Map.empty)
    decls ++= variableDecls
    assumes ++= variableAssumes
    
    val funDeclRenamings = 
      actor.functionDecls.map(fd =>  fd.name -> Id(actor.fullName+B.Sep+fd.name))
    
    new ActorVerStruct(
        actor,
        decls.toList,
        assumes.toList,
        useContracts,
        funDeclRenamings.toMap,
        //Map.empty
        stateChannelNames.toMap
        )
  }
  
  
  def forNetwork(network: Network, useContracts: Boolean): RootVerStruct[Network] = {
    
    val stmtTranslator = new StmtExpTranslator
    
    val decls = new ListBuffer[BDecl]
    val assumes = new ListBuffer[Boogie.Assume]
    val renamings = new ListBuffer[(String,Id)]
    val namePrefix = network.fullName
    
    val connections = network.structure.get.connections
    val entities = network.entities.get.entities
    
    val (contractModeDecls, contractModeAssumes) = createContractModeDeclsAndAssumes(network)
    decls ++= contractModeDecls
    assumes ++= contractModeAssumes
    
    val channels = new ListBuffer[BDecl]
    
    for (c <- connections) {
      renamings += c.id -> Id(namePrefix+B.Sep+c.id).withType(c.typ)
      channels += BDecl(namePrefix+B.Sep+c.id,c.typ)
    }
    
    //val transCtx = TranslatorContext(renamings.toMap, false, Map.empty)
    
    val ioInvariants = new ListBuffer[(Instance,List[Invariant])]
    for (e <- entities) {
      ioInvariants += e -> e.actor.streamInvariants(useContracts)
    }
    
    decls ++= channels
    assumes += B.Assume(createUniquenessCondition(channels.toList))
    
    val tempRenamings = renamings.toMap
    
    for (c <- connections) {
      val tempRenamings = renamings.toMap
      val name = tempRenamings(c.id)
      assumes += 
        B.Assume(B.Int(0) <= B.I(name.id) && B.I(name.id) <= B.R(name.id) && B.R(name.id) <= B.C(name.id))      
      if (c.isOutput) {
        assumes += B.Assume(B.I(name.id) ==@ B.R(name.id))
      }
    }
    
    // Add input/output port names as synonyms to the connected channels
    for (ip <- network.inports) {
      val ch = network.structure.get.getInputChannel(ip.id)
      ch match {
        case Some(c) => renamings += ip.id -> Id(namePrefix+B.Sep+c.id).withType(c.typ)
        case None =>
      }
    }
    for (op <- network.outports) {
      val ch = network.structure.get.getOutputChannel(op.id)
      ch match {
        case Some(c) => renamings += op.id -> Id(namePrefix+B.Sep+c.id).withType(c.typ)
        case None =>
      }
    }
    
    new NetworkVerStruct(
        network,
        decls.toList,
        assumes.toList,
        Map.empty, // State channels
        renamings.toMap,
        ioInvariants.toList,
        useContracts)
          
  }
  
  def forActorAction(
      parent: RootVerStruct[BasicActor], 
      action: ActorAction, 
      guard: GuardTranslation): ActionVerStruct = forActorAction(parent,action,guard,false)
  
  def forActorAction(
      parent: RootVerStruct[BasicActor], 
      action: ActorAction, 
      guard: GuardTranslation,
      includePatternVars: Boolean): ActionVerStruct = {
    
    val stmtTranslator = new StmtExpTranslator
    val transCtx = TranslatorContext(parent.renamings, false, parent.stateChannelNames)
    
    val decls = new ListBuffer[BDecl]
    val assumes = new ListBuffer[Boogie.Assume]
    val actionVariableInits = new ListBuffer[Expr]
    
    if (action.init) {
      assumes ++= 
        (parent.entity.inports ++ parent.entity.outports) map { 
          p => B.Assume(B.I(p.id) ==@ B.Int(0) && B.R(p.id) ==@ B.Int(0) && B.C(p.id) ==@ B.Int(0)) 
        }
      assumes ++= 
        parent.stateChannelNames.values map { 
          k => B.Assume(B.I(k.id) ==@ B.Int(0) && B.R(k.id) ==@ B.Int(0) && B.C(k.id) ==@ B.Int(0)) 
        }
    }
    else {
      assumes ++= parent.stateChannelNames.values.map { k => B.Assume((B.R(k.id) + B.Int(1)) ==@ B.C(k.id)) }
    }
    
    for (d <- action.variables) {
      decls += BDecl(d.id,d.typ)
      if (d.constant) {
        val id = Id(d.id).withType(d.typ)
        val exp = Eq(id, d.value.get).withType(BoolType)
        
        actionVariableInits += exp
      }
    }
    
//    for ((_,id) <- parent.stateChannelNames) {
//      decls += BDecl(id.id,ChanType(id.typ))
//    }
    
    decls ++= guard.declarations
    
    assumes += B.Assume(createUniquenessCondition(decls.toList))
    
    new ActionVerStruct(parent,action,decls.toList,assumes.toList,actionVariableInits.toList,guard)
  }
  
  
  def forSchedule[P<:DFActor](
      parent: VerStruct[P], 
      schedule: ContractSchedule,
      stateChannels: Seq[Id]): ScheduleVerStruct[P] = {
    
    val decls = new ListBuffer[BDecl]
    val assumes = new ListBuffer[Boogie.Assume]
    
    decls ++= stateChannels.map(s => BDecl(s.id,ChanType(s.typ)))
    
    if (schedule.entity.isActor) {
      assumes ++= 
        (parent.entity.inports ++ parent.entity.outports) map { 
          p => B.Assume(B.I(p.id) ==@ B.R(p.id) && B.R(p.id) ==@ B.C(p.id)) 
        }
    }
    assumes ++= stateChannels.map { case ch => B.Assume(B.C(ch.id) ==@ B.R(ch.id) + B.Int(1)) }
    
    val parentChannels = parent.declarations.filter { d => 
      d.decl.x.t match {
        case Boogie.IndexedType("Chan",_) => true
        case _ => false
      }
    }
    
    assumes += 
      B.Assume(createUniquenessCondition( parentChannels.toList ++ stateChannels.map{ x => BDecl(x.id,x.typ) }.toList ))
    
    new ScheduleVerStruct(parent,schedule,decls.toSeq,assumes.toList,Nil,null)
  }
  
  
  
  def forInstance(parent: VerStruct[Network], instance: Instance, useContracts: Boolean) = {
    
    val decls = new ListBuffer[BDecl]
    val renamings = new ListBuffer[(String,Expr)]
    
    renamings ++= instance.actor.parameters.map(_.id).zip(instance.arguments)
    
    for (p <- instance.actor.inports) {
      val newName = parent.connectionMap.getDst(instance.id,p.id)
      renamings += p.id -> Id(newName).withType(ChanType(p.portType))
    }
    
    for (p <- instance.actor.outports) {
      val newName = parent.connectionMap.getSrc(instance.id,p.id)
      renamings += p.id -> Id(newName).withType(ChanType(p.portType))
    }
    
    for (v <- instance.actor.variables) {
      val vName = instance.id + B.Sep + v.id
      decls += BDecl(vName,v.typ)
      renamings += v.id -> Id(vName).withType(v.typ)
    }
    
    val guardVariables = {
      if (useContracts) {
        GuardStateAnalyzer.analyze(
            instance.actor.contractActions, 
            instance.actor.variables)
      }
      else { 
        GuardStateAnalyzer.analyze(
            instance.actor.actorActions, 
            instance.actor.variables)
      }
    }
    
    val (stateDcls,stateChannelNames) = getStateChannels(instance.actor, instance.id)
    decls ++= stateDcls
    
    
    for (v <- instance.actor.variables) {
      if (guardVariables.contains(v.id)) {
        val newName = instance.id + B.Sep + v.id
        decls += BDecl(newName,v.typ)
        renamings +=  v.id -> Id(newName).withType(v.typ)
      }  
    }
    
    val assignedVariables = 
      instance.actor.variables
        .filter { v => !v.constant && guardVariables.contains(v.id) }
        .map { v => Id(v.id).withType(v.typ) }
    
    new InstanceVerStruct(
        parent, instance, useContracts, decls.toSeq, renamings.toMap, guardVariables,stateChannelNames)
  }
  
  def forSubAction(parent: InstanceVerStruct, action: AbstractAction) = {
    
    val instance = parent.entity
    
    val actor = instance.actor
    val vars = new ListBuffer[BDecl]()
    val renamings = new ListBuffer[(String,Id)]
    
    val replacements = scala.collection.mutable.HashMap.empty[Id,Expr]
    
    action match {
      case ac: ActorAction => {
        for (ipat <- ac.inputPattern) {
          val cId = parent.connectionMap.getDst(instance.id,ipat.portId)      
          for ((v,ind) <- ipat.vars.zipWithIndex) {
            val c = Elements.ch(cId,v.typ)
            val index = 
              if (ind == 0) Elements.rd(c.id,c.typ.asInstanceOf[ChanType]) 
              else Minus(Elements.rd(c.id,c.typ.asInstanceOf[ChanType]),IntLiteral(ind))
            val acc = Elements.chAcc(c,index)
            replacements += (v -> acc)
          }
        }
        
        if (!instance.actor.isNetwork) {
          for (ipat <- ac.inputPattern) {
            for (v <- ipat.vars) {
              val inVar = instance.id + B.Sep + ipat.portId + B.Sep + v.id
              vars += BDecl(inVar,B.Local(inVar,B.type2BType(v.typ)))
              renamings += v.id -> Id(inVar).withType(v.typ)
            }
          }
          for (v <- ac.variables) {
            val actionVar = instance.id + B.Sep + action.fullName + B.Sep + v.id
            vars += BDecl(actionVar,B.Local(actionVar,B.type2BType(v.typ)))
            renamings += v.id -> Id(actionVar).withType(v.typ)
          }
        }
        
        val assignedVars = AssignedVarsFinder.find(ac.body).map(_.id)
        
        val assignedVariables = 
          instance.actor.variables
          .filter { v => !v.constant && parent.guardStateVariables.contains(v.id) && assignedVars.contains(v.id) }
          .map { v => Id(v.id).withType(v.typ) }
        
        new SubActionVerStruct(parent, action, vars.toList, replacements.toMap, renamings.toMap, assignedVariables.toSet)
      }
      case c: ContractAction => {
        new SubActionVerStruct(parent, action, List.empty, Map.empty, Map.empty, Set.empty)
      }
    }
    
  }
  
  protected def createUniquenessCondition(names: List[BDecl]): Boogie.Expr = {
    val conds = createUniquenessConditionRec(names)
    if (conds.isEmpty) B.Bool(true)
    else conds.reduceLeft((a,b) => a && b)
  }
  
  protected def createUniquenessConditionRec(names: List[BDecl]): List[Boogie.Expr] = {
    names match {
      case first::rest => {
        val conditions = rest flatMap { 
          c => if (first.decl.x.t == c.decl.x.t) List(Boogie.VarExpr(first.name) !=@ Boogie.VarExpr(c.name)) else Nil
        }
        conditions:::createUniquenessConditionRec(rest)
      }
      case Nil => Nil
    }
  }
  
  protected def getStateChannels(actor: DFActor, prefix: String = "") = {
    val stateChannelNames = collection.mutable.Map[String,Id]()
    val decls = new ListBuffer[BDecl]();
    
    // Declaration of virtual channels for actor variables
    for (v <- actor.variables.filter(!_.constant)) {
      val name = if (prefix != "") prefix + B.Sep + v.id + B.Sep + "ch" else v.id + B.Sep + "ch"
      stateChannelNames += v.id -> Id(name).withType(v.typ)
      decls += BDecl(stateChannelNames(v.id).id, ChanType(v.typ))
    }
    
    (decls,stateChannelNames.toMap)
  }
  
  protected def createContractModeDeclsAndAssumes(entity: DFActor) = {
    val decls = new ListBuffer[BDecl]
    val assumes = new ListBuffer[Boogie.Assume]
    
    for ((s,i) <- entity.contractActions.zipWithIndex) {
      val decl = BDecl(s.fullName, IntType)
      decls += decl
      assumes += Boogie.Assume(Boogie.VarExpr(s.fullName) ==@ B.Int(i))
    }
    
    if (!entity.contractActions.isEmpty) {
      assumes += B.Assume(
        entity.contractActions.
        map { s => B.Mode(B.This) ==@ Boogie.VarExpr(s.fullName) }.
        reduceLeft { (a,b) => a || b })
    }
    
    (decls.toList,assumes.toList)
    
  }
  
  protected def createVarAndConstDecls(
      translator: StmtExpTranslator,
      varDecls: List[Declaration], 
      renamings: Map[String,Id]) = {
    val decls = new ListBuffer[BDecl]
    val assumes = new ListBuffer[Boogie.Assume]
    for (d <- varDecls) {
      decls += BDecl(d.id,d.typ)
      if (d.constant) {
        assumes += Boogie.Assume(
            Boogie.VarExpr(d.id) ==@ translator.transExpr(d.value.get, TranslatorContext(renamings, false))
          )
      }
    }
    (decls.toList,assumes.toList)
  }
  
}



package fi.abo.it.actortool.boogie

import fi.abo.it.actortool._
import fi.abo.it.actortool.util.PriorityMapBuilder
import collection.mutable.ListBuffer

trait VerStruct[T] {
  def entity: T
  def namePrefix: String
  def renamings: Map[String,Expr] = Map.empty
  def declarations: List[BDecl] = List.empty
  def assumes = List.empty[Boogie.Assume]
}

trait RootVerStruct[T<:DFActor] extends VerStruct[T] {
  def contracts: Seq[ContractAction]
  def priorities(useContracts: Boolean) = PriorityMapBuilder.buildPriorityMap(entity, false, useContracts)
}

trait ChildVerStruct[T,P] extends VerStruct[T] {
  def parent: VerStruct[P]
  override def renamings = parent.renamings
}

class ActorVerStruct(
    override val entity: BasicActor,
    override val declarations: List[BDecl],
    override val assumes: List[Boogie.Assume],
    val functionNames: Map[String,Id],
    val stateChannelNames: Map[String,Id]
    ) extends RootVerStruct[BasicActor] {
  
  override def contracts = entity.contractActions
  override def namePrefix = entity.id
  override def renamings = functionNames
  
}

class NwVerStruct(
    override val entity: Network,
    override val declarations: List[BDecl],
    override val assumes: List[Boogie.Assume],
    val stateChannelNames: Map[String,Id]
    ) extends RootVerStruct[Network] {
  
  override def contracts = entity.contractActions
  override def namePrefix = entity.id
  
}

class ActionVerStruct(
    override val parent: ActorVerStruct,
    override val entity: ActorAction,
    val actionDeclarations: List[BDecl],
    val actionAssumes: List[Boogie.Assume]
    ) extends ChildVerStruct[ActorAction,BasicActor] {
  
  override def namePrefix = parent.namePrefix + B.Sep + entity.fullName
  override def declarations = parent.declarations ::: actionDeclarations
  override def assumes = parent.assumes ::: actionAssumes
  def assignedVariables = AssignedVarsFinder.find(entity.body)
  
}

object VerStruct {
  
  def apply(actor: BasicActor, useContracts: Boolean) = {
    val stmtTranslator = new StmtExpTranslator
    val decls = new ListBuffer[BDecl]
    val assumes = new ListBuffer[Boogie.Assume]
    val stateChannelNames = collection.mutable.Map[String,Id]()
    val actionVerStructs = new ListBuffer[ActionVerStruct]
    
    // Declaration of ports
    for (p <- actor.inports ::: actor.outports) {
      decls += BDecl(p.id, ChanType(p.portType)) 
    }
    
    // Declaration of virtual channels for actor variables
    for (v <- actor.variables) {
      stateChannelNames += v.id -> Id(v.id + B.Sep + "ch").withType(v.typ)
      decls += BDecl(stateChannelNames(v.id).id, ChanType(v.typ))
    }
    
    assumes += B.Assume(createUniquenessCondition(decls.toList))
    
    assumes ++=
      actor.inports:::actor.outports map { 
        p => B.Assume(B.Int(0) <= B.I(p.id) && B.I(p.id) <= B.R(p.id) && B.R(p.id) <= B.C(p.id)) 
      }
    assumes ++=
      stateChannelNames.keys map { 
        k => B.Assume(B.Int(0) <= B.I(k) && B.I(k) <= B.R(k) && B.R(k) <= B.C(k)) 
      }
    
    val (contractModeDecls, contractModeAssumes) = createContractModeDeclsAndAssumes(actor)
    decls ++= contractModeDecls
    assumes ++= contractModeAssumes
    
    val (variableDecls, variableAssumes) = 
      createVarAndConstDecls(stmtTranslator, actor.variables, Map.empty)
    decls ++= variableDecls
    assumes ++= variableAssumes
    
    val priorityMap = PriorityMapBuilder.buildPriorityMap(actor, false, useContracts)
    val funDeclRenamings = actor.functionDecls.map(fd =>  fd.name -> Id(actor.fullName+B.Sep+fd.name))
    
    new ActorVerStruct(
        actor,
        decls.toList,
        assumes.toList,
        funDeclRenamings.toMap,
        stateChannelNames.toMap
        )
  }
  
  def apply(parent: ActorVerStruct, action: ActorAction, useContracts: Boolean) = {
    
    val stmtTranslator = new StmtExpTranslator
    val transCtx = TranslatorContext(parent.renamings, false, parent.stateChannelNames)
    
    val decls = new ListBuffer[BDecl]
    val assumes = new ListBuffer[Boogie.Assume]
    
    if (action.init) {
      assumes ++= 
        parent.entity.inports:::parent.entity.outports map { 
          p => B.Assume(B.I(p.id) ==@ B.Int(0) && B.R(p.id) ==@ B.Int(0) && B.C(p.id) ==@ B.Int(0)) 
        }
      assumes ++= 
        parent.stateChannelNames.keys map { 
          k => B.Assume(B.I(k) ==@ B.Int(0) && B.R(k) ==@ B.Int(0) && B.C(k) ==@ B.Int(0)) 
        }
    }
    else {
      assumes ++= parent.stateChannelNames.keys.map { k => B.Assume((B.R(k) + B.Int(1)) ==@ B.C(k)) }
    }
    
    for (d <- action.variables) {
      decls += BDecl(d.id,d.typ)
      if (d.constant) {
        assumes += Boogie.Assume(Boogie.VarExpr(d.id) ==@  stmtTranslator.transExpr(d.value.get, transCtx))
      }
    }
    
    new ActionVerStruct(parent,action,decls.toList,assumes.toList)
  }
  
  
  def apply(network: Network, useContracts: Boolean, typeCtx: Resolver.Context) = {
    
    val decls = new ListBuffer[BDecl]
    val assumes = new ListBuffer[Boogie.Assume]
    val renamings = new ListBuffer[(String,Id)]
    val namePrefix = network.fullName
    
    val connections = network.structure.get.connections
    val entities = network.entities.get.entities
    
    val (contractModeDecls, contractModeAssumes) = createContractModeDeclsAndAssumes(network)
    decls ++= contractModeDecls
    assumes ++= contractModeAssumes
    
    val nwInvariants = 
      createTokenInvariants(
          network.actorInvariants, 
          network.channelInvariants, 
          connections, 
          typeCtx)
    
    for (ip <- network.inports) {
      val ch = network.structure.get.getInputChannel(ip.id)
      ch match {
        case Some(c) => renamings += ip.id -> Id(namePrefix+c.id).withType(c.typ)
        case None =>
      }
    }
    
    for (op <- network.outports) {
      val ch = network.structure.get.getOutputChannel(op.id)
      ch match {
        case Some(c) => renamings += op.id -> Id(namePrefix+c.id).withType(c.typ)
        case None =>
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
  
  def createTokenInvariants(
      nwInvariants: List[ActorInvariant], 
      chInvariants: List[Invariant], 
      connections: List[Connection],
      typeCtx: Resolver.Context)  = {
    val explicitTokensAsserts: Set[String] = (TokensFinder.visit(nwInvariants) ::: TokensFinder.visit(chInvariants)).toSet
    val implicitTokensChs = connections.filter { c => !explicitTokensAsserts.contains(c.id)  }
    val implicitTokensAsserts = implicitTokensChs map { c =>
      val predicate = FunctionApp("tokens",List(Id(c.id).withType(c.typ),IntLiteral(0)))
      Resolver.resolveExpr(predicate, typeCtx) match {
        case Resolver.Success(_) =>
        case Resolver.Errors(errs) => assert(false,errs)
      }
      assert(predicate.typ != null)
      ActorInvariant(Assertion(predicate,false,Some("Unread tokens might be left on channel " + c.id)),true,false)
    }
    nwInvariants ::: implicitTokensAsserts
  }
  
  
  object TokensFinder {
    
    def visit(invs: List[Invariant]): List[String] = invs.flatMap { x => visit(x.expr) }
    
    def visit(expr: Expr): List[String] =
      expr match {
        case And(left,right) => visit(left) ::: visit(right)
        case FunctionApp("tokens",params) => List(params(0).asInstanceOf[Id].id)
        case _ => Nil
      }
    
  }
  
}



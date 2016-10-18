package fi.abo.it.actortool.boogie

import fi.abo.it.actortool._

trait VerificationStructure[T <: DFActor] {
  val entity: T
}

class ActorVerificationStructure(
    val entity: BasicActor,
    val actions: List[Action],
    val inports: List[InPort],
    val outports: List[OutPort],
    val invariants: List[ActorInvariant],
    val channelDecls: List[BDecl],
    val actorVarDecls: List[BDecl],
    val actorParamDecls: List[BDecl],
    val uniquenessCondition: Boogie.Expr,
    val schedule: Option[Schedule],
    val actorStates: List[String],
    val actorBoogieStates: List[Boogie.Const],
    val allowedStateInv: Option[Boogie.Expr],
    val basicAssumes: List[Boogie.Assume],
    val initAssumes: List[Boogie.Assume],
    val namePrefix: String) extends VerificationStructure[BasicActor]



class NetworkVerificationStructure(
    val entity: Network,
    val actions: List[Action],
    val nwInvariants: List[ActorInvariant],
    val chInvariants: List[ChannelInvariant],
    val publicSubInvariants: List[(ActorInvariant,Map[String,Expr])],
    val connections: List[Connection],
    val entities: List[Instance],
    val sourceMap: Map[PortRef,String],
    val targetMap: Map[PortRef,String],
    val nwRenamings: Map[String,Expr],
    val entityData: Map[Instance,EntityData],
    //val entityRenamings1: Map[Instance, Map[String, String]],
    //val entityVariables1: Map[Instance, List[String]],
    val entityDecls: List[BDecl],
    val subactorVarDecls: List[BDecl],
    val uniquenessConditions: List[Boogie.Expr],
    val basicAssumes: List[Boogie.Assume],
    val namePrefix: String) extends VerificationStructure[Network] {
  
  def instanceRenamings(instance: Instance) = nwRenamings ++ entityData(instance).renamings
  
  def subActionRenamings(instance: Instance, action: Action) = 
    instanceRenamings(instance) ++ entityData(instance).actionData(action).renamings
  
}

class EntityData(
    val declarations: List[BDecl], 
    val renamings: Map[String,Expr], 
    val variables: List[String],
    val actionData: Map[Action,ActionData])
    
class ActionData(
    val declarations: List[BDecl], 
    val renamings: Map[String,Id], 
    val replacements: Map[Id,Expr])
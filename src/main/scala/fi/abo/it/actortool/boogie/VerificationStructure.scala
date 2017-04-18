package fi.abo.it.actortool.boogie

import fi.abo.it.actortool._

trait VerificationStructure[T <: DFActor] {
  val entity: T
}

class ActorVerificationStructure(
    val entity: BasicActor,
    val actorActions: List[ActorAction],
    val contractActions: List[ContractAction],
    val inports: List[InPort],
    val outports: List[OutPort],
    val invariants: List[ActorInvariant],
    val functionDecls: List[FunctionDecl],
    val channelDecls: List[BDecl],
    val actorVarDecls: List[BDecl],
    val actorParamDecls: List[BDecl],
    val uniquenessCondition: Boogie.Expr,
    val priorityMap: Map[AbstractAction,List[AbstractAction]],
    val basicAssumes: List[Boogie.Assume],
    val initAssumes: List[Boogie.Assume],
    val renamings: Map[String,Id],
    val stateChanRenamings: Map[String,Id],
    val namePrefix: String) extends VerificationStructure[BasicActor]



class NetworkVerificationStructure(
    val entity: Network,
    val actions: List[ContractAction],
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
    val actionRatePredicates: Map[ContractAction,Boogie.Expr],
    val basicAssumes: List[Boogie.Assume],
    val namePrefix: String) extends VerificationStructure[Network] {
  
  def instanceRenamings(instance: Instance) = nwRenamings ++ entityData(instance).renamings
  
  def subActionRenamings(instance: Instance, action: AbstractAction) = {
    val actionRenamings = if (action.isActorAction) entityData(instance).actionData(action.asInstanceOf[ActorAction]).renamings else Map.empty
    instanceRenamings(instance) ++ actionRenamings
  }
  
  def getEntityActionData(instance: Instance, action: AbstractAction): ActionData  = {
    if (action.isInstanceOf[ActorAction]) entityData(instance).actionData(action.asInstanceOf[ActorAction])
    else EmptyActionData
  }
  
}

class EntityData(
    val declarations: List[BDecl], 
    val renamings: Map[String,Expr], 
    val variables: List[String],
    val actionData: Map[ActorAction,ActionData],
    val priorities: Map[AbstractAction,List[AbstractAction]])
    
class ActionData(
    val declarations: List[BDecl], 
    val renamings: Map[String,Id], 
    val replacements: Map[Id,Expr],
    val assignedVariables: Set[Assignable])
    
object EmptyActionData extends ActionData(List.empty,Map.empty,Map.empty,Set.empty)
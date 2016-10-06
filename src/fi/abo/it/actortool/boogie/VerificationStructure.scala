package fi.abo.it.actortool.boogie

import fi.abo.it.actortool._

trait VerificationStructure[T <: DFActor]{
  val entity: T
}

class ActorVerificationStructure(
    val entity: BasicActor,
    val actions: List[Action],
    val inports: List[InPort],
    val outports: List[OutPort],
    val invariants: List[ActorInvariant],
    val channelDecls: List[Boogie.LocalVar],
    val actorVarDecls: List[Boogie.LocalVar],
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
    val connections: List[Connection],
    val entities: List[Instance],
    val sourceMap: Map[PortRef,String],
    val targetMap: Map[PortRef,String],
    val nwRenamings: Map[String,String],
    val entityRenamings: Map[Instance, Map[String, String]],
    val entityVariables: Map[Instance, List[String]],
    val subactorVarDecls: List[Boogie.LocalVar],
    val basicAssumes: List[Boogie.Assume],
    val namePrefix: String) extends VerificationStructure[Network]
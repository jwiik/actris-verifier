package fi.abo.it.actortool.schedule

import fi.abo.it.actortool._

class Schedule[U](val network: Network, val sequence: List[U])

class ContractSchedule(
    override val network: Network, 
    val contract: ContractAction, 
    override val sequence: List[(Instance,ActorAction)]) extends Schedule(network,sequence)
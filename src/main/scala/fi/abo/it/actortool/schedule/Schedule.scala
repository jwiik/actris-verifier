package fi.abo.it.actortool.schedule

import fi.abo.it.actortool._

class Schedule[U](val entity: DFActor, val sequence: List[U])

class ContractSchedule(
    override val entity: DFActor, 
    val contract: ContractAction, 
    override val sequence: List[(Instance,ActorAction)]) extends Schedule(entity,sequence)
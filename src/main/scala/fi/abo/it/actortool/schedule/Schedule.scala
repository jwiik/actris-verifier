package fi.abo.it.actortool.schedule

import fi.abo.it.actortool._

class Schedule[U](val entity: DFActor, val sequence: List[U])

class ContractSchedule(
    override val entity: DFActor, 
    val contract: ContractAction, 
    override val sequence: List[(Instance,ActorAction)]) extends Schedule(entity,sequence) {
  
  override def toString = sequence.foldLeft("")((a,b) => a + "\n" + string(b)  )
  
  private def string(instance: (Instance,ActorAction)) = "(" + instance._1.id + ", " + instance._2.fullName + ")"
  
}
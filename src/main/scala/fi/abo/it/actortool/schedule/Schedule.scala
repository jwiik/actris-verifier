package fi.abo.it.actortool.schedule

import fi.abo.it.actortool._

abstract class Schedule[U](val entity: DFActor, val sequence: List[U]) {
  def length: Int
}

class ContractSchedule(
    override val entity: DFActor, 
    val contract: ContractAction,
    override val sequence: List[(Instance,ActorAction)], val cost: Int) extends Schedule(entity,sequence) {
  
  override def toString = sequence.foldLeft("")((a,b) => a + "\n" + string(b)  )
  
  lazy val length = sequence.size
  
  private def string(instance: (Instance,ActorAction)) = "(" + instance._1.id + ", " + instance._2.fullName + ")"
  
}
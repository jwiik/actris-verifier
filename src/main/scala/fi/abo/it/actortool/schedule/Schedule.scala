package fi.abo.it.actortool.schedule

import fi.abo.it.actortool._
import java.io.File
import xml.PrettyPrinter

trait ScheduleElement {
  def toXML: xml.Elem
  def print = { new PrettyPrinter(150,2).format(toXML) }
}

abstract class Schedule(val entity: DFActor) extends ScheduleElement {
  def length: Int
  def cost: Int
  def sequence: Seq[Firing]
}

case class ApplicationInformation(topActor: DFActor, val actors: Seq[ActorInformation]) extends ScheduleElement {
  def toXML = <schedules top_network={topActor.fullName}>{ actors.map(_.toXML) }</schedules>
}

case class ActorInformation(val entity: DFActor, val schedules: Seq[Schedule]) extends ScheduleElement {
  def toXML = <actor id={entity.fullName}>{ schedules.map(_.toXML) }</actor>
}

case class ContractSchedule(
    override val entity: DFActor, 
    val contract: ContractAction,
    override val sequence: Seq[Firing], 
    val cost: Int) extends Schedule(entity) {
  
  lazy val length = sequence.size
  
  def toXML = {
    <schedule id={contract.fullName} cost={cost.toString}>{ sequence.map(_.toXML) }</schedule>
  }
}

case class Firing(val instance: Instance, val action: ActorAction) extends ScheduleElement {
  def toXML = <firing inst={ instance.id } actor={ instance.actorId } action={ action.fullName } />
}
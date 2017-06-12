package fi.abo.it.actortool.promela

import collection.mutable.ListBuffer
import fi.abo.it.actortool._
import fi.abo.it.actortool.schedule.ContractSchedule

class SpinOutputParser(val translation: Translation) {
  
  private val schedules = new  ListBuffer[ContractSchedule]()
  private var current: ListBuffer[(Instance,ActorAction)] = null
  private var currentContract: ContractAction = null
  
  def startNewSchedule(contract: ContractAction) {
    current = new ListBuffer
    currentContract = contract
  }
  
  def allSchedules = schedules.toList
  
  def read(str: String) {
    if (str == "timeout") {
      val s = new ContractSchedule(translation.network,currentContract,current.toList)
      schedules += s
    }
    else {
      val elem = scala.xml.XML.loadString(str)
      val actionLbl = elem \ "@action"
      //val actor = elem \ "@actor"
      val instId = elem \ "@id"
      val instance = translation.idMap.getInstance(instId.text.toInt)
      val action = instance.actor.actorActions.find { a => a.fullName == actionLbl.text }
      action match {
        case Some(a) => current += ((instance,a))
        case None => throw new RuntimeException()
      }
    }
  }
  
}
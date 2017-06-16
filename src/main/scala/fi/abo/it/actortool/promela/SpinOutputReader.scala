package fi.abo.it.actortool.promela

import collection.mutable.ListBuffer
import fi.abo.it.actortool._
import fi.abo.it.actortool.schedule.ContractSchedule

class SpinOutputParser(val translation: Translation[_<:DFActor]) {
  
  private val schedules = new  ListBuffer[ContractSchedule]()
  private var current: ListBuffer[(Instance,ActorAction)] = null
  private var currentContract: ContractAction = null
  
  def startNewSchedule(contract: ContractAction) {
    current = new ListBuffer
    currentContract = contract
  }
  
  def endSchedule {
    val s = new ContractSchedule(translation.entity,currentContract,current.toList)
    schedules += s
    current = null
    currentContract = null
  }
  
  def allSchedules = schedules.toList
  
  def read(str: String) {
    val lines = str.split("\n")
    for (l <- lines) {
      //println(l)
      try {
        val elem = scala.xml.XML.loadString(l)
        val actionLbl = elem \ "@action"
        //val actor = elem \ "@actor"
        val instId = elem \ "@id"
        val instance = translation.idMap.getInstance(instId.text.toInt)
        val actor = translation.mergedActors.get(instance.actorId).getOrElse(instance.actor)
        val action = actor.actorActions.find { a => a.fullName == actionLbl.text }
        action match {
          case Some(a) => current += ((instance,a))
          case None => throw new RuntimeException(elem.toString)
        }
      }
      catch {
        case e: Exception =>  {
          if (l.startsWith("spin:")) {
            println("Spin message:" + l.substring(5))
          }
          else {
            println("Error parsing spin output: " + e.getMessage)
          }
        }
      }
    }
  }
  
}
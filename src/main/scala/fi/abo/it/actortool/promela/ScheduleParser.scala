package fi.abo.it.actortool.promela

import collection.mutable.ListBuffer
import fi.abo.it.actortool._
import fi.abo.it.actortool.schedule.ContractSchedule

class ScheduleParser(val translation: Translation[_<:DFActor]) {
  
  private var current: ListBuffer[(Instance,ActorAction)] = null
  private var currentContract: ContractAction = null
  private var schedule: ContractSchedule = null
  private var cost = -1
  
  def startSchedule(contract: ContractAction) {
    current = new ListBuffer
    currentContract = contract
  }
  
  def endSchedule {
    schedule = new ContractSchedule(translation.entity,currentContract,current.toList, cost)
    current = null
    currentContract = null
  }
  
  def setCost(cost: Int) { this.cost = cost }
  
  def getSchedule = schedule
  
  def read(str: String) {
    val lines = str.split("\n")
    for (l <- lines) {
      try {
        val elem = scala.xml.XML.loadString(l)
        val actionLbl = elem \ "@action"
        //val actor = elem \ "@actor"
        val instId = (elem \ "@id").text.toInt
        val instance = translation.idMap.getInstance(instId)
        val actor = translation.mergedActors.get(instance.actorId).getOrElse(instance.actor)
        val action = actor.actorActions.find { a => a.fullName == actionLbl.text }
        action match {
          case Some(a) => current += ((instance,a))
          case None => throw new RuntimeException(elem.toString)
        }
      }
      catch {
        case e: Exception =>  {
          if (l == "timeout") {}
          else {
//            println("SPIN: " + l)
          }
        }
      }
    }
  }
  
}
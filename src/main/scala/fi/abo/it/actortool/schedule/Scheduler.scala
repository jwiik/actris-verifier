package fi.abo.it.actortool.schedule

import java.io.File
import fi.abo.it.actortool._
import xml.NodeSeq

trait Scheduler {
  def schedule(entity: DFActor, mergedActors: Map[String,BasicActor], constants: List[Declaration]): List[ContractSchedule]
}

class XMLScheduler(file: File) extends Scheduler {
  
  val xmlSchedules = xml.XML.loadFile(file)
  
  def schedule(entity: DFActor, mergedActors: Map[String,BasicActor], constants: List[Declaration]): List[ContractSchedule] = {
    
    val instances = entity match {
      case ba: BasicActor => Map("this" -> Instance("this", ba.id, Nil))
      case nw: Network => {
        nw.entities.get.entities.map{ i => (i.id, i) }.toMap
      }
    }
    
    val actorData = xmlSchedules \ "actor" filter { n => (n \@ "id") == entity.id } 
    val actorSchedules = actorData \ "schedule"
    
    for (c <- entity.contractActions) yield {
      
      val xmlSchedule = actorSchedules filter { n => (n \@ "id") == c.fullName } 
      val xmlFirings = xmlSchedule \ "firing"
      
      val firings = xmlFirings map {
        f => {
          val instName = f \@ "inst"
          val actorName = f \@ "actor"
          val actionName =  f \@ "action"
          
          val inst = instances(instName)
          val actor = mergedActors(actorName)
          val actionLookup = actor.actorActions.find { a => a.fullName == actionName }
          
          val action = actionLookup match {
            case Some(a) => a
            case None => throw new RuntimeException("No action named " + actionName + " found")
          }
          
          Firing(inst,action)
          
        }
      }
      
      val cost = xmlSchedule \@ "cost"
      
      ContractSchedule(entity,c,firings,cost.toInt)
    }

  }
}
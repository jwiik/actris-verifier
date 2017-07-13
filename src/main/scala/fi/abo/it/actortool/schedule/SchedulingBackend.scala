package fi.abo.it.actortool.schedule

import java.io.File
import java.io.FileWriter
import fi.abo.it.actortool._
import fi.abo.it.actortool.merging.ActorMerger
import fi.abo.it.actortool.ActorTool.CommandLineParameters
import fi.abo.it.actortool.util.ASTPrinter

class SchedulingBackend(val scheduler: Scheduler, val params: CommandLineParameters) extends Backend[(BasicActor,List[ScheduleContext])] {
  
  def invoke(programCtx: ProgramContext): (BasicActor,List[ScheduleContext]) = {
    val topNwName = params.Schedule.get
    
    val topnw = programCtx.program.find { x => x.id == topNwName } match {
      case Some(a) => a match {
        case nw: Network => nw
        case _ => throw new RuntimeException("Enitity named " + topNwName + " is not a network")
      }
      case _ => throw new RuntimeException("There is no network named " + topNwName)
    }
    
    val allSchedules = new collection.mutable.ListBuffer[ScheduleContext]
    val actorScheduleInfo = new collection.mutable.ListBuffer[ActorInformation]
    
    val constants = (programCtx.program.collect { case DataUnit(_,constants) => constants }).flatten
    val mergerBackend = new ActorMerger(constants)

    val evaluationOrder = DepTree(topnw).postOrder
    
    val mergedActorMap = collection.mutable.Map[String,BasicActor]()
    for (entity <- evaluationOrder) {

      
      val doSchedule = entity match {
        case ba: BasicActor => {
          if (entity.contractActions.isEmpty || (!params.MergeActions && !ba.hasAnnotation("merge")))  {
            mergedActorMap += (entity.id -> ba)
            false
          }
          else {
            true
          }
        }
        case nw: Network => true
      }
      
      if (doSchedule) {
        val schedules = scheduler.schedule(entity, mergedActorMap.toMap, constants)
            
        actorScheduleInfo += ActorInformation(entity, schedules)
        val scheduleCtx = new ScheduleContext(
              entity, schedules, mergedActorMap.toMap,
              programCtx.program, programCtx.typeContext)
        allSchedules += scheduleCtx
        
        val actor = mergerBackend.invoke(scheduleCtx)
        actor match {
          case Some(a) => mergedActorMap += (entity.id -> a)
          case None => assert(false)
        }
      }
      
    }
    
    println("Actor merging done...")
    
    val finalActor = mergedActorMap(topNwName)
    writeFile("output/"+finalActor.id+".actor", ASTPrinter.orcc.print(finalActor))
    
    if (!params.ScheduleXML.isDefined) {
      val appInfo = ApplicationInformation(topnw, actorScheduleInfo.toList)
      writeFile("output/"+finalActor.id+"_schedules.xml", appInfo.print)
    }
    
    (finalActor,allSchedules.toList)
    
  }
  
  def writeFile(filename: String, text: String) {
    val writer = new FileWriter(new File(filename));
    writer.write(text)
    writer.flush
    writer.close
  }
  
}

object DepTree {
  def apply[T<:DFActor](entity: T): DepTree[DFActor] = {
    entity match {
      case nw: Network => {
        val entities = nw.entities.get.entities
        val children = for (e <- entities) yield DepTree(e.actor)
        if (children.isEmpty) Leaf(nw) else Branch(nw,children)
      }
      case ba: BasicActor => Leaf(ba)
    }
  }
}

sealed trait DepTree[+A<:DFActor] {
  def value: A
  def postOrder: List[A]
}
case class Leaf[A<:DFActor](val value: A) extends DepTree[A] {
  override def toString = "Leaf(" + value.id +")"
  def postOrder = List(value)
}
case class Branch[A<:DFActor](val value: A, val children: List[DepTree[A]]) extends DepTree[A] {
  override def toString = "Branch(" + value.id +","+ children.toString +")"
  def postOrder = children.flatMap { _.postOrder } ::: List(value)
}
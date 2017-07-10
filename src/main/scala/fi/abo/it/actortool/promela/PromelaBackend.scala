package fi.abo.it.actortool.promela

import java.io.File
import java.io.FileWriter
import fi.abo.it.actortool._
import fi.abo.it.actortool.schedule.ContractSchedule
import fi.abo.it.actortool.ActorTool.CommandLineParameters
import fi.abo.it.actortool.merging.ActorMerger
import fi.abo.it.actortool.boogie.BoogieScheduleVerifier
import fi.abo.it.actortool.util.ASTPrinter

class PromelaBackend(val params: CommandLineParameters) extends Backend[(BasicActor,List[ScheduleContext])] {
  
  val printer = new Promela.PromelaPrinter
  
  
  def invoke(programCtx: ProgramContext): (BasicActor,List[ScheduleContext]) = {
    val translator = new PromelaTranslator(params)
    
    val topNwName = params.Schedule.get
    val topnw = programCtx.program.find { x => x.id == topNwName }
    val allSchedules = new collection.mutable.ListBuffer[ScheduleContext]
    
    val constants = (programCtx.program.collect { case DataUnit(_,constants) => constants }).flatten
    val mergerBackend = new ActorMerger(constants)
    topnw match {
      case Some(nw) => {
        val evaluationOrder = buildDependencyTree(nw.asInstanceOf[DFActor]).postOrder
        //println(evaluationOrder map { _.id })
        val mergedActorMap = collection.mutable.Map[String,BasicActor]()
        for (entity <- evaluationOrder) {
          entity match {
            case ba: BasicActor => {
              if (entity.contractActions.isEmpty || (!params.MergeActions && !ba.hasAnnotation("merge"))) mergedActorMap += (entity.id -> ba)
              else {
                val translations = translator.invoke(ba,mergedActorMap.toMap,Map.empty,constants)
                val schedules = for (t <- translations) yield verifyForContract(t)
                
                val scheduleCtx = new ScheduleContext(
                    ba, schedules, mergedActorMap.toMap,
                    programCtx.program, programCtx.typeContext)
                allSchedules += scheduleCtx
//                println("Verifying obtained schedules...")
//                scheduleVerifier.invoke(scheduleCtx)
                val actor = mergerBackend.invoke(scheduleCtx)
                actor match {
                  case Some(a) => mergedActorMap += (entity.id -> a)
                  case None => assert(false)
                }
                //mergedActorMap += (entity.id -> actor)
              }
            }
            case nw: Network => {
              val translations = translator.invoke(nw,mergedActorMap.toMap,Map.empty,constants)
              
              val schedules = for (t <- translations) yield verifyForContract(t)
              
              val scheduleCtx = new ScheduleContext(
                    nw, schedules, mergedActorMap.toMap,
                    programCtx.program, programCtx.typeContext)
              allSchedules += scheduleCtx
//              println("Verifying obtained schedules...")
//              scheduleVerifier.invoke(scheduleCtx)
              val actor = mergerBackend.invoke(scheduleCtx)
              actor match {
                case Some(a) => mergedActorMap += (entity.id -> a)
                case None => assert(false)
              }
              //mergedActorMap += (entity.id -> actor)
            }
          }
        }
        println("Merging done")
        val finalActor = mergedActorMap(topNwName)
        writeFile("output/"+finalActor.id+".actor", ASTPrinter.orcc.print(finalActor))
        (finalActor,allSchedules.toList)
        
      }
      case None => throw new RuntimeException("There is no network named " + topNwName)
    }
    
  }
  
  def verifyForContract[T<:DFActor](translation: Translation[T]): ContractSchedule = {
    
    val outputParser = new ScheduleParser(translation)
    
    val promelaProg = translation.promelaProgram
    val contract = translation.contract
    val entity = translation.entity
    
    
    if (params.ScheduleSimulate) {
      println("Running spin simulation on contract '" + contract.fullName + "' of network '" + entity.id + "'...")
      val progTxt = PromelaPrelude.get + promelaProg.map(printer.print).foldLeft("")((a,b) => a + b)
      if (params.PromelaPrint) {
        println(progTxt)
      }
      outputParser.startSchedule(contract)
      PromelaRunner.simulate(progTxt, entity.id + "__" + contract.fullName+".pml", outputParser)
      outputParser.endSchedule
      outputParser.getSchedule
    }
    else {
      println("Running spin search on contract '" + contract.fullName + "' of network '" + entity.id + "'...")
      
      var cost: Option[Int] = None
      var schedule: Option[ContractSchedule] = None
      val ltlFormula = translation.ltlFormula
      
      val progTxt = PromelaPrelude.get + promelaProg.map(printer.print).foldLeft("")((a,b) => a + b)
      if (params.PromelaPrint) {
        println(progTxt)
      }
      
      var iters = 0
      var foundOptimal = false
      while (!foundOptimal && iters < 2) {
        val formula = {
          //cost match {
            //case Some(c) => 
              //val prevCost = if (c < 0) Promela.UnaryExpr("-",Promela.IntLiteral(-c)) else Promela.IntLiteral(c)
              Promela.Ltl("", Promela.UnaryExpr("[]",Promela.UnaryExpr("!",ltlFormula && Promela.VarExp("best_cost"))))
              //Promela.Ltl("", Promela.UnaryExpr("<>",ltlFormula && Promela.VarExp("best_cost")))
            //case None => Promela.Ltl("", Promela.UnaryExpr("[]",Promela.UnaryExpr("!",ltlFormula)))
          //}
        }
        val formulaTxt = printer.print(formula)
        outputParser.startSchedule(contract)
        val newCost = PromelaRunner.search(progTxt + formulaTxt, entity.id + "__" + contract.fullName+".pml", outputParser)
        
        newCost match {
          case None => {
            println(">> Found cost-optimal schedule")
            foundOptimal = true
            outputParser.endSchedule
            schedule = Some(outputParser.getSchedule)
          }
          case Some(c) => {
            println(">> Cost: " + c)
            cost = newCost
            outputParser.endSchedule
            schedule = Some(outputParser.getSchedule)
          }
        }
        iters = iters+1
      }
      schedule match {
        case None => throw new RuntimeException("Did not find any schedule")
        case Some(s) => s
      }
    }
    
    
  }
  
  def buildDependencyTree(entity: DFActor): DepTree[DFActor] = {
    entity match {
      case nw: Network => {
        val entities = nw.entities.get.entities
        val children = for (e <- entities) yield buildDependencyTree(e.actor)
        if (children.isEmpty) Leaf(nw) else Branch(nw,children)
      }
      case ba: BasicActor => Leaf(ba)
    }
  }
  
  def writeFile(filename: String, text: String) {
    val writer = new FileWriter(new File(filename));
    writer.write(text)
    writer.flush
    writer.close
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

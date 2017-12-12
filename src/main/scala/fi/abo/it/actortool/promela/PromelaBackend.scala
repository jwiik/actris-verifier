package fi.abo.it.actortool.promela

import java.io.File
import java.io.FileWriter
import fi.abo.it.actortool._
import fi.abo.it.actortool.schedule.ContractSchedule
import fi.abo.it.actortool.ActorTool.CommandLineParameters
import fi.abo.it.actortool.merging.ActorMerger
import fi.abo.it.actortool.util.ASTPrinter
import fi.abo.it.actortool.schedule.Scheduler
import fi.abo.it.actortool.schedule.ActorInformation
import fi.abo.it.actortool.schedule.ActorInformation
import fi.abo.it.actortool.schedule.ApplicationInformation

class PromelaBackend(val params: CommandLineParameters) extends Scheduler {
  
  val translator = new PromelaTranslator(params)
  val runner = new PromelaRunner(params)
  
  def schedule(entity: DFActor, mergedActors: Map[String,BasicActor], constants: Seq[Declaration]): List[ContractSchedule] = {
     val translations = translator.invoke(entity,mergedActors,Map.empty,constants)
     val translationsToSchedule = translations
     /*
     .filter { 
       t => params.ContractsToVerify.contains((t.entity.fullName -> t.contract.fullName)) 
     }
     */
     val schedules = for (t <- translationsToSchedule) yield scheduleForContract(t)
     schedules
  }
  
  def scheduleForContract[T<:DFActor](translation: Translation[T]): ContractSchedule = {
    
    val printerNoC = new Promela.PromelaPrinter(false,false)
    val printerC = new Promela.PromelaPrinter(true,false)
    val simOutputParser = new ScheduleParser(translation)
    
    val promelaProg = translation.promelaProgram
    val contract = translation.contract
    val entity = translation.entity
    
    val defines = "#define __INIT_COST %d\n#define __RUNS %d\n"
    val initCost = 100000
    val initRuns = 100000
    
    val initCostDef = defines.format(initCost,initRuns) 
    
    InstrumentationPrelude.setSize(initCost)
    PromelaPrelude.addComponent(InstrumentationPrelude)
    
    val progTxtNoC = initCostDef + PromelaPrelude.get + promelaProg.map(printerNoC.print).foldLeft("")((a,b) => a + b)
    
    println("Running spin simulations on contract '" + contract.fullName + "' of '" + entity.id + "'...")
    
    var simulatedSchedule: Option[ContractSchedule] = None 
    for (i <- (0 until 10)) {
      simOutputParser.startSchedule(contract)
      runner.simulate(progTxtNoC, entity.id + "__" + contract.fullName+"_sim.pml", simOutputParser)
      simOutputParser.endSchedule
      
      val schedule = simOutputParser.getSchedule
      
      simulatedSchedule match {
        case Some(bestSchedule) => {
          if (bestSchedule.cost > schedule.cost) {
            println(">> New best: " + schedule.cost)
            simulatedSchedule = Some(schedule)
          }
        }
        case None => {
          simulatedSchedule = Some(schedule)
        }
      }

    }
    
    if (params.ScheduleSimulate) {
      simulatedSchedule.get
    }
    else {
      val schedLength = simulatedSchedule.get.length
      val schedCost = simulatedSchedule.get.cost
      
      val outputParser = new ScheduleParser(translation)
      
      InstrumentationPrelude.setSize(schedCost)
      val initCostDef = defines.format(schedCost,schedLength) 
      
      val progTxt = initCostDef + PromelaPrelude.get + promelaProg.map(printerC.print).foldLeft("")((a,b) => a + b)
      
      if (params.PromelaPrint) {
        println(progTxt)
      }
      
      println("Simulation returned schedule with length " + schedLength + " and cost " + schedCost)
      
      println("Running spin search on contract '" + contract.fullName + "' of '" + entity.id + "'...")

      val formula = {
        Promela.Ltl("", Promela.UnaryExpr("<>", Promela.CExpr("now.__INSTR_COST > BEST_COST")  ))
      }
      
      val formulaTxt = printerC.print(formula)
      outputParser.startSchedule(contract)
      
      runner.search(progTxt + formulaTxt, entity.id + "__" + contract.fullName+".pml", outputParser)
      
      outputParser.endSchedule
      val schedule = outputParser.getSchedule
      
      if (schedule.cost == -1) {
        simulatedSchedule.get
      }
      else {
        schedule
      }
    }
    
    
  }
  
}


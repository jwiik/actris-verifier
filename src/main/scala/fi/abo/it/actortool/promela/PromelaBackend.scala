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
  
  def schedule(entity: DFActor, mergedActors: Map[String,BasicActor], constants: List[Declaration]): List[ContractSchedule] = {
     val translations = translator.invoke(entity,mergedActors,Map.empty,constants)
     val schedules = for (t <- translations) yield scheduleForContract(t)
     schedules
  }
  
  def scheduleForContract[T<:DFActor](translation: Translation[T]): ContractSchedule = {
    
    val printerNoC = new Promela.PromelaPrinter(false)
    val printerC = new Promela.PromelaPrinter(true)
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
    
    println("Running spin simulation on contract '" + contract.fullName + "' of '" + entity.id + "'...")
      
    simOutputParser.startSchedule(contract)
    PromelaRunner.simulate(progTxtNoC, entity.id + "__" + contract.fullName+"_sim.pml", simOutputParser)
    simOutputParser.endSchedule
    val simulatedSchedule = simOutputParser.getSchedule
    if (params.ScheduleSimulate) {
      simulatedSchedule
    }
    else {
      val schedLength = simulatedSchedule.length
      val schedCost = simulatedSchedule.cost
      
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
      
      PromelaRunner.search(progTxt + formulaTxt, entity.id + "__" + contract.fullName+".pml", outputParser)
      
      outputParser.endSchedule
      val schedule = outputParser.getSchedule
      
      schedule
    }
    
    
  }
  
}


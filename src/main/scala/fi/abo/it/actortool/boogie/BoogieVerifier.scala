package fi.abo.it.actortool.boogie

import scala.concurrent.Future
import scala.concurrent.Await
import scala.concurrent.ExecutionContext
import scala.concurrent.duration._
import fi.abo.it.actortool._
import fi.abo.it.actortool.schedule._
import fi.abo.it.actortool.ActorTool.CommandLineParameters


import ExecutionContext.Implicits.global

class BoogieVerifier(val params: CommandLineParameters, val actorActionsOnly: Boolean) extends Backend[Unit] {
  
  val sep = java.io.File.separator
  
  def invoke(programCtx: ProgramContext) {
    val translator = new Translator(params.SmokeTest, false, actorActionsOnly)
    val bplProgs = translator.invoke(programCtx)
    assert(bplProgs.size == 1) 
    val result = BoogieRunner.run(params, bplProgs(0).program, params.OutputDir+sep+"output.bpl")  
    println(result.toString + "\n")
  }
  
}

class BoogieScheduleVerifier(
    val params: CommandLineParameters) extends GeneralBackend[ScheduleContext, Unit] {
  
  val sep = java.io.File.separator
  
  def invoke(scheduleCtx: ScheduleContext) {
    
    val translator = 
      new BoogieScheduleCheckTranslator(
          params.MergeActions, params.ContractsToVerify, params.SmokeTest)
    val typeCtx = scheduleCtx.typeContext
    
    val schedBplProcs = translator.invoke(scheduleCtx)
    
    val futures = schedBplProcs.map { 
      p => Future { 
        assert(p.entities.size == 1)
        val fileName = scheduleCtx.entity.fullName + "__" + p.entities(0).fullName + ".bpl"
        val result = BoogieRunner.run(params, p.program, params.OutputDir+sep+fileName) 
        result
      }
    }
    
    val res = Await.result(Future.sequence(futures), Duration(48, HOURS))
    
    val combinedResult = res.reduceLeft {
      (a,b) => a combine b
    }
    
    println(combinedResult.toString + "\n")
    
  }
}
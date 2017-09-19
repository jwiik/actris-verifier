package fi.abo.it.actortool.boogie

import scala.concurrent.Future
import scala.concurrent.Await
import scala.concurrent.ExecutionContext
import scala.concurrent.duration._
import fi.abo.it.actortool._
import fi.abo.it.actortool.schedule._
import fi.abo.it.actortool.ActorTool.CommandLineParameters


import ExecutionContext.Implicits.global

class BoogieVerifier(val params: CommandLineParameters) extends Backend[Unit] {
  
  def invoke(programCtx: ProgramContext) {
    val translator = new Translator(params.SmokeTest, false)
    val bplProg = translator.invoke(programCtx)
    val res = BoogieRunner.run(params, bplProg(0).program, params.BplFile)
    println("Verification finished: " + res.verified + " verified, " + res.errors + " errors")
  }
  
}

class BoogieScheduleVerifier(val params: CommandLineParameters) extends GeneralBackend[ScheduleContext, Unit] {
  def invoke(scheduleCtx: ScheduleContext) {
    val translator = new BoogieScheduleCheckTranslator(params.MergeActions, params.ContractsToVerify)
    val bplProgs = translator.invoke(scheduleCtx)
    val futures = bplProgs.map { 
      p => Future { 
        val fileName = scheduleCtx.entity.fullName + "__" + p.entity.contract.fullName + ".bpl"
        val result = BoogieRunner.run(params, p.program, "output/"+fileName) 
        println("Verification of schedule for contract " + p.entity.contract.fullName + " finished with " + result.errors + " errors")
        result
      }
    }
    val res = Await.result(Future.sequence(futures), Duration(48, HOURS))
    
    val combinedResult = res.reduceLeft {
      (a,b) => new BoogieRunner.BoogieResult(a.verified+b.verified,a.errors+b.errors,a.messages++b.messages) 
    }
    
    println("Verification finished: " + combinedResult.verified + " verified, " + combinedResult.errors + " errors")
    
    //BoogieRunner.run(params, bplProgs(0))
  }
}
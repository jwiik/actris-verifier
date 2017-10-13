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
    val typeCtx = scheduleCtx.typeContext
    val actionTranslator = new BasicActorTranslator(params.SmokeTest,false, scheduleCtx.typeContext, false)  
    
    
    val schedBplProcs = translator.invoke(scheduleCtx)
    val actionBplProg = scheduleCtx.entity match {
      case ba: BasicActor => actionTranslator.translateEntity(ba)
      case nw: Network => Seq.empty
    }
    
    
    val futures = schedBplProcs.map { 
      p => Future { 
        val fileName = scheduleCtx.entity.fullName + "__" + p.entity.contract.fullName + ".bpl"
        val result = BoogieRunner.run(params, p.program, "output/"+fileName)
        
        println(
            "Verification of schedule for contract " + p.entity.contract.fullName + 
            " finished with " + result.errors + " errors")
            
        result
      }
    }
    
    val actionResults =
      if (!actionBplProg.isEmpty) {
        val fileName = scheduleCtx.entity.fullName + "__actions.bpl"
        val actionResults = BoogieRunner.run(params, actionBplProg(0).program, fileName)
        
        println(
              "Verification of actor actions for actor " + scheduleCtx.entity.fullName + 
              " finished with " + actionResults.errors + " errors")
        
        Seq(actionResults)
      }
      else Seq.empty
    
    val res = Await.result(Future.sequence(futures), Duration(48, HOURS))
    
    val combinedResult = (actionResults ++ res).reduceLeft {
      (a,b) => new BoogieRunner.BoogieResult(a.verified+b.verified,a.errors+b.errors,a.messages++b.messages) 
    }
    
    println("Verification finished: " + combinedResult.verified + " verified, " + combinedResult.errors + " errors")
    
    
  }
}
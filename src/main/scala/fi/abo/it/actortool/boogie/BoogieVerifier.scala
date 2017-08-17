package fi.abo.it.actortool.boogie


import fi.abo.it.actortool._
import fi.abo.it.actortool.schedule._
import fi.abo.it.actortool.ActorTool.CommandLineParameters

class BoogieVerifier(val params: CommandLineParameters) extends Backend[Unit] {
  
  def invoke(programCtx: ProgramContext) {
    val translator = new Translator(params.SmokeTest, false)
    val bplProg = translator.invoke(programCtx)
    BoogieRunner.run(params, bplProg)
  }
  
}

class BoogieScheduleVerifier(val params: CommandLineParameters) extends GeneralBackend[ScheduleContext, Unit] {
  def invoke(scheduleCtx: ScheduleContext) {
    val translator = new BoogieScheduleCheckTranslator(params.MergeActions, params.ContractsToVerify)
    val bplProg = translator.invoke(scheduleCtx)
    BoogieRunner.run(params, bplProg)
  }
}
package fi.abo.it.actortool.promela

import fi.abo.it.actortool._
import fi.abo.it.actortool.schedule.ContractSchedule
import fi.abo.it.actortool.ActorTool.CommandLineParameters

class PromelaBackend(val params: CommandLineParameters) extends Backend[List[ContractSchedule]] {
  val printer = new Promela.PromelaPrinter
  
  def invoke(programCtx: ProgramContext): List[ContractSchedule] = {
    val translator = new PromelaTranslator(params)
    val translations = translator.invoke(programCtx)
    translations.flatMap { t =>
      val outputParser = new SpinOutputParser(t)
      for ((contract,prog) <- t.promelaPrograms) {
        verifyForContract(t.network, contract, prog,outputParser)
      }
      outputParser.allSchedules
    }
  }
  
  def verifyForContract(network: Network, contract: ContractAction, promelaProg: List[Promela.Decl], outputParser: SpinOutputParser) = {
    val progTxt = PromelaPrelude.get + promelaProg.map(printer.print).foldLeft("")((a,b) => a + b)
    if (params.PromelaPrint) {
      println(progTxt)
    }
    outputParser.startNewSchedule(contract)
    println("Running spin on contract '" + contract.fullName + "' of network '" + network.id + "'...")
    PromelaRunner.run(progTxt, outputParser)
  }
}
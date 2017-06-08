package fi.abo.it.actortool.promela

import java.io.File
import java.io.FileWriter
import collection.mutable.ListBuffer
import java.io.BufferedReader
import java.io.InputStreamReader
import fi.abo.it.actortool._
import fi.abo.it.actortool.ActorTool.CommandLineParameters

class PromelaRunner(val params: CommandLineParameters) extends Verifier[Map[ContractAction,List[Promela.Decl]], Unit]  {
  
  val translator = new PromelaTranslator(params)
  val printer = new Promela.PromelaPrinter
  
  def translateProgram(decls: List[TopDecl], typeCtx: Resolver.Context): Map[ContractAction,List[Promela.Decl]] = {
    translator.translateProgram(decls, typeCtx) 
  }
  
  def verify(promelaPrograms: Map[ContractAction,List[Promela.Decl]]): Unit = {
    for ((contract,prog) <- promelaPrograms) {
      verifyForContract(contract, prog)
    }
  }
  
  def verifyForContract(contract: ContractAction, promelaProg: List[Promela.Decl]) = {
    val progTxt = promelaProg.map(printer.print).foldLeft("")((a,b) => a + b)
    //println(progTxt)
    println("Running spin on contract " + contract.fullName + "...")
    writeFile("output/spin.pml",progTxt)
    val spin = Runtime.getRuntime.exec("/Users/jonatan/Tools/bin/spin -T -B output/spin.pml")
//    val output = spin.getOutputStream
//    output.write(progTxt.getBytes)
//    output.close
    
    Runtime.getRuntime.addShutdownHook(new Thread(new Runnable() {
      def run {
        spin.destroy
      }
    }))
    
    val errorReadingThread = new Thread(new Runnable() {
      def run {
        val err = new BufferedReader(new InputStreamReader(spin.getErrorStream))
        var line = err.readLine;
        while(line!=null) {Console.err.println(line); Console.err.flush; line = err.readLine}
      }
    });
    errorReadingThread.start()
    val input = new BufferedReader(new InputStreamReader(spin.getInputStream))
    var line = input.readLine()
    var previousLine = null: String
    val spinOutput: ListBuffer[String] = new ListBuffer
    while (line != null) {
      println(line)
      spinOutput += line
      previousLine = line
      line = input.readLine()
    }
    spin.waitFor
    input.close
  }
  
  def writeFile(filename: String, text: String) {
    val writer = new FileWriter(new File(filename));
    writer.write(text)
    writer.flush
    writer.close
  }
  
}
package fi.abo.it.actortool.promela

import java.io.File
import java.io.FileWriter
import collection.mutable.ListBuffer
import java.io.BufferedReader
import java.io.InputStreamReader
import fi.abo.it.actortool._
import fi.abo.it.actortool.schedule.ContractSchedule
import fi.abo.it.actortool.ActorTool.CommandLineParameters

object PromelaRunner {
  
  def run(progTxt: String, outputFile: String, outputParser: SpinOutputParser) = {
    
    writeFile("output/"+outputFile,progTxt)
    
    val outputLog = new ListBuffer[String]
    outputLog += "spin ##########################################\n"
    var output = sys.process.Process(Seq("/Users/jonatan/Tools/bin/spin","-T","-B",outputFile), new java.io.File("output")).!!
//    outputLog += "spin -a ##########################################\n"
//    var output = sys.process.Process(Seq("/Users/jonatan/Tools/bin/spin","-a",outputFile), new java.io.File("output")).!!
//    //println(output)
//    outputLog += "gcc ##############################################\n"
//    output = sys.process.Process(Seq("gcc","-DVECTORSZ=6000","-o","pan","pan.c"), new java.io.File("output")).!!
//    outputLog += output + "\n"
//    //println(output)
//    outputLog += "pan ##############################################\n"
//    output = sys.process.Process(Seq("./pan"), new java.io.File("output")).!!
//    outputLog += output + "\n"
//    //println(output)
//    outputLog += "spin -t ##########################################\n"
//    output = sys.process.Process(Seq("/Users/jonatan/Tools/bin/spin","-t", "-T","-B",outputFile), new java.io.File("output")).!!
//    //println(output)
//    outputLog += output + "\n"
    
    outputParser.read(output)
    
    writeFile("output/pml_backend.log",outputLog.toString)
//    val spinGenerate = Runtime.getRuntime.exec("/Users/jonatan/Tools/bin/spin -search " + outputFile)
//    Runtime.getRuntime.addShutdownHook(new Thread(new Runnable() {
//      def run {
//        spinGenerate.destroy
//      }
//    }))
//    spinGenerate.waitFor
//    
//    val panCompile = Runtime.getRuntime.exec("gcc -DVECTORSZ=6000 -o output/pan output/pan.c")
//    Runtime.getRuntime.addShutdownHook(new Thread(new Runnable() {
//      def run {
//        panCompile.destroy
//      }
//    }))
//    panCompile.waitFor
//    
//    val panRun = Runtime.getRuntime.exec("output/pan")
//    Runtime.getRuntime.addShutdownHook(new Thread(new Runnable() {
//      def run {
//        panRun.destroy
//      }
//    }))
//    panRun.waitFor
//    
//    val spin = Runtime.getRuntime.exec("/Users/jonatan/Tools/bin/spin -t -T -B " + outputFile)
//    Runtime.getRuntime.addShutdownHook(new Thread(new Runnable() {
//      def run {
//        spin.destroy
//      }
//    }))
//    
//    val errorReadingThread = new Thread(new Runnable() {
//      def run {
//        val err = new BufferedReader(new InputStreamReader(spin.getErrorStream))
//        var line = err.readLine;
//        while(line!=null) {Console.err.println(line); Console.err.flush; line = err.readLine}
//      }
//    });
//    errorReadingThread.start()
//    val input = new BufferedReader(new InputStreamReader(spin.getInputStream))
//    var line = input.readLine()
//    var previousLine = null: String
//    val spinOutput: ListBuffer[String] = new ListBuffer
//    while (line != null) {
//      //println(line)
//      outputParser.read(line)
//      spinOutput += line
//      previousLine = line
//      line = input.readLine()
//    }
//    spin.waitFor
//    input.close
  }
  
  def writeFile(filename: String, text: String) {
    val writer = new FileWriter(new File(filename));
    writer.write(text)
    writer.flush
    writer.close
  }
  
}
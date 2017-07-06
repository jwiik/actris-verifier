package fi.abo.it.actortool.promela

import sys.process.Process
import sys.process.ProcessLogger
import java.io.File
import java.io.FileWriter
import collection.mutable.ListBuffer
import java.io.BufferedReader
import java.io.InputStreamReader
import fi.abo.it.actortool._
import fi.abo.it.actortool.schedule.ContractSchedule
import fi.abo.it.actortool.ActorTool.CommandLineParameters

object PromelaRunner {
  
  def simulate(progTxt: String, outputFile: String, outputParser: SpinOutputParser) = {
    
    writeFile("output/"+outputFile,progTxt)
    
    val outputLog = new ListBuffer[String]
    outputLog += "spin ##########################################\n"
    var output = Process(Seq("/Users/jonatan/Tools/bin/spin","-T","-B",outputFile), new java.io.File("output")).!!
    outputParser.read(output)
    writeFile("output/pml_backend.log",outputLog.toString)

  }
  
  def search(progTxt: String, outputFile: String, outputParser: SpinOutputParser) = {
    val pipeline = 
      Process(Seq("/Users/jonatan/Tools/bin/spin","-a",outputFile), new java.io.File("output")) ###
      Process(Seq("gcc","-DVECTORSZ=6000","-o","pan","pan.c"), new java.io.File("output")) ###
      Process(Seq("./pan"), new java.io.File("output")) ###
      Process(Seq("/Users/jonatan/Tools/bin/spin","-t", "-T","-B",outputFile), new java.io.File("output"))
    
    writeFile("output/"+outputFile,progTxt)
    
    val out = new StringBuilder
    val logger = ProcessLogger(out append _ + "\n" , out append _ + "\n")

    var exitCode = pipeline ! logger
    if (exitCode != 0) {
      System.err.println(out.mkString)
      throw new RuntimeException("Non-zero exit code from spin")
    }
    outputParser.read(out.mkString)
    
    writeFile("output/pml_backend.log", out.mkString)
  }
  
  def writeFile(filename: String, text: String) {
    val writer = new FileWriter(new File(filename));
    writer.write(text)
    writer.flush
    writer.close
  }
  
  
}
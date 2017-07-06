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
  
  def simulate(progTxt: String, outputFile: String, scheduleParser: ScheduleParser) = {
    
    writeFile("output/"+outputFile,progTxt)
    
    val outputLog = new ListBuffer[String]
    outputLog += "spin ##########################################\n"
    var output = Process(Seq("/Users/jonatan/Tools/bin/spin","-T","-B",outputFile), new java.io.File("output")).!!
    scheduleParser.read(output)
    writeFile("output/pml_backend.log",outputLog.toString)

  }
  
  def search(progTxt: String, outputFile: String, scheduleParser: ScheduleParser) = {
    
    val processes = List(
        Process(Seq("/Users/jonatan/Tools/bin/spin","-a","-o3",outputFile), new java.io.File("output")),
        Process(Seq("gcc","-DVECTORSZ=1000000","-o","pan","pan.c"), new java.io.File("output")),
        Process(Seq("./pan", "-m1000000", "-a"), new java.io.File("output")),
        Process(Seq("/Users/jonatan/Tools/bin/spin","-t", "-T","-B",outputFile), new java.io.File("output"))
      )

    
    
    //val pipeline = pGenerate ### pCompile ### pVerify ### pSimulate
    
    writeFile("output/"+outputFile,progTxt)
    
    val out = new SpinParser(scheduleParser)
    val logger = ProcessLogger(out append _  , out append _ )
    
    for (p <- processes) {
      var exitCode = p ! logger
      if (exitCode != 0) {
        System.err.println(out.mkString)
        throw new RuntimeException("Non-zero exit code from spin")
      }
      out.nextStep
    }
    
    //outputParser.read(out.mkString)
    
    writeFile("output/" + outputFile + "_pml_backend.log", out.mkString)
  }
  
  def writeFile(filename: String, text: String) {
    val writer = new FileWriter(new File(filename));
    writer.write(text)
    writer.flush
    writer.close
  }
  
  class SpinParser(scheduleParser: ScheduleParser) {
    object State {
      val Generate = 0
      val Compile = 1
      val Verify = 2
      val Simulate = 3
      val Done = 4
    }
    
    val assertionViolatedRegex = """.*assertion violated.*""".r
    
    private var state = 0
    private var violated = false
    private val lines = new StringBuilder
    private val schedule = new StringBuilder
    
    def nextStep { state = state + 1 }
    
    def append(str: String) = {
      lines.append(str + "\n")
      if (state == State.Verify) {
        if (!violated && assertionViolatedRegex.findFirstIn(str).isDefined) {
          violated = true
        }
        //println("VERIFY: " + str)
      }
      if (state == State.Simulate) {
        if (!violated) {
          assert(false,"Did not find schedule")
        }
        if (str.startsWith("<action")) {
          scheduleParser.read(str)
        }
      }
    }
    
    def mkString = lines.mkString
    
  }
  
  
}
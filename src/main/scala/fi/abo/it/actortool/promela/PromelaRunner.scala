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
  
  def search(progTxt: String, outputFile: String, scheduleParser: ScheduleParser): Option[Int] = {
    
    val processes = List(
        Process(Seq("/Users/jonatan/Tools/bin/spin","-a","-o3",outputFile), new java.io.File("output")),
        Process(Seq("gcc","-DVECTORSZ=1000000","-DCOLLAPSE","-DSAFETY","-DMEMLIM=1024","-o","pan","pan.c"), new java.io.File("output")),
        Process(Seq("./pan", "-m1000000" /*, "-c1000", "-e"*/), new java.io.File("output")),
        Process(Seq("/Users/jonatan/Tools/bin/spin","-t", "-T",outputFile), new java.io.File("output"))
      )

    
    
    //val pipeline = pGenerate ### pCompile ### pVerify ### pSimulate
    
    writeFile("output/"+outputFile,progTxt)
    
    val parser = new SpinParser
    val logger = ProcessLogger(parser append _  , parser append _ )
    
    var cost: Option[Int] = None
    
    for ((p,step) <- processes.zipWithIndex) {
      
      if (step == Step.Simulate && !parser.foundSchedule) {
        
        //assert(false,"Did not find schedule")
      }
      else {
        var exitCode = p ! logger
        if (exitCode != 0) {
          val output = parser.mkString
          System.err.println(output)
          writeFile("output/" + outputFile + "_pml_backend.log", output)
          throw new RuntimeException("Non-zero exit code from spin: " + exitCode)
        }
        if (step == Step.Simulate) {
          //println(parser.schedule)
          cost = Some(parser.variables(Instrumentation.COST).toInt)
          scheduleParser.read(parser.schedule)
        }
      }
      
      
      
      parser.nextStep
    }
    
    //outputParser.read(out.mkString)
    
    writeFile("output/" + outputFile + "_pml_backend.log", parser.mkString)
    
    cost 
  }
  
  def writeFile(filename: String, text: String) {
    val writer = new FileWriter(new File(filename));
    writer.write(text)
    writer.flush
    writer.close
  }
  
  
  
  
}

object Step {
  val Generate = 0
  val Compile = 1
  val Verify = 2
  val Simulate = 3
  val Done = 4
}

class SpinParser {
  
  val assertionViolatedRegex = """.*assertion violated.*""".r
  val variable = """\s*([_\w]*)\s=\s([\d-]*)""".r
  
  private var state = 0
  private var violated = false
  private var variableMap = Map.empty[String,String]
  private val lines = new StringBuilder
  private val scheduleData = new StringBuilder
  
  def nextStep { state = state + 1 }
  
  def foundSchedule = violated
  
  def append(str: String) = {
    lines.append(str + "\n")
    if (state == Step.Verify) {
      if (!violated && assertionViolatedRegex.findFirstIn(str).isDefined) {
        violated = true
      }
      //println("VERIFY: " + str)
    }
    if (state == Step.Simulate) {
      //println(str)
      if (str.startsWith("<action")) {
        scheduleData.append(str+ "\n")
      }
      else {
        str match {
          case variable(name,value) => variableMap += (name -> value)
          case _ =>
        }
      }
    }
  }
  
  def mkString = lines.mkString
  def schedule = scheduleData.mkString
  def variables = variableMap
  
}



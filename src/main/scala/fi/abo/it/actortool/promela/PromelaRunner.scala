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
    val process = Process(Seq("/Users/jonatan/Tools/bin/spin","-T",outputFile), new java.io.File("output"))
    writeFile("output/"+outputFile,progTxt)
    val parser = new SpinParser(Step.Simulate)
    val logger = ProcessLogger(parser append _  , parser append _ )
    var exitCode = process ! logger
    
    if (exitCode != 0) {
      val output = parser.mkString
      System.err.println(output)
      writeFile("output/" + outputFile + "_pml_backend_sim.log", output)
      throw new RuntimeException("Non-zero exit code from spin: " + exitCode)
    }
    
    val cost = parser.variables("__INSTR_COST").toInt
    
    scheduleParser.setCost(cost)
    scheduleParser.read(parser.schedule)
    
    
    
    writeFile("output/" + outputFile + "_backend_sim.log", parser.mkString)

  }
  
  def search(progTxt: String, outputFile: String, scheduleParser: ScheduleParser): Option[Int] = {
    val commands = List(
        Seq("/Users/jonatan/Tools/bin/spin","-a","-o3",outputFile),
        Seq("gcc","-DVECTORSZ=1000000", "-DCOLLAPSE", "-DSAFETY","-DMEMLIM=6144" ,"-o","pan","pan.c"),
        Seq("./pan", "-m1000000"),
        Seq("./pan", "-r", "-n")
      )
        
    val processes = commands.map { cmd => Process(cmd, new java.io.File("output")) }

    
    writeFile("output/"+outputFile,progTxt)
    
    val parser = new SpinParser(Step.Generate)
    val logger = ProcessLogger(parser append _  , parser append _ )
    
    var cost: Option[Int] = None
    
    for ((p,step) <- processes.zipWithIndex) {
      parser.append(">> " + commands(step).mkString(" "))
      var exitCode = p ! logger
      if (exitCode != 0) {
        val output = parser.mkString
        System.err.println(output)
        writeFile("output/" + outputFile + "_pml_backend.log", output)
        throw new RuntimeException("Non-zero exit code from spin: " + exitCode)
      }
      if (step == Step.Simulate) {
        scheduleParser.read(parser.schedule)
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

class SpinParser(startStep: Int) {
  
  val assertionViolatedRegex = """.*assertion violated.*""".r
  val variable = """\s*([_\w]*)\s=\s([\d-]*)""".r
  
  private var state = startStep
  private var violated = false
  private var variableMap = Map.empty[String,String]
  private val lines = new StringBuilder
  private val scheduleData = new StringBuilder
  
  def nextStep { state = state + 1 }
  
  def foundSchedule = violated
  
  def append(str: String) = {
    //println(str)
    if (str.startsWith(">>")) {
      println(str)
    }
    lines.append(str + "\n")
    if (state == Step.Verify) {
      if (!violated && assertionViolatedRegex.findFirstIn(str).isDefined) {
        violated = true
      }
      //println("VERIFY: " + str)
    }
    
    if (state == Step.Simulate) {
      if (str.startsWith("<action")) {
        scheduleData.append(str+ "\n")
      }
      else {
        str match {
          case variable(name,value) => {
            variableMap += (name -> value)
          }
          case _ =>
        }
      }
    }
  }
  
  def mkString = lines.mkString
  def schedule = scheduleData.mkString
  def variables = variableMap
  
}



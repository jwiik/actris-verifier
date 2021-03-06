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

class PromelaRunner(params: CommandLineParameters) {
  
  val outputDir = params.OutputDir
  val sep = java.io.File.separator
  
  def simulate(progTxt: String, outputFile: String, scheduleParser: ScheduleParser) = {
    val seed = scala.util.Random.nextInt
    val process = Process(
        Seq(params.SpinPath,
            "-T",
            "-n"+seed,
            outputDir + sep + outputFile))
    writeFile(outputDir+sep+outputFile,progTxt)
    val parser = new SpinParser(Step.Simulate)
    var exitCode = process ! parser
    
    if (exitCode != 0) {
      val output = parser.mkString
      System.err.println(output)
      writeFile(outputDir + sep + outputFile + "_pml_backend_sim.log", output)
      throw new RuntimeException("Non-zero exit code from spin: " + exitCode)
    }
    
    val cost = parser.variables("__INSTR_COST").toInt
    
    scheduleParser.setCost(cost)
    scheduleParser.read(parser.schedule)

    writeFile(outputDir + sep + outputFile + "_backend_sim.log", parser.mkString)

  }
  
  def search(progTxt: String, outputFile: String, scheduleParser: ScheduleParser): Int = {
    val commands = List(
        Seq(params.SpinPath,"-a","-o3",outputFile) -> Some(outputDir),
        Seq("gcc", 
            "-O2" ,
            "-DVECTORSZ=1000000", 
            "-DCOLLAPSE", "-DSAFETY",
            "-DMEMLIM=4096" ,
            "-o",
            "pan",
            "pan.c") -> Some(outputDir),
        Seq(outputDir + sep + "pan", "-m1000000") -> None,
        Seq(outputDir + sep + "pan", "-r", "-n") -> None)
        
    //val processes = commands.map { cmd => Process(cmd, new java.io.File("output")) }

    
    writeFile(outputDir+sep+outputFile,progTxt)
    
    val parser = new SpinParser(Step.Generate)
    
    var cost: Option[Int] = None
    
    for (((cmd,dir),step) <- commands.zipWithIndex) {
      parser.append(">> " + cmd.mkString(" "))
      //val process = Process(cmd, new java.io.File("output"))
      
      val proc = {
        if (dir.isDefined) { 
          Runtime.getRuntime.exec(
              cmd.toArray, 
              Array.empty[String], 
              dir.get)
        }
        else {
          Runtime.getRuntime.exec(cmd.toArray, Array.empty[String])
        }
      }
      Runtime.getRuntime.addShutdownHook(new Thread(new Runnable() {
        def run {
          proc.destroy
        }
      }))
      // the process blocks until we exhaust input and error streams 
      // (this extra thread reads all from error stream, and buffers it)
      val errorReadingThread = new Thread(new Runnable() {
        def run {
          val err = new BufferedReader(new InputStreamReader(proc.getErrorStream))
          var line = err.readLine;
          while (line!=null) { parser.append(line); line = err.readLine }
        }
      });
      errorReadingThread.start()
      val input = new BufferedReader(new InputStreamReader(proc.getInputStream))
      var line = input.readLine()
      var previousLine = null: String
      val procOutput: ListBuffer[String] = new ListBuffer()
      while (line != null) {
        //println(line)
        parser.append(line)
        procOutput += line
        previousLine = line
        line = input.readLine()
      }
      
      proc.waitFor
      input.close
      
      var exitCode = proc.exitValue
      if (exitCode != 0) {
        if (step == Step.Simulate) {
          System.out.println("No better schedules were found during search")
        }
        else {
          val output = parser.mkString
          System.err.println(output)
          writeFile(outputDir+ sep + outputFile + "_pml_backend.log", output)
          throw new RuntimeException("Non-zero exit code from spin: " + exitCode)
        }
      }
      else {
        if (step == Step.Simulate) {
          scheduleParser.setCost(parser.cost)
          scheduleParser.read(parser.schedule)
        }
      }
      parser.nextStep
    }
    
    //outputParser.read(out.mkString)
    
    writeFile(outputDir + sep + outputFile + "_pml_backend.log", parser.mkString)
    
    parser.cost
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

class SpinParser(startStep: Int) extends ProcessLogger {
  
  val assertionViolatedRegex = """.*assertion violated.*""".r
  val variable = """\s*([_\w]*)\s=\s([\d-]*)""".r
  val newBest = """>>\sNew best:\s([\d]*)""".r
  
  private var state = startStep
  private var variableMap = Map.empty[String,String]
  private var bestCost: Int = -1
  private val lines = new StringBuilder
  private val scheduleData = new StringBuilder
  
  def buffer[T](f: => T): T = f
  
  def err(s: => String) = append(s)
  def out(s: => String) = append(s)
  
  def nextStep { state = state + 1 }
  
  def append(str: String) = {
    //println(str)
    if (str.startsWith(">>")) {
      //println(str)
    }
    lines.append(str + "\n")
    if (state == Step.Verify) {
      str match {
          case newBest(value) => {
            bestCost = value.toInt
          }
          case _ =>
        }
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
  def cost = bestCost
  
}



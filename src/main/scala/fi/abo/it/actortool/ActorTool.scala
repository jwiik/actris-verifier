package fi.abo.it.actortool

import java.io.File
import io.Source
import collection.mutable.ListBuffer
import java.io.BufferedReader
import java.io.InputStreamReader
import java.io.File
import java.io.FileWriter
import java.io.{FileNotFoundException, IOException}
import java.nio.file.Path
import scala.util.parsing.input.Position
import fi.abo.it.actortool.boogie.Boogie
import fi.abo.it.actortool.boogie.BoogieVerifier
import fi.abo.it.actortool.promela.PromelaBackend
import fi.abo.it.actortool.util.ASTPrinter
import fi.abo.it.actortool.util.Config
import fi.abo.it.actortool.boogie.BoogieScheduleVerifier
import fi.abo.it.actortool.schedule.ContractSchedule
import fi.abo.it.actortool.merging.ActorMerger
import fi.abo.it.actortool.schedule.XMLScheduler
import fi.abo.it.actortool.schedule.SchedulingBackend

trait ProgramContext {
  def program: Seq[TopDecl]
  def typeContext: Resolver.Context
}

class BasicProgramContext(
    val program: Seq[TopDecl], 
    val typeContext: Resolver.Context) extends ProgramContext

class ScheduleContext(
    val entity: DFActor,
    val schedules: Seq[ContractSchedule],
    val mergedActors: Map[String,BasicActor],
    val program: Seq[TopDecl], 
    val typeContext: Resolver.Context) extends ProgramContext {
  
  val entities = entity match {
    case nw: Network => nw.entities.get.entities
    case ba: BasicActor => Nil
  }
  
}

trait GeneralBackend[T,U] {
  def invoke(program: T): U
}

trait Backend[U] extends GeneralBackend[ProgramContext,U] {
  def invoke(program: ProgramContext): U
}

object ActorTool {

  val DEBUG = Config.DEBUG
  
  class TranslationException(val pos: Position, val msg: String) extends Exception(msg)

  final val Param = "(?:--)(.*)".r

  object Step extends Enumeration {
    type Step = Value
    val Parse = Value("Parse")
    val Resolve = Value("Typecheck")
    val Infer = Value("Inference")
    val Verification = Value("Verification")
    val Scheduling = Value("Scheduling")
  }

  /**
   * Holds all command line arguments
   */
  abstract class CommandLineParameters {
    val BoogiePath: String
    val Files: List[File]
    val PrintProgram: Boolean
    val DoTypecheck: Boolean
    val DoInfer: Boolean
    val DoTranslate: Boolean
    val DoVerify: Boolean
    val BoogieArgs: String
    val NoBplFile: Boolean
    val BplFile: String
    val Timing: Int
    val InferModules: List[String]
    val SmokeTest: Boolean
    val ReplaceMaps: Boolean
    val BoogieTimeout: Int
    val AssumeGenInvs: Boolean
    val ComponentsToVerify: List[String]
    val PrintInvariantStats: Boolean
    val SizedIntsAsBitvectors: Boolean
    val Schedule: Option[String]
    val ScheduleWeights: Map[String,Int]
    val ScheduleSimulate: Boolean
    val ScheduleXML: Option[File]
    val ScheduleAbstraction: Boolean
    val MergeActions: Boolean
    val PromelaPrint: Boolean
    val PromelaChanSize: Int
    val PrintXMLDescription: Boolean
    val ContractsToVerify: List[(String,String)]
    val SpinPath: String
    val OutputDir: File
    final lazy val help = "actris [option] <filename>+\n"
  }

  //val actorSystem = ActorSystem("actortool")

  def parseCommandLine(args: Array[String]): Option[CommandLineParameters] = {
    var aBoogiePath = "boogie"
    var aBoogieArgs = ""
    var aPrintProgram = false
    var aNoBplFile = false
    var aBplFile = "out.bpl"
    var aDoTypecheck = true
    var aDoInfer = true
    var aDoTranslate = true
    var aDoVerify = true
    var aTiming = if (DEBUG) 2 else 1
    var aInferModules = List("default")
    var aSoundnessChecks = false
    var aSmokeTest = false
    var aReplaceMaps = false
    var aBoogieTimeout = if (DEBUG) 1000000 else 3000
    var aAssumeInvs = true //if (DEBUG) false else true
    var aPrintInvariantStats = false
    var aToVerify: List[String] = List.empty
    var aSizedIntsAsBitVectors = true
    var aSpinPath: String = "spin"
    var aSchedule: Option[String] = None
    var aMergeActions: Boolean = true
    var aPromelaPrint: Boolean = false
    var aScheduleSimulate: Boolean = false
    var aPromelaChanSize: Int = 512
    var aScheduleWeights: Map[String,Int] = Map.empty
    var aScheduleXML: Option[File] = None
    var aScheduleAbstraction = true
    var aPrintXMLDescription: Boolean = false
    var aContractsToVerify: List[(String,String)] = List.empty
    var aOutputDir = 
      java.nio.file.Files.createTempDirectory("actris-output-").toFile
    

    lazy val help = {
      "actortool [option] <filename>+\n"
    }

    val inputs = new ListBuffer[String]()

    for (a <- args) {
      val paramval = a.split(":", 2)
      val (param, value) = 
        if (paramval.size == 1) (paramval(0), None) else (paramval(0), Some(paramval(1)))
      param match {
        case Param("version") => {
          if (System.getProperty("prog.version") != null) {
            val ver = System.getProperty("prog.version")
            val rev = System.getProperty("prog.revision")
            println("Actris verifier v" + ver + " (" + rev + ")")
          }
          else {
            println("Actris verifier (development version)")
          }
          return None
        }
        case Param("boogie-print") => aPrintProgram = true
        case Param("boogie-path") => value match {
          case None    =>
            reportCommandLineError("parameter boogie-path takes an argument"); return None
          case Some(v) => aBoogiePath = v
        }
        case Param("boogie-timeout") => value match {
          case None =>
            reportCommandLineError("parameter boogie-timeout takes an integer argument"); return None
          case Some(v) =>
            try aBoogieTimeout = v.toInt
            catch {
              case e: NumberFormatException =>
                reportCommandLineError("parameter boogie-timeout takes an integer as argument.")
                return None
            }
        }
        case Param("no-typecheck")     => aDoTypecheck = false
        case Param("no-infer")         => aDoInfer = false
        case Param("no-translate")     => aDoTranslate = false
        case Param("no-verify")        => aDoVerify = false
        case Param("no-assume-gen-invs") => aAssumeInvs = false
        case Param("timings") => {
          value match {
            case Some(v) =>
              try {
                aTiming = v.toInt
              } catch {
                case e: NumberFormatException =>
                  reportCommandLineError("parameter timing takes an integer as argument.")
                  return None
              }
            case None =>
              reportCommandLineError("parameter timing takes an integer as argument.")
              return None
          }
        }
        case Param("infer-modules") => {
          value match {
            case Some(v) => {
              val modules = Inferencer.Modules
              val valList = v.split(",")
              for (m <- valList) {
                if (!(modules contains m)) reportCommandLineError("no inference module named " + m)
              }
              aInferModules = valList.toList
            }
            case None => 
              reportCommandLineError("parameter " + param + " takes a comma-separated list as parameter")
          }
        }
        case Param("only-mathematical-ints") => aSizedIntsAsBitVectors = false
        case Param("smoke-test")            => aSmokeTest = true
        case Param("replace-maps")          => aReplaceMaps = true
        case Param("to-verify") => {
          value match {
            case Some(list) => {
              aToVerify = list.split(",").toList
            }
            case None =>
              reportCommandLineError("parameter to-verify takes a comma-separated list of components to verify.")
              return None
          }
        }
        case Param("contracts-to-verify") => {
          value match {
            case Some(list) => {
              val strings = list.split(",").toList
              for (s <- strings) {
                val componentName = s.split("\\.")
                if (componentName.size != 2) {
                  reportCommandLineError(
                      "parameter contracts-to-verify takes contracts in the format <Component>.<Contract>")
                  return None
                }
                else {
                  aContractsToVerify = aContractsToVerify :+ (componentName(0), componentName(1))
                }
              }
            }
            case None =>
              reportCommandLineError(
                  "parameter contracts-to-verify takes a comma-separated list of components to verify.")
              return None
          }
        }
        case Param("print-invariant-stats") => aPrintInvariantStats = true
        case Param("spin-path") => {
          value match {
            case Some(s) => aSpinPath = s
            case None => reportCommandLineError("parameter spin-path takes a string as argument")
          }
        }
        case Param("schedule") => {
          value match {
            case s@Some(_) => {
              //aDoInfer = false // Invariant inference is turned of for scheduling mode
              aSchedule = s
            }
            case None => 
              reportCommandLineError(
                  "parameter 'schedule' takes a string identifying the top network as argument")
          }
        }
        case Param("merge-actions") => aMergeActions = true
        case Param("no-merge-actions") => aMergeActions = false
        case Param("promela-print") => aPromelaPrint = true
        case Param("promela-chan-size") => {
          value match {
            case Some(sz) => {
              try {
                aPromelaChanSize = sz.toInt
              } catch {
                case e: NumberFormatException =>
                  reportCommandLineError("parameter promela-chan-size takes an integer as argument.")
              }
            }
            case None => reportCommandLineError("parameter promela-chan-size takes an integer as argument.")
          }
        }
        case Param("schedule-simulate") => aScheduleSimulate = true
        case Param("schedule-weights") => {
          val errMsg = 
            "parameter schedule-weights takes a comma-separated where each element is of " + 
            "format W=x, wherw W is an identifier and x is an integer"

          value match {
            case Some(list) => {
              try {
                val elems = list.split(",").toList
                for (e <- elems) {
                  val v = e.split("=")
                  val name = v(0)
                  val value = v(1).toInt
                  aScheduleWeights += (name -> value)
                }
              } catch {
                case e: Exception =>
                  reportCommandLineError(errMsg)
              }
              
            }
            case None =>
              reportCommandLineError(errMsg)
              return None
          }
        }
        case Param("schedule-xml") => {
          value match {
            case Some(fp) => {
              val file = new File(fp)
              if (!file.exists) {
                reportCommandLineError("schedule file " + file.getName + " could not be found");
                return None
              }
              aScheduleXML = Some(file)
            }
            case None => {
              reportCommandLineError("parameter schedule-xml takes a file path as argument");
            }
          }
        }
        case Param("no-schedule-abstraction") => {
          aScheduleAbstraction = false
        }
        case Param("print-xml-desc") => {
          aPrintXMLDescription = true
        }
        case Param("output-dir") => {
          value match {
            case Some(path) => {
              aOutputDir = new File(path)
            }
            case None => reportCommandLineError("parameter output-dir")
          }
          
        }   
        case Param(x) =>
          reportCommandLineError("unknown command line parameter " + x)
          return None
        case _ => inputs += param
      }
    }

    if (inputs.isEmpty) reportCommandLineError("No input file(s) provided.", help);
    else {
      if (inputs.size == 1) {
        aBplFile = inputs(0) + ".bpl"
      }
      else {
        aBplFile = "output/output.bpl"
      }
    }

    // check that input files exist
    var aFiles = for (input <- inputs.toList) yield {
      val file = new File(input)
      if (!file.exists) {
        reportCommandLineError("input file " + file.getName() + " could not be found", help);
        return None
      }
      file
    }
    
    Some(new CommandLineParameters {
      val BoogiePath = aBoogiePath
      val Files = aFiles
      val BoogieArgs = aBoogieArgs
      val PrintProgram = aPrintProgram
      val DoTypecheck = aDoTypecheck
      val DoInfer = aDoInfer
      val DoTranslate = aDoTranslate
      val DoVerify = aDoVerify
      val NoBplFile = aNoBplFile
      val BplFile = aBplFile
      val Timing = aTiming
      val InferModules = aInferModules
      val AssumeGenInvs = aAssumeInvs
      val SmokeTest = aSmokeTest
      val ReplaceMaps = aReplaceMaps
      val BoogieTimeout = aBoogieTimeout
      val ComponentsToVerify = aToVerify
      val PrintInvariantStats = aPrintInvariantStats
      val SizedIntsAsBitvectors = aSizedIntsAsBitVectors
      val Schedule = aSchedule
      val PromelaPrint = aPromelaPrint
      val MergeActions = aMergeActions
      val ScheduleSimulate = aScheduleSimulate
      val PromelaChanSize = aPromelaChanSize
      val ScheduleWeights = aScheduleWeights
      val ScheduleXML = aScheduleXML
      val ScheduleAbstraction = aScheduleAbstraction
      val PrintXMLDescription = aPrintXMLDescription
      val ContractsToVerify = aContractsToVerify
      val SpinPath = aSpinPath
      val OutputDir = aOutputDir
    })
    
  }

  def parsePrograms(params: CommandLineParameters): Option[List[TopDecl]] = {
    val files = params.Files
    val printProgram = params.PrintProgram

    // parse programs
    val parser = new Parser(params)
    val parseResults = if (files.isEmpty) {
      //reportCommandLineError("No input file(s) provided.", params.help)
      Nil
    } else for (file <- files) yield {
      parser.parseFile(file)
    }

    // report errors and merge declarations
    var parseErrors = false;
    val program: List[TopDecl] = parseResults.map(result => result match {
      case e: parser.NoSuccess =>
        parseErrors = true;
        println("Error: " + e);
        Nil
      case parser.Success(prog, _) =>
        prog
    }).flatten;
    if (parseErrors) None else Some(program)
  }

  def main(args: Array[String]) {
    // Parse command line arguments
    var configArgs: Array[String] = Array.empty 
    try {
      configArgs = Source.fromFile("actris_args").getLines.toArray
    } 
    catch {
      case e: FileNotFoundException =>
      case e: IOException => 
    }
    val allArgs = configArgs ++ args
    val params = parseCommandLine(allArgs) match {
      case Some(p) => p
      case None    => return //invalid arguments, help has been displayed
    }
    verify(params)
  }
  
  def verify(params: CommandLineParameters) {
    var timings = scala.collection.immutable.ListMap[Step.Value, Long]()
    for (step <- Step.values) timings += (step -> 0)
    var startTime = System.nanoTime
    var tmpTime = startTime

    var program = parsePrograms(params) match {
      case Some(p) => p
      case None    => return //illegal program, errors have already been displayed
    }
    
    timings += (Step.Parse -> (System.nanoTime - tmpTime))
    tmpTime = System.nanoTime

    // Create a pipeline of preprocessors
    val preprocessor = 
      ImplicitNwInvariantHandler | 
      InitActionNormaliser | 
      ActionScheduleProcessor | 
      ProcedureExpander | 
      EnumLiteralToBvHandler 
    program = preprocessor.process(program)
    //println(new ASTPrinter().print(program))
    
    
    if (program.isEmpty) return // Error message has already been displayed
    if (!params.DoTypecheck) return
    
    
    var typeCtx = Resolver.resolve(program,params) match {
      case Resolver.Errors(msgs) =>
        msgs foreach { case (pos, msg) => reportError(pos, msg) }; return
      case Resolver.Success(rootCtx) =>
        Some(rootCtx)
    }
    
    program = (RangeExpander | ForEachExpander | OutputPatternNormaliser).process(program)

    typeCtx = Resolver.resolve(program,params) match {
      case Resolver.Errors(msgs) =>
        msgs foreach { case (pos, msg) => reportError(pos, msg) }; return
      case Resolver.Success(rootCtx) =>
        Some(rootCtx)
    }
    
    timings += (Step.Resolve -> (System.nanoTime - tmpTime))
    tmpTime = System.nanoTime
    
    val componentsToVerify = {
      if (params.ComponentsToVerify.isEmpty) {
        program
      }
      else {
        program.filter { 
          x => params.ComponentsToVerify.contains(x.id) || x.isUnit || x.isType 
        }
      }
    }.map { x => x.id -> x }
    
    if (params.DoInfer) {
      Inferencer.infer(program, typeCtx.get, params.InferModules, params.AssumeGenInvs) match {
        case Inferencer.Errors(msgs) =>
          msgs foreach { case (pos, msg) => reportError(pos, msg) }; return
        case Inferencer.Success() =>
      }
    }
    
    timings += (Step.Infer -> (System.nanoTime - tmpTime))
    tmpTime = System.nanoTime
    
    if (params.PrintXMLDescription) {
      println(util.XMLPrinter.printPretty(program))
      return
    }
    
    if (params.Schedule.isDefined) {
      // Scheduling (and possibly verification)
      
      val schedulingBackend = params.ScheduleXML match {
        case Some(file) => 
          new SchedulingBackend(new XMLScheduler(file),params)
        case None =>
          new SchedulingBackend(new PromelaBackend(params),params)
      }
      
      val schedulingProgramCtx: ProgramContext = 
        new BasicProgramContext(program,typeCtx.get)
      val verificationProgramCtx: ProgramContext = 
        new BasicProgramContext(componentsToVerify.unzip._2,typeCtx.get)
      
      val promelaBackend = new PromelaBackend(params)
      val (ba,scheduleCtxs) = schedulingBackend.invoke(schedulingProgramCtx) match {
        case schedule.Success(ba,scheduleCtxs) => (ba,scheduleCtxs)
        case schedule.Failure(errs) => {
          errs.map { case (pos,msg) => reportError(pos, msg) }
          return
        }
      }
      
      timings += (Step.Scheduling -> (System.nanoTime - tmpTime))
      tmpTime = System.nanoTime
      
      if (params.DoVerify) {
        
        val actionsVerifier = new BoogieVerifier(params,true)
        println("\nVerifying actor actions... ")
        actionsVerifier.invoke(verificationProgramCtx)
        
        val scheduleVerifier = new BoogieScheduleVerifier(params)
        
        val componentMap = componentsToVerify.toMap
        for (s <- scheduleCtxs) {
          if (componentMap.contains(s.entity.id)) {
            println("Verifying " + s.schedules.size + " schedule(s) for " + s.entity.fullName + "...")
            scheduleVerifier.invoke(s)
          }
        }
        
        timings += (Step.Verification -> (System.nanoTime - tmpTime))
        tmpTime = System.nanoTime
      }
      
    }
    else {
      // Verification
      
      if (!params.DoTranslate) return
      
      val verifier = new BoogieVerifier(params,false)
      
      if (!params.DoVerify) return
      val programContext = new BasicProgramContext(componentsToVerify.unzip._2,typeCtx.get)
      verifier.invoke(programContext)
  
      timings += (Step.Verification -> (System.nanoTime - tmpTime))
      tmpTime = System.nanoTime
    }
    
    val totalTime = System.nanoTime - startTime

    if (0 < params.Timing)
      println("Execution finished in %1.3f seconds" format (totalTime / 1000000000.0))
    if (1 < params.Timing) {
      for (s <- Step.values) {
        println(s + ": %1.3fs".format(timings(s) / 1000000000.0))
      }
    }

    if (params.PrintInvariantStats) {
      println("Number of invariants: ")
      var totUserProvided, totGenerated = 0
      componentsToVerify.unzip._2 map {
        c =>
          c match {
            case a: DFActor =>
              val generated = 
                (a.contractInvariants.count { inv => inv.generated }) + 
                (a.actionInvariants.count { inv => inv.generated })
              val userProvided = 
                (a.contractInvariants.size + a.actionInvariants.size) - generated
              totUserProvided += userProvided
              totGenerated += generated
              println(a.fullName + " U:" + userProvided + " G:" + generated)
            case _ =>
          }
      }
      println("Total U:" + totUserProvided + " G:" + totGenerated)
    }
  }

  def writeFile(filename: String, text: String) {
    val writer = new FileWriter(new File(filename));
    writer.write(text)
    writer.flush()
    writer.close()
  }

  def reportCommandLineError(msg: String) {
    reportCommandLineError(msg, None)
  }

  def reportCommandLineError(msg: String, help: String) {
    reportCommandLineError(msg, Some(help))
  }

  def reportCommandLineError(msg: String, help: Option[String]) {
    println("Error: " + msg + (help match {
      case Some(h) => " Usage: " + h
      case None    => ""
    }))
  }

  def reportError(pos: Position, msg: String) = {
    println("Error " + pos + ": " + msg)
  }

}
package fi.abo.it.actortool

import java.io.File
import collection.mutable.ListBuffer
import java.io.BufferedReader
import java.io.InputStreamReader
import java.io.File
import java.io.FileWriter
import scala.util.parsing.input.Position
import fi.abo.it.actortool.boogie.Boogie
import fi.abo.it.actortool.boogie.BoogieVerifier
import fi.abo.it.actortool.orcc.OrccGuardTranslator
import fi.abo.it.actortool.promela.PromelaRunner
import fi.abo.it.actortool.util.ASTPrinter


trait Translator[U] {
  def translateProgram(decls: List[TopDecl], typeCtx: Resolver.Context): U
}

abstract class Verifier[U, T] extends Translator[U] {
  def verify(input: U): T
  def translateAndVerify(decls: List[TopDecl], typeCtx: Resolver.Context): T = verify(translateProgram(decls, typeCtx))
}

object ActorTool {

  val DEBUG = true
  
  class TranslationException(val pos: Position, val msg: String) extends Exception(msg) {
    //def this(pos: Position, msg: String) = this(pos, msg)
  }

  final val Param = "(?:[-/])(.*)".r

  object Step extends Enumeration {
    type Step = Value
    val Parse = Value("Parse")
    val Resolve = Value("Typecheck")
    val Infer = Value("Inference")
    val Translation = Value("Translation")
    val Verification = Value("Verification")
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
    val ScheduleFile: Option[File]
    val Promela: Option[String]
    final lazy val help = "actortool [option] <filename>+\n"
  }

  //val actorSystem = ActorSystem("actortool")

  def parseCommandLine(args: Array[String]): Option[CommandLineParameters] = {
    var aBoogiePath = if (DEBUG) "./boogie" else "boogie"
    var aBoogieArgs = ""
    var aPrintProgram = if (DEBUG) false else false
    var aNoBplFile = if (DEBUG) false else true
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
    var aBoogieTimeout = 300
    var aAssumeInvs = if (DEBUG) false else true
    var aPrintInvariantStats = false
    var aToVerify: List[String] = List.empty
    var aSizedIntsAsBitVectors = true
    var aScheduleFile: Option[File] = None
    var aPromela: Option[String] = None

    lazy val help = {
      "actortool [option] <filename>+\n"
    }

    val inputs = new ListBuffer[String]()

    for (a <- args) {
      val paramval = a.split(":", 2)
      val (param, value) = (if (paramval.size == 1) (paramval(0), None) else (paramval(0), Some(paramval(1))));
      param match {
        case Param("print") => aPrintProgram = true
        case Param("boogiePath") => value match {
          case None    =>
            reportCommandLineError("parameter boogiePath takes an argument"); return None
          case Some(v) => aBoogiePath = v
        }
        case Param("boogieTimeout") => value match {
          case None =>
            reportCommandLineError("parameter boogieTimeout takes an integer argument"); return None
          case Some(v) =>
            try aBoogieTimeout = v.toInt
            catch {
              case e: NumberFormatException =>
                reportCommandLineError("parameter boogieTimeout takes an integer as argument.")
                return None
            }
        }
        case Param("noTypecheck")     => aDoTypecheck = false
        case Param("noInfer")         => aDoInfer = false
        case Param("noTranslate")     => aDoTranslate = false
        case Param("noVerify")        => aDoVerify = false
        case Param("bvMode")          => reportCommandLineError("parameter bvMode is obsolete.")
        case Param("noAssumeGenInvs") => aAssumeInvs = false
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
        case Param("inferModules") => {
          value match {
            case Some(v) => {
              val modules = Inferencer.Modules
              val valList = v.split(",")
              for (m <- valList) {
                if (!(modules contains m)) reportCommandLineError("no inference module named " + m)
              }
              aInferModules = valList.toList
            }
            case None => reportCommandLineError("parameter " + param + " takes a comma-separated list as parameter")
          }
        }
        case Param("onlyMathematicalInts") => aSizedIntsAsBitVectors = false
        case Param("smokeTest")            => aSmokeTest = true
        case Param("replaceMaps")          => aReplaceMaps = true
        case Param("toVerify") => {
          value match {
            case Some(list) => {
              aToVerify = list.split(",").toList
            }
            case None =>
              reportCommandLineError("parameter toVerify takes a comma-separated list of components to verify.")
              return None
          }
        }
        case Param("printInvariantStats") => aPrintInvariantStats = true
        case Param("promela") => {
          value match {
            case s@Some(nwId) => aPromela = s
            case None => reportCommandLineError("parameter 'promela' takes a string as argument")
          }
        }
        case Param("scheduleFile") => {
          value match {
            case Some(path) => {
              val file = new File(path)
              if (!file.exists) {
                reportCommandLineError("schedule file " + file.getName + " could not be found", help);
                return None
              }
              aScheduleFile = Some(file)
            }
            case None => {
              reportCommandLineError("parameter scheduleFile takes a file path as argument")
              return None
            }
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
        aBplFile = "output.bpl"
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
      val ScheduleFile = aScheduleFile
      val Promela = aPromela
    })
  }

  def parsePrograms(params: CommandLineParameters): Option[List[TopDecl]] = {
    val files = params.Files
    val printProgram = params.PrintProgram

    // parse programs
    val parser = new Parser(params.SizedIntsAsBitvectors)
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
    val params = parseCommandLine(args) match {
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

    // Create a pipeline of preprocessors
    val preprocessor = InitActionNormaliser | ActionScheduleProcessor /*| NetworkFlattener*/
    program = preprocessor.process(program)
    //println(new ASTPrinter().print(program))
    
    timings += (Step.Parse -> (System.nanoTime - tmpTime))
    tmpTime = System.nanoTime
    if (program.isEmpty) return // Error message has already been displayed
    if (!params.DoTypecheck) return

    val typeCtx = Resolver.resolve(program) match {
      case Resolver.Errors(msgs) =>
        msgs foreach { case (pos, msg) => reportError(pos, msg) }; return
      case Resolver.Success(rootCtx) =>
        Some(rootCtx)
    }

    timings += (Step.Resolve -> (System.nanoTime - tmpTime))
    tmpTime = System.nanoTime
    
    if (params.Promela.isDefined) {
      val promelaTranslator = new PromelaRunner(params)
      promelaTranslator.translateAndVerify(program, typeCtx.get)
      return
    }

    if (params.DoInfer) {
      Inferencer.infer(program, typeCtx.get, params.InferModules, params.AssumeGenInvs) match {
        case Inferencer.Errors(msgs) =>
          msgs foreach { case (pos, msg) => reportError(pos, msg) }; return
        case Inferencer.Success() =>
      }
    }

    timings += (Step.Infer -> (System.nanoTime - tmpTime))
    tmpTime = System.nanoTime

    if (!params.DoTranslate) return

    //val translator = new Translator(params.FixedBaseLength, params.FTMode, params.BVMode);

    val verifier = new BoogieVerifier(params)

    val componentsToVerify =
      if (params.ComponentsToVerify.isEmpty) program
      else program.filter { x => params.ComponentsToVerify.contains(x.id) || x.isUnit || x.isType }

    val bplProg =
      try {
        verifier.translateProgram(componentsToVerify, typeCtx.get);
      } catch {
        case ex: TranslationException =>
          reportError(ex.pos, ex.msg)
          return
      }

    timings += (Step.Translation -> (System.nanoTime - tmpTime))
    tmpTime = System.nanoTime

    if (!params.DoVerify) return

    verifier.verify(bplProg)

    timings += (Step.Verification -> (System.nanoTime - tmpTime))
    tmpTime = System.nanoTime
    
    if (params.ScheduleFile.isDefined) {
      val orccTranslator = new OrccGuardTranslator()
      orccTranslator.translateGuards(program,params.ScheduleFile.get)
    }

    val totalTime = System.nanoTime - startTime

    if (0 < params.Timing)
      println("Verification finished in %1.3f seconds" format (totalTime / 1000000000.0))
    if (1 < params.Timing) {
      for (s <- Step.values) {
        println(s + ": %1.3fs".format(timings(s) / 1000000000.0))
      }
    }

    if (params.PrintInvariantStats) {
      println("Number of invariants: ")
      var totUserProvided, totGenerated = 0
      componentsToVerify map {
        c =>
          c match {
            case ba: BasicActor =>
              val generated = (ba.actorInvariants.count { inv => inv.generated })
              val userProvided = ba.actorInvariants.size - generated
              totUserProvided += userProvided
              totGenerated += generated
              println(ba.fullName + " U:" + userProvided + " G:" + generated)
            case nw: Network =>
              val generated = (nw.actorInvariants.count { inv => inv.generated }) + (nw.channelInvariants.count { inv => inv.generated })
              val userProvided = (nw.actorInvariants.size + nw.channelInvariants.size) - generated
              totUserProvided += userProvided
              totGenerated += generated
              println(nw.fullName + " U:" + userProvided + " G:" + generated)
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
      case None    =>
    }))
  }

  def reportError(pos: Position, msg: String) = {
    println("Error " + pos + ": " + msg)
  }

}
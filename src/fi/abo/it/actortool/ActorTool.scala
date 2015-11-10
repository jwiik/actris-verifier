package fi.abo.it.actortool

import java.io.File
import collection.mutable.ListBuffer
import java.io.BufferedReader
import java.io.InputStreamReader
import java.io.File
import java.io.FileWriter

import scala.util.parsing.input.Position

object ActorTool {
  
  final val Param = "(?:[-/])(.*)".r
  
  object Step extends Enumeration {
    type Step = Value
    val Parse = Value("Parse")
    val Resolve = Value("Analysis")
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
    final lazy val help = "Usage: actortool [option] <filename>+\n"
  }
  
  def parseCommandLine(args: Array[String]): Option[CommandLineParameters] = {

    var aBoogiePath = "./boogie"
    var aBoogieArgs = ""
    var aPrintProgram = true
    var aNoBplFile = false
    var aBplFile = "out.bpl"
    var aDoTypecheck = true
    var aDoInfer = true
    var aDoTranslate = true
    var aDoVerify = true
    var aTiming = 2
    
    
    lazy val help = {
      "actortool [option] <filename>+\n"
    }
    
    val inputs = new ListBuffer[String]()

    for (a <- args) {
      val paramval = a.split(":", 2)
      val (param,value) = (if (paramval.size == 1) (paramval(0),None) else (paramval(0),Some(paramval(1))));
      param match {
        case Param("print") => aPrintProgram = true
        case Param("boogiePath") => value match {
          case None => reportCommandLineError("parameter boogiePath takes an argument"); return None
          case Some(v) => aBoogiePath = v
        }
        case Param("noTypecheck") => aDoTypecheck = false
        case Param("noInfer") => aDoInfer = false
        case Param("noTranslate") => aDoTranslate = false
        case Param("noVerify") => aDoVerify = false
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
        case Param(x,_) => 
          reportCommandLineError("unknown command line parameter " + x)
          return None
        case _ => inputs += param
      }
    }
    
    if (inputs.isEmpty) reportCommandLineError("No input file(s) provided.", help);
    else {
      if (inputs(0).endsWith(".actor")) aBplFile = inputs(0).substring(0,inputs(0).length-6)+".bpl"
      else aBplFile = inputs(0)+".bpl"
    }
    
    // check that input files exist
    var aFiles = for (input <- inputs.toList) yield {
    	val file = new File(input)
    	if(! file.exists) {
    		reportCommandLineError("input file " + file.getName() + " could not be found", help);
    		return None
    	}
    	file
    }
    
    Some(new CommandLineParameters{
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
    })
  }
  
  def parsePrograms(params: CommandLineParameters): Option[List[TopDecl]] = {
    val files = params.Files
    val printProgram = params.PrintProgram
    
    // parse programs
    val parser = new Parser
    val parseResults = if (files.isEmpty) {
      reportCommandLineError("No input file(s) provided.", params.help)
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
      case None => return //invalid arguments, help has been displayed
    }
    verify(params)
  }
  
	def verify(params: CommandLineParameters) {
    var timings = scala.collection.immutable.ListMap[Step.Value,Long]()
    for (step <- Step.values) timings += (step -> 0)
    var startTime = System.nanoTime
    var tmpTime = startTime
    
//    timings += (Step.Init -> (System.nanoTime - tmpTime))
//    tmpTime = System.nanoTime
    
    val program = parsePrograms(params) match {
      case Some(p) => p
      case None => return //illegal program, errors have already been displayed
    }
    
    timings += (Step.Parse -> (System.nanoTime - tmpTime))
    tmpTime = System.nanoTime
    
    if (program.isEmpty) return // Error message has already been displayed
    if (!params.DoTypecheck) return
    
    val typeCheck = Resolver.resolve(program) match {
      case Resolver.Errors(msgs) =>
        msgs foreach { case (pos,msg) => reportError(pos, msg) }; return
      case Resolver.Success() =>
        true
    }
    
    timings += (Step.Resolve -> (System.nanoTime - tmpTime))
    tmpTime = System.nanoTime
    
    if (params.DoInfer) Inferencer.infer(program)
    
    timings += (Step.Infer -> (System.nanoTime - tmpTime))
    tmpTime = System.nanoTime
    
    if (!params.DoTranslate) return
    
    val translator = new Translator();
    val bplProg: List[Boogie.Decl] = translator.translateProgram(program);
    
    timings += (Step.Translation -> (System.nanoTime - tmpTime))
    tmpTime = System.nanoTime
    
    if (!params.DoVerify) return
    
		val boogiePath = params.BoogiePath
		val boogieArgs = params.BoogieArgs
		
    val bplText = BoogiePrelude.get + (bplProg map Boogie.Print).foldLeft(""){ (a, b) => a + b };
    val bplFilename = if (params.NoBplFile) "stdin.bpl" else params.BplFile
    if (params.PrintProgram) println(bplText)
    if (!params.NoBplFile) writeFile(bplFilename, bplText);
    
    val boogie = Runtime.getRuntime.exec(boogiePath + " /errorTrace:0 " + boogieArgs + " stdin.bpl")
    
    val output = boogie.getOutputStream()
    output.write(bplText.getBytes)
    output.close
    
    // terminate boogie if interrupted
    Runtime.getRuntime.addShutdownHook(new Thread(new Runnable() {
      def run {
        boogie.destroy
      }
    }))
    // the process blocks until we exhaust input and error streams 
    // (this extra thread reads all from error stream, and buffers it)
    val errorReadingThread = new Thread(new Runnable() {
      def run {
        val err = new BufferedReader(new InputStreamReader(boogie.getErrorStream))
        var line = err.readLine;
        while(line!=null) {Console.err.println(line); Console.err.flush; line = err.readLine}
      }
    });
    errorReadingThread.start()
    val input = new BufferedReader(new InputStreamReader(boogie.getInputStream))
    var line = input.readLine()
    var previousLine = null: String
    val boogieOutput: ListBuffer[String] = new ListBuffer()
    while (line!=null){
      if (previousLine != null) println
      Console.out.print(line)
      Console.out.flush
      boogieOutput += line
      previousLine = line
      line = input.readLine()
    }
    boogie.waitFor
    input.close
    Console.out.println
    
    timings += (Step.Verification -> (System.nanoTime - tmpTime))
    tmpTime = System.nanoTime
    
    val totalTime = System.nanoTime - startTime
    
    if (0 < params.Timing)
      Console.out.println("Verification finished in %1.3f seconds" format (totalTime/1000000000.0))
    if (1 < params.Timing) {
      for (s <- Step.values) {
        Console.out.println(s + ": %1.3fs" format (timings(s)/1000000000.0))
      }
    }
    
	}
  
  def writeFile(filename: String, text: String) {
    val writer = new FileWriter(new File(filename));
    writer.write(text)
    writer.flush()
    writer.close()
  }
  
  def reportCommandLineError(msg: String) {
    reportCommandLineError(msg,None)
  }
  
  def reportCommandLineError(msg: String, help: String) {
    reportCommandLineError(msg,Some(help))
  }
  
  def reportCommandLineError(msg: String, help: Option[String]) {
    println("Error: " + msg + (help match {
      case Some(h) =>" Usage: " + h
      case None =>
    }))
  }
  
  def reportError(pos: Position, msg: String) = {
    println("Error " + pos + ": " + msg)
  }

}
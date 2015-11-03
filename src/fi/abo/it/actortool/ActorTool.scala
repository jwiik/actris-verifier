package fi.abo.it.actortool

import java.io.File
import collection.mutable.ListBuffer
import java.io.BufferedReader
import java.io.InputStreamReader
import java.io.File
import java.io.FileWriter

import scala.util.parsing.input.Position

object ActorTool {
  
  final val Param = "(?:[-/])(.*)(?::)?(.*)".r

    
  /**
   * Holds all command line arguments
   */
  sealed abstract class CommandLineParameters {
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
    final lazy val help = "Usage: actortool [option] <filename>+\n"
  }
  
  def parseCommandLine(args: Array[String]): Option[CommandLineParameters] = {
    var aBoogiePath = "./boogie"
    var aBoogieArgs = ""
    var aPrintProgram = true
    var aNoBplFile = true
    var aBplFile = "out.bpl"
    var aDoTypecheck = true
    var aDoInfer = true
    var aDoTranslate = true
    var aDoVerify = true
    
    val inputs = new ListBuffer[String]()
    
    lazy val help = {
      "Usage: actortool [option] <filename>+\n"
    }
    
    for (a <- args) {
      a match {
        case Param("print",_) => aPrintProgram = true
        case Param("boogiePath",v) => aBoogiePath = v
        case Param("noTypecheck",_) => aDoTypecheck = false
        case Param("noInfer",_) => aDoInfer = false
        case Param("noTranslate",_) => aDoTranslate = false
        case Param("noVerify",_) => aDoVerify = false
        case _ => inputs += a
      }
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
    })
  }
  
  def parsePrograms(params: CommandLineParameters): Option[List[Actor]] = {
    val files = params.Files
    val printProgram = params.PrintProgram
    
    // parse programs
    val parser = new Parser
    val parseResults = if (files.isEmpty) {
      println("No input file provided. Use 'actortool -help' for a list of all available command line options.")
      Nil
    } else for (file <- files) yield {
      parser.parseFile(file)
    }
    
    // report errors and merge declarations
    var parseErrors = false;
    val program: List[Actor] = parseResults.map(result => result match {
     case e: parser.NoSuccess =>
       parseErrors = true;
       println("Error: " + e);
       Nil
     case parser.Success(prog, _) =>
       prog
    }).flatten;
    if (parseErrors) None else Some(program)
  }
  
	def main(args: Array[String]): Unit = {
    // Parse command line arguments
    val params = parseCommandLine(args) match {
      case Some(p) => p
      case None => return //invalid arguments, help has been displayed
    }
    
    val program = parsePrograms(params) match {
      case Some(p) => p
      case None => return //illegal program, errors have already been displayed
    }
    
    if (program.isEmpty) return // Error message has already been displayed
    
    if (!params.DoTypecheck) return
    
    val typeCheck = Resolver.resolve(program) match {
      case Resolver.Errors(msgs) =>
        msgs foreach { case (pos,msg) => reportError(pos, msg) }; return
      case Resolver.Success() =>
        true
    }
    
    if (params.DoInfer) Inferencer.infer(program)
    
    if (!params.DoTranslate) return
    
    val translator = new Translator();
    val bplProg: List[Boogie.Decl] = translator.translateProgram(program);
    
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
    var previous_line = null: String
    val boogieOutput: ListBuffer[String] = new ListBuffer()
    while (line!=null){
      if (previous_line != null) println
      Console.out.print(line)
      Console.out.flush
      boogieOutput += line
      previous_line = line
      line = input.readLine()
    }
    boogie.waitFor
    input.close
	}
  
  def writeFile(filename: String, text: String) {
    val writer = new FileWriter(new File(filename));
    writer.write(text)
    writer.flush()
    writer.close()
  }
  
  def reportCommandLineError(msg: String, help: String) = {
    println("Error: " + msg +" Usage: " + help)
  }
  
  def reportError(pos: Position, msg: String) = {
    println("Error " + pos + ": " + msg)
  }

}
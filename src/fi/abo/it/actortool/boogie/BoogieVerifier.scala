package fi.abo.it.actortool.boogie

import java.io.File
import collection.mutable.ListBuffer
import java.io.BufferedReader
import java.io.InputStreamReader
import java.io.File
import java.io.FileWriter
import java.util.Timer
import java.util.TimerTask
import fi.abo.it.actortool.ActorTool.Verifier
import fi.abo.it.actortool._
import fi.abo.it.actortool.ActorTool.CommandLineParameters

class BoogieVerifier(val params: CommandLineParameters) extends Verifier[List[Boogie.Decl], Unit] {
  
  def translateProgram(decls: List[TopDecl]): List[Boogie.Decl] = {
    val translator = new Translator(params.FixedBaseLength, params.FTMode, params.SmokeTest, false, params.BVMode)
    translator.translateProgram(decls)
  }
  
  def verify(bplProg: List[Boogie.Decl]): Unit = {
    val boogiePath = params.BoogiePath
		val boogieArgs = params.BoogieArgs
		if (params.BVMode) BoogiePrelude.addComponent(BitwisePL)
    val bplText = BoogiePrelude.get(params.BVMode) + (bplProg map Boogie.Print).foldLeft(""){ (a, b) => a + b };
    val bplFilename = if (params.NoBplFile) "stdin.bpl" else params.BplFile
    if (params.PrintProgram) println(bplText)
    if (!params.NoBplFile) writeFile(bplFilename, bplText);
    
    val destroyTimer = new Timer
    
    val boogie = Runtime.getRuntime.exec(boogiePath + " /errorTrace:0 " + boogieArgs + " stdin.bpl")
    val output = boogie.getOutputStream()
    output.write(bplText.getBytes)
    output.close
    
    destroyTimer.schedule(new TimerTask() {
      def run {
        boogie.destroy
        println("\nBoogie backend timed out during verification")
      }
    }, params.BoogieTimeout*1000)
    
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
    while (line != null) {
      if (!(line.startsWith("[smoke]"))) {
        if (previousLine != null) println
        Console.out.print(line)
        Console.out.flush
      }
      boogieOutput += line
      previousLine = line
      line = input.readLine()
    }
    boogie.waitFor
    input.close
    
    if (params.SmokeTest) {
      println
      for (d <- bplProg) {
        d match {
          case p: Boogie.Proc => {
            var found = false
            for (line <- boogieOutput) {
              if (line.startsWith("[smoke]")) {
                if (line.substring(7, line.indexOf(" ")) == p.id) found = true
              }
            }
            if (!found) {
              Console.out.println("Smoke test failed for Boogie procedure '" + p.id + "'")
            }
          }
          case _ =>
        }
      }
      println("Smoke test finished")
    }
    
    destroyTimer.cancel
    
    Console.out.println
  }
  
  def writeFile(filename: String, text: String) {
    val writer = new FileWriter(new File(filename));
    writer.write(text)
    writer.flush()
    writer.close()
  }
  
}
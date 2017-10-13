package fi.abo.it.actortool.boogie

import java.io.File
import collection.mutable.ListBuffer
import java.io.BufferedReader
import java.io.InputStreamReader
import java.io.File
import java.io.FileWriter
import java.util.Timer
import java.util.TimerTask
import fi.abo.it.actortool.ActorTool.CommandLineParameters

object BoogieRunner {

  class BoogieResult(val verified: Int, val errors: Int, val messages: Seq[String]) {
    def success = (errors == 0)
  }
  
  val summaryLine = """Boogie program verifier finished with ([\d]*) verified, ([\d]*) errors.*""".r
  val summaryLine2 = """Boogie.*""".r
  val smokeLine = """\[smoke\].*""".r
  
  def run(params: CommandLineParameters, bplProg: Seq[Boogie.Decl], fileName: String): BoogieResult = {
    val boogiePath = params.BoogiePath
		val boogieArgs = params.BoogieArgs
		//if (params.BVMode) BoogiePrelude.addComponent(BitwisePL)
    val bplText = BoogiePrelude.get + (bplProg map Boogie.Print).foldLeft(""){ (a, b) => a + b };
    
    val bplFilename = if (params.NoBplFile) "stdin.bpl" else fileName
    
    if (params.PrintProgram) {
      println(bplText)
    }
    
    if (!params.NoBplFile) {
      writeFile(bplFilename, bplText);
    }
    
    val destroyTimer = new Timer
    
    val boogie = Runtime.getRuntime.exec(boogiePath + " /nologo /noinfer /errorTrace:0 " + boogieArgs + " stdin.bpl")
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
    val smokeLines: ListBuffer[String] = new ListBuffer()
    val errorLines: ListBuffer[String] = new ListBuffer()
    var verified, errors: Int = -1
    while (line != null) {
      //if (previousLine != null) println
      line match {
        case summaryLine(ver,err) => {
          verified = ver.toInt
          errors = err.toInt
//          val formattedLine = "Verified: " + verified + " Errors: " + errors
//          boogieOutput += formattedLine
//          Console.out.print(formattedLine)
//          Console.out.flush
        }
        case smokeLine(_) => {
          smokeLines += line
        }
        case _ => {
          errorLines += line
          boogieOutput += line
          Console.out.println(line)
        }
      }
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
            for (line <- smokeLines) {
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
    
    //Console.out.println
    
    new BoogieResult(verified,errors,errorLines.toSeq)
  }
  
  def writeFile(filename: String, text: String) {
    val writer = new FileWriter(new File(filename));
    writer.write(text)
    writer.flush()
    writer.close()
  }
}
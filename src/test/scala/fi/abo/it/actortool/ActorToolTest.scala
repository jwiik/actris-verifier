package fi.abo.it.actortool

import org.scalatest.FunSuite
import org.scalatest.BeforeAndAfter
import java.io.File
import scala.sys.process._

class ActorToolTestSuite extends FunSuite {
  
  def createParams(filePath: String) =
    new ActorTool.CommandLineParameters{
      val BoogiePath = "./boogie"
      val Files = List(new File(filePath))
      val BoogieArgs = ""
      val PrintProgram = false
      val DoTypecheck = true
      val DoInfer = true
      val DoTranslate = true
      val DoVerify = true
      val NoBplFile = true
      val BplFile = "out.bpl"
      val Timing = 1
      val FixedBaseLength = 0
      val InferModules = List("default")
      val AssumeGenInvs = true
      val SmokeTest = false
      val ReplaceMaps = false
      val BoogieTimeout = 5
      val ComponentsToVerify = List.empty
    }
  
  
  test("Run example programs") {
    val folder = new File("tests")
    for (file <- folder.listFiles) {
      if (file.getName.endsWith(".actor")) {
        println("\n\n===============================")
        println("Running " + file.getName)
        ActorTool.verify(createParams(file.getAbsolutePath))
      }
    }
    
    // Try to cleanup possible non-terminated z3 instances
    try {
      for (s <- (Process("ps x") #| Process("grep -e z3.exe") #| Process("grep -v grep") lineStream)) {
        val pid = s.substring(0, s.indexOf(" "))
        Process("kill -9 " + pid)!
      }
    }
    catch {
      case e: RuntimeException =>
    }
  }
  
  
}
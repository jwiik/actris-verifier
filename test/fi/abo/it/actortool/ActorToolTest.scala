package fi.abo.it.actortool

import org.scalatest.FunSuite
import org.scalatest.BeforeAndAfter
import java.io.File
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class ActorToolTestSuite extends FunSuite {
  
  test("Schedule.actor") {
    val params = new ActorTool.CommandLineParameters{
        val BoogiePath = "./boogie"
        val Files = List(new File("tests/Schedule.actor"))
        val BoogieArgs = ""
        val PrintProgram = true
        val DoTypecheck = true
        val DoInfer = true
        val DoTranslate = true
        val DoVerify = true
        val NoBplFile = true
        val BplFile = "out.bpl"
        val Timing = 2
        val InferModules = List("default")
    }
    
    ActorTool.verify(params)
  }
  
  
}
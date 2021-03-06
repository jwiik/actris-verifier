package fi.abo.it.actortool

import org.scalatest._
import org.scalatest.BeforeAndAfter
import java.io.File
import scala.sys.process._

class ActorToolTestSuite extends FlatSpec with Matchers {
  val TestSet = List(
      "AddDelay.actor"
      )
  
  "All the networks" should "be verified without errors" in {
    for (path <- TestSet) {
      val file = new File("examples/"+path)
      println("\n\n===============================")
      println("Verifying " + file.getName)
      ActorTool.verify(createParams(file.getAbsolutePath))
    }
  }
  
  def createParams(filePath: String) =
    new ActorTool.CommandLineParameters{
      val BoogiePath = "boogie"
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
      val InferModules = List("default")
      val AssumeGenInvs = true
      val SmokeTest = false
      val ReplaceMaps = false
      val BoogieTimeout = 5
      val ComponentsToVerify = List.empty
      val PrintInvariantStats = false
      val SizedIntsAsBitvectors = true
      val Schedule = None
      val ScheduleSimulate = false
      val SpinPath = "spin"
      val PromelaPrint = false
      val MergeActions = false
      val PromelaChanSize = 100
      val ScheduleWeights = Map.empty[String,Int]
      val ScheduleXML = None
      val PrintXMLDescription = false
      val ContractsToVerify = List.empty
      val OutputDir = new File("actris-output")
      val ScheduleAbstraction = true
    } 
}
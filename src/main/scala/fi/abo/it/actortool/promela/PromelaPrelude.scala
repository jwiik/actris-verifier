package fi.abo.it.actortool.promela

import fi.abo.it.actortool._

object PromelaPrelude extends Prelude {
  override def defaultComponents = Set(MaskPrelude)
}
object PromelaPreludeOrder extends PreludeOrder {
  lazy val order = List(MaskPrelude)
}
abstract class PromelaPreludeComponent extends PreludeComponent(PromelaPreludeOrder)

object MaskPrelude extends PromelaPreludeComponent {
  override def text = "// Mask definitions\n" + ((1 to 31).map { i =>  generateMask(i) }).mkString("\n") + "\n"
  def generateMask(i: Int) = "#define MASK" + i.toString + "  " + ((scala.math.pow(2, i).toInt)-1).toString
}

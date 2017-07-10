package fi.abo.it.actortool.promela

import fi.abo.it.actortool._

object PromelaPrelude extends Prelude {
  override def defaultComponents = Set(MaskPrelude,InstrumentationPrelude)
}
object PromelaPreludeOrder extends PreludeOrder {
  lazy val order = List(MaskPrelude,InstrumentationPrelude)
}
abstract class PromelaPreludeComponent extends PreludeComponent(PromelaPreludeOrder)

object MaskPrelude extends PromelaPreludeComponent {
  override def text = "// Mask definitions\n" + ((1 to 31).map { i =>  generateMask(i) }).mkString("\n") + "\n"
  def generateMask(i: Int) = "#define MASK" + i.toString + "  " + ((scala.math.pow(2, i).toInt)-1).toString
}

object InstrumentationPrelude extends PromelaPreludeComponent {
  override def text = 
"""
#define best_cost c_expr { best() }
#define more_expensive c_expr { more_exp() }
int __INSTR_COST = 100000;
  int __INSTR_PREV_ACTOR = -1;
  int __INSTR_PREV_ACTION = -1;
  int __INSTR_ACC_BUFFER_SUM = 0;
  int __INSTR_NUM_FIRINGS = 0;
  int __INSTR_ACTOR_SWITCHES = 0;
  int __INSTR_ACTION_SWITCHES = 0;

"""
/*
int __INSTR_PREV_ACTOR = -1;
int __INSTR_PREV_ACTION = -1;
int __INSTR_ACC_BUFFER_SUM = 0;
int __INSTR_NUM_FIRINGS = 0;
int __INSTR_ACTOR_SWITCHES = 0;
int __INSTR_ACTION_SWITCHES = 0;
 */
}

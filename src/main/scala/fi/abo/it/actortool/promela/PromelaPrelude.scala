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
#define best_cost c_expr { best_c() }
#define more_expensive c_expr { more_exp() }
int __INSTR_COST = 100000;
int __INSTR_ACC_BUFFER_SUM = 0;

c_code {
  int __BEST_COST = 1000000;
  
  int best_c() {
    if (now.__INSTR_COST < __BEST_COST) {
      return 1;
    }
    else {
      return 0;
    }
  }
  
  int best() {
    if (now.__INSTR_COST < __BEST_COST) {
      __BEST_COST = now.__INSTR_COST;
      printf(">> New best: %d\n", __BEST_COST);
      putrail();
      //Nr_Trails--;
    }
    return 0;
  }
}

"""
/*
int __INSTR_PREV_ACTOR = -1;
int __INSTR_PREV_ACTION = -1;
int __INSTR_NUM_FIRINGS = 0;
int __INSTR_ACTOR_SWITCHES = 0;
int __INSTR_ACTION_SWITCHES = 0; 
*/
}

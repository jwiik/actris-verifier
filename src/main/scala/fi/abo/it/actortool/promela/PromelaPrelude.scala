package fi.abo.it.actortool.promela

import fi.abo.it.actortool._

object PromelaPrelude extends Prelude {
  override def defaultComponents = Set(MaskPrelude)
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
  private var sz = -1
  def setSize(size: Int) { sz = size }
  
  def text = {
    if (sz == -1) throw new IllegalStateException()
    else new InstrumentationSubPrelude(sz).text
  }
}

class InstrumentationSubPrelude(initCost: Int) extends PromelaPreludeComponent {
  
  override def text = template.replace("@init_cost@",initCost.toString)
  
  def template = 
"""
#define best_cost c_expr { best_c() }
#define more_expensive c_expr { more_exp() }

int __INSTR_COST = 0;
int __INSTR_ACC_BUFFER_SUM = 0;
int __INSTR_NUM_FIRINGS = 0;

c_state "int BEST_COST = @init_cost@" "Hidden"

c_code {
  
  int best_c() {
    if (now.__INSTR_COST < BEST_COST) {
      return 1;
    }
    else {
      return 0;
    }
  }
  
  int best() {
    if (now.__INSTR_COST < BEST_COST) {
      BEST_COST = now.__INSTR_COST;
      printf(">> New best: %d\n", BEST_COST);
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

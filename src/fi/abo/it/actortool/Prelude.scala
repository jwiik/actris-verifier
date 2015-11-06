package fi.abo.it.actortool

object BoogiePrelude {
  
  // adds component c to the prelude. has no effect if c is already present.
  def addComponent(c: PreludeComponent*): Unit = {
    components = components ++ c
  }

  // removes a component from the prelude. use with great care, as other parts of
  // the system could depend on the component c being present in the prelude.
  def removeComponent(c: PreludeComponent*): Unit = {
    components = components -- c
  }

  // records that a predicate occurs in the program (used for generating the
  // correct triggers for an axiom in the prelude)
  //def addPredicate(p: Predicate*): Unit = {
  //  predicates ++= p
  //}
  //val predicates: Set[Predicate] = Set()
  
  // default components
  private var components: Set[PreludeComponent] = Set(TypesAndGlobalVarsPL,FooterPL)

  // get the prelude (with all components currently included)
  def get: String = {
    val l = components.toList.sortWith((a,b) => a compare b)
    l.foldLeft("")((s:String,a:PreludeComponent) => s + (a text))
  }
}

sealed abstract class PreludeComponent {
  // determines the order in which the components are output
  def compare(that: PreludeComponent): Boolean = {
    val order: List[PreludeComponent] = List(TypesAndGlobalVarsPL,DivModAbsPL,FooterPL)
    if (!order.contains(this)) false
    else order.indexOf(this) < order.indexOf(that)
  }
  def text: String
}

object TypesAndGlobalVarsPL extends PreludeComponent {
  val text = 
"""
// ---------------------------------------------------------------
// -- Types and global variables ---------------------------------
// ---------------------------------------------------------------
type Chan a;
type CType = <a>[Chan a]int;
type MType = <a>[Chan a][int]a;
type State;
var M: MType;
var C: CType;
var R: CType; 
var C#init: CType;
"""
}

object DivModAbsPL extends PreludeComponent {
  val text =
"""
function at$abs(x: int): int { if 0 <= x then x else -x }
function at$div(int, int): int;
function at$mod(int, int): int;
axiom (forall a,b: int :: at$div(a,b)*b + at$mod(a,b) == a);
axiom (forall a,b: int :: 0 <= at$mod(a,b) && at$mod(a,b) < at$abs(b));
"""
}

object FooterPL extends PreludeComponent {
  val text =
"""
// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

"""
}



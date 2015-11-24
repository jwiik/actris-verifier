package fi.abo.it.actortool

object BoogiePrelude {
  
  // adds component c to the prelude. has no effect if c is already present.
  def addComponent(c: PreludeComponent*): Unit = {
    for (comp <- c) {
      for (d <- comp.dependencies) {
        components = components + d
      }
      components = components + comp
    }
    
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
    val order: List[PreludeComponent] = List(TypesAndGlobalVarsPL,DivModAbsPL,ShiftsPL,FooterPL)
    if (!order.contains(this)) false
    else order.indexOf(this) < order.indexOf(that)
  }
  def text: String
  def dependencies = Set.empty[PreludeComponent]
}

object TypesAndGlobalVarsPL extends PreludeComponent {
  val text = 
"""// ---------------------------------------------------------------
// -- Types and global variables ---------------------------------
// ---------------------------------------------------------------
type Chan a;
type Actor;
type CType = <a>[Chan a]int;
type MType = <a>[Chan a][int]a;
type State;

var M: MType;
var C: CType;
var R: CType; 
var C#init: CType;
var St: [Actor]State;

const unique this#: Actor;

type List a = [int]a;
var AT#intlst: List int;

"""
}

object DivModAbsPL extends PreludeComponent {
  val text =
"""
function AT#Abs(x: int): int { if 0 <= x then x else -x }
function AT#Div(int, int): int;
function AT#Mod(int, int): int;
axiom (forall a,b: int :: AT#Div(a,b)*b + AT#Mod(a,b) == a);
axiom (forall a,b: int :: 0 <= AT#Mod(a,b) && AT#Mod(a,b) < AT#Abs(b));
"""
}

object ShiftsPL extends PreludeComponent {
  
  override def dependencies = Set(DivModAbsPL)
  
  val text =
"""
function AT#RShift(int, int): int;
function AT#LShift(int, int): int;
axiom (forall a: int :: (
  AT#RShift(a,1) == AT#Div(a,2) &&
  AT#RShift(a,2) == AT#Div(a,4) &&
  AT#RShift(a,3) == AT#Div(a,8) &&
  AT#RShift(a,4) == AT#Div(a,16) &&
  AT#RShift(a,5) == AT#Div(a,32) &&
  AT#RShift(a,6) == AT#Div(a,64) &&
  AT#RShift(a,7) == AT#Div(a,128) &&
  AT#RShift(a,8) == AT#Div(a,256)
));
"""
}

object ChAggregates extends PreludeComponent {
  
  //override def dependencies = Set(DivModAbsPL)
  
  val text =
"""
function AT#ChSum(Chan int, int): int;
axiom (forall ch: Chan int, limit: int :: (AT#ChSum(ch,limit) == ch[limit]+AT#ChSum(ch,limit-1)));
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



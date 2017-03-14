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
    val comps = components //+ PureBitwisePL
    val l = comps.toList.sortWith((a,b) => a compare b)
    l.foldLeft("")((s:String,a:PreludeComponent) => s + (a.text.replace("@inttype@", /*if (bvMode) "bv32" else*/ "int" )))
  }
}

sealed abstract class PreludeComponent {
  // determines the order in which the components are output
  def compare(that: PreludeComponent): Boolean = {
    val order: List[PreludeComponent] = List(TypesAndGlobalVarsPL,SeqNumberingPL,DivModAbsPL,BitwisePL,FooterPL)
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
type Ref;
type Chan a;
type Field a;
type Actor;
type CType = <a>[Chan a]@inttype@;
type MType = <a>[Chan a][@inttype@]a;
type Obj = <a>[Field a]a;
type HType = [Ref]Obj;

var M: MType;
var C: CType;
var R: CType;
var I: CType;

var H: HType;

const unique this#: Actor;

function AT#Min(x:int, y: int): int { if x <= y then x else y }
"""
}

object SeqNumberingPL extends PreludeComponent {
  val text = 
"""
// -- Sequence numbering for FT ----------------------------------
const unique sqn#: Field int;
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

object PureBitwisePL extends PreludeComponent {
  
  
  val text =
"""
function {:bvbuiltin "bvand"} AT#BvAnd(a: bv32, b: bv32): bv32;
function {:bvbuiltin "bvadd"} AT#BvAdd(a: bv32, b: bv32): bv32;
function {:bvbuiltin "bvsub"} AT#BvSub(a: bv32, b: bv32): bv32;
function {:bvbuiltin "bvule"} AT#BvUle(a: bv32, b: bv32): bool;
function {:bvbuiltin "bvult"} AT#BvUlt(a: bv32, b: bv32): bool;
function AT#RShift(bv32,bv32): bv32;
function AT#LShift(bv32,bv32): bv32;
"""
}

class BitvectorPL(val size: Int) extends PreludeComponent {
   private val template =
"""
function {:bvbuiltin "bvand"} AT#BvAnd(a: @bvsize@, b: @bvsize@): @bvsize@;
function {:bvbuiltin "bvor"} AT#BvOr(a: @bvsize@, b: @bvsize@): @bvsize@;
function {:bvbuiltin "bvnot"} AT#BvNot(a: @bvsize@): @bvsize@;
function {:bvbuiltin "bvadd"} AT#BvAdd(a: @bvsize@, b: @bvsize@): @bvsize@;
function {:bvbuiltin "bvsub"} AT#BvSub(a: @bvsize@, b: @bvsize@): @bvsize@;
function {:bvbuiltin "bvmul"} AT#BvMul(a: @bvsize@, b: @bvsize@): @bvsize@;
function {:bvbuiltin "bvshl"} AT#BvShl(@bvsize@,@bvsize@): @bvsize@;
function {:bvbuiltin "bvlshr"} AT#BvLshr(@bvsize@,@bvsize@): @bvsize@;
function {:bvbuiltin "bvashr"} AT#BvAshr(@bvsize@,@bvsize@): @bvsize@;
function {:bvbuiltin "bvule"} AT#BvUle(a: @bvsize@, b: @bvsize@): bool;
function {:bvbuiltin "bvult"} AT#BvUlt(a: @bvsize@, b: @bvsize@): bool;
function {:bvbuiltin "bvuge"} AT#BvUge(a: @bvsize@, b: @bvsize@): bool;
function {:bvbuiltin "bvugt"} AT#BvUgt(a: @bvsize@, b: @bvsize@): bool;
"""
   
  val text = template.replace("@bvsize@", "bv"+size)

  override def equals(that: Any): Boolean = that match {
     case bvpl: BitvectorPL => bvpl.size == this.size
     case _ => false
  }
   
  override def hashCode: Int = BitvectorPL.hashCode+size
}

object BitvectorPL {
  def createPL(size: Int) = new BitvectorPL(size)
  def createPL(typ: BvType) = new BitvectorPL(typ.size)
}

object BitwisePL extends PreludeComponent {
  
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
  AT#RShift(a,8) == AT#Div(a,256) &&
  AT#RShift(a,9) == AT#Div(a,512)
));
axiom (forall a: int :: (
  AT#LShift(a,1) == a * 2 &&
  AT#LShift(a,2) == a * 4 &&
  AT#LShift(a,3) == a * 8 &&
  AT#LShift(a,4) == a * 16 &&
  AT#LShift(a,5) == a * 32 &&
  AT#LShift(a,6) == a * 64 &&
  AT#LShift(a,7) == a * 128 &&
  AT#LShift(a,8) == a * 256 &&
  AT#LShift(a,9) == a * 512
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



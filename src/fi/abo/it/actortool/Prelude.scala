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
  private var components: Set[PreludeComponent] = Set(TypesAndGlobalVarsPL)

  // get the prelude (with all components currently included)
  def get: String = {
    var l = components.toList.sortWith((a,b) => a compare b)
    l = l.:+ (FooterPL)
    l.foldLeft("")((s:String,a:PreludeComponent) => s + a.text)
  }
}

sealed abstract class PreludeComponent {
  // determines the order in which the components are output
  def compare(that: PreludeComponent): Boolean = {
    val order: List[PreludeComponent] = List(TypesAndGlobalVarsPL,SeqNumberingPL,DivModAbsPL,BitwisePL,MapPL,Bitvector2IntPL)
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
type CType = <a>[Chan a]int;
type MType = <a>[Chan a][int]a;
type Obj = <a>[Field a]a;
type HType = [Ref]Obj;

var M: MType;
var C: CType;
var R: CType;
var I: CType;
var B: CType;

var H: HType;

const unique this#: Actor;

function AT#Min(x:int, y: int): int { if x <= y then x else y }
function AT#Ite<T>(bool, T, T): T;
axiom (
  forall<T> cond: bool, thn: T, els: T :: { AT#Ite(cond, thn, els) }
    (cond ==> AT#Ite(cond,thn,els) == thn &&
    !cond ==> AT#Ite(cond,thn,els) == els)
);
"""
}

object SeqNumberingPL extends PreludeComponent {
  val text = 
"""// -- Sequence numbering for FT ----------------------------------
const unique sqn#: Field int;
"""
}

object DivModAbsPL extends PreludeComponent {
  val text =
"""
// ---------------------------------------------------------------
// -- Integer division and modulo --------------------------------
// ---------------------------------------------------------------
function AT#Abs(x: int): int { if 0 <= x then x else -x }
function AT#Div(int, int): int;
function AT#Mod(int, int): int;
axiom (forall a,b: int :: AT#Div(a,b)*b + AT#Mod(a,b) == a);
axiom (forall a,b: int :: 0 <= AT#Mod(a,b) && AT#Mod(a,b) < AT#Abs(b));
"""
}

class BitvectorPL(val size: Int) extends PreludeComponent {
   private val template =
"""
// ---------------------------------------------------------------
// -- Bit vector operations --------------------------------------
// ---------------------------------------------------------------
// Size: @bvsize@
function {:bvbuiltin "bvand"} AT#BvAnd@bvsize@(a: bv@bvsize@, b: bv@bvsize@): bv@bvsize@;
function {:bvbuiltin "bvor"} AT#BvOr@bvsize@(a: bv@bvsize@, b: bv@bvsize@): bv@bvsize@;
function {:bvbuiltin "bvnot"} AT#BvNot@bvsize@(a: bv@bvsize@): bv@bvsize@;
function {:bvbuiltin "bvadd"} AT#BvAdd@bvsize@(a: bv@bvsize@, b: bv@bvsize@): bv@bvsize@;
function {:bvbuiltin "bvsub"} AT#BvSub@bvsize@(a: bv@bvsize@, b: bv@bvsize@): bv@bvsize@;
function {:bvbuiltin "bvmul"} AT#BvMul@bvsize@(a: bv@bvsize@, b: bv@bvsize@): bv@bvsize@;
function {:bvbuiltin "bvshl"} AT#BvShl@bvsize@(bv@bvsize@,bv@bvsize@): bv@bvsize@;
function {:bvbuiltin "bvlshr"} AT#BvLshr@bvsize@(bv@bvsize@,bv@bvsize@): bv@bvsize@;
function {:bvbuiltin "bvashr"} AT#BvAshr@bvsize@(bv@bvsize@,bv@bvsize@): bv@bvsize@;
function {:bvbuiltin "bvule"} AT#BvUle@bvsize@(a: bv@bvsize@, b: bv@bvsize@): bool;
function {:bvbuiltin "bvult"} AT#BvUlt@bvsize@(a: bv@bvsize@, b: bv@bvsize@): bool;
function {:bvbuiltin "bvuge"} AT#BvUge@bvsize@(a: bv@bvsize@, b: bv@bvsize@): bool;
function {:bvbuiltin "bvugt"} AT#BvUgt@bvsize@(a: bv@bvsize@, b: bv@bvsize@): bool;
function AT#BvXor@bvsize@(a: bv@bvsize@, b: bv@bvsize@): bv@bvsize@;

axiom (forall a,b: bv@bvsize@ :: AT#BvXor@bvsize@(a,b) == AT#BvAnd@bvsize@(AT#BvOr@bvsize@(a,b), AT#BvNot@bvsize@(AT#BvAnd@bvsize@(a,b))) );
"""
   
  val text = template.replace("@bvsize@", size.toString)

  override def equals(that: Any): Boolean = that match {
     case bvpl: BitvectorPL => bvpl.size == this.size
     case _ => false
  }
   
  override def hashCode: Int = BitvectorPL.hashCode+size
}

object Bitvector2IntPL extends PreludeComponent {
    val text =
"""
// ---------------------------------------------------------------
// -- Bitvector to integer ---------------------------------------
// ---------------------------------------------------------------
function AT#Bit0(vec: bv8): bool { AT#BvAnd8(vec,1bv8) != 0bv8 }
function AT#Bit1(vec: bv8): bool { AT#BvAnd8(vec,2bv8) != 0bv8 }
function AT#Bit2(vec: bv8): bool { AT#BvAnd8(vec,4bv8) != 0bv8 }
function AT#Bit3(vec: bv8): bool { AT#BvAnd8(vec,8bv8) != 0bv8 }
function AT#Bit4(vec: bv8): bool { AT#BvAnd8(vec,16bv8) != 0bv8 }
function AT#Bit5(vec: bv8): bool { AT#BvAnd8(vec,32bv8) != 0bv8 }
function AT#Bit6(vec: bv8): bool { AT#BvAnd8(vec,64bv8) != 0bv8 }
function AT#Bit7(vec: bv8): bool { AT#BvAnd8(vec,128bv8) != 0bv8 }

function AT#Bv2Int(vec: bv8): int {
  128*( if AT#Bit7(vec) then 1 else 0 ) +
  64*( if AT#Bit6(vec) then 1 else 0 ) +
  32*( if AT#Bit5(vec) then 1 else 0 ) +
  16*( if AT#Bit4(vec) then 1 else 0 ) +
  8*( if AT#Bit3(vec) then 1 else 0 ) +
  4*( if AT#Bit2(vec) then 1 else 0 ) +
  2*( if AT#Bit1(vec) then 1 else 0 ) +
  1*( if AT#Bit0(vec) then 1 else 0 )
}
"""
}

object BitvectorPL {
  def createPL(size: Int) = new BitvectorPL(size)
  def createPL(typ: BvType) = new BitvectorPL(typ.size)
}

object BitwisePL extends PreludeComponent {
  
  override def dependencies = Set(DivModAbsPL)
  
  val text =
"""
// ---------------------------------------------------------------
// -- Shift operations for integers ------------------------------
// ---------------------------------------------------------------
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
function AT#ChSum(MType, Chan int, int): int;
axiom (
  forall mm: MType, ch: Chan int, limit: int :: {AT#ChSum(mm,ch,limit)} {AT#ChSum(mm,ch,limit-1)} 
    (limit > 0 ==> AT#ChSum(mm,ch,limit) == mm[ch][limit-1]+AT#ChSum(mm,ch,limit-1)) &&
    (limit == 0 ==> AT#ChSum(mm,ch,limit) == 0)
);
axiom (
  forall mm: MType, ch: Chan int :: {AT#ChSum(mm,ch,0)} 
    AT#ChSum(mm,ch,0) == 0
);
"""
}

object MapPL extends PreludeComponent {
  
  //override def dependencies = Set(DivModAbsPL)
  
  val text =
"""
// ---------------------------------------------------------------
// -- Axiomatisation for map data type ---------------------------
// ---------------------------------------------------------------
type Map a b;

function Map#Select<T,U>(Map T U, T): U;
function Map#Store<T,U>(Map T U, T, U): Map T U;
axiom (
  forall<T,U> m: Map T U, k1: T, val: U :: { Map#Store(m,k1,val) }
    Map#Select(Map#Store(m,k1,val),k1) == val
);
axiom (
  forall<T,U> m: Map T U, k1: T, k2: T, val: U :: { Map#Select(Map#Store(m,k1,val),k2) }
    k1 != k2 ==> Map#Select(Map#Store(m,k1,val),k2) == Map#Select(m,k2)
);
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



package fi.abo.it.actortool.boogie

import fi.abo.it.actortool._

object BoogiePrelude extends Prelude {

  // default components
  override def defaultComponents = Set(TypesAndGlobalVarsPL,FooterPL)

}

object BoogiePreludeOrder extends PreludeOrder {
  lazy val order = List(TypesAndGlobalVarsPL,DivModAbsPL,MapPL,BitwisePL,BitvectorPL,Bitvector2IntPL,ChAggregates,FooterPL)
}

abstract class BoogiePreludeComponent extends PreludeComponent(BoogiePreludeOrder)

object TypesAndGlobalVarsPL extends BoogiePreludeComponent {
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
type ModeType = [Actor]int;

var M#: MType;
var C#: CType;
var R#: CType;
var I#: CType;
var B#: CType;
var Mode#: ModeType;
var I#sub: CType;

var H#: HType;

const unique this#: Actor;
function AT#Min(x:int, y: int): int { if x <= y then x else y }
"""
}

object DivModAbsPL extends BoogiePreludeComponent {
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

class BitvectorSubPL(val size: Int) extends BoogiePreludeComponent {
   private val template =
"""
// ---------------------------------------------------------------
// -- Bit vector operations --------------------------------------
// ---------------------------------------------------------------
// Size: @bvsize@
function {:bvbuiltin "bvand"} AT#BvAnd@bvsize@(a: bv@bvsize@, b: bv@bvsize@): bv@bvsize@;
function {:bvbuiltin "bvor"} AT#BvOr@bvsize@(a: bv@bvsize@, b: bv@bvsize@): bv@bvsize@;
function {:bvbuiltin "bvnot"} AT#BvNot@bvsize@(a: bv@bvsize@): bv@bvsize@;
function {:bvbuiltin "bvneg"} AT#BvNeg@bvsize@(a: bv@bvsize@): bv@bvsize@;
function {:bvbuiltin "bvadd"} AT#BvAdd@bvsize@(a: bv@bvsize@, b: bv@bvsize@): bv@bvsize@;
function {:bvbuiltin "bvsub"} AT#BvSub@bvsize@(a: bv@bvsize@, b: bv@bvsize@): bv@bvsize@;
function {:bvbuiltin "bvmul"} AT#BvMul@bvsize@(a: bv@bvsize@, b: bv@bvsize@): bv@bvsize@;
function {:bvbuiltin "bvsdiv"} AT#BvSdiv@bvsize@(a: bv@bvsize@, b: bv@bvsize@): bv@bvsize@;
function {:bvbuiltin "bvudiv"} AT#BvUdiv@bvsize@(a: bv@bvsize@, b: bv@bvsize@): bv@bvsize@;
function {:bvbuiltin "bvshl"} AT#BvShl@bvsize@(bv@bvsize@,bv@bvsize@): bv@bvsize@;
function {:bvbuiltin "bvlshr"} AT#BvLshr@bvsize@(bv@bvsize@,bv@bvsize@): bv@bvsize@;
function {:bvbuiltin "bvashr"} AT#BvAshr@bvsize@(bv@bvsize@,bv@bvsize@): bv@bvsize@;
function {:bvbuiltin "bvule"} AT#BvUle@bvsize@(a: bv@bvsize@, b: bv@bvsize@): bool;
function {:bvbuiltin "bvult"} AT#BvUlt@bvsize@(a: bv@bvsize@, b: bv@bvsize@): bool;
function {:bvbuiltin "bvuge"} AT#BvUge@bvsize@(a: bv@bvsize@, b: bv@bvsize@): bool;
function {:bvbuiltin "bvugt"} AT#BvUgt@bvsize@(a: bv@bvsize@, b: bv@bvsize@): bool;
function {:bvbuiltin "bvsle"} AT#BvSle@bvsize@(a: bv@bvsize@, b: bv@bvsize@): bool;
function {:bvbuiltin "bvslt"} AT#BvSlt@bvsize@(a: bv@bvsize@, b: bv@bvsize@): bool;
function {:bvbuiltin "bvsge"} AT#BvSge@bvsize@(a: bv@bvsize@, b: bv@bvsize@): bool;
function {:bvbuiltin "bvsgt"} AT#BvSgt@bvsize@(a: bv@bvsize@, b: bv@bvsize@): bool;
function AT#BvXor@bvsize@(a: bv@bvsize@, b: bv@bvsize@): bv@bvsize@;
function AT#BvAbs@bvsize@(a: bv@bvsize@): bv@bvsize@;

axiom (forall a,b: bv@bvsize@ :: AT#BvXor@bvsize@(a,b) == AT#BvAnd@bvsize@(AT#BvOr@bvsize@(a,b), AT#BvNot@bvsize@(AT#BvAnd@bvsize@(a,b))) );
axiom (forall a,b: bv@bvsize@ :: AT#BvAbs@bvsize@(a) == (if AT#BvSle@bvsize@(0bv@bvsize@,a) then a else AT#BvNeg@bvsize@(a)) );
"""
   
  val text = template.replace("@bvsize@", size.toString)

  override def equals(that: Any): Boolean = that match {
     case bvpl: BitvectorSubPL => bvpl.size == this.size
     case _ => false
  }
   
  override def hashCode: Int = BitvectorPL.hashCode+size
}

class Bitvector2IntSubPL(val size: Int) extends BoogiePreludeComponent {
  
  val bitFuncTemplate = "AT#Bit@bitnum@bv@bvsize@(@argument@)"
  
  val bitFuncDeclTemplate = 
    "function AT#Bit@bitnum@bv@bvsize@(vec: bv@bvsize@): bool { AT#BvAnd@bvsize@(vec,@bitexp@bv@bvsize@) != 0bv@bvsize@ }"
  
  val bv2intDeclTemplate = "function AT#Bv2Int@bvsize@(vec: bv@bvsize@): int { @expr@ }"
  
  def generateBitFunc(n: Int) = bitFuncDeclTemplate.replace("@bvsize@", size.toString).replace("@bitnum@", n.toString)
  
  def generateBv2Int = {
    "function AT#Bv2Int" + size + "(vec: bv" + size  + "): int {\n  " +
    (for (i <- 0 to size-1) yield {
      val bitFunc = bitFuncTemplate
        .replace("@bitnum@", i.toString)
        .replace("@argument@", "vec")
        .replace("@bvsize@", size.toString)
       "(if " + bitFunc + " then " + scala.math.pow(2,i).toLong.toString + " else 0)"
    }).mkString(" +\n  ") + 
    "\n}\n"
  }
  
  def generateText: String = {
    header+
    "// Size: " + size + "\n" +
    (for (i <- 0 to size-1) yield {
      bitFuncDeclTemplate
        .replace("@bvsize@", size.toString)
        .replace("@bitnum@", i.toString)
        .replace("@bitexp@", scala.math.pow(2,i).toLong.toString)
    }).mkString("\n") + "\n\n" +
    generateBv2Int
  }
  
  val header = 
"""
// ---------------------------------------------------------------
// -- Bitvector to integer ---------------------------------------
// ---------------------------------------------------------------
"""
  
  val text = generateText
  
  override def equals(that: Any): Boolean = that match {
     case bvpl: Bitvector2IntSubPL => bvpl.size == this.size
     case _ => false
  }
  
  override def hashCode: Int = Bitvector2IntPL.hashCode+size
}


object BitvectorPL extends BoogiePreludeComponent {
  def createPL(size: Int): this.type = { subPLs = subPLs + new BitvectorSubPL(size); BitvectorPL }
  def createPL(typ: BvType): this.type = createPL(typ.size)
  
  private var subPLs: Set[BitvectorSubPL] = Set.empty
  
  def text = {
    subPLs.foldLeft("")((s:String,a:PreludeComponent) => s + a.text)
  }
  
}

object Bitvector2IntPL extends BoogiePreludeComponent {
  
  def createPL(size: Int): this.type = { subPLs = subPLs + new Bitvector2IntSubPL(size); Bitvector2IntPL }
  def createPL(typ: BvType): this.type = createPL(typ.size)
  
  private var subPLs: Set[Bitvector2IntSubPL] = Set.empty
  
  def text = {
    subPLs.foldLeft("")((s:String,a:PreludeComponent) => s + a.text)
  }
  
}

object BitwisePL extends BoogiePreludeComponent {
  
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

object ChAggregates extends BoogiePreludeComponent {
  
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

object MapPL extends BoogiePreludeComponent {
  
  //override def dependencies = Set(DivModAbsPL)
  
  val text =
"""
// ---------------------------------------------------------------
// -- Axiomatisation for map data type ---------------------------
// ---------------------------------------------------------------
type Map a b;
function List#Empty<U>(U): Map int U;
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

object FooterPL extends BoogiePreludeComponent {
  val text =
"""
// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

"""
}

// ---------------------------------------------------------------
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

// ---------------------------------------------------------------
// -- Bit vector operations --------------------------------------
// ---------------------------------------------------------------
// Size: 8
function {:bvbuiltin "bvand"} AT#BvAnd8(a: bv8, b: bv8): bv8;
function {:bvbuiltin "bvor"} AT#BvOr8(a: bv8, b: bv8): bv8;
function {:bvbuiltin "bvnot"} AT#BvNot8(a: bv8): bv8;
function {:bvbuiltin "bvadd"} AT#BvAdd8(a: bv8, b: bv8): bv8;
function {:bvbuiltin "bvsub"} AT#BvSub8(a: bv8, b: bv8): bv8;
function {:bvbuiltin "bvmul"} AT#BvMul8(a: bv8, b: bv8): bv8;
function {:bvbuiltin "bvshl"} AT#BvShl8(bv8,bv8): bv8;
function {:bvbuiltin "bvlshr"} AT#BvLshr8(bv8,bv8): bv8;
function {:bvbuiltin "bvashr"} AT#BvAshr8(bv8,bv8): bv8;
function {:bvbuiltin "bvule"} AT#BvUle8(a: bv8, b: bv8): bool;
function {:bvbuiltin "bvult"} AT#BvUlt8(a: bv8, b: bv8): bool;
function {:bvbuiltin "bvuge"} AT#BvUge8(a: bv8, b: bv8): bool;
function {:bvbuiltin "bvugt"} AT#BvUgt8(a: bv8, b: bv8): bool;
function AT#BvXor8(a: bv8, b: bv8): bv8;

axiom (forall a,b: bv8 :: AT#BvXor8(a,b) == AT#BvAnd8(AT#BvOr8(a,b), AT#BvNot8(AT#BvAnd8(a,b))) );

// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

procedure chipMapper#init#0()
  modifies C, R, M, I, H;
{
  var data: Chan (bv8);
  var chip: Chan (bv32);
  var Chip_map_table: Map (bv8) (bv32);
  var lsn: bv8;
  var msn: bv8;
  assume true;
  assume R[data] == 0;
  assume C[chip] == 0;
  assert {:msg "17.19: Initialization might not establish the invariant (#0)"} (2 * R[data]) == C[chip];
}
procedure chipMapper#anon$0#1()
  modifies C, R, M, I, H;
{
  var data: Chan (bv8);
  var chip: Chan (bv32);
  var Chip_map_table: Map (bv8) (bv32);
  var lsn: bv8;
  var msn: bv8;
  var data#0: bv8;
  assume true;
  assume 0 <= R[data];
  assume 0 <= C[chip];
  assume (2 * R[data]) == C[chip];
  data#0 := M[data][R[data]];
  R[data] := R[data] + 1;
  lsn := AT#BvAnd8(data#0, 15bv8);
  msn := AT#BvAnd8(AT#BvLshr8(data#0, 4bv8), 15bv8);
  M[chip][C[chip]] := Map#Select(Chip_map_table, lsn);
  C[chip] := C[chip] + 1;
  M[chip][C[chip]] := Map#Select(Chip_map_table, msn);
  C[chip] := C[chip] + 1;
  assert {:msg "17.19: Action at 25.2 might not preserve invariant (#1)"} (2 * R[data]) == C[chip];
}

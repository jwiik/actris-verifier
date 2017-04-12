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
// Size: 32
function {:bvbuiltin "bvand"} AT#BvAnd32(a: bv32, b: bv32): bv32;
function {:bvbuiltin "bvor"} AT#BvOr32(a: bv32, b: bv32): bv32;
function {:bvbuiltin "bvnot"} AT#BvNot32(a: bv32): bv32;
function {:bvbuiltin "bvadd"} AT#BvAdd32(a: bv32, b: bv32): bv32;
function {:bvbuiltin "bvsub"} AT#BvSub32(a: bv32, b: bv32): bv32;
function {:bvbuiltin "bvmul"} AT#BvMul32(a: bv32, b: bv32): bv32;
function {:bvbuiltin "bvshl"} AT#BvShl32(bv32,bv32): bv32;
function {:bvbuiltin "bvlshr"} AT#BvLshr32(bv32,bv32): bv32;
function {:bvbuiltin "bvashr"} AT#BvAshr32(bv32,bv32): bv32;
function {:bvbuiltin "bvule"} AT#BvUle32(a: bv32, b: bv32): bool;
function {:bvbuiltin "bvult"} AT#BvUlt32(a: bv32, b: bv32): bool;
function {:bvbuiltin "bvuge"} AT#BvUge32(a: bv32, b: bv32): bool;
function {:bvbuiltin "bvugt"} AT#BvUgt32(a: bv32, b: bv32): bool;
function AT#BvXor32(a: bv32, b: bv32): bv32;

axiom (forall a,b: bv32 :: AT#BvXor32(a,b) == AT#BvAnd32(AT#BvOr32(a,b), AT#BvNot32(AT#BvAnd32(a,b))) );

// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

function qpskMod#q7_map(bit: bv32) returns (out: bv8);
procedure qpskMod#init#0()
  modifies C, R, M, I, H;
{
  var chip: Chan (bv32);
  var symb: Chan (bv8);
  var IQ: Map (int) (bv8);
  assume true;
  assume R[chip] == 0;
  assume C[symb] == 0;
  assert {:msg "qpskMod.cal(13.19): Initialization might not establish the invariant (#0)"} (32 * R[chip]) == C[symb];
  assert {:msg "Initialization might not establish the invariant (#1)"} (32 * R[chip]) == C[symb];
}
procedure qpskMod#anon$0#1()
  modifies C, R, M, I, H;
{
  var chip: Chan (bv32);
  var symb: Chan (bv8);
  var IQ: Map (int) (bv8);
  var chip#0: bv32;
  assume true;
  assume 0 <= R[chip];
  assume 0 <= C[symb];
  assume (32 * R[chip]) == C[symb];
  assume (32 * R[chip]) == C[symb];
  chip#0 := M[chip][R[chip]];
  R[chip] := R[chip] + 1;
  IQ := Map#Store(IQ, 0, qpskMod#q7_map(AT#BvAnd32(AT#BvLshr32(chip#0, 0bv32), 1bv32)));
  IQ := Map#Store(IQ, 1, qpskMod#q7_map(AT#BvAnd32(AT#BvLshr32(chip#0, 1bv32), 1bv32)));
  IQ := Map#Store(IQ, 2, qpskMod#q7_map(AT#BvAnd32(AT#BvLshr32(chip#0, 2bv32), 1bv32)));
  IQ := Map#Store(IQ, 3, qpskMod#q7_map(AT#BvAnd32(AT#BvLshr32(chip#0, 3bv32), 1bv32)));
  IQ := Map#Store(IQ, 4, qpskMod#q7_map(AT#BvAnd32(AT#BvLshr32(chip#0, 4bv32), 1bv32)));
  IQ := Map#Store(IQ, 5, qpskMod#q7_map(AT#BvAnd32(AT#BvLshr32(chip#0, 5bv32), 1bv32)));
  IQ := Map#Store(IQ, 6, qpskMod#q7_map(AT#BvAnd32(AT#BvLshr32(chip#0, 6bv32), 1bv32)));
  IQ := Map#Store(IQ, 7, qpskMod#q7_map(AT#BvAnd32(AT#BvLshr32(chip#0, 7bv32), 1bv32)));
  IQ := Map#Store(IQ, 8, qpskMod#q7_map(AT#BvAnd32(AT#BvLshr32(chip#0, 8bv32), 1bv32)));
  IQ := Map#Store(IQ, 9, qpskMod#q7_map(AT#BvAnd32(AT#BvLshr32(chip#0, 9bv32), 1bv32)));
  IQ := Map#Store(IQ, 10, qpskMod#q7_map(AT#BvAnd32(AT#BvLshr32(chip#0, 10bv32), 1bv32)));
  IQ := Map#Store(IQ, 11, qpskMod#q7_map(AT#BvAnd32(AT#BvLshr32(chip#0, 11bv32), 1bv32)));
  IQ := Map#Store(IQ, 12, qpskMod#q7_map(AT#BvAnd32(AT#BvLshr32(chip#0, 12bv32), 1bv32)));
  IQ := Map#Store(IQ, 13, qpskMod#q7_map(AT#BvAnd32(AT#BvLshr32(chip#0, 13bv32), 1bv32)));
  IQ := Map#Store(IQ, 14, qpskMod#q7_map(AT#BvAnd32(AT#BvLshr32(chip#0, 14bv32), 1bv32)));
  IQ := Map#Store(IQ, 15, qpskMod#q7_map(AT#BvAnd32(AT#BvLshr32(chip#0, 15bv32), 1bv32)));
  IQ := Map#Store(IQ, 16, qpskMod#q7_map(AT#BvAnd32(AT#BvLshr32(chip#0, 16bv32), 1bv32)));
  IQ := Map#Store(IQ, 17, qpskMod#q7_map(AT#BvAnd32(AT#BvLshr32(chip#0, 17bv32), 1bv32)));
  IQ := Map#Store(IQ, 18, qpskMod#q7_map(AT#BvAnd32(AT#BvLshr32(chip#0, 18bv32), 1bv32)));
  IQ := Map#Store(IQ, 19, qpskMod#q7_map(AT#BvAnd32(AT#BvLshr32(chip#0, 19bv32), 1bv32)));
  IQ := Map#Store(IQ, 20, qpskMod#q7_map(AT#BvAnd32(AT#BvLshr32(chip#0, 20bv32), 1bv32)));
  IQ := Map#Store(IQ, 21, qpskMod#q7_map(AT#BvAnd32(AT#BvLshr32(chip#0, 21bv32), 1bv32)));
  IQ := Map#Store(IQ, 22, qpskMod#q7_map(AT#BvAnd32(AT#BvLshr32(chip#0, 22bv32), 1bv32)));
  IQ := Map#Store(IQ, 23, qpskMod#q7_map(AT#BvAnd32(AT#BvLshr32(chip#0, 23bv32), 1bv32)));
  IQ := Map#Store(IQ, 24, qpskMod#q7_map(AT#BvAnd32(AT#BvLshr32(chip#0, 24bv32), 1bv32)));
  IQ := Map#Store(IQ, 25, qpskMod#q7_map(AT#BvAnd32(AT#BvLshr32(chip#0, 25bv32), 1bv32)));
  IQ := Map#Store(IQ, 26, qpskMod#q7_map(AT#BvAnd32(AT#BvLshr32(chip#0, 26bv32), 1bv32)));
  IQ := Map#Store(IQ, 27, qpskMod#q7_map(AT#BvAnd32(AT#BvLshr32(chip#0, 27bv32), 1bv32)));
  IQ := Map#Store(IQ, 28, qpskMod#q7_map(AT#BvAnd32(AT#BvLshr32(chip#0, 28bv32), 1bv32)));
  IQ := Map#Store(IQ, 29, qpskMod#q7_map(AT#BvAnd32(AT#BvLshr32(chip#0, 29bv32), 1bv32)));
  IQ := Map#Store(IQ, 30, qpskMod#q7_map(AT#BvAnd32(AT#BvLshr32(chip#0, 30bv32), 1bv32)));
  IQ := Map#Store(IQ, 31, qpskMod#q7_map(AT#BvAnd32(AT#BvLshr32(chip#0, 31bv32), 1bv32)));
  M[symb][C[symb]] := Map#Select(IQ, 0);
  C[symb] := C[symb] + 1;
  M[symb][C[symb]] := Map#Select(IQ, 1);
  C[symb] := C[symb] + 1;
  M[symb][C[symb]] := Map#Select(IQ, 2);
  C[symb] := C[symb] + 1;
  M[symb][C[symb]] := Map#Select(IQ, 3);
  C[symb] := C[symb] + 1;
  M[symb][C[symb]] := Map#Select(IQ, 4);
  C[symb] := C[symb] + 1;
  M[symb][C[symb]] := Map#Select(IQ, 5);
  C[symb] := C[symb] + 1;
  M[symb][C[symb]] := Map#Select(IQ, 6);
  C[symb] := C[symb] + 1;
  M[symb][C[symb]] := Map#Select(IQ, 7);
  C[symb] := C[symb] + 1;
  M[symb][C[symb]] := Map#Select(IQ, 8);
  C[symb] := C[symb] + 1;
  M[symb][C[symb]] := Map#Select(IQ, 9);
  C[symb] := C[symb] + 1;
  M[symb][C[symb]] := Map#Select(IQ, 10);
  C[symb] := C[symb] + 1;
  M[symb][C[symb]] := Map#Select(IQ, 11);
  C[symb] := C[symb] + 1;
  M[symb][C[symb]] := Map#Select(IQ, 12);
  C[symb] := C[symb] + 1;
  M[symb][C[symb]] := Map#Select(IQ, 13);
  C[symb] := C[symb] + 1;
  M[symb][C[symb]] := Map#Select(IQ, 14);
  C[symb] := C[symb] + 1;
  M[symb][C[symb]] := Map#Select(IQ, 15);
  C[symb] := C[symb] + 1;
  M[symb][C[symb]] := Map#Select(IQ, 16);
  C[symb] := C[symb] + 1;
  M[symb][C[symb]] := Map#Select(IQ, 17);
  C[symb] := C[symb] + 1;
  M[symb][C[symb]] := Map#Select(IQ, 18);
  C[symb] := C[symb] + 1;
  M[symb][C[symb]] := Map#Select(IQ, 19);
  C[symb] := C[symb] + 1;
  M[symb][C[symb]] := Map#Select(IQ, 20);
  C[symb] := C[symb] + 1;
  M[symb][C[symb]] := Map#Select(IQ, 21);
  C[symb] := C[symb] + 1;
  M[symb][C[symb]] := Map#Select(IQ, 22);
  C[symb] := C[symb] + 1;
  M[symb][C[symb]] := Map#Select(IQ, 23);
  C[symb] := C[symb] + 1;
  M[symb][C[symb]] := Map#Select(IQ, 24);
  C[symb] := C[symb] + 1;
  M[symb][C[symb]] := Map#Select(IQ, 25);
  C[symb] := C[symb] + 1;
  M[symb][C[symb]] := Map#Select(IQ, 26);
  C[symb] := C[symb] + 1;
  M[symb][C[symb]] := Map#Select(IQ, 27);
  C[symb] := C[symb] + 1;
  M[symb][C[symb]] := Map#Select(IQ, 28);
  C[symb] := C[symb] + 1;
  M[symb][C[symb]] := Map#Select(IQ, 29);
  C[symb] := C[symb] + 1;
  M[symb][C[symb]] := Map#Select(IQ, 30);
  C[symb] := C[symb] + 1;
  M[symb][C[symb]] := Map#Select(IQ, 31);
  C[symb] := C[symb] + 1;
  assert {:msg "qpskMod.cal(13.19): Action at qpskMod.cal(18.2) might not preserve invariant (#2)"} (32 * R[chip]) == C[symb];
  assert {:msg "Action at qpskMod.cal(18.2) might not preserve invariant (#3)"} (32 * R[chip]) == C[symb];
}

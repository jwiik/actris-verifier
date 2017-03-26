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

var H: HType;

const unique this#: Actor;

function AT#Min(x:int, y: int): int { if x <= y then x else y }

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

function pulseShape#mul8(x: bv8, y: bv8) returns (out: bv8);
procedure pulseShape#init#0()
  modifies C, R, M, I, H;
{
  var symb: Chan (bv8);
  var len: Chan (bv8);
  var done: Chan (bool);
  var hsp: Chan (bv8);
  var symb_mem: bv8;
  var body_iterations: bv8;
  var body_index: bv8;
  var FILT_COEFF0: bv8;
  var FILT_COEFF1: bv8;
  var FILT_COEFF2: bv8;
  var FILT_COEFF3: bv8;
  var FILT_COEFF4: bv8;
  var hsps: Map (int) (bv8);
  var St: int;
  assume (symb != len) && (symb != hsp) && (len != hsp);
  assume R[symb] == 0;
  assume R[len] == 0;
  assume C[done] == 0;
  assume C[hsp] == 0;
  St := 0;
  assert {:msg "24.15: Initialization might not establish the invariant (#0)"} (St == 0) || (St == 1);
}
procedure pulseShape#init#1()
  modifies C, R, M, I, H;
{
  var symb: Chan (bv8);
  var len: Chan (bv8);
  var done: Chan (bool);
  var hsp: Chan (bv8);
  var symb_mem: bv8;
  var body_iterations: bv8;
  var body_index: bv8;
  var FILT_COEFF0: bv8;
  var FILT_COEFF1: bv8;
  var FILT_COEFF2: bv8;
  var FILT_COEFF3: bv8;
  var FILT_COEFF4: bv8;
  var hsps: Map (int) (bv8);
  var St: int;
  var len#0: bv8;
  var symb#0: bv8;
  var symb#1: bv8;
  assume (symb != len) && (symb != hsp) && (len != hsp);
  assume 0 <= R[symb];
  assume 0 <= R[len];
  assume 0 <= C[done];
  assume 0 <= C[hsp];
  assume (St == 0) || (St == 1);
  len#0 := M[len][R[len]];
  R[len] := R[len] + 1;
  assume St == 0;
  body_iterations := AT#BvMul8(len#0, 32bv8);
  body_index := 0bv8;
  symb_mem := 127bv8;
  St := 1;
  assert {:msg "24.15: Action at 39.2 might not preserve invariant (#1)"} (St == 0) || (St == 1);
}
procedure pulseShape#tx_body#2()
  modifies C, R, M, I, H;
{
  var symb: Chan (bv8);
  var len: Chan (bv8);
  var done: Chan (bool);
  var hsp: Chan (bv8);
  var symb_mem: bv8;
  var body_iterations: bv8;
  var body_index: bv8;
  var FILT_COEFF0: bv8;
  var FILT_COEFF1: bv8;
  var FILT_COEFF2: bv8;
  var FILT_COEFF3: bv8;
  var FILT_COEFF4: bv8;
  var hsps: Map (int) (bv8);
  var St: int;
  var len#0: bv8;
  var symb#0: bv8;
  var symb#1: bv8;
  assume (symb != len) && (symb != hsp) && (len != hsp);
  assume 0 <= R[symb];
  assume 0 <= R[len];
  assume 0 <= C[done];
  assume 0 <= C[hsp];
  assume (St == 0) || (St == 1);
  symb#0 := M[symb][R[symb]];
  R[symb] := R[symb] + 1;
  symb#1 := M[symb][R[symb]];
  R[symb] := R[symb] + 1;
  assume (St == 1) && AT#BvUlt8(body_index, body_iterations);
  hsps := Map#Store(hsps, 0, pulseShape#mul8(FILT_COEFF0, symb#0));
  hsps := Map#Store(hsps, 1, pulseShape#mul8(FILT_COEFF4, symb_mem));
  hsps := Map#Store(hsps, 2, pulseShape#mul8(FILT_COEFF1, symb#0));
  hsps := Map#Store(hsps, 3, pulseShape#mul8(FILT_COEFF3, symb_mem));
  hsps := Map#Store(hsps, 4, pulseShape#mul8(FILT_COEFF2, symb#0));
  hsps := Map#Store(hsps, 5, pulseShape#mul8(FILT_COEFF2, symb_mem));
  hsps := Map#Store(hsps, 6, pulseShape#mul8(FILT_COEFF3, symb#0));
  hsps := Map#Store(hsps, 7, pulseShape#mul8(FILT_COEFF1, symb_mem));
  hsps := Map#Store(hsps, 8, pulseShape#mul8(FILT_COEFF4, symb#0));
  hsps := Map#Store(hsps, 9, pulseShape#mul8(FILT_COEFF0, symb#1));
  hsps := Map#Store(hsps, 10, pulseShape#mul8(FILT_COEFF3, symb#0));
  hsps := Map#Store(hsps, 11, pulseShape#mul8(FILT_COEFF1, symb#1));
  hsps := Map#Store(hsps, 12, pulseShape#mul8(FILT_COEFF2, symb#0));
  hsps := Map#Store(hsps, 13, pulseShape#mul8(FILT_COEFF2, symb#1));
  hsps := Map#Store(hsps, 14, pulseShape#mul8(FILT_COEFF1, symb#0));
  hsps := Map#Store(hsps, 15, pulseShape#mul8(FILT_COEFF3, symb#1));
  symb_mem := symb#1;
  body_index := AT#BvAdd8(body_index, 1bv8);
  St := 1;
  M[hsp][C[hsp]] := Map#Select(hsps, 0);
  C[hsp] := C[hsp] + 1;
  M[hsp][C[hsp]] := Map#Select(hsps, 1);
  C[hsp] := C[hsp] + 1;
  M[hsp][C[hsp]] := Map#Select(hsps, 2);
  C[hsp] := C[hsp] + 1;
  M[hsp][C[hsp]] := Map#Select(hsps, 3);
  C[hsp] := C[hsp] + 1;
  M[hsp][C[hsp]] := Map#Select(hsps, 4);
  C[hsp] := C[hsp] + 1;
  M[hsp][C[hsp]] := Map#Select(hsps, 5);
  C[hsp] := C[hsp] + 1;
  M[hsp][C[hsp]] := Map#Select(hsps, 6);
  C[hsp] := C[hsp] + 1;
  M[hsp][C[hsp]] := Map#Select(hsps, 7);
  C[hsp] := C[hsp] + 1;
  M[hsp][C[hsp]] := Map#Select(hsps, 8);
  C[hsp] := C[hsp] + 1;
  M[hsp][C[hsp]] := Map#Select(hsps, 9);
  C[hsp] := C[hsp] + 1;
  M[hsp][C[hsp]] := Map#Select(hsps, 10);
  C[hsp] := C[hsp] + 1;
  M[hsp][C[hsp]] := Map#Select(hsps, 11);
  C[hsp] := C[hsp] + 1;
  M[hsp][C[hsp]] := Map#Select(hsps, 12);
  C[hsp] := C[hsp] + 1;
  M[hsp][C[hsp]] := Map#Select(hsps, 13);
  C[hsp] := C[hsp] + 1;
  M[hsp][C[hsp]] := Map#Select(hsps, 14);
  C[hsp] := C[hsp] + 1;
  M[hsp][C[hsp]] := Map#Select(hsps, 15);
  C[hsp] := C[hsp] + 1;
  assert {:msg "24.15: Action at 50.2 might not preserve invariant (#2)"} (St == 0) || (St == 1);
}
procedure pulseShape#tx_tail#3()
  modifies C, R, M, I, H;
{
  var symb: Chan (bv8);
  var len: Chan (bv8);
  var done: Chan (bool);
  var hsp: Chan (bv8);
  var symb_mem: bv8;
  var body_iterations: bv8;
  var body_index: bv8;
  var FILT_COEFF0: bv8;
  var FILT_COEFF1: bv8;
  var FILT_COEFF2: bv8;
  var FILT_COEFF3: bv8;
  var FILT_COEFF4: bv8;
  var hsps: Map (int) (bv8);
  var St: int;
  var len#0: bv8;
  var symb#0: bv8;
  var symb#1: bv8;
  assume (symb != len) && (symb != hsp) && (len != hsp);
  assume 0 <= R[symb];
  assume 0 <= R[len];
  assume 0 <= C[done];
  assume 0 <= C[hsp];
  assume (St == 0) || (St == 1);
  assume (St == 1) && (body_index == body_iterations);
  hsps := Map#Store(hsps, 0, pulseShape#mul8(FILT_COEFF0, 127bv8));
  hsps := Map#Store(hsps, 1, pulseShape#mul8(FILT_COEFF4, symb_mem));
  hsps := Map#Store(hsps, 2, pulseShape#mul8(FILT_COEFF1, 127bv8));
  hsps := Map#Store(hsps, 3, pulseShape#mul8(FILT_COEFF3, symb_mem));
  hsps := Map#Store(hsps, 4, pulseShape#mul8(FILT_COEFF2, 127bv8));
  hsps := Map#Store(hsps, 5, pulseShape#mul8(FILT_COEFF2, symb_mem));
  hsps := Map#Store(hsps, 6, pulseShape#mul8(FILT_COEFF3, 127bv8));
  hsps := Map#Store(hsps, 7, pulseShape#mul8(FILT_COEFF1, symb_mem));
  St := 0;
  M[hsp][C[hsp]] := Map#Select(hsps, 0);
  C[hsp] := C[hsp] + 1;
  M[hsp][C[hsp]] := Map#Select(hsps, 1);
  C[hsp] := C[hsp] + 1;
  M[hsp][C[hsp]] := Map#Select(hsps, 2);
  C[hsp] := C[hsp] + 1;
  M[hsp][C[hsp]] := Map#Select(hsps, 3);
  C[hsp] := C[hsp] + 1;
  M[hsp][C[hsp]] := Map#Select(hsps, 4);
  C[hsp] := C[hsp] + 1;
  M[hsp][C[hsp]] := Map#Select(hsps, 5);
  C[hsp] := C[hsp] + 1;
  M[hsp][C[hsp]] := Map#Select(hsps, 6);
  C[hsp] := C[hsp] + 1;
  M[hsp][C[hsp]] := Map#Select(hsps, 7);
  C[hsp] := C[hsp] + 1;
  M[done][C[done]] := true;
  C[done] := C[done] + 1;
  assert {:msg "24.15: Action at 89.2 might not preserve invariant (#3)"} (St == 0) || (St == 1);
}
procedure pulseShape##GuardWD#4()
  modifies C, R, M, I, H;
{
  var symb: Chan (bv8);
  var len: Chan (bv8);
  var done: Chan (bool);
  var hsp: Chan (bv8);
  var symb_mem: bv8;
  var body_iterations: bv8;
  var body_index: bv8;
  var FILT_COEFF0: bv8;
  var FILT_COEFF1: bv8;
  var FILT_COEFF2: bv8;
  var FILT_COEFF3: bv8;
  var FILT_COEFF4: bv8;
  var hsps: Map (int) (bv8);
  var St: int;
  var len#0: bv8;
  var symb#0: bv8;
  var symb#1: bv8;
  assume (symb != len) && (symb != hsp) && (len != hsp);
  assert {:msg "1.1: The actions 'init' and 'tx_body' of actor 'pulseShape' might not have mutually exclusive guards (#4)"} !(true && (1 <= (C[len] - R[len])) && (St == 0) && true && (2 <= (C[symb] - R[symb])) && (St == 1) && AT#BvUlt8(body_index, body_iterations));
  assert {:msg "1.1: The actions 'init' and 'tx_tail' of actor 'pulseShape' might not have mutually exclusive guards (#5)"} !(true && (1 <= (C[len] - R[len])) && (St == 0) && true && true && (St == 1) && (body_index == body_iterations));
  assert {:msg "1.1: The actions 'tx_body' and 'tx_tail' of actor 'pulseShape' might not have mutually exclusive guards (#6)"} !(true && (2 <= (C[symb] - R[symb])) && (St == 1) && AT#BvUlt8(body_index, body_iterations) && true && true && (St == 1) && (body_index == body_iterations));
}

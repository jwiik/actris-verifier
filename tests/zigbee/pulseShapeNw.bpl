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
// Size: 14
function {:bvbuiltin "bvand"} AT#BvAnd14(a: bv14, b: bv14): bv14;
function {:bvbuiltin "bvor"} AT#BvOr14(a: bv14, b: bv14): bv14;
function {:bvbuiltin "bvnot"} AT#BvNot14(a: bv14): bv14;
function {:bvbuiltin "bvadd"} AT#BvAdd14(a: bv14, b: bv14): bv14;
function {:bvbuiltin "bvsub"} AT#BvSub14(a: bv14, b: bv14): bv14;
function {:bvbuiltin "bvmul"} AT#BvMul14(a: bv14, b: bv14): bv14;
function {:bvbuiltin "bvshl"} AT#BvShl14(bv14,bv14): bv14;
function {:bvbuiltin "bvlshr"} AT#BvLshr14(bv14,bv14): bv14;
function {:bvbuiltin "bvashr"} AT#BvAshr14(bv14,bv14): bv14;
function {:bvbuiltin "bvule"} AT#BvUle14(a: bv14, b: bv14): bool;
function {:bvbuiltin "bvult"} AT#BvUlt14(a: bv14, b: bv14): bool;
function {:bvbuiltin "bvuge"} AT#BvUge14(a: bv14, b: bv14): bool;
function {:bvbuiltin "bvugt"} AT#BvUgt14(a: bv14, b: bv14): bool;
function AT#BvXor14(a: bv14, b: bv14): bv14;

axiom (forall a,b: bv14 :: AT#BvXor14(a,b) == AT#BvAnd14(AT#BvOr14(a,b), AT#BvNot14(AT#BvAnd14(a,b))) );

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
// -- Bitvector to integer ---------------------------------------
// ---------------------------------------------------------------
// Size: 8
function AT#Bit0bv8(vec: bv8): bool { AT#BvAnd8(vec,1bv8) != 0bv8 }
function AT#Bit1bv8(vec: bv8): bool { AT#BvAnd8(vec,2bv8) != 0bv8 }
function AT#Bit2bv8(vec: bv8): bool { AT#BvAnd8(vec,4bv8) != 0bv8 }
function AT#Bit3bv8(vec: bv8): bool { AT#BvAnd8(vec,8bv8) != 0bv8 }
function AT#Bit4bv8(vec: bv8): bool { AT#BvAnd8(vec,16bv8) != 0bv8 }
function AT#Bit5bv8(vec: bv8): bool { AT#BvAnd8(vec,32bv8) != 0bv8 }
function AT#Bit6bv8(vec: bv8): bool { AT#BvAnd8(vec,64bv8) != 0bv8 }
function AT#Bit7bv8(vec: bv8): bool { AT#BvAnd8(vec,128bv8) != 0bv8 }

function AT#Bv2Int8(vec: bv8): int {
  (if AT#Bit0bv8(vec) then 1 else 0) +
  (if AT#Bit1bv8(vec) then 2 else 0) +
  (if AT#Bit2bv8(vec) then 4 else 0) +
  (if AT#Bit3bv8(vec) then 8 else 0) +
  (if AT#Bit4bv8(vec) then 16 else 0) +
  (if AT#Bit5bv8(vec) then 32 else 0) +
  (if AT#Bit6bv8(vec) then 64 else 0) +
  (if AT#Bit7bv8(vec) then 128 else 0)
}

// ---------------------------------------------------------------
// -- Bitvector to integer ---------------------------------------
// ---------------------------------------------------------------
// Size: 14
function AT#Bit0bv14(vec: bv14): bool { AT#BvAnd14(vec,1bv14) != 0bv14 }
function AT#Bit1bv14(vec: bv14): bool { AT#BvAnd14(vec,2bv14) != 0bv14 }
function AT#Bit2bv14(vec: bv14): bool { AT#BvAnd14(vec,4bv14) != 0bv14 }
function AT#Bit3bv14(vec: bv14): bool { AT#BvAnd14(vec,8bv14) != 0bv14 }
function AT#Bit4bv14(vec: bv14): bool { AT#BvAnd14(vec,16bv14) != 0bv14 }
function AT#Bit5bv14(vec: bv14): bool { AT#BvAnd14(vec,32bv14) != 0bv14 }
function AT#Bit6bv14(vec: bv14): bool { AT#BvAnd14(vec,64bv14) != 0bv14 }
function AT#Bit7bv14(vec: bv14): bool { AT#BvAnd14(vec,128bv14) != 0bv14 }
function AT#Bit8bv14(vec: bv14): bool { AT#BvAnd14(vec,256bv14) != 0bv14 }
function AT#Bit9bv14(vec: bv14): bool { AT#BvAnd14(vec,512bv14) != 0bv14 }
function AT#Bit10bv14(vec: bv14): bool { AT#BvAnd14(vec,1024bv14) != 0bv14 }
function AT#Bit11bv14(vec: bv14): bool { AT#BvAnd14(vec,2048bv14) != 0bv14 }
function AT#Bit12bv14(vec: bv14): bool { AT#BvAnd14(vec,4096bv14) != 0bv14 }
function AT#Bit13bv14(vec: bv14): bool { AT#BvAnd14(vec,8192bv14) != 0bv14 }

function AT#Bv2Int14(vec: bv14): int {
  (if AT#Bit0bv14(vec) then 1 else 0) +
  (if AT#Bit1bv14(vec) then 2 else 0) +
  (if AT#Bit2bv14(vec) then 4 else 0) +
  (if AT#Bit3bv14(vec) then 8 else 0) +
  (if AT#Bit4bv14(vec) then 16 else 0) +
  (if AT#Bit5bv14(vec) then 32 else 0) +
  (if AT#Bit6bv14(vec) then 64 else 0) +
  (if AT#Bit7bv14(vec) then 128 else 0) +
  (if AT#Bit8bv14(vec) then 256 else 0) +
  (if AT#Bit9bv14(vec) then 512 else 0) +
  (if AT#Bit10bv14(vec) then 1024 else 0) +
  (if AT#Bit11bv14(vec) then 2048 else 0) +
  (if AT#Bit12bv14(vec) then 4096 else 0) +
  (if AT#Bit13bv14(vec) then 8192 else 0)
}

// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

function pulseShape#mul8(x: bv8, y: bv8) returns (out: bv8);
procedure pulseShape#init#0()
  modifies C, R, M, I, H;
{
  var symb: Chan (bv8);
  var len: Chan (bv8);
  var body_iterations_in: Chan (bv14);
  var body_index_in: Chan (bv14);
  var St_in: Chan (int);
  var done: Chan (bool);
  var hsp: Chan (bv8);
  var body_iterations_out: Chan (bv14);
  var body_index_out: Chan (bv14);
  var St_out: Chan (int);
  var symb_mem: bv8;
  var body_iterations: bv8;
  var body_index: bv8;
  var FILT_COEFF0: bv8;
  var FILT_COEFF1: bv8;
  var FILT_COEFF2: bv8;
  var FILT_COEFF3: bv8;
  var FILT_COEFF4: bv8;
  var hsps: Map (int) (bv8);
  assume (symb != len) && (symb != hsp) && (len != hsp) && (body_iterations_in != body_index_in) && (body_iterations_in != body_iterations_out) && (body_iterations_in != body_index_out) && (body_index_in != body_iterations_out) && (body_index_in != body_index_out) && (St_in != St_out) && (body_iterations_out != body_index_out);
  assume R[symb] == 0;
  assume R[len] == 0;
  assume R[body_iterations_in] == 0;
  assume R[body_index_in] == 0;
  assume R[St_in] == 0;
  assume C[done] == 0;
  assume C[hsp] == 0;
  assume C[body_iterations_out] == 0;
  assume C[body_index_out] == 0;
  assume C[St_out] == 0;
  M[body_iterations_out][C[body_iterations_out]] := 0bv14;
  C[body_iterations_out] := C[body_iterations_out] + 1;
  M[body_index_out][C[body_index_out]] := 0bv14;
  C[body_index_out] := C[body_index_out] + 1;
  M[St_out][C[St_out]] := 0;
  C[St_out] := C[St_out] + 1;
}
procedure pulseShape#init#1()
  modifies C, R, M, I, H;
{
  var symb: Chan (bv8);
  var len: Chan (bv8);
  var body_iterations_in: Chan (bv14);
  var body_index_in: Chan (bv14);
  var St_in: Chan (int);
  var done: Chan (bool);
  var hsp: Chan (bv8);
  var body_iterations_out: Chan (bv14);
  var body_index_out: Chan (bv14);
  var St_out: Chan (int);
  var symb_mem: bv8;
  var body_iterations: bv8;
  var body_index: bv8;
  var FILT_COEFF0: bv8;
  var FILT_COEFF1: bv8;
  var FILT_COEFF2: bv8;
  var FILT_COEFF3: bv8;
  var FILT_COEFF4: bv8;
  var hsps: Map (int) (bv8);
  var body_index_in#0: bv14;
  var body_iterations_in#0: bv14;
  var symb#0: bv8;
  var St_in#0: int;
  var len#0: bv8;
  var symb#1: bv8;
  assume (symb != len) && (symb != hsp) && (len != hsp) && (body_iterations_in != body_index_in) && (body_iterations_in != body_iterations_out) && (body_iterations_in != body_index_out) && (body_index_in != body_iterations_out) && (body_index_in != body_index_out) && (St_in != St_out) && (body_iterations_out != body_index_out);
  assume 0 <= R[symb];
  assume 0 <= R[len];
  assume 0 <= R[body_iterations_in];
  assume 0 <= R[body_index_in];
  assume 0 <= R[St_in];
  assume 0 <= C[done];
  assume 0 <= C[hsp];
  assume 0 <= C[body_iterations_out];
  assume 0 <= C[body_index_out];
  assume 0 <= C[St_out];
  len#0 := M[len][R[len]];
  R[len] := R[len] + 1;
  body_iterations_in#0 := M[body_iterations_in][R[body_iterations_in]];
  R[body_iterations_in] := R[body_iterations_in] + 1;
  body_index_in#0 := M[body_index_in][R[body_index_in]];
  R[body_index_in] := R[body_index_in] + 1;
  St_in#0 := M[St_in][R[St_in]];
  R[St_in] := R[St_in] + 1;
  assume St_in#0 == 0;
  symb_mem := 127bv8;
  M[body_iterations_out][C[body_iterations_out]] := AT#BvMul14(0bv6 ++ len#0, 32bv14);
  C[body_iterations_out] := C[body_iterations_out] + 1;
  M[body_index_out][C[body_index_out]] := 0bv14;
  C[body_index_out] := C[body_index_out] + 1;
  M[St_out][C[St_out]] := 1;
  C[St_out] := C[St_out] + 1;
}
procedure pulseShape#tx_body#2()
  modifies C, R, M, I, H;
{
  var symb: Chan (bv8);
  var len: Chan (bv8);
  var body_iterations_in: Chan (bv14);
  var body_index_in: Chan (bv14);
  var St_in: Chan (int);
  var done: Chan (bool);
  var hsp: Chan (bv8);
  var body_iterations_out: Chan (bv14);
  var body_index_out: Chan (bv14);
  var St_out: Chan (int);
  var symb_mem: bv8;
  var body_iterations: bv8;
  var body_index: bv8;
  var FILT_COEFF0: bv8;
  var FILT_COEFF1: bv8;
  var FILT_COEFF2: bv8;
  var FILT_COEFF3: bv8;
  var FILT_COEFF4: bv8;
  var hsps: Map (int) (bv8);
  var body_index_in#0: bv14;
  var body_iterations_in#0: bv14;
  var symb#0: bv8;
  var St_in#0: int;
  var len#0: bv8;
  var symb#1: bv8;
  assume (symb != len) && (symb != hsp) && (len != hsp) && (body_iterations_in != body_index_in) && (body_iterations_in != body_iterations_out) && (body_iterations_in != body_index_out) && (body_index_in != body_iterations_out) && (body_index_in != body_index_out) && (St_in != St_out) && (body_iterations_out != body_index_out);
  assume 0 <= R[symb];
  assume 0 <= R[len];
  assume 0 <= R[body_iterations_in];
  assume 0 <= R[body_index_in];
  assume 0 <= R[St_in];
  assume 0 <= C[done];
  assume 0 <= C[hsp];
  assume 0 <= C[body_iterations_out];
  assume 0 <= C[body_index_out];
  assume 0 <= C[St_out];
  symb#0 := M[symb][R[symb]];
  R[symb] := R[symb] + 1;
  symb#1 := M[symb][R[symb]];
  R[symb] := R[symb] + 1;
  body_iterations_in#0 := M[body_iterations_in][R[body_iterations_in]];
  R[body_iterations_in] := R[body_iterations_in] + 1;
  body_index_in#0 := M[body_index_in][R[body_index_in]];
  R[body_index_in] := R[body_index_in] + 1;
  St_in#0 := M[St_in][R[St_in]];
  R[St_in] := R[St_in] + 1;
  assume (St_in#0 == 1) && AT#BvUlt14(body_index_in#0, body_iterations_in#0);
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
  M[body_iterations_out][C[body_iterations_out]] := body_iterations_in#0;
  C[body_iterations_out] := C[body_iterations_out] + 1;
  M[body_index_out][C[body_index_out]] := AT#BvAdd14(body_index_in#0, 1bv14);
  C[body_index_out] := C[body_index_out] + 1;
  M[St_out][C[St_out]] := 1;
  C[St_out] := C[St_out] + 1;
}
procedure pulseShape#tx_tail#3()
  modifies C, R, M, I, H;
{
  var symb: Chan (bv8);
  var len: Chan (bv8);
  var body_iterations_in: Chan (bv14);
  var body_index_in: Chan (bv14);
  var St_in: Chan (int);
  var done: Chan (bool);
  var hsp: Chan (bv8);
  var body_iterations_out: Chan (bv14);
  var body_index_out: Chan (bv14);
  var St_out: Chan (int);
  var symb_mem: bv8;
  var body_iterations: bv8;
  var body_index: bv8;
  var FILT_COEFF0: bv8;
  var FILT_COEFF1: bv8;
  var FILT_COEFF2: bv8;
  var FILT_COEFF3: bv8;
  var FILT_COEFF4: bv8;
  var hsps: Map (int) (bv8);
  var body_index_in#0: bv14;
  var body_iterations_in#0: bv14;
  var symb#0: bv8;
  var St_in#0: int;
  var len#0: bv8;
  var symb#1: bv8;
  assume (symb != len) && (symb != hsp) && (len != hsp) && (body_iterations_in != body_index_in) && (body_iterations_in != body_iterations_out) && (body_iterations_in != body_index_out) && (body_index_in != body_iterations_out) && (body_index_in != body_index_out) && (St_in != St_out) && (body_iterations_out != body_index_out);
  assume 0 <= R[symb];
  assume 0 <= R[len];
  assume 0 <= R[body_iterations_in];
  assume 0 <= R[body_index_in];
  assume 0 <= R[St_in];
  assume 0 <= C[done];
  assume 0 <= C[hsp];
  assume 0 <= C[body_iterations_out];
  assume 0 <= C[body_index_out];
  assume 0 <= C[St_out];
  body_iterations_in#0 := M[body_iterations_in][R[body_iterations_in]];
  R[body_iterations_in] := R[body_iterations_in] + 1;
  body_index_in#0 := M[body_index_in][R[body_index_in]];
  R[body_index_in] := R[body_index_in] + 1;
  St_in#0 := M[St_in][R[St_in]];
  R[St_in] := R[St_in] + 1;
  assume (St_in#0 == 1) && (body_index_in#0 == body_iterations_in#0);
  hsps := Map#Store(hsps, 0, pulseShape#mul8(FILT_COEFF0, 127bv8));
  hsps := Map#Store(hsps, 1, pulseShape#mul8(FILT_COEFF4, symb_mem));
  hsps := Map#Store(hsps, 2, pulseShape#mul8(FILT_COEFF1, 127bv8));
  hsps := Map#Store(hsps, 3, pulseShape#mul8(FILT_COEFF3, symb_mem));
  hsps := Map#Store(hsps, 4, pulseShape#mul8(FILT_COEFF2, 127bv8));
  hsps := Map#Store(hsps, 5, pulseShape#mul8(FILT_COEFF2, symb_mem));
  hsps := Map#Store(hsps, 6, pulseShape#mul8(FILT_COEFF3, 127bv8));
  hsps := Map#Store(hsps, 7, pulseShape#mul8(FILT_COEFF1, symb_mem));
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
  M[body_iterations_out][C[body_iterations_out]] := body_iterations_in#0;
  C[body_iterations_out] := C[body_iterations_out] + 1;
  M[body_index_out][C[body_index_out]] := body_index_in#0;
  C[body_index_out] := C[body_index_out] + 1;
  M[St_out][C[St_out]] := 0;
  C[St_out] := C[St_out] + 1;
}
procedure pulseShape##GuardWD#4()
  modifies C, R, M, I, H;
{
  var symb: Chan (bv8);
  var len: Chan (bv8);
  var body_iterations_in: Chan (bv14);
  var body_index_in: Chan (bv14);
  var St_in: Chan (int);
  var done: Chan (bool);
  var hsp: Chan (bv8);
  var body_iterations_out: Chan (bv14);
  var body_index_out: Chan (bv14);
  var St_out: Chan (int);
  var symb_mem: bv8;
  var body_iterations: bv8;
  var body_index: bv8;
  var FILT_COEFF0: bv8;
  var FILT_COEFF1: bv8;
  var FILT_COEFF2: bv8;
  var FILT_COEFF3: bv8;
  var FILT_COEFF4: bv8;
  var hsps: Map (int) (bv8);
  var body_index_in#0: bv14;
  var len#0: bv8;
  var St_in#0: int;
  var symb#1: bv8;
  var symb#0: bv8;
  var body_iterations_in#0: bv14;
  assume (symb != len) && (symb != hsp) && (len != hsp) && (body_iterations_in != body_index_in) && (body_iterations_in != body_iterations_out) && (body_iterations_in != body_index_out) && (body_index_in != body_iterations_out) && (body_index_in != body_index_out) && (St_in != St_out) && (body_iterations_out != body_index_out);
  assert {:msg "pulseShapeNw.actor(1.1): The actions 'init' and 'tx_body' of actor 'pulseShape' might not have mutually exclusive guards (#0)"} !(true && (1 <= (C[len] - R[len])) && (1 <= (C[body_iterations_in] - R[body_iterations_in])) && (1 <= (C[body_index_in] - R[body_index_in])) && (1 <= (C[St_in] - R[St_in])) && (St_in#0 == 0) && true && (2 <= (C[symb] - R[symb])) && (1 <= (C[body_iterations_in] - R[body_iterations_in])) && (1 <= (C[body_index_in] - R[body_index_in])) && (1 <= (C[St_in] - R[St_in])) && (St_in#0 == 1) && AT#BvUlt14(body_index_in#0, body_iterations_in#0));
  assert {:msg "pulseShapeNw.actor(1.1): The actions 'init' and 'tx_tail' of actor 'pulseShape' might not have mutually exclusive guards (#1)"} !(true && (1 <= (C[len] - R[len])) && (1 <= (C[body_iterations_in] - R[body_iterations_in])) && (1 <= (C[body_index_in] - R[body_index_in])) && (1 <= (C[St_in] - R[St_in])) && (St_in#0 == 0) && true && (1 <= (C[body_iterations_in] - R[body_iterations_in])) && (1 <= (C[body_index_in] - R[body_index_in])) && (1 <= (C[St_in] - R[St_in])) && (St_in#0 == 1) && (body_index_in#0 == body_iterations_in#0));
  assert {:msg "pulseShapeNw.actor(1.1): The actions 'tx_body' and 'tx_tail' of actor 'pulseShape' might not have mutually exclusive guards (#2)"} !(true && (2 <= (C[symb] - R[symb])) && (1 <= (C[body_iterations_in] - R[body_iterations_in])) && (1 <= (C[body_index_in] - R[body_index_in])) && (1 <= (C[St_in] - R[St_in])) && (St_in#0 == 1) && AT#BvUlt14(body_index_in#0, body_iterations_in#0) && true && (1 <= (C[body_iterations_in] - R[body_iterations_in])) && (1 <= (C[body_index_in] - R[body_index_in])) && (1 <= (C[St_in] - R[St_in])) && (St_in#0 == 1) && (body_index_in#0 == body_iterations_in#0));
}
procedure pulseShapeNw#init#5()
  modifies C, R, M, I, H;
{
  var pulseShapeNw#a: Actor;
  var pulseShapeNw#in_symb: Chan (bv8);
  var pulseShapeNw#in_len: Chan (bv8);
  var pulseShapeNw#body_iterations: Chan (bv14);
  var pulseShapeNw#body_index: Chan (bv14);
  var pulseShapeNw#St: Chan (int);
  var pulseShapeNw#out_hsp: Chan (bv8);
  var pulseShapeNw#out_done: Chan (bool);
  var AV#a#symb_mem: bv8;
  var AV#a#body_iterations: bv8;
  var AV#a#body_index: bv8;
  var AV#a#FILT_COEFF0: bv8;
  var AV#a#FILT_COEFF1: bv8;
  var AV#a#FILT_COEFF2: bv8;
  var AV#a#FILT_COEFF3: bv8;
  var AV#a#FILT_COEFF4: bv8;
  var AV#a#hsps: Map (int) (bv8);
  assume (pulseShapeNw#in_symb != pulseShapeNw#in_len) && (pulseShapeNw#in_symb != pulseShapeNw#out_hsp) && (pulseShapeNw#in_len != pulseShapeNw#out_hsp) && (pulseShapeNw#body_iterations != pulseShapeNw#body_index);
  assume 0 <= I[pulseShapeNw#in_symb];
  assume I[pulseShapeNw#in_symb] <= R[pulseShapeNw#in_symb];
  assume R[pulseShapeNw#in_symb] <= C[pulseShapeNw#in_symb];
  assume 0 <= I[pulseShapeNw#in_len];
  assume I[pulseShapeNw#in_len] <= R[pulseShapeNw#in_len];
  assume R[pulseShapeNw#in_len] <= C[pulseShapeNw#in_len];
  assume 0 <= I[pulseShapeNw#body_iterations];
  assume I[pulseShapeNw#body_iterations] <= R[pulseShapeNw#body_iterations];
  assume R[pulseShapeNw#body_iterations] <= C[pulseShapeNw#body_iterations];
  assume 0 <= I[pulseShapeNw#body_index];
  assume I[pulseShapeNw#body_index] <= R[pulseShapeNw#body_index];
  assume R[pulseShapeNw#body_index] <= C[pulseShapeNw#body_index];
  assume 0 <= I[pulseShapeNw#St];
  assume I[pulseShapeNw#St] <= R[pulseShapeNw#St];
  assume R[pulseShapeNw#St] <= C[pulseShapeNw#St];
  assume 0 <= I[pulseShapeNw#out_hsp];
  assume I[pulseShapeNw#out_hsp] <= R[pulseShapeNw#out_hsp];
  assume R[pulseShapeNw#out_hsp] <= C[pulseShapeNw#out_hsp];
  assume I[pulseShapeNw#out_hsp] == R[pulseShapeNw#out_hsp];
  assume 0 <= I[pulseShapeNw#out_done];
  assume I[pulseShapeNw#out_done] <= R[pulseShapeNw#out_done];
  assume R[pulseShapeNw#out_done] <= C[pulseShapeNw#out_done];
  assume I[pulseShapeNw#out_done] == R[pulseShapeNw#out_done];
  assume (B[pulseShapeNw#in_symb] == 576) && (B[pulseShapeNw#in_len] == 1) && (B[pulseShapeNw#out_done] == 1) && (B[pulseShapeNw#out_hsp] == 4616);
  assume C[pulseShapeNw#in_symb] == 0;
  assume R[pulseShapeNw#in_symb] == 0;
  assume C[pulseShapeNw#in_len] == 0;
  assume R[pulseShapeNw#in_len] == 0;
  assume C[pulseShapeNw#body_iterations] == 0;
  assume R[pulseShapeNw#body_iterations] == 0;
  assume C[pulseShapeNw#body_index] == 0;
  assume R[pulseShapeNw#body_index] == 0;
  assume C[pulseShapeNw#St] == 0;
  assume R[pulseShapeNw#St] == 0;
  assume C[pulseShapeNw#out_hsp] == 0;
  assume R[pulseShapeNw#out_hsp] == 0;
  assume C[pulseShapeNw#out_done] == 0;
  assume R[pulseShapeNw#out_done] == 0;
  M[pulseShapeNw#body_iterations][C[pulseShapeNw#body_iterations]] := 0bv14;
  C[pulseShapeNw#body_iterations] := C[pulseShapeNw#body_iterations] + 1;
  M[pulseShapeNw#body_index][C[pulseShapeNw#body_index]] := 0bv14;
  C[pulseShapeNw#body_index] := C[pulseShapeNw#body_index] + 1;
  M[pulseShapeNw#St][C[pulseShapeNw#St]] := 0;
  C[pulseShapeNw#St] := C[pulseShapeNw#St] + 1;
  assert {:msg "pulseShapeNw.actor(140.15): Initialization of network 'pulseShapeNw' might not establish the channel invariant (#3)"} I[pulseShapeNw#in_symb] == (576 * I[pulseShapeNw#out_done]);
  assert {:msg "pulseShapeNw.actor(141.15): Initialization of network 'pulseShapeNw' might not establish the channel invariant (#4)"} I[pulseShapeNw#in_len] == I[pulseShapeNw#out_done];
  assert {:msg "pulseShapeNw.actor(142.15): Initialization of network 'pulseShapeNw' might not establish the channel invariant (#5)"} I[pulseShapeNw#out_hsp] == (4616 * I[pulseShapeNw#in_len]);
  assert {:msg "pulseShapeNw.actor(147.15): Initialization of network 'pulseShapeNw' might not establish the channel invariant (#6)"} ((C[pulseShapeNw#body_iterations] - R[pulseShapeNw#body_iterations]) == 1) && ((C[pulseShapeNw#body_index] - R[pulseShapeNw#body_index]) == 1) && ((C[pulseShapeNw#St] - R[pulseShapeNw#St]) == 1);
  assert {:msg "pulseShapeNw.actor(150.15): Initialization of network 'pulseShapeNw' might not establish the channel invariant (#7)"} (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 0) || (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 1);
  assert {:msg "pulseShapeNw.actor(151.15): Initialization of network 'pulseShapeNw' might not establish the channel invariant (#8)"} AT#BvUle14(0bv14, M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]]) && AT#BvUle14(M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]], M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]]);
  assert {:msg "pulseShapeNw.actor(153.15): Initialization of network 'pulseShapeNw' might not establish the channel invariant (#9)"} ((C[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 1) ==> (B[pulseShapeNw#in_symb] == (64 * AT#Bv2Int8(M[pulseShapeNw#in_len][I[pulseShapeNw#in_len]])));
  assert {:msg "pulseShapeNw.actor(154.15): Initialization of network 'pulseShapeNw' might not establish the channel invariant (#10)"} ((R[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 1) ==> (M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]] == AT#BvMul14(0bv6 ++ M[pulseShapeNw#in_len][I[pulseShapeNw#in_len]], 32bv14)) && ((2 * AT#Bv2Int14(M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]])) == B[pulseShapeNw#in_symb]) && ((R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) == (2 * AT#Bv2Int14(M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]])));
  assert {:msg "pulseShapeNw.actor(160.15): Initialization of network 'pulseShapeNw' might not establish the channel invariant (#11)"} (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 1) ==> ((R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) == (2 * AT#Bv2Int14(M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]]))) && ((C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]) == (16 * AT#Bv2Int14(M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]]))) && ((16 * (R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb])) == (2 * (C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]))) && ((C[pulseShapeNw#out_done] - I[pulseShapeNw#out_done]) == 0) && ((R[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 1);
  assert {:msg "pulseShapeNw.actor(168.15): Initialization of network 'pulseShapeNw' might not establish the channel invariant (#12)"} (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 0) && ((R[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 1) ==> ((R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) == (2 * AT#Bv2Int14(M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]]))) && ((C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]) == ((16 * AT#Bv2Int14(M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]])) + 8)) && ((16 * (R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb])) == (2 * ((C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]) - 8))) && ((C[pulseShapeNw#out_done] - I[pulseShapeNw#out_done]) == 1);
  assert {:msg "pulseShapeNw.actor(175.15): Initialization of network 'pulseShapeNw' might not establish the channel invariant (#13)"} (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 0) && ((R[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 0) ==> ((R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) == 0) && ((C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]) == 0) && ((C[pulseShapeNw#out_done] - I[pulseShapeNw#out_done]) == 0);
  I := R;
  assert {:msg "pulseShapeNw.actor(145.13): Initialization of network 'pulseShapeNw' might not establish the network invariant (#14)"} ((C[pulseShapeNw#body_iterations] - R[pulseShapeNw#body_iterations]) == 1) && ((C[pulseShapeNw#body_index] - R[pulseShapeNw#body_index]) == 1) && ((C[pulseShapeNw#St] - R[pulseShapeNw#St]) == 1);
  assert {:msg "pulseShapeNw.actor(146.13): Initialization of network 'pulseShapeNw' might not establish the network invariant (#15)"} M[pulseShapeNw#St][R[pulseShapeNw#St]] == 0;
  assert {:msg "Initialization of network 'pulseShapeNw' might not establish the network invariant (#16)"} R[pulseShapeNw#in_symb] == (576 * C[pulseShapeNw#out_done]);
  assert {:msg "Initialization of network 'pulseShapeNw' might not establish the network invariant (#17)"} R[pulseShapeNw#in_len] == C[pulseShapeNw#out_done];
  assert {:msg "Initialization of network 'pulseShapeNw' might not establish the network invariant (#18)"} (4616 * R[pulseShapeNw#in_symb]) == (576 * C[pulseShapeNw#out_hsp]);
  assert {:msg "Initialization of network 'pulseShapeNw' might not establish the network invariant (#19)"} (4616 * R[pulseShapeNw#in_len]) == C[pulseShapeNw#out_hsp];
  assert {:msg "Initialization of network 'pulseShapeNw' might not establish the network invariant: Unread tokens might be left on channel in_symb (#20)"} (C[pulseShapeNw#in_symb] - R[pulseShapeNw#in_symb]) == 0;
  assert {:msg "Initialization of network 'pulseShapeNw' might not establish the network invariant: Unread tokens might be left on channel in_len (#21)"} (C[pulseShapeNw#in_len] - R[pulseShapeNw#in_len]) == 0;
  assert {:msg "Initialization of network 'pulseShapeNw' might not establish the network invariant: Unread tokens might be left on channel out_hsp (#22)"} (C[pulseShapeNw#out_hsp] - R[pulseShapeNw#out_hsp]) == 0;
  assert {:msg "Initialization of network 'pulseShapeNw' might not establish the network invariant: Unread tokens might be left on channel out_done (#23)"} (C[pulseShapeNw#out_done] - R[pulseShapeNw#out_done]) == 0;
}
procedure pulseShapeNw##pulseShape#init#6()
  modifies C, R, M, I, H;
{
  var pulseShapeNw#a: Actor;
  var pulseShapeNw#in_symb: Chan (bv8);
  var pulseShapeNw#in_len: Chan (bv8);
  var pulseShapeNw#body_iterations: Chan (bv14);
  var pulseShapeNw#body_index: Chan (bv14);
  var pulseShapeNw#St: Chan (int);
  var pulseShapeNw#out_hsp: Chan (bv8);
  var pulseShapeNw#out_done: Chan (bool);
  var AV#a#symb_mem: bv8;
  var AV#a#body_iterations: bv8;
  var AV#a#body_index: bv8;
  var AV#a#FILT_COEFF0: bv8;
  var AV#a#FILT_COEFF1: bv8;
  var AV#a#FILT_COEFF2: bv8;
  var AV#a#FILT_COEFF3: bv8;
  var AV#a#FILT_COEFF4: bv8;
  var AV#a#hsps: Map (int) (bv8);
  var len#len_in: bv8;
  var body_iterations_in#body_iterations: bv14;
  var body_index_in#body_index: bv14;
  var St_in#St: int;
  assume (pulseShapeNw#in_symb != pulseShapeNw#in_len) && (pulseShapeNw#in_symb != pulseShapeNw#out_hsp) && (pulseShapeNw#in_len != pulseShapeNw#out_hsp) && (pulseShapeNw#body_iterations != pulseShapeNw#body_index);
  assume 0 <= I[pulseShapeNw#in_symb];
  assume I[pulseShapeNw#in_symb] <= R[pulseShapeNw#in_symb];
  assume R[pulseShapeNw#in_symb] <= C[pulseShapeNw#in_symb];
  assume 0 <= I[pulseShapeNw#in_len];
  assume I[pulseShapeNw#in_len] <= R[pulseShapeNw#in_len];
  assume R[pulseShapeNw#in_len] <= C[pulseShapeNw#in_len];
  assume 0 <= I[pulseShapeNw#body_iterations];
  assume I[pulseShapeNw#body_iterations] <= R[pulseShapeNw#body_iterations];
  assume R[pulseShapeNw#body_iterations] <= C[pulseShapeNw#body_iterations];
  assume 0 <= I[pulseShapeNw#body_index];
  assume I[pulseShapeNw#body_index] <= R[pulseShapeNw#body_index];
  assume R[pulseShapeNw#body_index] <= C[pulseShapeNw#body_index];
  assume 0 <= I[pulseShapeNw#St];
  assume I[pulseShapeNw#St] <= R[pulseShapeNw#St];
  assume R[pulseShapeNw#St] <= C[pulseShapeNw#St];
  assume 0 <= I[pulseShapeNw#out_hsp];
  assume I[pulseShapeNw#out_hsp] <= R[pulseShapeNw#out_hsp];
  assume R[pulseShapeNw#out_hsp] <= C[pulseShapeNw#out_hsp];
  assume I[pulseShapeNw#out_hsp] == R[pulseShapeNw#out_hsp];
  assume 0 <= I[pulseShapeNw#out_done];
  assume I[pulseShapeNw#out_done] <= R[pulseShapeNw#out_done];
  assume R[pulseShapeNw#out_done] <= C[pulseShapeNw#out_done];
  assume I[pulseShapeNw#out_done] == R[pulseShapeNw#out_done];
  assume (B[pulseShapeNw#in_symb] == 576) && (B[pulseShapeNw#in_len] == 1) && (B[pulseShapeNw#out_done] == 1) && (B[pulseShapeNw#out_hsp] == 4616);
  assume I[pulseShapeNw#in_symb] == (576 * I[pulseShapeNw#out_done]);
  assume I[pulseShapeNw#in_len] == I[pulseShapeNw#out_done];
  assume I[pulseShapeNw#out_hsp] == (4616 * I[pulseShapeNw#in_len]);
  assume ((C[pulseShapeNw#body_iterations] - R[pulseShapeNw#body_iterations]) == 1) && ((C[pulseShapeNw#body_index] - R[pulseShapeNw#body_index]) == 1) && ((C[pulseShapeNw#St] - R[pulseShapeNw#St]) == 1);
  assume (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 0) || (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 1);
  assume AT#BvUle14(0bv14, M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]]) && AT#BvUle14(M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]], M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]]);
  assume ((C[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 1) ==> (B[pulseShapeNw#in_symb] == (64 * AT#Bv2Int8(M[pulseShapeNw#in_len][I[pulseShapeNw#in_len]])));
  assume ((R[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 1) ==> (M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]] == AT#BvMul14(0bv6 ++ M[pulseShapeNw#in_len][I[pulseShapeNw#in_len]], 32bv14)) && ((2 * AT#Bv2Int14(M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]])) == B[pulseShapeNw#in_symb]) && ((R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) == (2 * AT#Bv2Int14(M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]])));
  assume (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 1) ==> ((R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) == (2 * AT#Bv2Int14(M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]]))) && ((C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]) == (16 * AT#Bv2Int14(M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]]))) && ((16 * (R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb])) == (2 * (C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]))) && ((C[pulseShapeNw#out_done] - I[pulseShapeNw#out_done]) == 0) && ((R[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 1);
  assume (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 0) && ((R[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 1) ==> ((R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) == (2 * AT#Bv2Int14(M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]]))) && ((C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]) == ((16 * AT#Bv2Int14(M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]])) + 8)) && ((16 * (R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb])) == (2 * ((C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]) - 8))) && ((C[pulseShapeNw#out_done] - I[pulseShapeNw#out_done]) == 1);
  assume (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 0) && ((R[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 0) ==> ((R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) == 0) && ((C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]) == 0) && ((C[pulseShapeNw#out_done] - I[pulseShapeNw#out_done]) == 0);
  assume M[pulseShapeNw#in_len][I[pulseShapeNw#in_len]] == 9bv8;
  assume ((C[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) <= 576) && ((C[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) <= 1);
  assume (1 <= (C[pulseShapeNw#in_len] - R[pulseShapeNw#in_len])) && (1 <= (C[pulseShapeNw#body_iterations] - R[pulseShapeNw#body_iterations])) && (1 <= (C[pulseShapeNw#body_index] - R[pulseShapeNw#body_index])) && (1 <= (C[pulseShapeNw#St] - R[pulseShapeNw#St])) && (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 0);
  len#len_in := M[pulseShapeNw#in_len][R[pulseShapeNw#in_len]];
  R[pulseShapeNw#in_len] := R[pulseShapeNw#in_len] + 1;
  body_iterations_in#body_iterations := M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]];
  R[pulseShapeNw#body_iterations] := R[pulseShapeNw#body_iterations] + 1;
  body_index_in#body_index := M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]];
  R[pulseShapeNw#body_index] := R[pulseShapeNw#body_index] + 1;
  St_in#St := M[pulseShapeNw#St][R[pulseShapeNw#St]];
  R[pulseShapeNw#St] := R[pulseShapeNw#St] + 1;
  havoc AV#a#symb_mem;
  M[pulseShapeNw#body_iterations][C[pulseShapeNw#body_iterations]] := AT#BvMul14(0bv6 ++ len#len_in, 32bv14);
  C[pulseShapeNw#body_iterations] := C[pulseShapeNw#body_iterations] + 1;
  M[pulseShapeNw#body_index][C[pulseShapeNw#body_index]] := 0bv14;
  C[pulseShapeNw#body_index] := C[pulseShapeNw#body_index] + 1;
  M[pulseShapeNw#St][C[pulseShapeNw#St]] := 1;
  C[pulseShapeNw#St] := C[pulseShapeNw#St] + 1;
  assert {:msg "pulseShapeNw.actor(140.15): Action at pulseShapeNw.actor(44.2) ('init') for actor instance 'a' might not preserve the channel invariant (#24)"} I[pulseShapeNw#in_symb] == (576 * I[pulseShapeNw#out_done]);
  assert {:msg "pulseShapeNw.actor(141.15): Action at pulseShapeNw.actor(44.2) ('init') for actor instance 'a' might not preserve the channel invariant (#25)"} I[pulseShapeNw#in_len] == I[pulseShapeNw#out_done];
  assert {:msg "pulseShapeNw.actor(142.15): Action at pulseShapeNw.actor(44.2) ('init') for actor instance 'a' might not preserve the channel invariant (#26)"} I[pulseShapeNw#out_hsp] == (4616 * I[pulseShapeNw#in_len]);
  assert {:msg "pulseShapeNw.actor(147.15): Action at pulseShapeNw.actor(44.2) ('init') for actor instance 'a' might not preserve the channel invariant (#27)"} ((C[pulseShapeNw#body_iterations] - R[pulseShapeNw#body_iterations]) == 1) && ((C[pulseShapeNw#body_index] - R[pulseShapeNw#body_index]) == 1) && ((C[pulseShapeNw#St] - R[pulseShapeNw#St]) == 1);
  assert {:msg "pulseShapeNw.actor(150.15): Action at pulseShapeNw.actor(44.2) ('init') for actor instance 'a' might not preserve the channel invariant (#28)"} (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 0) || (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 1);
  assert {:msg "pulseShapeNw.actor(151.15): Action at pulseShapeNw.actor(44.2) ('init') for actor instance 'a' might not preserve the channel invariant (#29)"} AT#BvUle14(0bv14, M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]]) && AT#BvUle14(M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]], M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]]);
  assert {:msg "pulseShapeNw.actor(153.15): Action at pulseShapeNw.actor(44.2) ('init') for actor instance 'a' might not preserve the channel invariant (#30)"} ((C[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 1) ==> (B[pulseShapeNw#in_symb] == (64 * AT#Bv2Int8(M[pulseShapeNw#in_len][I[pulseShapeNw#in_len]])));
  assert {:msg "pulseShapeNw.actor(154.15): Action at pulseShapeNw.actor(44.2) ('init') for actor instance 'a' might not preserve the channel invariant (#31)"} ((R[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 1) ==> (M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]] == AT#BvMul14(0bv6 ++ M[pulseShapeNw#in_len][I[pulseShapeNw#in_len]], 32bv14)) && ((2 * AT#Bv2Int14(M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]])) == B[pulseShapeNw#in_symb]) && ((R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) == (2 * AT#Bv2Int14(M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]])));
  assert {:msg "pulseShapeNw.actor(160.15): Action at pulseShapeNw.actor(44.2) ('init') for actor instance 'a' might not preserve the channel invariant (#32)"} (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 1) ==> ((R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) == (2 * AT#Bv2Int14(M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]]))) && ((C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]) == (16 * AT#Bv2Int14(M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]]))) && ((16 * (R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb])) == (2 * (C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]))) && ((C[pulseShapeNw#out_done] - I[pulseShapeNw#out_done]) == 0) && ((R[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 1);
  assert {:msg "pulseShapeNw.actor(168.15): Action at pulseShapeNw.actor(44.2) ('init') for actor instance 'a' might not preserve the channel invariant (#33)"} (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 0) && ((R[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 1) ==> ((R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) == (2 * AT#Bv2Int14(M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]]))) && ((C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]) == ((16 * AT#Bv2Int14(M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]])) + 8)) && ((16 * (R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb])) == (2 * ((C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]) - 8))) && ((C[pulseShapeNw#out_done] - I[pulseShapeNw#out_done]) == 1);
  assert {:msg "pulseShapeNw.actor(175.15): Action at pulseShapeNw.actor(44.2) ('init') for actor instance 'a' might not preserve the channel invariant (#34)"} (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 0) && ((R[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 0) ==> ((R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) == 0) && ((C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]) == 0) && ((C[pulseShapeNw#out_done] - I[pulseShapeNw#out_done]) == 0);
}
procedure pulseShapeNw##pulseShape#tx_body#7()
  modifies C, R, M, I, H;
{
  var pulseShapeNw#a: Actor;
  var pulseShapeNw#in_symb: Chan (bv8);
  var pulseShapeNw#in_len: Chan (bv8);
  var pulseShapeNw#body_iterations: Chan (bv14);
  var pulseShapeNw#body_index: Chan (bv14);
  var pulseShapeNw#St: Chan (int);
  var pulseShapeNw#out_hsp: Chan (bv8);
  var pulseShapeNw#out_done: Chan (bool);
  var AV#a#symb_mem: bv8;
  var AV#a#body_iterations: bv8;
  var AV#a#body_index: bv8;
  var AV#a#FILT_COEFF0: bv8;
  var AV#a#FILT_COEFF1: bv8;
  var AV#a#FILT_COEFF2: bv8;
  var AV#a#FILT_COEFF3: bv8;
  var AV#a#FILT_COEFF4: bv8;
  var AV#a#hsps: Map (int) (bv8);
  var symb#symb_1: bv8;
  var symb#symb_2: bv8;
  var body_iterations_in#body_iterations: bv14;
  var body_index_in#body_index: bv14;
  var St_in#St: int;
  assume (pulseShapeNw#in_symb != pulseShapeNw#in_len) && (pulseShapeNw#in_symb != pulseShapeNw#out_hsp) && (pulseShapeNw#in_len != pulseShapeNw#out_hsp) && (pulseShapeNw#body_iterations != pulseShapeNw#body_index);
  assume 0 <= I[pulseShapeNw#in_symb];
  assume I[pulseShapeNw#in_symb] <= R[pulseShapeNw#in_symb];
  assume R[pulseShapeNw#in_symb] <= C[pulseShapeNw#in_symb];
  assume 0 <= I[pulseShapeNw#in_len];
  assume I[pulseShapeNw#in_len] <= R[pulseShapeNw#in_len];
  assume R[pulseShapeNw#in_len] <= C[pulseShapeNw#in_len];
  assume 0 <= I[pulseShapeNw#body_iterations];
  assume I[pulseShapeNw#body_iterations] <= R[pulseShapeNw#body_iterations];
  assume R[pulseShapeNw#body_iterations] <= C[pulseShapeNw#body_iterations];
  assume 0 <= I[pulseShapeNw#body_index];
  assume I[pulseShapeNw#body_index] <= R[pulseShapeNw#body_index];
  assume R[pulseShapeNw#body_index] <= C[pulseShapeNw#body_index];
  assume 0 <= I[pulseShapeNw#St];
  assume I[pulseShapeNw#St] <= R[pulseShapeNw#St];
  assume R[pulseShapeNw#St] <= C[pulseShapeNw#St];
  assume 0 <= I[pulseShapeNw#out_hsp];
  assume I[pulseShapeNw#out_hsp] <= R[pulseShapeNw#out_hsp];
  assume R[pulseShapeNw#out_hsp] <= C[pulseShapeNw#out_hsp];
  assume I[pulseShapeNw#out_hsp] == R[pulseShapeNw#out_hsp];
  assume 0 <= I[pulseShapeNw#out_done];
  assume I[pulseShapeNw#out_done] <= R[pulseShapeNw#out_done];
  assume R[pulseShapeNw#out_done] <= C[pulseShapeNw#out_done];
  assume I[pulseShapeNw#out_done] == R[pulseShapeNw#out_done];
  assume (B[pulseShapeNw#in_symb] == 576) && (B[pulseShapeNw#in_len] == 1) && (B[pulseShapeNw#out_done] == 1) && (B[pulseShapeNw#out_hsp] == 4616);
  assume I[pulseShapeNw#in_symb] == (576 * I[pulseShapeNw#out_done]);
  assume I[pulseShapeNw#in_len] == I[pulseShapeNw#out_done];
  assume I[pulseShapeNw#out_hsp] == (4616 * I[pulseShapeNw#in_len]);
  assume ((C[pulseShapeNw#body_iterations] - R[pulseShapeNw#body_iterations]) == 1) && ((C[pulseShapeNw#body_index] - R[pulseShapeNw#body_index]) == 1) && ((C[pulseShapeNw#St] - R[pulseShapeNw#St]) == 1);
  assume (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 0) || (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 1);
  assume AT#BvUle14(0bv14, M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]]) && AT#BvUle14(M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]], M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]]);
  assume ((C[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 1) ==> (B[pulseShapeNw#in_symb] == (64 * AT#Bv2Int8(M[pulseShapeNw#in_len][I[pulseShapeNw#in_len]])));
  assume ((R[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 1) ==> (M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]] == AT#BvMul14(0bv6 ++ M[pulseShapeNw#in_len][I[pulseShapeNw#in_len]], 32bv14)) && ((2 * AT#Bv2Int14(M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]])) == B[pulseShapeNw#in_symb]) && ((R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) == (2 * AT#Bv2Int14(M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]])));
  assume (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 1) ==> ((R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) == (2 * AT#Bv2Int14(M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]]))) && ((C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]) == (16 * AT#Bv2Int14(M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]]))) && ((16 * (R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb])) == (2 * (C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]))) && ((C[pulseShapeNw#out_done] - I[pulseShapeNw#out_done]) == 0) && ((R[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 1);
  assume (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 0) && ((R[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 1) ==> ((R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) == (2 * AT#Bv2Int14(M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]]))) && ((C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]) == ((16 * AT#Bv2Int14(M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]])) + 8)) && ((16 * (R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb])) == (2 * ((C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]) - 8))) && ((C[pulseShapeNw#out_done] - I[pulseShapeNw#out_done]) == 1);
  assume (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 0) && ((R[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 0) ==> ((R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) == 0) && ((C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]) == 0) && ((C[pulseShapeNw#out_done] - I[pulseShapeNw#out_done]) == 0);
  assume M[pulseShapeNw#in_len][I[pulseShapeNw#in_len]] == 9bv8;
  assume ((C[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) <= 576) && ((C[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) <= 1);
  assume (2 <= (C[pulseShapeNw#in_symb] - R[pulseShapeNw#in_symb])) && (1 <= (C[pulseShapeNw#body_iterations] - R[pulseShapeNw#body_iterations])) && (1 <= (C[pulseShapeNw#body_index] - R[pulseShapeNw#body_index])) && (1 <= (C[pulseShapeNw#St] - R[pulseShapeNw#St])) && (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 1) && AT#BvUlt14(M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]], M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]]);
  symb#symb_1 := M[pulseShapeNw#in_symb][R[pulseShapeNw#in_symb]];
  R[pulseShapeNw#in_symb] := R[pulseShapeNw#in_symb] + 1;
  symb#symb_2 := M[pulseShapeNw#in_symb][R[pulseShapeNw#in_symb]];
  R[pulseShapeNw#in_symb] := R[pulseShapeNw#in_symb] + 1;
  body_iterations_in#body_iterations := M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]];
  R[pulseShapeNw#body_iterations] := R[pulseShapeNw#body_iterations] + 1;
  body_index_in#body_index := M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]];
  R[pulseShapeNw#body_index] := R[pulseShapeNw#body_index] + 1;
  St_in#St := M[pulseShapeNw#St][R[pulseShapeNw#St]];
  R[pulseShapeNw#St] := R[pulseShapeNw#St] + 1;
  havoc AV#a#symb_mem;
  M[pulseShapeNw#out_hsp][C[pulseShapeNw#out_hsp]] := Map#Select(AV#a#hsps, 0);
  C[pulseShapeNw#out_hsp] := C[pulseShapeNw#out_hsp] + 1;
  M[pulseShapeNw#out_hsp][C[pulseShapeNw#out_hsp]] := Map#Select(AV#a#hsps, 1);
  C[pulseShapeNw#out_hsp] := C[pulseShapeNw#out_hsp] + 1;
  M[pulseShapeNw#out_hsp][C[pulseShapeNw#out_hsp]] := Map#Select(AV#a#hsps, 2);
  C[pulseShapeNw#out_hsp] := C[pulseShapeNw#out_hsp] + 1;
  M[pulseShapeNw#out_hsp][C[pulseShapeNw#out_hsp]] := Map#Select(AV#a#hsps, 3);
  C[pulseShapeNw#out_hsp] := C[pulseShapeNw#out_hsp] + 1;
  M[pulseShapeNw#out_hsp][C[pulseShapeNw#out_hsp]] := Map#Select(AV#a#hsps, 4);
  C[pulseShapeNw#out_hsp] := C[pulseShapeNw#out_hsp] + 1;
  M[pulseShapeNw#out_hsp][C[pulseShapeNw#out_hsp]] := Map#Select(AV#a#hsps, 5);
  C[pulseShapeNw#out_hsp] := C[pulseShapeNw#out_hsp] + 1;
  M[pulseShapeNw#out_hsp][C[pulseShapeNw#out_hsp]] := Map#Select(AV#a#hsps, 6);
  C[pulseShapeNw#out_hsp] := C[pulseShapeNw#out_hsp] + 1;
  M[pulseShapeNw#out_hsp][C[pulseShapeNw#out_hsp]] := Map#Select(AV#a#hsps, 7);
  C[pulseShapeNw#out_hsp] := C[pulseShapeNw#out_hsp] + 1;
  M[pulseShapeNw#out_hsp][C[pulseShapeNw#out_hsp]] := Map#Select(AV#a#hsps, 8);
  C[pulseShapeNw#out_hsp] := C[pulseShapeNw#out_hsp] + 1;
  M[pulseShapeNw#out_hsp][C[pulseShapeNw#out_hsp]] := Map#Select(AV#a#hsps, 9);
  C[pulseShapeNw#out_hsp] := C[pulseShapeNw#out_hsp] + 1;
  M[pulseShapeNw#out_hsp][C[pulseShapeNw#out_hsp]] := Map#Select(AV#a#hsps, 10);
  C[pulseShapeNw#out_hsp] := C[pulseShapeNw#out_hsp] + 1;
  M[pulseShapeNw#out_hsp][C[pulseShapeNw#out_hsp]] := Map#Select(AV#a#hsps, 11);
  C[pulseShapeNw#out_hsp] := C[pulseShapeNw#out_hsp] + 1;
  M[pulseShapeNw#out_hsp][C[pulseShapeNw#out_hsp]] := Map#Select(AV#a#hsps, 12);
  C[pulseShapeNw#out_hsp] := C[pulseShapeNw#out_hsp] + 1;
  M[pulseShapeNw#out_hsp][C[pulseShapeNw#out_hsp]] := Map#Select(AV#a#hsps, 13);
  C[pulseShapeNw#out_hsp] := C[pulseShapeNw#out_hsp] + 1;
  M[pulseShapeNw#out_hsp][C[pulseShapeNw#out_hsp]] := Map#Select(AV#a#hsps, 14);
  C[pulseShapeNw#out_hsp] := C[pulseShapeNw#out_hsp] + 1;
  M[pulseShapeNw#out_hsp][C[pulseShapeNw#out_hsp]] := Map#Select(AV#a#hsps, 15);
  C[pulseShapeNw#out_hsp] := C[pulseShapeNw#out_hsp] + 1;
  M[pulseShapeNw#body_iterations][C[pulseShapeNw#body_iterations]] := body_iterations_in#body_iterations;
  C[pulseShapeNw#body_iterations] := C[pulseShapeNw#body_iterations] + 1;
  M[pulseShapeNw#body_index][C[pulseShapeNw#body_index]] := AT#BvAdd14(body_index_in#body_index, 1bv14);
  C[pulseShapeNw#body_index] := C[pulseShapeNw#body_index] + 1;
  M[pulseShapeNw#St][C[pulseShapeNw#St]] := 1;
  C[pulseShapeNw#St] := C[pulseShapeNw#St] + 1;
  assert {:msg "pulseShapeNw.actor(140.15): Action at pulseShapeNw.actor(60.2) ('tx_body') for actor instance 'a' might not preserve the channel invariant (#35)"} I[pulseShapeNw#in_symb] == (576 * I[pulseShapeNw#out_done]);
  assert {:msg "pulseShapeNw.actor(141.15): Action at pulseShapeNw.actor(60.2) ('tx_body') for actor instance 'a' might not preserve the channel invariant (#36)"} I[pulseShapeNw#in_len] == I[pulseShapeNw#out_done];
  assert {:msg "pulseShapeNw.actor(142.15): Action at pulseShapeNw.actor(60.2) ('tx_body') for actor instance 'a' might not preserve the channel invariant (#37)"} I[pulseShapeNw#out_hsp] == (4616 * I[pulseShapeNw#in_len]);
  assert {:msg "pulseShapeNw.actor(147.15): Action at pulseShapeNw.actor(60.2) ('tx_body') for actor instance 'a' might not preserve the channel invariant (#38)"} ((C[pulseShapeNw#body_iterations] - R[pulseShapeNw#body_iterations]) == 1) && ((C[pulseShapeNw#body_index] - R[pulseShapeNw#body_index]) == 1) && ((C[pulseShapeNw#St] - R[pulseShapeNw#St]) == 1);
  assert {:msg "pulseShapeNw.actor(150.15): Action at pulseShapeNw.actor(60.2) ('tx_body') for actor instance 'a' might not preserve the channel invariant (#39)"} (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 0) || (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 1);
  assert {:msg "pulseShapeNw.actor(151.15): Action at pulseShapeNw.actor(60.2) ('tx_body') for actor instance 'a' might not preserve the channel invariant (#40)"} AT#BvUle14(0bv14, M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]]) && AT#BvUle14(M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]], M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]]);
  assert {:msg "pulseShapeNw.actor(153.15): Action at pulseShapeNw.actor(60.2) ('tx_body') for actor instance 'a' might not preserve the channel invariant (#41)"} ((C[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 1) ==> (B[pulseShapeNw#in_symb] == (64 * AT#Bv2Int8(M[pulseShapeNw#in_len][I[pulseShapeNw#in_len]])));
  assert {:msg "pulseShapeNw.actor(154.15): Action at pulseShapeNw.actor(60.2) ('tx_body') for actor instance 'a' might not preserve the channel invariant (#42)"} ((R[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 1) ==> (M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]] == AT#BvMul14(0bv6 ++ M[pulseShapeNw#in_len][I[pulseShapeNw#in_len]], 32bv14)) && ((2 * AT#Bv2Int14(M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]])) == B[pulseShapeNw#in_symb]) && ((R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) == (2 * AT#Bv2Int14(M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]])));
  assert {:msg "pulseShapeNw.actor(160.15): Action at pulseShapeNw.actor(60.2) ('tx_body') for actor instance 'a' might not preserve the channel invariant (#43)"} (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 1) ==> ((R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) == (2 * AT#Bv2Int14(M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]]))) && ((C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]) == (16 * AT#Bv2Int14(M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]]))) && ((16 * (R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb])) == (2 * (C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]))) && ((C[pulseShapeNw#out_done] - I[pulseShapeNw#out_done]) == 0) && ((R[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 1);
  assert {:msg "pulseShapeNw.actor(168.15): Action at pulseShapeNw.actor(60.2) ('tx_body') for actor instance 'a' might not preserve the channel invariant (#44)"} (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 0) && ((R[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 1) ==> ((R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) == (2 * AT#Bv2Int14(M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]]))) && ((C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]) == ((16 * AT#Bv2Int14(M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]])) + 8)) && ((16 * (R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb])) == (2 * ((C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]) - 8))) && ((C[pulseShapeNw#out_done] - I[pulseShapeNw#out_done]) == 1);
  assert {:msg "pulseShapeNw.actor(175.15): Action at pulseShapeNw.actor(60.2) ('tx_body') for actor instance 'a' might not preserve the channel invariant (#45)"} (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 0) && ((R[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 0) ==> ((R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) == 0) && ((C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]) == 0) && ((C[pulseShapeNw#out_done] - I[pulseShapeNw#out_done]) == 0);
}
procedure pulseShapeNw##pulseShape#tx_tail#8()
  modifies C, R, M, I, H;
{
  var pulseShapeNw#a: Actor;
  var pulseShapeNw#in_symb: Chan (bv8);
  var pulseShapeNw#in_len: Chan (bv8);
  var pulseShapeNw#body_iterations: Chan (bv14);
  var pulseShapeNw#body_index: Chan (bv14);
  var pulseShapeNw#St: Chan (int);
  var pulseShapeNw#out_hsp: Chan (bv8);
  var pulseShapeNw#out_done: Chan (bool);
  var AV#a#symb_mem: bv8;
  var AV#a#body_iterations: bv8;
  var AV#a#body_index: bv8;
  var AV#a#FILT_COEFF0: bv8;
  var AV#a#FILT_COEFF1: bv8;
  var AV#a#FILT_COEFF2: bv8;
  var AV#a#FILT_COEFF3: bv8;
  var AV#a#FILT_COEFF4: bv8;
  var AV#a#hsps: Map (int) (bv8);
  var body_iterations_in#body_iterations: bv14;
  var body_index_in#body_index: bv14;
  var St_in#St: int;
  assume (pulseShapeNw#in_symb != pulseShapeNw#in_len) && (pulseShapeNw#in_symb != pulseShapeNw#out_hsp) && (pulseShapeNw#in_len != pulseShapeNw#out_hsp) && (pulseShapeNw#body_iterations != pulseShapeNw#body_index);
  assume 0 <= I[pulseShapeNw#in_symb];
  assume I[pulseShapeNw#in_symb] <= R[pulseShapeNw#in_symb];
  assume R[pulseShapeNw#in_symb] <= C[pulseShapeNw#in_symb];
  assume 0 <= I[pulseShapeNw#in_len];
  assume I[pulseShapeNw#in_len] <= R[pulseShapeNw#in_len];
  assume R[pulseShapeNw#in_len] <= C[pulseShapeNw#in_len];
  assume 0 <= I[pulseShapeNw#body_iterations];
  assume I[pulseShapeNw#body_iterations] <= R[pulseShapeNw#body_iterations];
  assume R[pulseShapeNw#body_iterations] <= C[pulseShapeNw#body_iterations];
  assume 0 <= I[pulseShapeNw#body_index];
  assume I[pulseShapeNw#body_index] <= R[pulseShapeNw#body_index];
  assume R[pulseShapeNw#body_index] <= C[pulseShapeNw#body_index];
  assume 0 <= I[pulseShapeNw#St];
  assume I[pulseShapeNw#St] <= R[pulseShapeNw#St];
  assume R[pulseShapeNw#St] <= C[pulseShapeNw#St];
  assume 0 <= I[pulseShapeNw#out_hsp];
  assume I[pulseShapeNw#out_hsp] <= R[pulseShapeNw#out_hsp];
  assume R[pulseShapeNw#out_hsp] <= C[pulseShapeNw#out_hsp];
  assume I[pulseShapeNw#out_hsp] == R[pulseShapeNw#out_hsp];
  assume 0 <= I[pulseShapeNw#out_done];
  assume I[pulseShapeNw#out_done] <= R[pulseShapeNw#out_done];
  assume R[pulseShapeNw#out_done] <= C[pulseShapeNw#out_done];
  assume I[pulseShapeNw#out_done] == R[pulseShapeNw#out_done];
  assume (B[pulseShapeNw#in_symb] == 576) && (B[pulseShapeNw#in_len] == 1) && (B[pulseShapeNw#out_done] == 1) && (B[pulseShapeNw#out_hsp] == 4616);
  assume I[pulseShapeNw#in_symb] == (576 * I[pulseShapeNw#out_done]);
  assume I[pulseShapeNw#in_len] == I[pulseShapeNw#out_done];
  assume I[pulseShapeNw#out_hsp] == (4616 * I[pulseShapeNw#in_len]);
  assume ((C[pulseShapeNw#body_iterations] - R[pulseShapeNw#body_iterations]) == 1) && ((C[pulseShapeNw#body_index] - R[pulseShapeNw#body_index]) == 1) && ((C[pulseShapeNw#St] - R[pulseShapeNw#St]) == 1);
  assume (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 0) || (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 1);
  assume AT#BvUle14(0bv14, M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]]) && AT#BvUle14(M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]], M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]]);
  assume ((C[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 1) ==> (B[pulseShapeNw#in_symb] == (64 * AT#Bv2Int8(M[pulseShapeNw#in_len][I[pulseShapeNw#in_len]])));
  assume ((R[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 1) ==> (M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]] == AT#BvMul14(0bv6 ++ M[pulseShapeNw#in_len][I[pulseShapeNw#in_len]], 32bv14)) && ((2 * AT#Bv2Int14(M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]])) == B[pulseShapeNw#in_symb]) && ((R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) == (2 * AT#Bv2Int14(M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]])));
  assume (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 1) ==> ((R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) == (2 * AT#Bv2Int14(M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]]))) && ((C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]) == (16 * AT#Bv2Int14(M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]]))) && ((16 * (R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb])) == (2 * (C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]))) && ((C[pulseShapeNw#out_done] - I[pulseShapeNw#out_done]) == 0) && ((R[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 1);
  assume (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 0) && ((R[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 1) ==> ((R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) == (2 * AT#Bv2Int14(M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]]))) && ((C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]) == ((16 * AT#Bv2Int14(M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]])) + 8)) && ((16 * (R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb])) == (2 * ((C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]) - 8))) && ((C[pulseShapeNw#out_done] - I[pulseShapeNw#out_done]) == 1);
  assume (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 0) && ((R[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 0) ==> ((R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) == 0) && ((C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]) == 0) && ((C[pulseShapeNw#out_done] - I[pulseShapeNw#out_done]) == 0);
  assume M[pulseShapeNw#in_len][I[pulseShapeNw#in_len]] == 9bv8;
  assume ((C[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) <= 576) && ((C[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) <= 1);
  assume (1 <= (C[pulseShapeNw#body_iterations] - R[pulseShapeNw#body_iterations])) && (1 <= (C[pulseShapeNw#body_index] - R[pulseShapeNw#body_index])) && (1 <= (C[pulseShapeNw#St] - R[pulseShapeNw#St])) && (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 1) && (M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]] == M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]]);
  body_iterations_in#body_iterations := M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]];
  R[pulseShapeNw#body_iterations] := R[pulseShapeNw#body_iterations] + 1;
  body_index_in#body_index := M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]];
  R[pulseShapeNw#body_index] := R[pulseShapeNw#body_index] + 1;
  St_in#St := M[pulseShapeNw#St][R[pulseShapeNw#St]];
  R[pulseShapeNw#St] := R[pulseShapeNw#St] + 1;
  M[pulseShapeNw#out_hsp][C[pulseShapeNw#out_hsp]] := Map#Select(AV#a#hsps, 0);
  C[pulseShapeNw#out_hsp] := C[pulseShapeNw#out_hsp] + 1;
  M[pulseShapeNw#out_hsp][C[pulseShapeNw#out_hsp]] := Map#Select(AV#a#hsps, 1);
  C[pulseShapeNw#out_hsp] := C[pulseShapeNw#out_hsp] + 1;
  M[pulseShapeNw#out_hsp][C[pulseShapeNw#out_hsp]] := Map#Select(AV#a#hsps, 2);
  C[pulseShapeNw#out_hsp] := C[pulseShapeNw#out_hsp] + 1;
  M[pulseShapeNw#out_hsp][C[pulseShapeNw#out_hsp]] := Map#Select(AV#a#hsps, 3);
  C[pulseShapeNw#out_hsp] := C[pulseShapeNw#out_hsp] + 1;
  M[pulseShapeNw#out_hsp][C[pulseShapeNw#out_hsp]] := Map#Select(AV#a#hsps, 4);
  C[pulseShapeNw#out_hsp] := C[pulseShapeNw#out_hsp] + 1;
  M[pulseShapeNw#out_hsp][C[pulseShapeNw#out_hsp]] := Map#Select(AV#a#hsps, 5);
  C[pulseShapeNw#out_hsp] := C[pulseShapeNw#out_hsp] + 1;
  M[pulseShapeNw#out_hsp][C[pulseShapeNw#out_hsp]] := Map#Select(AV#a#hsps, 6);
  C[pulseShapeNw#out_hsp] := C[pulseShapeNw#out_hsp] + 1;
  M[pulseShapeNw#out_hsp][C[pulseShapeNw#out_hsp]] := Map#Select(AV#a#hsps, 7);
  C[pulseShapeNw#out_hsp] := C[pulseShapeNw#out_hsp] + 1;
  M[pulseShapeNw#out_done][C[pulseShapeNw#out_done]] := true;
  C[pulseShapeNw#out_done] := C[pulseShapeNw#out_done] + 1;
  M[pulseShapeNw#body_iterations][C[pulseShapeNw#body_iterations]] := body_iterations_in#body_iterations;
  C[pulseShapeNw#body_iterations] := C[pulseShapeNw#body_iterations] + 1;
  M[pulseShapeNw#body_index][C[pulseShapeNw#body_index]] := body_index_in#body_index;
  C[pulseShapeNw#body_index] := C[pulseShapeNw#body_index] + 1;
  M[pulseShapeNw#St][C[pulseShapeNw#St]] := 0;
  C[pulseShapeNw#St] := C[pulseShapeNw#St] + 1;
  assert {:msg "pulseShapeNw.actor(140.15): Action at pulseShapeNw.actor(104.2) ('tx_tail') for actor instance 'a' might not preserve the channel invariant (#46)"} I[pulseShapeNw#in_symb] == (576 * I[pulseShapeNw#out_done]);
  assert {:msg "pulseShapeNw.actor(141.15): Action at pulseShapeNw.actor(104.2) ('tx_tail') for actor instance 'a' might not preserve the channel invariant (#47)"} I[pulseShapeNw#in_len] == I[pulseShapeNw#out_done];
  assert {:msg "pulseShapeNw.actor(142.15): Action at pulseShapeNw.actor(104.2) ('tx_tail') for actor instance 'a' might not preserve the channel invariant (#48)"} I[pulseShapeNw#out_hsp] == (4616 * I[pulseShapeNw#in_len]);
  assert {:msg "pulseShapeNw.actor(147.15): Action at pulseShapeNw.actor(104.2) ('tx_tail') for actor instance 'a' might not preserve the channel invariant (#49)"} ((C[pulseShapeNw#body_iterations] - R[pulseShapeNw#body_iterations]) == 1) && ((C[pulseShapeNw#body_index] - R[pulseShapeNw#body_index]) == 1) && ((C[pulseShapeNw#St] - R[pulseShapeNw#St]) == 1);
  assert {:msg "pulseShapeNw.actor(150.15): Action at pulseShapeNw.actor(104.2) ('tx_tail') for actor instance 'a' might not preserve the channel invariant (#50)"} (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 0) || (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 1);
  assert {:msg "pulseShapeNw.actor(151.15): Action at pulseShapeNw.actor(104.2) ('tx_tail') for actor instance 'a' might not preserve the channel invariant (#51)"} AT#BvUle14(0bv14, M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]]) && AT#BvUle14(M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]], M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]]);
  assert {:msg "pulseShapeNw.actor(153.15): Action at pulseShapeNw.actor(104.2) ('tx_tail') for actor instance 'a' might not preserve the channel invariant (#52)"} ((C[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 1) ==> (B[pulseShapeNw#in_symb] == (64 * AT#Bv2Int8(M[pulseShapeNw#in_len][I[pulseShapeNw#in_len]])));
  assert {:msg "pulseShapeNw.actor(154.15): Action at pulseShapeNw.actor(104.2) ('tx_tail') for actor instance 'a' might not preserve the channel invariant (#53)"} ((R[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 1) ==> (M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]] == AT#BvMul14(0bv6 ++ M[pulseShapeNw#in_len][I[pulseShapeNw#in_len]], 32bv14)) && ((2 * AT#Bv2Int14(M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]])) == B[pulseShapeNw#in_symb]) && ((R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) == (2 * AT#Bv2Int14(M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]])));
  assert {:msg "pulseShapeNw.actor(160.15): Action at pulseShapeNw.actor(104.2) ('tx_tail') for actor instance 'a' might not preserve the channel invariant (#54)"} (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 1) ==> ((R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) == (2 * AT#Bv2Int14(M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]]))) && ((C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]) == (16 * AT#Bv2Int14(M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]]))) && ((16 * (R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb])) == (2 * (C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]))) && ((C[pulseShapeNw#out_done] - I[pulseShapeNw#out_done]) == 0) && ((R[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 1);
  assert {:msg "pulseShapeNw.actor(168.15): Action at pulseShapeNw.actor(104.2) ('tx_tail') for actor instance 'a' might not preserve the channel invariant (#55)"} (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 0) && ((R[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 1) ==> ((R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) == (2 * AT#Bv2Int14(M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]]))) && ((C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]) == ((16 * AT#Bv2Int14(M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]])) + 8)) && ((16 * (R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb])) == (2 * ((C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]) - 8))) && ((C[pulseShapeNw#out_done] - I[pulseShapeNw#out_done]) == 1);
  assert {:msg "pulseShapeNw.actor(175.15): Action at pulseShapeNw.actor(104.2) ('tx_tail') for actor instance 'a' might not preserve the channel invariant (#56)"} (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 0) && ((R[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 0) ==> ((R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) == 0) && ((C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]) == 0) && ((C[pulseShapeNw#out_done] - I[pulseShapeNw#out_done]) == 0);
}
procedure pulseShapeNw#anon$1#input#symb#9()
  modifies C, R, M, I, H;
{
  var pulseShapeNw#a: Actor;
  var pulseShapeNw#in_symb: Chan (bv8);
  var pulseShapeNw#in_len: Chan (bv8);
  var pulseShapeNw#body_iterations: Chan (bv14);
  var pulseShapeNw#body_index: Chan (bv14);
  var pulseShapeNw#St: Chan (int);
  var pulseShapeNw#out_hsp: Chan (bv8);
  var pulseShapeNw#out_done: Chan (bool);
  var AV#a#symb_mem: bv8;
  var AV#a#body_iterations: bv8;
  var AV#a#body_index: bv8;
  var AV#a#FILT_COEFF0: bv8;
  var AV#a#FILT_COEFF1: bv8;
  var AV#a#FILT_COEFF2: bv8;
  var AV#a#FILT_COEFF3: bv8;
  var AV#a#FILT_COEFF4: bv8;
  var AV#a#hsps: Map (int) (bv8);
  assume (pulseShapeNw#in_symb != pulseShapeNw#in_len) && (pulseShapeNw#in_symb != pulseShapeNw#out_hsp) && (pulseShapeNw#in_len != pulseShapeNw#out_hsp) && (pulseShapeNw#body_iterations != pulseShapeNw#body_index);
  assume 0 <= I[pulseShapeNw#in_symb];
  assume I[pulseShapeNw#in_symb] <= R[pulseShapeNw#in_symb];
  assume R[pulseShapeNw#in_symb] <= C[pulseShapeNw#in_symb];
  assume 0 <= I[pulseShapeNw#in_len];
  assume I[pulseShapeNw#in_len] <= R[pulseShapeNw#in_len];
  assume R[pulseShapeNw#in_len] <= C[pulseShapeNw#in_len];
  assume 0 <= I[pulseShapeNw#body_iterations];
  assume I[pulseShapeNw#body_iterations] <= R[pulseShapeNw#body_iterations];
  assume R[pulseShapeNw#body_iterations] <= C[pulseShapeNw#body_iterations];
  assume 0 <= I[pulseShapeNw#body_index];
  assume I[pulseShapeNw#body_index] <= R[pulseShapeNw#body_index];
  assume R[pulseShapeNw#body_index] <= C[pulseShapeNw#body_index];
  assume 0 <= I[pulseShapeNw#St];
  assume I[pulseShapeNw#St] <= R[pulseShapeNw#St];
  assume R[pulseShapeNw#St] <= C[pulseShapeNw#St];
  assume 0 <= I[pulseShapeNw#out_hsp];
  assume I[pulseShapeNw#out_hsp] <= R[pulseShapeNw#out_hsp];
  assume R[pulseShapeNw#out_hsp] <= C[pulseShapeNw#out_hsp];
  assume I[pulseShapeNw#out_hsp] == R[pulseShapeNw#out_hsp];
  assume 0 <= I[pulseShapeNw#out_done];
  assume I[pulseShapeNw#out_done] <= R[pulseShapeNw#out_done];
  assume R[pulseShapeNw#out_done] <= C[pulseShapeNw#out_done];
  assume I[pulseShapeNw#out_done] == R[pulseShapeNw#out_done];
  assume (B[pulseShapeNw#in_symb] == 576) && (B[pulseShapeNw#in_len] == 1) && (B[pulseShapeNw#out_done] == 1) && (B[pulseShapeNw#out_hsp] == 4616);
  assume (B[pulseShapeNw#in_symb] == 576) && (B[pulseShapeNw#in_len] == 1) && (B[pulseShapeNw#out_done] == 1) && (B[pulseShapeNw#out_hsp] == 4616);
  assume (C[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) < 576;
  assume I[pulseShapeNw#in_symb] == (576 * I[pulseShapeNw#out_done]);
  assume I[pulseShapeNw#in_len] == I[pulseShapeNw#out_done];
  assume I[pulseShapeNw#out_hsp] == (4616 * I[pulseShapeNw#in_len]);
  assume ((C[pulseShapeNw#body_iterations] - R[pulseShapeNw#body_iterations]) == 1) && ((C[pulseShapeNw#body_index] - R[pulseShapeNw#body_index]) == 1) && ((C[pulseShapeNw#St] - R[pulseShapeNw#St]) == 1);
  assume (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 0) || (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 1);
  assume AT#BvUle14(0bv14, M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]]) && AT#BvUle14(M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]], M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]]);
  assume ((C[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 1) ==> (B[pulseShapeNw#in_symb] == (64 * AT#Bv2Int8(M[pulseShapeNw#in_len][I[pulseShapeNw#in_len]])));
  assume ((R[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 1) ==> (M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]] == AT#BvMul14(0bv6 ++ M[pulseShapeNw#in_len][I[pulseShapeNw#in_len]], 32bv14)) && ((2 * AT#Bv2Int14(M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]])) == B[pulseShapeNw#in_symb]) && ((R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) == (2 * AT#Bv2Int14(M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]])));
  assume (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 1) ==> ((R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) == (2 * AT#Bv2Int14(M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]]))) && ((C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]) == (16 * AT#Bv2Int14(M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]]))) && ((16 * (R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb])) == (2 * (C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]))) && ((C[pulseShapeNw#out_done] - I[pulseShapeNw#out_done]) == 0) && ((R[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 1);
  assume (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 0) && ((R[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 1) ==> ((R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) == (2 * AT#Bv2Int14(M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]]))) && ((C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]) == ((16 * AT#Bv2Int14(M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]])) + 8)) && ((16 * (R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb])) == (2 * ((C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]) - 8))) && ((C[pulseShapeNw#out_done] - I[pulseShapeNw#out_done]) == 1);
  assume (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 0) && ((R[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 0) ==> ((R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) == 0) && ((C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]) == 0) && ((C[pulseShapeNw#out_done] - I[pulseShapeNw#out_done]) == 0);
  assume M[pulseShapeNw#in_len][I[pulseShapeNw#in_len]] == 9bv8;
  assume ((C[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) <= 576) && ((C[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) <= 1);
  C[pulseShapeNw#in_symb] := C[pulseShapeNw#in_symb] + 1;
  assume M[pulseShapeNw#in_len][I[pulseShapeNw#in_len]] == 9bv8;
  assert {:msg "pulseShapeNw.actor(140.15): Channel invariant might be falsified by network input (#57)"} I[pulseShapeNw#in_symb] == (576 * I[pulseShapeNw#out_done]);
  assert {:msg "pulseShapeNw.actor(141.15): Channel invariant might be falsified by network input (#58)"} I[pulseShapeNw#in_len] == I[pulseShapeNw#out_done];
  assert {:msg "pulseShapeNw.actor(142.15): Channel invariant might be falsified by network input (#59)"} I[pulseShapeNw#out_hsp] == (4616 * I[pulseShapeNw#in_len]);
  assert {:msg "pulseShapeNw.actor(147.15): Channel invariant might be falsified by network input (#60)"} ((C[pulseShapeNw#body_iterations] - R[pulseShapeNw#body_iterations]) == 1) && ((C[pulseShapeNw#body_index] - R[pulseShapeNw#body_index]) == 1) && ((C[pulseShapeNw#St] - R[pulseShapeNw#St]) == 1);
  assert {:msg "pulseShapeNw.actor(150.15): Channel invariant might be falsified by network input (#61)"} (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 0) || (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 1);
  assert {:msg "pulseShapeNw.actor(151.15): Channel invariant might be falsified by network input (#62)"} AT#BvUle14(0bv14, M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]]) && AT#BvUle14(M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]], M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]]);
  assert {:msg "pulseShapeNw.actor(153.15): Channel invariant might be falsified by network input (#63)"} ((C[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 1) ==> (B[pulseShapeNw#in_symb] == (64 * AT#Bv2Int8(M[pulseShapeNw#in_len][I[pulseShapeNw#in_len]])));
  assert {:msg "pulseShapeNw.actor(154.15): Channel invariant might be falsified by network input (#64)"} ((R[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 1) ==> (M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]] == AT#BvMul14(0bv6 ++ M[pulseShapeNw#in_len][I[pulseShapeNw#in_len]], 32bv14)) && ((2 * AT#Bv2Int14(M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]])) == B[pulseShapeNw#in_symb]) && ((R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) == (2 * AT#Bv2Int14(M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]])));
  assert {:msg "pulseShapeNw.actor(160.15): Channel invariant might be falsified by network input (#65)"} (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 1) ==> ((R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) == (2 * AT#Bv2Int14(M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]]))) && ((C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]) == (16 * AT#Bv2Int14(M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]]))) && ((16 * (R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb])) == (2 * (C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]))) && ((C[pulseShapeNw#out_done] - I[pulseShapeNw#out_done]) == 0) && ((R[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 1);
  assert {:msg "pulseShapeNw.actor(168.15): Channel invariant might be falsified by network input (#66)"} (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 0) && ((R[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 1) ==> ((R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) == (2 * AT#Bv2Int14(M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]]))) && ((C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]) == ((16 * AT#Bv2Int14(M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]])) + 8)) && ((16 * (R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb])) == (2 * ((C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]) - 8))) && ((C[pulseShapeNw#out_done] - I[pulseShapeNw#out_done]) == 1);
  assert {:msg "pulseShapeNw.actor(175.15): Channel invariant might be falsified by network input (#67)"} (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 0) && ((R[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 0) ==> ((R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) == 0) && ((C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]) == 0) && ((C[pulseShapeNw#out_done] - I[pulseShapeNw#out_done]) == 0);
  assert {:msg "pulseShapeNw.actor(137.14): Channel invariant might be falsified by network input (#68)"} M[pulseShapeNw#in_len][I[pulseShapeNw#in_len]] == 9bv8;
  assert {:msg "Channel invariant might be falsified by network input (#69)"} ((C[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) <= 576) && ((C[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) <= 1);
}
procedure pulseShapeNw#anon$1#input#len#10()
  modifies C, R, M, I, H;
{
  var pulseShapeNw#a: Actor;
  var pulseShapeNw#in_symb: Chan (bv8);
  var pulseShapeNw#in_len: Chan (bv8);
  var pulseShapeNw#body_iterations: Chan (bv14);
  var pulseShapeNw#body_index: Chan (bv14);
  var pulseShapeNw#St: Chan (int);
  var pulseShapeNw#out_hsp: Chan (bv8);
  var pulseShapeNw#out_done: Chan (bool);
  var AV#a#symb_mem: bv8;
  var AV#a#body_iterations: bv8;
  var AV#a#body_index: bv8;
  var AV#a#FILT_COEFF0: bv8;
  var AV#a#FILT_COEFF1: bv8;
  var AV#a#FILT_COEFF2: bv8;
  var AV#a#FILT_COEFF3: bv8;
  var AV#a#FILT_COEFF4: bv8;
  var AV#a#hsps: Map (int) (bv8);
  assume (pulseShapeNw#in_symb != pulseShapeNw#in_len) && (pulseShapeNw#in_symb != pulseShapeNw#out_hsp) && (pulseShapeNw#in_len != pulseShapeNw#out_hsp) && (pulseShapeNw#body_iterations != pulseShapeNw#body_index);
  assume 0 <= I[pulseShapeNw#in_symb];
  assume I[pulseShapeNw#in_symb] <= R[pulseShapeNw#in_symb];
  assume R[pulseShapeNw#in_symb] <= C[pulseShapeNw#in_symb];
  assume 0 <= I[pulseShapeNw#in_len];
  assume I[pulseShapeNw#in_len] <= R[pulseShapeNw#in_len];
  assume R[pulseShapeNw#in_len] <= C[pulseShapeNw#in_len];
  assume 0 <= I[pulseShapeNw#body_iterations];
  assume I[pulseShapeNw#body_iterations] <= R[pulseShapeNw#body_iterations];
  assume R[pulseShapeNw#body_iterations] <= C[pulseShapeNw#body_iterations];
  assume 0 <= I[pulseShapeNw#body_index];
  assume I[pulseShapeNw#body_index] <= R[pulseShapeNw#body_index];
  assume R[pulseShapeNw#body_index] <= C[pulseShapeNw#body_index];
  assume 0 <= I[pulseShapeNw#St];
  assume I[pulseShapeNw#St] <= R[pulseShapeNw#St];
  assume R[pulseShapeNw#St] <= C[pulseShapeNw#St];
  assume 0 <= I[pulseShapeNw#out_hsp];
  assume I[pulseShapeNw#out_hsp] <= R[pulseShapeNw#out_hsp];
  assume R[pulseShapeNw#out_hsp] <= C[pulseShapeNw#out_hsp];
  assume I[pulseShapeNw#out_hsp] == R[pulseShapeNw#out_hsp];
  assume 0 <= I[pulseShapeNw#out_done];
  assume I[pulseShapeNw#out_done] <= R[pulseShapeNw#out_done];
  assume R[pulseShapeNw#out_done] <= C[pulseShapeNw#out_done];
  assume I[pulseShapeNw#out_done] == R[pulseShapeNw#out_done];
  assume (B[pulseShapeNw#in_symb] == 576) && (B[pulseShapeNw#in_len] == 1) && (B[pulseShapeNw#out_done] == 1) && (B[pulseShapeNw#out_hsp] == 4616);
  assume (B[pulseShapeNw#in_symb] == 576) && (B[pulseShapeNw#in_len] == 1) && (B[pulseShapeNw#out_done] == 1) && (B[pulseShapeNw#out_hsp] == 4616);
  assume (C[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) < 1;
  assume I[pulseShapeNw#in_symb] == (576 * I[pulseShapeNw#out_done]);
  assume I[pulseShapeNw#in_len] == I[pulseShapeNw#out_done];
  assume I[pulseShapeNw#out_hsp] == (4616 * I[pulseShapeNw#in_len]);
  assume ((C[pulseShapeNw#body_iterations] - R[pulseShapeNw#body_iterations]) == 1) && ((C[pulseShapeNw#body_index] - R[pulseShapeNw#body_index]) == 1) && ((C[pulseShapeNw#St] - R[pulseShapeNw#St]) == 1);
  assume (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 0) || (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 1);
  assume AT#BvUle14(0bv14, M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]]) && AT#BvUle14(M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]], M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]]);
  assume ((C[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 1) ==> (B[pulseShapeNw#in_symb] == (64 * AT#Bv2Int8(M[pulseShapeNw#in_len][I[pulseShapeNw#in_len]])));
  assume ((R[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 1) ==> (M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]] == AT#BvMul14(0bv6 ++ M[pulseShapeNw#in_len][I[pulseShapeNw#in_len]], 32bv14)) && ((2 * AT#Bv2Int14(M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]])) == B[pulseShapeNw#in_symb]) && ((R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) == (2 * AT#Bv2Int14(M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]])));
  assume (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 1) ==> ((R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) == (2 * AT#Bv2Int14(M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]]))) && ((C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]) == (16 * AT#Bv2Int14(M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]]))) && ((16 * (R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb])) == (2 * (C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]))) && ((C[pulseShapeNw#out_done] - I[pulseShapeNw#out_done]) == 0) && ((R[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 1);
  assume (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 0) && ((R[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 1) ==> ((R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) == (2 * AT#Bv2Int14(M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]]))) && ((C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]) == ((16 * AT#Bv2Int14(M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]])) + 8)) && ((16 * (R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb])) == (2 * ((C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]) - 8))) && ((C[pulseShapeNw#out_done] - I[pulseShapeNw#out_done]) == 1);
  assume (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 0) && ((R[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 0) ==> ((R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) == 0) && ((C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]) == 0) && ((C[pulseShapeNw#out_done] - I[pulseShapeNw#out_done]) == 0);
  assume M[pulseShapeNw#in_len][I[pulseShapeNw#in_len]] == 9bv8;
  assume ((C[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) <= 576) && ((C[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) <= 1);
  C[pulseShapeNw#in_len] := C[pulseShapeNw#in_len] + 1;
  assume M[pulseShapeNw#in_len][I[pulseShapeNw#in_len]] == 9bv8;
  assert {:msg "pulseShapeNw.actor(140.15): Channel invariant might be falsified by network input (#70)"} I[pulseShapeNw#in_symb] == (576 * I[pulseShapeNw#out_done]);
  assert {:msg "pulseShapeNw.actor(141.15): Channel invariant might be falsified by network input (#71)"} I[pulseShapeNw#in_len] == I[pulseShapeNw#out_done];
  assert {:msg "pulseShapeNw.actor(142.15): Channel invariant might be falsified by network input (#72)"} I[pulseShapeNw#out_hsp] == (4616 * I[pulseShapeNw#in_len]);
  assert {:msg "pulseShapeNw.actor(147.15): Channel invariant might be falsified by network input (#73)"} ((C[pulseShapeNw#body_iterations] - R[pulseShapeNw#body_iterations]) == 1) && ((C[pulseShapeNw#body_index] - R[pulseShapeNw#body_index]) == 1) && ((C[pulseShapeNw#St] - R[pulseShapeNw#St]) == 1);
  assert {:msg "pulseShapeNw.actor(150.15): Channel invariant might be falsified by network input (#74)"} (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 0) || (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 1);
  assert {:msg "pulseShapeNw.actor(151.15): Channel invariant might be falsified by network input (#75)"} AT#BvUle14(0bv14, M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]]) && AT#BvUle14(M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]], M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]]);
  assert {:msg "pulseShapeNw.actor(153.15): Channel invariant might be falsified by network input (#76)"} ((C[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 1) ==> (B[pulseShapeNw#in_symb] == (64 * AT#Bv2Int8(M[pulseShapeNw#in_len][I[pulseShapeNw#in_len]])));
  assert {:msg "pulseShapeNw.actor(154.15): Channel invariant might be falsified by network input (#77)"} ((R[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 1) ==> (M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]] == AT#BvMul14(0bv6 ++ M[pulseShapeNw#in_len][I[pulseShapeNw#in_len]], 32bv14)) && ((2 * AT#Bv2Int14(M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]])) == B[pulseShapeNw#in_symb]) && ((R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) == (2 * AT#Bv2Int14(M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]])));
  assert {:msg "pulseShapeNw.actor(160.15): Channel invariant might be falsified by network input (#78)"} (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 1) ==> ((R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) == (2 * AT#Bv2Int14(M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]]))) && ((C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]) == (16 * AT#Bv2Int14(M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]]))) && ((16 * (R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb])) == (2 * (C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]))) && ((C[pulseShapeNw#out_done] - I[pulseShapeNw#out_done]) == 0) && ((R[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 1);
  assert {:msg "pulseShapeNw.actor(168.15): Channel invariant might be falsified by network input (#79)"} (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 0) && ((R[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 1) ==> ((R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) == (2 * AT#Bv2Int14(M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]]))) && ((C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]) == ((16 * AT#Bv2Int14(M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]])) + 8)) && ((16 * (R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb])) == (2 * ((C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]) - 8))) && ((C[pulseShapeNw#out_done] - I[pulseShapeNw#out_done]) == 1);
  assert {:msg "pulseShapeNw.actor(175.15): Channel invariant might be falsified by network input (#80)"} (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 0) && ((R[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 0) ==> ((R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) == 0) && ((C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]) == 0) && ((C[pulseShapeNw#out_done] - I[pulseShapeNw#out_done]) == 0);
  assert {:msg "pulseShapeNw.actor(137.14): Channel invariant might be falsified by network input (#81)"} M[pulseShapeNw#in_len][I[pulseShapeNw#in_len]] == 9bv8;
  assert {:msg "Channel invariant might be falsified by network input (#82)"} ((C[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) <= 576) && ((C[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) <= 1);
}
procedure pulseShapeNw#anon$1#exit#11()
  modifies C, R, M, I, H;
{
  var pulseShapeNw#a: Actor;
  var pulseShapeNw#in_symb: Chan (bv8);
  var pulseShapeNw#in_len: Chan (bv8);
  var pulseShapeNw#body_iterations: Chan (bv14);
  var pulseShapeNw#body_index: Chan (bv14);
  var pulseShapeNw#St: Chan (int);
  var pulseShapeNw#out_hsp: Chan (bv8);
  var pulseShapeNw#out_done: Chan (bool);
  var AV#a#symb_mem: bv8;
  var AV#a#body_iterations: bv8;
  var AV#a#body_index: bv8;
  var AV#a#FILT_COEFF0: bv8;
  var AV#a#FILT_COEFF1: bv8;
  var AV#a#FILT_COEFF2: bv8;
  var AV#a#FILT_COEFF3: bv8;
  var AV#a#FILT_COEFF4: bv8;
  var AV#a#hsps: Map (int) (bv8);
  assume (pulseShapeNw#in_symb != pulseShapeNw#in_len) && (pulseShapeNw#in_symb != pulseShapeNw#out_hsp) && (pulseShapeNw#in_len != pulseShapeNw#out_hsp) && (pulseShapeNw#body_iterations != pulseShapeNw#body_index);
  assume 0 <= I[pulseShapeNw#in_symb];
  assume I[pulseShapeNw#in_symb] <= R[pulseShapeNw#in_symb];
  assume R[pulseShapeNw#in_symb] <= C[pulseShapeNw#in_symb];
  assume 0 <= I[pulseShapeNw#in_len];
  assume I[pulseShapeNw#in_len] <= R[pulseShapeNw#in_len];
  assume R[pulseShapeNw#in_len] <= C[pulseShapeNw#in_len];
  assume 0 <= I[pulseShapeNw#body_iterations];
  assume I[pulseShapeNw#body_iterations] <= R[pulseShapeNw#body_iterations];
  assume R[pulseShapeNw#body_iterations] <= C[pulseShapeNw#body_iterations];
  assume 0 <= I[pulseShapeNw#body_index];
  assume I[pulseShapeNw#body_index] <= R[pulseShapeNw#body_index];
  assume R[pulseShapeNw#body_index] <= C[pulseShapeNw#body_index];
  assume 0 <= I[pulseShapeNw#St];
  assume I[pulseShapeNw#St] <= R[pulseShapeNw#St];
  assume R[pulseShapeNw#St] <= C[pulseShapeNw#St];
  assume 0 <= I[pulseShapeNw#out_hsp];
  assume I[pulseShapeNw#out_hsp] <= R[pulseShapeNw#out_hsp];
  assume R[pulseShapeNw#out_hsp] <= C[pulseShapeNw#out_hsp];
  assume I[pulseShapeNw#out_hsp] == R[pulseShapeNw#out_hsp];
  assume 0 <= I[pulseShapeNw#out_done];
  assume I[pulseShapeNw#out_done] <= R[pulseShapeNw#out_done];
  assume R[pulseShapeNw#out_done] <= C[pulseShapeNw#out_done];
  assume I[pulseShapeNw#out_done] == R[pulseShapeNw#out_done];
  assume (B[pulseShapeNw#in_symb] == 576) && (B[pulseShapeNw#in_len] == 1) && (B[pulseShapeNw#out_done] == 1) && (B[pulseShapeNw#out_hsp] == 4616);
  assume (B[pulseShapeNw#in_symb] == 576) && (B[pulseShapeNw#in_len] == 1) && (B[pulseShapeNw#out_done] == 1) && (B[pulseShapeNw#out_hsp] == 4616);
  assume I[pulseShapeNw#in_symb] == (576 * I[pulseShapeNw#out_done]);
  assume I[pulseShapeNw#in_len] == I[pulseShapeNw#out_done];
  assume I[pulseShapeNw#out_hsp] == (4616 * I[pulseShapeNw#in_len]);
  assume ((C[pulseShapeNw#body_iterations] - R[pulseShapeNw#body_iterations]) == 1) && ((C[pulseShapeNw#body_index] - R[pulseShapeNw#body_index]) == 1) && ((C[pulseShapeNw#St] - R[pulseShapeNw#St]) == 1);
  assume (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 0) || (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 1);
  assume AT#BvUle14(0bv14, M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]]) && AT#BvUle14(M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]], M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]]);
  assume ((C[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 1) ==> (B[pulseShapeNw#in_symb] == (64 * AT#Bv2Int8(M[pulseShapeNw#in_len][I[pulseShapeNw#in_len]])));
  assume ((R[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 1) ==> (M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]] == AT#BvMul14(0bv6 ++ M[pulseShapeNw#in_len][I[pulseShapeNw#in_len]], 32bv14)) && ((2 * AT#Bv2Int14(M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]])) == B[pulseShapeNw#in_symb]) && ((R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) == (2 * AT#Bv2Int14(M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]])));
  assume (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 1) ==> ((R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) == (2 * AT#Bv2Int14(M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]]))) && ((C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]) == (16 * AT#Bv2Int14(M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]]))) && ((16 * (R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb])) == (2 * (C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]))) && ((C[pulseShapeNw#out_done] - I[pulseShapeNw#out_done]) == 0) && ((R[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 1);
  assume (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 0) && ((R[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 1) ==> ((R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) == (2 * AT#Bv2Int14(M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]]))) && ((C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]) == ((16 * AT#Bv2Int14(M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]])) + 8)) && ((16 * (R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb])) == (2 * ((C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]) - 8))) && ((C[pulseShapeNw#out_done] - I[pulseShapeNw#out_done]) == 1);
  assume (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 0) && ((R[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 0) ==> ((R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) == 0) && ((C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]) == 0) && ((C[pulseShapeNw#out_done] - I[pulseShapeNw#out_done]) == 0);
  assume M[pulseShapeNw#in_len][I[pulseShapeNw#in_len]] == 9bv8;
  assume ((C[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) <= 576) && ((C[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) <= 1);
  assume (C[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) == 576;
  assume (C[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 1;
  assume M[pulseShapeNw#in_len][I[pulseShapeNw#in_len]] == 9bv8;
  assume !((1 <= (C[pulseShapeNw#in_len] - R[pulseShapeNw#in_len])) && (1 <= (C[pulseShapeNw#body_iterations] - R[pulseShapeNw#body_iterations])) && (1 <= (C[pulseShapeNw#body_index] - R[pulseShapeNw#body_index])) && (1 <= (C[pulseShapeNw#St] - R[pulseShapeNw#St])) && (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 0));
  assume !((2 <= (C[pulseShapeNw#in_symb] - R[pulseShapeNw#in_symb])) && (1 <= (C[pulseShapeNw#body_iterations] - R[pulseShapeNw#body_iterations])) && (1 <= (C[pulseShapeNw#body_index] - R[pulseShapeNw#body_index])) && (1 <= (C[pulseShapeNw#St] - R[pulseShapeNw#St])) && (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 1) && AT#BvUlt14(M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]], M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]]));
  assume !((1 <= (C[pulseShapeNw#body_iterations] - R[pulseShapeNw#body_iterations])) && (1 <= (C[pulseShapeNw#body_index] - R[pulseShapeNw#body_index])) && (1 <= (C[pulseShapeNw#St] - R[pulseShapeNw#St])) && (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 1) && (M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]] == M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]]));
  R[pulseShapeNw#out_hsp] := R[pulseShapeNw#out_hsp] + 4616;
  R[pulseShapeNw#out_done] := R[pulseShapeNw#out_done] + 1;
  I := R;
  assert {:msg "pulseShapeNw.actor(140.15): The network might not preserve the channel invariant (#83)"} I[pulseShapeNw#in_symb] == (576 * I[pulseShapeNw#out_done]);
  assert {:msg "pulseShapeNw.actor(141.15): The network might not preserve the channel invariant (#84)"} I[pulseShapeNw#in_len] == I[pulseShapeNw#out_done];
  assert {:msg "pulseShapeNw.actor(142.15): The network might not preserve the channel invariant (#85)"} I[pulseShapeNw#out_hsp] == (4616 * I[pulseShapeNw#in_len]);
  assert {:msg "pulseShapeNw.actor(147.15): The network might not preserve the channel invariant (#86)"} ((C[pulseShapeNw#body_iterations] - R[pulseShapeNw#body_iterations]) == 1) && ((C[pulseShapeNw#body_index] - R[pulseShapeNw#body_index]) == 1) && ((C[pulseShapeNw#St] - R[pulseShapeNw#St]) == 1);
  assert {:msg "pulseShapeNw.actor(150.15): The network might not preserve the channel invariant (#87)"} (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 0) || (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 1);
  assert {:msg "pulseShapeNw.actor(151.15): The network might not preserve the channel invariant (#88)"} AT#BvUle14(0bv14, M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]]) && AT#BvUle14(M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]], M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]]);
  assert {:msg "pulseShapeNw.actor(153.15): The network might not preserve the channel invariant (#89)"} ((C[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 1) ==> (B[pulseShapeNw#in_symb] == (64 * AT#Bv2Int8(M[pulseShapeNw#in_len][I[pulseShapeNw#in_len]])));
  assert {:msg "pulseShapeNw.actor(154.15): The network might not preserve the channel invariant (#90)"} ((R[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 1) ==> (M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]] == AT#BvMul14(0bv6 ++ M[pulseShapeNw#in_len][I[pulseShapeNw#in_len]], 32bv14)) && ((2 * AT#Bv2Int14(M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]])) == B[pulseShapeNw#in_symb]) && ((R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) == (2 * AT#Bv2Int14(M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]])));
  assert {:msg "pulseShapeNw.actor(160.15): The network might not preserve the channel invariant (#91)"} (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 1) ==> ((R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) == (2 * AT#Bv2Int14(M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]]))) && ((C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]) == (16 * AT#Bv2Int14(M[pulseShapeNw#body_index][R[pulseShapeNw#body_index]]))) && ((16 * (R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb])) == (2 * (C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]))) && ((C[pulseShapeNw#out_done] - I[pulseShapeNw#out_done]) == 0) && ((R[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 1);
  assert {:msg "pulseShapeNw.actor(168.15): The network might not preserve the channel invariant (#92)"} (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 0) && ((R[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 1) ==> ((R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) == (2 * AT#Bv2Int14(M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]]))) && ((C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]) == ((16 * AT#Bv2Int14(M[pulseShapeNw#body_iterations][R[pulseShapeNw#body_iterations]])) + 8)) && ((16 * (R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb])) == (2 * ((C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]) - 8))) && ((C[pulseShapeNw#out_done] - I[pulseShapeNw#out_done]) == 1);
  assert {:msg "pulseShapeNw.actor(175.15): The network might not preserve the channel invariant (#93)"} (M[pulseShapeNw#St][R[pulseShapeNw#St]] == 0) && ((R[pulseShapeNw#in_len] - I[pulseShapeNw#in_len]) == 0) ==> ((R[pulseShapeNw#in_symb] - I[pulseShapeNw#in_symb]) == 0) && ((C[pulseShapeNw#out_hsp] - I[pulseShapeNw#out_hsp]) == 0) && ((C[pulseShapeNw#out_done] - I[pulseShapeNw#out_done]) == 0);
  assert {:msg "pulseShapeNw.actor(145.13): The network might not preserve the network invariant (#94)"} ((C[pulseShapeNw#body_iterations] - R[pulseShapeNw#body_iterations]) == 1) && ((C[pulseShapeNw#body_index] - R[pulseShapeNw#body_index]) == 1) && ((C[pulseShapeNw#St] - R[pulseShapeNw#St]) == 1);
  assert {:msg "pulseShapeNw.actor(146.13): The network might not preserve the network invariant (#95)"} M[pulseShapeNw#St][R[pulseShapeNw#St]] == 0;
  assert {:msg "The network might not preserve the network invariant (#96)"} R[pulseShapeNw#in_symb] == (576 * C[pulseShapeNw#out_done]);
  assert {:msg "The network might not preserve the network invariant (#97)"} R[pulseShapeNw#in_len] == C[pulseShapeNw#out_done];
  assert {:msg "The network might not preserve the network invariant (#98)"} (4616 * R[pulseShapeNw#in_symb]) == (576 * C[pulseShapeNw#out_hsp]);
  assert {:msg "The network might not preserve the network invariant (#99)"} (4616 * R[pulseShapeNw#in_len]) == C[pulseShapeNw#out_hsp];
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel in_symb (#100)"} (C[pulseShapeNw#in_symb] - R[pulseShapeNw#in_symb]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel in_len (#101)"} (C[pulseShapeNw#in_len] - R[pulseShapeNw#in_len]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel out_hsp (#102)"} (C[pulseShapeNw#out_hsp] - R[pulseShapeNw#out_hsp]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel out_done (#103)"} (C[pulseShapeNw#out_done] - R[pulseShapeNw#out_done]) == 0;
}

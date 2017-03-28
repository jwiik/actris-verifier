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

// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

procedure headerAdd#init#0()
  modifies C, R, M, I, H;
{
  var pl_bits: Chan (bv8);
  var St_in: Chan (int);
  var octet_count_in: Chan (bv8);
  var octet_index_in: Chan (bv8);
  var data: Chan (bv8);
  var len: Chan (bv8);
  var St_out: Chan (int);
  var octet_count_out: Chan (bv8);
  var octet_index_out: Chan (bv8);
  var octet_count: bv8;
  var octet_index: bv8;
  var HEADER_LEN: int;
  var Header: Map (bv8) (bv8);
  var data_out: bv8;
  assume (pl_bits != octet_count_in) && (pl_bits != octet_index_in) && (pl_bits != data) && (pl_bits != len) && (pl_bits != octet_count_out) && (pl_bits != octet_index_out) && (St_in != St_out) && (octet_count_in != octet_index_in) && (octet_count_in != data) && (octet_count_in != len) && (octet_count_in != octet_count_out) && (octet_count_in != octet_index_out) && (octet_index_in != data) && (octet_index_in != len) && (octet_index_in != octet_count_out) && (octet_index_in != octet_index_out) && (data != len) && (data != octet_count_out) && (data != octet_index_out) && (len != octet_count_out) && (len != octet_index_out) && (octet_count_out != octet_index_out);
  assume R[pl_bits] == 0;
  assume R[St_in] == 0;
  assume R[octet_count_in] == 0;
  assume R[octet_index_in] == 0;
  assume C[data] == 0;
  assume C[len] == 0;
  assume C[St_out] == 0;
  assume C[octet_count_out] == 0;
  assume C[octet_index_out] == 0;
  M[octet_index_out][C[octet_index_out]] := 0bv8;
  C[octet_index_out] := C[octet_index_out] + 1;
  M[octet_count_out][C[octet_count_out]] := 0bv8;
  C[octet_count_out] := C[octet_count_out] + 1;
  M[St_out][C[St_out]] := 0;
  C[St_out] := C[St_out] + 1;
}
procedure headerAdd#get_data_len#1()
  modifies C, R, M, I, H;
{
  var pl_bits: Chan (bv8);
  var St_in: Chan (int);
  var octet_count_in: Chan (bv8);
  var octet_index_in: Chan (bv8);
  var data: Chan (bv8);
  var len: Chan (bv8);
  var St_out: Chan (int);
  var octet_count_out: Chan (bv8);
  var octet_index_out: Chan (bv8);
  var octet_count: bv8;
  var octet_index: bv8;
  var HEADER_LEN: int;
  var Header: Map (bv8) (bv8);
  var data_out: bv8;
  var pl_bits#0: bv8;
  var octet_index_in#0: bv8;
  var octet_count_in#0: bv8;
  var St_in#0: int;
  assume (pl_bits != octet_count_in) && (pl_bits != octet_index_in) && (pl_bits != data) && (pl_bits != len) && (pl_bits != octet_count_out) && (pl_bits != octet_index_out) && (St_in != St_out) && (octet_count_in != octet_index_in) && (octet_count_in != data) && (octet_count_in != len) && (octet_count_in != octet_count_out) && (octet_count_in != octet_index_out) && (octet_index_in != data) && (octet_index_in != len) && (octet_index_in != octet_count_out) && (octet_index_in != octet_index_out) && (data != len) && (data != octet_count_out) && (data != octet_index_out) && (len != octet_count_out) && (len != octet_index_out) && (octet_count_out != octet_index_out);
  assume 0 <= R[pl_bits];
  assume 0 <= R[St_in];
  assume 0 <= R[octet_count_in];
  assume 0 <= R[octet_index_in];
  assume 0 <= C[data];
  assume 0 <= C[len];
  assume 0 <= C[St_out];
  assume 0 <= C[octet_count_out];
  assume 0 <= C[octet_index_out];
  pl_bits#0 := M[pl_bits][R[pl_bits]];
  R[pl_bits] := R[pl_bits] + 1;
  octet_index_in#0 := M[octet_index_in][R[octet_index_in]];
  R[octet_index_in] := R[octet_index_in] + 1;
  octet_count_in#0 := M[octet_count_in][R[octet_count_in]];
  R[octet_count_in] := R[octet_count_in] + 1;
  St_in#0 := M[St_in][R[St_in]];
  R[St_in] := R[St_in] + 1;
  assume St_in#0 == 0;
  M[octet_index_out][C[octet_index_out]] := 0bv8;
  C[octet_index_out] := C[octet_index_out] + 1;
  M[octet_count_out][C[octet_count_out]] := AT#BvAdd8(AT#BvAdd8(pl_bits#0, 5bv8), 1bv8);
  C[octet_count_out] := C[octet_count_out] + 1;
  M[St_out][C[St_out]] := 1;
  C[St_out] := C[St_out] + 1;
  M[len][C[len]] := AT#BvAdd8(AT#BvAdd8(pl_bits#0, 5bv8), 1bv8);
  C[len] := C[len] + 1;
}
procedure headerAdd#send_header#2()
  modifies C, R, M, I, H;
{
  var pl_bits: Chan (bv8);
  var St_in: Chan (int);
  var octet_count_in: Chan (bv8);
  var octet_index_in: Chan (bv8);
  var data: Chan (bv8);
  var len: Chan (bv8);
  var St_out: Chan (int);
  var octet_count_out: Chan (bv8);
  var octet_index_out: Chan (bv8);
  var octet_count: bv8;
  var octet_index: bv8;
  var HEADER_LEN: int;
  var Header: Map (bv8) (bv8);
  var data_out: bv8;
  var pl_bits#0: bv8;
  var octet_index_in#0: bv8;
  var octet_count_in#0: bv8;
  var St_in#0: int;
  assume (pl_bits != octet_count_in) && (pl_bits != octet_index_in) && (pl_bits != data) && (pl_bits != len) && (pl_bits != octet_count_out) && (pl_bits != octet_index_out) && (St_in != St_out) && (octet_count_in != octet_index_in) && (octet_count_in != data) && (octet_count_in != len) && (octet_count_in != octet_count_out) && (octet_count_in != octet_index_out) && (octet_index_in != data) && (octet_index_in != len) && (octet_index_in != octet_count_out) && (octet_index_in != octet_index_out) && (data != len) && (data != octet_count_out) && (data != octet_index_out) && (len != octet_count_out) && (len != octet_index_out) && (octet_count_out != octet_index_out);
  assume 0 <= R[pl_bits];
  assume 0 <= R[St_in];
  assume 0 <= R[octet_count_in];
  assume 0 <= R[octet_index_in];
  assume 0 <= C[data];
  assume 0 <= C[len];
  assume 0 <= C[St_out];
  assume 0 <= C[octet_count_out];
  assume 0 <= C[octet_index_out];
  octet_index_in#0 := M[octet_index_in][R[octet_index_in]];
  R[octet_index_in] := R[octet_index_in] + 1;
  octet_count_in#0 := M[octet_count_in][R[octet_count_in]];
  R[octet_count_in] := R[octet_count_in] + 1;
  St_in#0 := M[St_in][R[St_in]];
  R[St_in] := R[St_in] + 1;
  assume AT#BvUlt8(octet_index_in#0, 5bv8) && (St_in#0 == 1);
  data_out := Map#Select(Header, octet_index_in#0);
  M[St_out][C[St_out]] := 1;
  C[St_out] := C[St_out] + 1;
  M[octet_index_out][C[octet_index_out]] := AT#BvAdd8(octet_index_in#0, 1bv8);
  C[octet_index_out] := C[octet_index_out] + 1;
  M[octet_count_out][C[octet_count_out]] := octet_count_in#0;
  C[octet_count_out] := C[octet_count_out] + 1;
  M[data][C[data]] := data_out;
  C[data] := C[data] + 1;
}
procedure headerAdd#send_length#3()
  modifies C, R, M, I, H;
{
  var pl_bits: Chan (bv8);
  var St_in: Chan (int);
  var octet_count_in: Chan (bv8);
  var octet_index_in: Chan (bv8);
  var data: Chan (bv8);
  var len: Chan (bv8);
  var St_out: Chan (int);
  var octet_count_out: Chan (bv8);
  var octet_index_out: Chan (bv8);
  var octet_count: bv8;
  var octet_index: bv8;
  var HEADER_LEN: int;
  var Header: Map (bv8) (bv8);
  var data_out: bv8;
  var pl_bits#0: bv8;
  var octet_index_in#0: bv8;
  var octet_count_in#0: bv8;
  var St_in#0: int;
  assume (pl_bits != octet_count_in) && (pl_bits != octet_index_in) && (pl_bits != data) && (pl_bits != len) && (pl_bits != octet_count_out) && (pl_bits != octet_index_out) && (St_in != St_out) && (octet_count_in != octet_index_in) && (octet_count_in != data) && (octet_count_in != len) && (octet_count_in != octet_count_out) && (octet_count_in != octet_index_out) && (octet_index_in != data) && (octet_index_in != len) && (octet_index_in != octet_count_out) && (octet_index_in != octet_index_out) && (data != len) && (data != octet_count_out) && (data != octet_index_out) && (len != octet_count_out) && (len != octet_index_out) && (octet_count_out != octet_index_out);
  assume 0 <= R[pl_bits];
  assume 0 <= R[St_in];
  assume 0 <= R[octet_count_in];
  assume 0 <= R[octet_index_in];
  assume 0 <= C[data];
  assume 0 <= C[len];
  assume 0 <= C[St_out];
  assume 0 <= C[octet_count_out];
  assume 0 <= C[octet_index_out];
  octet_index_in#0 := M[octet_index_in][R[octet_index_in]];
  R[octet_index_in] := R[octet_index_in] + 1;
  octet_count_in#0 := M[octet_count_in][R[octet_count_in]];
  R[octet_count_in] := R[octet_count_in] + 1;
  St_in#0 := M[St_in][R[St_in]];
  R[St_in] := R[St_in] + 1;
  assume (octet_index_in#0 == 5bv8) && (St_in#0 == 1);
  M[St_out][C[St_out]] := 2;
  C[St_out] := C[St_out] + 1;
  M[octet_index_out][C[octet_index_out]] := AT#BvAdd8(octet_index_in#0, 1bv8);
  C[octet_index_out] := C[octet_index_out] + 1;
  M[octet_count_out][C[octet_count_out]] := octet_count_in#0;
  C[octet_count_out] := C[octet_count_out] + 1;
  M[data][C[data]] := AT#BvSub8(AT#BvSub8(octet_count_in#0, 5bv8), 1bv8);
  C[data] := C[data] + 1;
}
procedure headerAdd#send_payload_octet#4()
  modifies C, R, M, I, H;
{
  var pl_bits: Chan (bv8);
  var St_in: Chan (int);
  var octet_count_in: Chan (bv8);
  var octet_index_in: Chan (bv8);
  var data: Chan (bv8);
  var len: Chan (bv8);
  var St_out: Chan (int);
  var octet_count_out: Chan (bv8);
  var octet_index_out: Chan (bv8);
  var octet_count: bv8;
  var octet_index: bv8;
  var HEADER_LEN: int;
  var Header: Map (bv8) (bv8);
  var data_out: bv8;
  var pl_bits#0: bv8;
  var octet_index_in#0: bv8;
  var octet_count_in#0: bv8;
  var St_in#0: int;
  assume (pl_bits != octet_count_in) && (pl_bits != octet_index_in) && (pl_bits != data) && (pl_bits != len) && (pl_bits != octet_count_out) && (pl_bits != octet_index_out) && (St_in != St_out) && (octet_count_in != octet_index_in) && (octet_count_in != data) && (octet_count_in != len) && (octet_count_in != octet_count_out) && (octet_count_in != octet_index_out) && (octet_index_in != data) && (octet_index_in != len) && (octet_index_in != octet_count_out) && (octet_index_in != octet_index_out) && (data != len) && (data != octet_count_out) && (data != octet_index_out) && (len != octet_count_out) && (len != octet_index_out) && (octet_count_out != octet_index_out);
  assume 0 <= R[pl_bits];
  assume 0 <= R[St_in];
  assume 0 <= R[octet_count_in];
  assume 0 <= R[octet_index_in];
  assume 0 <= C[data];
  assume 0 <= C[len];
  assume 0 <= C[St_out];
  assume 0 <= C[octet_count_out];
  assume 0 <= C[octet_index_out];
  pl_bits#0 := M[pl_bits][R[pl_bits]];
  R[pl_bits] := R[pl_bits] + 1;
  octet_index_in#0 := M[octet_index_in][R[octet_index_in]];
  R[octet_index_in] := R[octet_index_in] + 1;
  octet_count_in#0 := M[octet_count_in][R[octet_count_in]];
  R[octet_count_in] := R[octet_count_in] + 1;
  St_in#0 := M[St_in][R[St_in]];
  R[St_in] := R[St_in] + 1;
  assume AT#BvUlt8(octet_index_in#0, octet_count_in#0) && (St_in#0 == 2);
  M[St_out][C[St_out]] := (if AT#BvAdd8(octet_index_in#0, 1bv8) == octet_count_in#0 then 0 else 2);
  C[St_out] := C[St_out] + 1;
  M[octet_index_out][C[octet_index_out]] := AT#BvAdd8(octet_index_in#0, 1bv8);
  C[octet_index_out] := C[octet_index_out] + 1;
  M[octet_count_out][C[octet_count_out]] := octet_count_in#0;
  C[octet_count_out] := C[octet_count_out] + 1;
  M[data][C[data]] := pl_bits#0;
  C[data] := C[data] + 1;
}
procedure headerAdd##GuardWD#5()
  modifies C, R, M, I, H;
{
  var pl_bits: Chan (bv8);
  var St_in: Chan (int);
  var octet_count_in: Chan (bv8);
  var octet_index_in: Chan (bv8);
  var data: Chan (bv8);
  var len: Chan (bv8);
  var St_out: Chan (int);
  var octet_count_out: Chan (bv8);
  var octet_index_out: Chan (bv8);
  var octet_count: bv8;
  var octet_index: bv8;
  var HEADER_LEN: int;
  var Header: Map (bv8) (bv8);
  var data_out: bv8;
  var pl_bits#0: bv8;
  var octet_index_in#0: bv8;
  var octet_count_in#0: bv8;
  var St_in#0: int;
  assume (pl_bits != octet_count_in) && (pl_bits != octet_index_in) && (pl_bits != data) && (pl_bits != len) && (pl_bits != octet_count_out) && (pl_bits != octet_index_out) && (St_in != St_out) && (octet_count_in != octet_index_in) && (octet_count_in != data) && (octet_count_in != len) && (octet_count_in != octet_count_out) && (octet_count_in != octet_index_out) && (octet_index_in != data) && (octet_index_in != len) && (octet_index_in != octet_count_out) && (octet_index_in != octet_index_out) && (data != len) && (data != octet_count_out) && (data != octet_index_out) && (len != octet_count_out) && (len != octet_index_out) && (octet_count_out != octet_index_out);
  assert {:msg "1.1: The actions 'get_data_len' and 'send_header' of actor 'headerAdd' might not have mutually exclusive guards (#0)"} !(true && (1 <= (C[pl_bits] - R[pl_bits])) && (1 <= (C[octet_index_in] - R[octet_index_in])) && (1 <= (C[octet_count_in] - R[octet_count_in])) && (1 <= (C[St_in] - R[St_in])) && (St_in#0 == 0) && true && (1 <= (C[octet_index_in] - R[octet_index_in])) && (1 <= (C[octet_count_in] - R[octet_count_in])) && (1 <= (C[St_in] - R[St_in])) && AT#BvUlt8(octet_index_in#0, 5bv8) && (St_in#0 == 1));
  assert {:msg "1.1: The actions 'get_data_len' and 'send_length' of actor 'headerAdd' might not have mutually exclusive guards (#1)"} !(true && (1 <= (C[pl_bits] - R[pl_bits])) && (1 <= (C[octet_index_in] - R[octet_index_in])) && (1 <= (C[octet_count_in] - R[octet_count_in])) && (1 <= (C[St_in] - R[St_in])) && (St_in#0 == 0) && true && (1 <= (C[octet_index_in] - R[octet_index_in])) && (1 <= (C[octet_count_in] - R[octet_count_in])) && (1 <= (C[St_in] - R[St_in])) && (octet_index_in#0 == 5bv8) && (St_in#0 == 1));
  assert {:msg "1.1: The actions 'get_data_len' and 'send_payload_octet' of actor 'headerAdd' might not have mutually exclusive guards (#2)"} !(true && (1 <= (C[pl_bits] - R[pl_bits])) && (1 <= (C[octet_index_in] - R[octet_index_in])) && (1 <= (C[octet_count_in] - R[octet_count_in])) && (1 <= (C[St_in] - R[St_in])) && (St_in#0 == 0) && true && (1 <= (C[pl_bits] - R[pl_bits])) && (1 <= (C[octet_index_in] - R[octet_index_in])) && (1 <= (C[octet_count_in] - R[octet_count_in])) && (1 <= (C[St_in] - R[St_in])) && AT#BvUlt8(octet_index_in#0, octet_count_in#0) && (St_in#0 == 2));
  assert {:msg "1.1: The actions 'send_header' and 'send_length' of actor 'headerAdd' might not have mutually exclusive guards (#3)"} !(true && (1 <= (C[octet_index_in] - R[octet_index_in])) && (1 <= (C[octet_count_in] - R[octet_count_in])) && (1 <= (C[St_in] - R[St_in])) && AT#BvUlt8(octet_index_in#0, 5bv8) && (St_in#0 == 1) && true && (1 <= (C[octet_index_in] - R[octet_index_in])) && (1 <= (C[octet_count_in] - R[octet_count_in])) && (1 <= (C[St_in] - R[St_in])) && (octet_index_in#0 == 5bv8) && (St_in#0 == 1));
  assert {:msg "1.1: The actions 'send_header' and 'send_payload_octet' of actor 'headerAdd' might not have mutually exclusive guards (#4)"} !(true && (1 <= (C[octet_index_in] - R[octet_index_in])) && (1 <= (C[octet_count_in] - R[octet_count_in])) && (1 <= (C[St_in] - R[St_in])) && AT#BvUlt8(octet_index_in#0, 5bv8) && (St_in#0 == 1) && true && (1 <= (C[pl_bits] - R[pl_bits])) && (1 <= (C[octet_index_in] - R[octet_index_in])) && (1 <= (C[octet_count_in] - R[octet_count_in])) && (1 <= (C[St_in] - R[St_in])) && AT#BvUlt8(octet_index_in#0, octet_count_in#0) && (St_in#0 == 2));
  assert {:msg "1.1: The actions 'send_length' and 'send_payload_octet' of actor 'headerAdd' might not have mutually exclusive guards (#5)"} !(true && (1 <= (C[octet_index_in] - R[octet_index_in])) && (1 <= (C[octet_count_in] - R[octet_count_in])) && (1 <= (C[St_in] - R[St_in])) && (octet_index_in#0 == 5bv8) && (St_in#0 == 1) && true && (1 <= (C[pl_bits] - R[pl_bits])) && (1 <= (C[octet_index_in] - R[octet_index_in])) && (1 <= (C[octet_count_in] - R[octet_count_in])) && (1 <= (C[St_in] - R[St_in])) && AT#BvUlt8(octet_index_in#0, octet_count_in#0) && (St_in#0 == 2));
}
procedure NW#init#6()
  modifies C, R, M, I, H;
{
  var NW#a: Actor;
  var NW#input: Chan (bv8);
  var NW#octet_count: Chan (bv8);
  var NW#octet_index: Chan (bv8);
  var NW#St: Chan (int);
  var NW#data: Chan (bv8);
  var NW#len: Chan (bv8);
  var AV#a#octet_count: bv8;
  var AV#a#octet_index: bv8;
  var AV#a#HEADER_LEN: int;
  var AV#a#Header: Map (bv8) (bv8);
  var AV#a#data_out: bv8;
  assume (NW#input != NW#octet_count) && (NW#input != NW#octet_index) && (NW#input != NW#data) && (NW#input != NW#len) && (NW#octet_count != NW#octet_index) && (NW#octet_count != NW#data) && (NW#octet_count != NW#len) && (NW#octet_index != NW#data) && (NW#octet_index != NW#len) && (NW#data != NW#len);
  assume 0 <= I[NW#input];
  assume I[NW#input] <= R[NW#input];
  assume R[NW#input] <= C[NW#input];
  assume 0 <= I[NW#octet_count];
  assume I[NW#octet_count] <= R[NW#octet_count];
  assume R[NW#octet_count] <= C[NW#octet_count];
  assume 0 <= I[NW#octet_index];
  assume I[NW#octet_index] <= R[NW#octet_index];
  assume R[NW#octet_index] <= C[NW#octet_index];
  assume 0 <= I[NW#St];
  assume I[NW#St] <= R[NW#St];
  assume R[NW#St] <= C[NW#St];
  assume 0 <= I[NW#data];
  assume I[NW#data] <= R[NW#data];
  assume R[NW#data] <= C[NW#data];
  assume I[NW#data] == R[NW#data];
  assume 0 <= I[NW#len];
  assume I[NW#len] <= R[NW#len];
  assume R[NW#len] <= C[NW#len];
  assume I[NW#len] == R[NW#len];
  assume C[NW#input] == 0;
  assume R[NW#input] == 0;
  assume C[NW#octet_count] == 0;
  assume R[NW#octet_count] == 0;
  assume C[NW#octet_index] == 0;
  assume R[NW#octet_index] == 0;
  assume C[NW#St] == 0;
  assume R[NW#St] == 0;
  assume C[NW#data] == 0;
  assume R[NW#data] == 0;
  assume C[NW#len] == 0;
  assume R[NW#len] == 0;
  M[NW#octet_index][C[NW#octet_index]] := 0bv8;
  C[NW#octet_index] := C[NW#octet_index] + 1;
  M[NW#octet_count][C[NW#octet_count]] := 0bv8;
  C[NW#octet_count] := C[NW#octet_count] + 1;
  M[NW#St][C[NW#St]] := 0;
  C[NW#St] := C[NW#St] + 1;
  assert {:msg "148.15: Initialization of network 'NW' might not establish the channel invariant (#6)"} ((C[NW#octet_count] - R[NW#octet_count]) == 1) && ((C[NW#octet_index] - R[NW#octet_index]) == 1) && ((C[NW#St] - R[NW#St]) == 1);
  assert {:msg "151.15: Initialization of network 'NW' might not establish the channel invariant (#7)"} AT#BvUle8(0bv8, M[NW#octet_index][R[NW#octet_index]]) && AT#BvUle8(M[NW#octet_index][R[NW#octet_index]], M[NW#octet_count][R[NW#octet_count]]);
  assert {:msg "154.15: Initialization of network 'NW' might not establish the channel invariant (#8)"} (0 <= M[NW#St][R[NW#St]]) && (M[NW#St][R[NW#St]] <= 2);
  assert {:msg "156.15: Initialization of network 'NW' might not establish the channel invariant (#9)"} (C[NW#input] - I[NW#input]) <= 2;
  assert {:msg "157.15: Initialization of network 'NW' might not establish the channel invariant (#10)"} ((C[NW#input] - I[NW#input]) > 0) ==> (M[NW#input][I[NW#input]] == 1bv8);
  assert {:msg "159.15: Initialization of network 'NW' might not establish the channel invariant (#11)"} (M[NW#St][R[NW#St]] == 0) ==> (M[NW#octet_index][R[NW#octet_index]] == M[NW#octet_count][R[NW#octet_count]]);
  assert {:msg "160.15: Initialization of network 'NW' might not establish the channel invariant (#12)"} (M[NW#St][R[NW#St]] == 1) ==> AT#BvUle8(0bv8, M[NW#octet_index][R[NW#octet_index]]) && AT#BvUle8(M[NW#octet_index][R[NW#octet_index]], 5bv8);
  assert {:msg "161.15: Initialization of network 'NW' might not establish the channel invariant (#13)"} (M[NW#St][R[NW#St]] == 2) ==> AT#BvUle8(6bv8, M[NW#octet_index][R[NW#octet_index]]) && AT#BvUlt8(M[NW#octet_index][R[NW#octet_index]], M[NW#octet_count][R[NW#octet_count]]);
  assert {:msg "163.15: Initialization of network 'NW' might not establish the channel invariant (#14)"} (M[NW#St][R[NW#St]] == 0) && ((R[NW#input] - I[NW#input]) == 0) ==> ((C[NW#data] - I[NW#data]) == 0);
  assert {:msg "164.15: Initialization of network 'NW' might not establish the channel invariant (#15)"} (M[NW#St][R[NW#St]] == 0) && ((R[NW#input] - I[NW#input]) > 0) ==> ((C[NW#data] - I[NW#data]) == AT#Bv2Int(M[NW#octet_count][R[NW#octet_count]]));
  assert {:msg "166.15: Initialization of network 'NW' might not establish the channel invariant (#16)"} (M[NW#St][R[NW#St]] == 1) ==> ((R[NW#input] - I[NW#input]) == 1);
  assert {:msg "167.15: Initialization of network 'NW' might not establish the channel invariant (#17)"} ((M[NW#St][R[NW#St]] == 1) || (M[NW#St][R[NW#St]] == 2)) ==> ((C[NW#data] - I[NW#data]) == AT#Bv2Int(M[NW#octet_index][R[NW#octet_index]]));
  assert {:msg "168.15: Initialization of network 'NW' might not establish the channel invariant (#18)"} (M[NW#St][R[NW#St]] == 2) ==> ((R[NW#input] - I[NW#input]) == ((C[NW#data] - I[NW#data]) - 5));
  assert {:msg "170.15: Initialization of network 'NW' might not establish the channel invariant (#19)"} (M[NW#St][R[NW#St]] == 0) <==> (((R[NW#input] - I[NW#input]) == 0) || ((R[NW#input] - I[NW#input]) == 2));
  assert {:msg "172.15: Initialization of network 'NW' might not establish the channel invariant (#20)"} ((R[NW#input] - I[NW#input]) == 0) ==> ((C[NW#len] - I[NW#len]) == 0);
  assert {:msg "173.15: Initialization of network 'NW' might not establish the channel invariant (#21)"} ((R[NW#input] - I[NW#input]) > 0) ==> (M[NW#octet_count][R[NW#octet_count]] == AT#BvAdd8(M[NW#input][I[NW#input]], 6bv8));
  assert {:msg "175.15: Initialization of network 'NW' might not establish the channel invariant (#22)"} ((R[NW#input] - I[NW#input]) > 0) ==> ((C[NW#len] - I[NW#len]) == 1);
  I := R;
  assert {:msg "144.13: Initialization of network 'NW' might not establish the network invariant (#23)"} ((C[NW#octet_count] - R[NW#octet_count]) == 1) && ((C[NW#octet_index] - R[NW#octet_index]) == 1) && ((C[NW#St] - R[NW#St]) == 1);
  assert {:msg "145.13: Initialization of network 'NW' might not establish the network invariant (#24)"} (M[NW#St][R[NW#St]] == 0) && (M[NW#octet_index][R[NW#octet_index]] == M[NW#octet_count][R[NW#octet_count]]);
  assert {:msg "Initialization of network 'NW' might not establish the network invariant: Unread tokens might be left on channel input (#25)"} (C[NW#input] - R[NW#input]) == 0;
  assert {:msg "Initialization of network 'NW' might not establish the network invariant: Unread tokens might be left on channel data (#26)"} (C[NW#data] - R[NW#data]) == 0;
  assert {:msg "Initialization of network 'NW' might not establish the network invariant: Unread tokens might be left on channel len (#27)"} (C[NW#len] - R[NW#len]) == 0;
}
procedure NW##headerAdd#get_data_len#7()
  modifies C, R, M, I, H;
{
  var NW#a: Actor;
  var NW#input: Chan (bv8);
  var NW#octet_count: Chan (bv8);
  var NW#octet_index: Chan (bv8);
  var NW#St: Chan (int);
  var NW#data: Chan (bv8);
  var NW#len: Chan (bv8);
  var AV#a#octet_count: bv8;
  var AV#a#octet_index: bv8;
  var AV#a#HEADER_LEN: int;
  var AV#a#Header: Map (bv8) (bv8);
  var AV#a#data_out: bv8;
  var pl_bits#bits_in: bv8;
  var octet_index_in#octet_index: bv8;
  var octet_count_in#octet_count: bv8;
  var St_in#St: int;
  assume (NW#input != NW#octet_count) && (NW#input != NW#octet_index) && (NW#input != NW#data) && (NW#input != NW#len) && (NW#octet_count != NW#octet_index) && (NW#octet_count != NW#data) && (NW#octet_count != NW#len) && (NW#octet_index != NW#data) && (NW#octet_index != NW#len) && (NW#data != NW#len);
  assume 0 <= I[NW#input];
  assume I[NW#input] <= R[NW#input];
  assume R[NW#input] <= C[NW#input];
  assume 0 <= I[NW#octet_count];
  assume I[NW#octet_count] <= R[NW#octet_count];
  assume R[NW#octet_count] <= C[NW#octet_count];
  assume 0 <= I[NW#octet_index];
  assume I[NW#octet_index] <= R[NW#octet_index];
  assume R[NW#octet_index] <= C[NW#octet_index];
  assume 0 <= I[NW#St];
  assume I[NW#St] <= R[NW#St];
  assume R[NW#St] <= C[NW#St];
  assume 0 <= I[NW#data];
  assume I[NW#data] <= R[NW#data];
  assume R[NW#data] <= C[NW#data];
  assume I[NW#data] == R[NW#data];
  assume 0 <= I[NW#len];
  assume I[NW#len] <= R[NW#len];
  assume R[NW#len] <= C[NW#len];
  assume I[NW#len] == R[NW#len];
  assume ((C[NW#octet_count] - R[NW#octet_count]) == 1) && ((C[NW#octet_index] - R[NW#octet_index]) == 1) && ((C[NW#St] - R[NW#St]) == 1);
  assume AT#BvUle8(0bv8, M[NW#octet_index][R[NW#octet_index]]) && AT#BvUle8(M[NW#octet_index][R[NW#octet_index]], M[NW#octet_count][R[NW#octet_count]]);
  assume (0 <= M[NW#St][R[NW#St]]) && (M[NW#St][R[NW#St]] <= 2);
  assume (C[NW#input] - I[NW#input]) <= 2;
  assume ((C[NW#input] - I[NW#input]) > 0) ==> (M[NW#input][I[NW#input]] == 1bv8);
  assume (M[NW#St][R[NW#St]] == 0) ==> (M[NW#octet_index][R[NW#octet_index]] == M[NW#octet_count][R[NW#octet_count]]);
  assume (M[NW#St][R[NW#St]] == 1) ==> AT#BvUle8(0bv8, M[NW#octet_index][R[NW#octet_index]]) && AT#BvUle8(M[NW#octet_index][R[NW#octet_index]], 5bv8);
  assume (M[NW#St][R[NW#St]] == 2) ==> AT#BvUle8(6bv8, M[NW#octet_index][R[NW#octet_index]]) && AT#BvUlt8(M[NW#octet_index][R[NW#octet_index]], M[NW#octet_count][R[NW#octet_count]]);
  assume (M[NW#St][R[NW#St]] == 0) && ((R[NW#input] - I[NW#input]) == 0) ==> ((C[NW#data] - I[NW#data]) == 0);
  assume (M[NW#St][R[NW#St]] == 0) && ((R[NW#input] - I[NW#input]) > 0) ==> ((C[NW#data] - I[NW#data]) == AT#Bv2Int(M[NW#octet_count][R[NW#octet_count]]));
  assume (M[NW#St][R[NW#St]] == 1) ==> ((R[NW#input] - I[NW#input]) == 1);
  assume ((M[NW#St][R[NW#St]] == 1) || (M[NW#St][R[NW#St]] == 2)) ==> ((C[NW#data] - I[NW#data]) == AT#Bv2Int(M[NW#octet_index][R[NW#octet_index]]));
  assume (M[NW#St][R[NW#St]] == 2) ==> ((R[NW#input] - I[NW#input]) == ((C[NW#data] - I[NW#data]) - 5));
  assume (M[NW#St][R[NW#St]] == 0) <==> (((R[NW#input] - I[NW#input]) == 0) || ((R[NW#input] - I[NW#input]) == 2));
  assume ((R[NW#input] - I[NW#input]) == 0) ==> ((C[NW#len] - I[NW#len]) == 0);
  assume ((R[NW#input] - I[NW#input]) > 0) ==> (M[NW#octet_count][R[NW#octet_count]] == AT#BvAdd8(M[NW#input][I[NW#input]], 6bv8));
  assume ((R[NW#input] - I[NW#input]) > 0) ==> ((C[NW#len] - I[NW#len]) == 1);
  assume M[NW#input][I[NW#input]] == 1bv8;
  assume (1 <= (C[NW#input] - R[NW#input])) && (1 <= (C[NW#octet_index] - R[NW#octet_index])) && (1 <= (C[NW#octet_count] - R[NW#octet_count])) && (1 <= (C[NW#St] - R[NW#St])) && (M[NW#St][R[NW#St]] == 0);
  pl_bits#bits_in := M[NW#input][R[NW#input]];
  R[NW#input] := R[NW#input] + 1;
  octet_index_in#octet_index := M[NW#octet_index][R[NW#octet_index]];
  R[NW#octet_index] := R[NW#octet_index] + 1;
  octet_count_in#octet_count := M[NW#octet_count][R[NW#octet_count]];
  R[NW#octet_count] := R[NW#octet_count] + 1;
  St_in#St := M[NW#St][R[NW#St]];
  R[NW#St] := R[NW#St] + 1;
  M[NW#octet_index][C[NW#octet_index]] := 0bv8;
  C[NW#octet_index] := C[NW#octet_index] + 1;
  M[NW#octet_count][C[NW#octet_count]] := AT#BvAdd8(AT#BvAdd8(pl_bits#bits_in, 5bv8), 1bv8);
  C[NW#octet_count] := C[NW#octet_count] + 1;
  M[NW#St][C[NW#St]] := 1;
  C[NW#St] := C[NW#St] + 1;
  M[NW#len][C[NW#len]] := AT#BvAdd8(AT#BvAdd8(pl_bits#bits_in, 5bv8), 1bv8);
  C[NW#len] := C[NW#len] + 1;
  assert {:msg "148.15: Action at 37.2 ('get_data_len') for actor instance 'a' might not preserve the channel invariant (#28)"} ((C[NW#octet_count] - R[NW#octet_count]) == 1) && ((C[NW#octet_index] - R[NW#octet_index]) == 1) && ((C[NW#St] - R[NW#St]) == 1);
  assert {:msg "151.15: Action at 37.2 ('get_data_len') for actor instance 'a' might not preserve the channel invariant (#29)"} AT#BvUle8(0bv8, M[NW#octet_index][R[NW#octet_index]]) && AT#BvUle8(M[NW#octet_index][R[NW#octet_index]], M[NW#octet_count][R[NW#octet_count]]);
  assert {:msg "154.15: Action at 37.2 ('get_data_len') for actor instance 'a' might not preserve the channel invariant (#30)"} (0 <= M[NW#St][R[NW#St]]) && (M[NW#St][R[NW#St]] <= 2);
  assert {:msg "156.15: Action at 37.2 ('get_data_len') for actor instance 'a' might not preserve the channel invariant (#31)"} (C[NW#input] - I[NW#input]) <= 2;
  assert {:msg "157.15: Action at 37.2 ('get_data_len') for actor instance 'a' might not preserve the channel invariant (#32)"} ((C[NW#input] - I[NW#input]) > 0) ==> (M[NW#input][I[NW#input]] == 1bv8);
  assert {:msg "159.15: Action at 37.2 ('get_data_len') for actor instance 'a' might not preserve the channel invariant (#33)"} (M[NW#St][R[NW#St]] == 0) ==> (M[NW#octet_index][R[NW#octet_index]] == M[NW#octet_count][R[NW#octet_count]]);
  assert {:msg "160.15: Action at 37.2 ('get_data_len') for actor instance 'a' might not preserve the channel invariant (#34)"} (M[NW#St][R[NW#St]] == 1) ==> AT#BvUle8(0bv8, M[NW#octet_index][R[NW#octet_index]]) && AT#BvUle8(M[NW#octet_index][R[NW#octet_index]], 5bv8);
  assert {:msg "161.15: Action at 37.2 ('get_data_len') for actor instance 'a' might not preserve the channel invariant (#35)"} (M[NW#St][R[NW#St]] == 2) ==> AT#BvUle8(6bv8, M[NW#octet_index][R[NW#octet_index]]) && AT#BvUlt8(M[NW#octet_index][R[NW#octet_index]], M[NW#octet_count][R[NW#octet_count]]);
  assert {:msg "163.15: Action at 37.2 ('get_data_len') for actor instance 'a' might not preserve the channel invariant (#36)"} (M[NW#St][R[NW#St]] == 0) && ((R[NW#input] - I[NW#input]) == 0) ==> ((C[NW#data] - I[NW#data]) == 0);
  assert {:msg "164.15: Action at 37.2 ('get_data_len') for actor instance 'a' might not preserve the channel invariant (#37)"} (M[NW#St][R[NW#St]] == 0) && ((R[NW#input] - I[NW#input]) > 0) ==> ((C[NW#data] - I[NW#data]) == AT#Bv2Int(M[NW#octet_count][R[NW#octet_count]]));
  assert {:msg "166.15: Action at 37.2 ('get_data_len') for actor instance 'a' might not preserve the channel invariant (#38)"} (M[NW#St][R[NW#St]] == 1) ==> ((R[NW#input] - I[NW#input]) == 1);
  assert {:msg "167.15: Action at 37.2 ('get_data_len') for actor instance 'a' might not preserve the channel invariant (#39)"} ((M[NW#St][R[NW#St]] == 1) || (M[NW#St][R[NW#St]] == 2)) ==> ((C[NW#data] - I[NW#data]) == AT#Bv2Int(M[NW#octet_index][R[NW#octet_index]]));
  assert {:msg "168.15: Action at 37.2 ('get_data_len') for actor instance 'a' might not preserve the channel invariant (#40)"} (M[NW#St][R[NW#St]] == 2) ==> ((R[NW#input] - I[NW#input]) == ((C[NW#data] - I[NW#data]) - 5));
  assert {:msg "170.15: Action at 37.2 ('get_data_len') for actor instance 'a' might not preserve the channel invariant (#41)"} (M[NW#St][R[NW#St]] == 0) <==> (((R[NW#input] - I[NW#input]) == 0) || ((R[NW#input] - I[NW#input]) == 2));
  assert {:msg "172.15: Action at 37.2 ('get_data_len') for actor instance 'a' might not preserve the channel invariant (#42)"} ((R[NW#input] - I[NW#input]) == 0) ==> ((C[NW#len] - I[NW#len]) == 0);
  assert {:msg "173.15: Action at 37.2 ('get_data_len') for actor instance 'a' might not preserve the channel invariant (#43)"} ((R[NW#input] - I[NW#input]) > 0) ==> (M[NW#octet_count][R[NW#octet_count]] == AT#BvAdd8(M[NW#input][I[NW#input]], 6bv8));
  assert {:msg "175.15: Action at 37.2 ('get_data_len') for actor instance 'a' might not preserve the channel invariant (#44)"} ((R[NW#input] - I[NW#input]) > 0) ==> ((C[NW#len] - I[NW#len]) == 1);
}
procedure NW##headerAdd#send_header#8()
  modifies C, R, M, I, H;
{
  var NW#a: Actor;
  var NW#input: Chan (bv8);
  var NW#octet_count: Chan (bv8);
  var NW#octet_index: Chan (bv8);
  var NW#St: Chan (int);
  var NW#data: Chan (bv8);
  var NW#len: Chan (bv8);
  var AV#a#octet_count: bv8;
  var AV#a#octet_index: bv8;
  var AV#a#HEADER_LEN: int;
  var AV#a#Header: Map (bv8) (bv8);
  var AV#a#data_out: bv8;
  var octet_index_in#octet_index: bv8;
  var octet_count_in#octet_count: bv8;
  var St_in#St: int;
  assume (NW#input != NW#octet_count) && (NW#input != NW#octet_index) && (NW#input != NW#data) && (NW#input != NW#len) && (NW#octet_count != NW#octet_index) && (NW#octet_count != NW#data) && (NW#octet_count != NW#len) && (NW#octet_index != NW#data) && (NW#octet_index != NW#len) && (NW#data != NW#len);
  assume 0 <= I[NW#input];
  assume I[NW#input] <= R[NW#input];
  assume R[NW#input] <= C[NW#input];
  assume 0 <= I[NW#octet_count];
  assume I[NW#octet_count] <= R[NW#octet_count];
  assume R[NW#octet_count] <= C[NW#octet_count];
  assume 0 <= I[NW#octet_index];
  assume I[NW#octet_index] <= R[NW#octet_index];
  assume R[NW#octet_index] <= C[NW#octet_index];
  assume 0 <= I[NW#St];
  assume I[NW#St] <= R[NW#St];
  assume R[NW#St] <= C[NW#St];
  assume 0 <= I[NW#data];
  assume I[NW#data] <= R[NW#data];
  assume R[NW#data] <= C[NW#data];
  assume I[NW#data] == R[NW#data];
  assume 0 <= I[NW#len];
  assume I[NW#len] <= R[NW#len];
  assume R[NW#len] <= C[NW#len];
  assume I[NW#len] == R[NW#len];
  assume ((C[NW#octet_count] - R[NW#octet_count]) == 1) && ((C[NW#octet_index] - R[NW#octet_index]) == 1) && ((C[NW#St] - R[NW#St]) == 1);
  assume AT#BvUle8(0bv8, M[NW#octet_index][R[NW#octet_index]]) && AT#BvUle8(M[NW#octet_index][R[NW#octet_index]], M[NW#octet_count][R[NW#octet_count]]);
  assume (0 <= M[NW#St][R[NW#St]]) && (M[NW#St][R[NW#St]] <= 2);
  assume (C[NW#input] - I[NW#input]) <= 2;
  assume ((C[NW#input] - I[NW#input]) > 0) ==> (M[NW#input][I[NW#input]] == 1bv8);
  assume (M[NW#St][R[NW#St]] == 0) ==> (M[NW#octet_index][R[NW#octet_index]] == M[NW#octet_count][R[NW#octet_count]]);
  assume (M[NW#St][R[NW#St]] == 1) ==> AT#BvUle8(0bv8, M[NW#octet_index][R[NW#octet_index]]) && AT#BvUle8(M[NW#octet_index][R[NW#octet_index]], 5bv8);
  assume (M[NW#St][R[NW#St]] == 2) ==> AT#BvUle8(6bv8, M[NW#octet_index][R[NW#octet_index]]) && AT#BvUlt8(M[NW#octet_index][R[NW#octet_index]], M[NW#octet_count][R[NW#octet_count]]);
  assume (M[NW#St][R[NW#St]] == 0) && ((R[NW#input] - I[NW#input]) == 0) ==> ((C[NW#data] - I[NW#data]) == 0);
  assume (M[NW#St][R[NW#St]] == 0) && ((R[NW#input] - I[NW#input]) > 0) ==> ((C[NW#data] - I[NW#data]) == AT#Bv2Int(M[NW#octet_count][R[NW#octet_count]]));
  assume (M[NW#St][R[NW#St]] == 1) ==> ((R[NW#input] - I[NW#input]) == 1);
  assume ((M[NW#St][R[NW#St]] == 1) || (M[NW#St][R[NW#St]] == 2)) ==> ((C[NW#data] - I[NW#data]) == AT#Bv2Int(M[NW#octet_index][R[NW#octet_index]]));
  assume (M[NW#St][R[NW#St]] == 2) ==> ((R[NW#input] - I[NW#input]) == ((C[NW#data] - I[NW#data]) - 5));
  assume (M[NW#St][R[NW#St]] == 0) <==> (((R[NW#input] - I[NW#input]) == 0) || ((R[NW#input] - I[NW#input]) == 2));
  assume ((R[NW#input] - I[NW#input]) == 0) ==> ((C[NW#len] - I[NW#len]) == 0);
  assume ((R[NW#input] - I[NW#input]) > 0) ==> (M[NW#octet_count][R[NW#octet_count]] == AT#BvAdd8(M[NW#input][I[NW#input]], 6bv8));
  assume ((R[NW#input] - I[NW#input]) > 0) ==> ((C[NW#len] - I[NW#len]) == 1);
  assume M[NW#input][I[NW#input]] == 1bv8;
  assume (1 <= (C[NW#octet_index] - R[NW#octet_index])) && (1 <= (C[NW#octet_count] - R[NW#octet_count])) && (1 <= (C[NW#St] - R[NW#St])) && AT#BvUlt8(M[NW#octet_index][R[NW#octet_index]], 5bv8) && (M[NW#St][R[NW#St]] == 1);
  octet_index_in#octet_index := M[NW#octet_index][R[NW#octet_index]];
  R[NW#octet_index] := R[NW#octet_index] + 1;
  octet_count_in#octet_count := M[NW#octet_count][R[NW#octet_count]];
  R[NW#octet_count] := R[NW#octet_count] + 1;
  St_in#St := M[NW#St][R[NW#St]];
  R[NW#St] := R[NW#St] + 1;
  havoc AV#a#data_out;
  M[NW#St][C[NW#St]] := 1;
  C[NW#St] := C[NW#St] + 1;
  M[NW#octet_index][C[NW#octet_index]] := AT#BvAdd8(octet_index_in#octet_index, 1bv8);
  C[NW#octet_index] := C[NW#octet_index] + 1;
  M[NW#octet_count][C[NW#octet_count]] := octet_count_in#octet_count;
  C[NW#octet_count] := C[NW#octet_count] + 1;
  M[NW#data][C[NW#data]] := AV#a#data_out;
  C[NW#data] := C[NW#data] + 1;
  assert {:msg "148.15: Action at 53.2 ('send_header') for actor instance 'a' might not preserve the channel invariant (#45)"} ((C[NW#octet_count] - R[NW#octet_count]) == 1) && ((C[NW#octet_index] - R[NW#octet_index]) == 1) && ((C[NW#St] - R[NW#St]) == 1);
  assert {:msg "151.15: Action at 53.2 ('send_header') for actor instance 'a' might not preserve the channel invariant (#46)"} AT#BvUle8(0bv8, M[NW#octet_index][R[NW#octet_index]]) && AT#BvUle8(M[NW#octet_index][R[NW#octet_index]], M[NW#octet_count][R[NW#octet_count]]);
  assert {:msg "154.15: Action at 53.2 ('send_header') for actor instance 'a' might not preserve the channel invariant (#47)"} (0 <= M[NW#St][R[NW#St]]) && (M[NW#St][R[NW#St]] <= 2);
  assert {:msg "156.15: Action at 53.2 ('send_header') for actor instance 'a' might not preserve the channel invariant (#48)"} (C[NW#input] - I[NW#input]) <= 2;
  assert {:msg "157.15: Action at 53.2 ('send_header') for actor instance 'a' might not preserve the channel invariant (#49)"} ((C[NW#input] - I[NW#input]) > 0) ==> (M[NW#input][I[NW#input]] == 1bv8);
  assert {:msg "159.15: Action at 53.2 ('send_header') for actor instance 'a' might not preserve the channel invariant (#50)"} (M[NW#St][R[NW#St]] == 0) ==> (M[NW#octet_index][R[NW#octet_index]] == M[NW#octet_count][R[NW#octet_count]]);
  assert {:msg "160.15: Action at 53.2 ('send_header') for actor instance 'a' might not preserve the channel invariant (#51)"} (M[NW#St][R[NW#St]] == 1) ==> AT#BvUle8(0bv8, M[NW#octet_index][R[NW#octet_index]]) && AT#BvUle8(M[NW#octet_index][R[NW#octet_index]], 5bv8);
  assert {:msg "161.15: Action at 53.2 ('send_header') for actor instance 'a' might not preserve the channel invariant (#52)"} (M[NW#St][R[NW#St]] == 2) ==> AT#BvUle8(6bv8, M[NW#octet_index][R[NW#octet_index]]) && AT#BvUlt8(M[NW#octet_index][R[NW#octet_index]], M[NW#octet_count][R[NW#octet_count]]);
  assert {:msg "163.15: Action at 53.2 ('send_header') for actor instance 'a' might not preserve the channel invariant (#53)"} (M[NW#St][R[NW#St]] == 0) && ((R[NW#input] - I[NW#input]) == 0) ==> ((C[NW#data] - I[NW#data]) == 0);
  assert {:msg "164.15: Action at 53.2 ('send_header') for actor instance 'a' might not preserve the channel invariant (#54)"} (M[NW#St][R[NW#St]] == 0) && ((R[NW#input] - I[NW#input]) > 0) ==> ((C[NW#data] - I[NW#data]) == AT#Bv2Int(M[NW#octet_count][R[NW#octet_count]]));
  assert {:msg "166.15: Action at 53.2 ('send_header') for actor instance 'a' might not preserve the channel invariant (#55)"} (M[NW#St][R[NW#St]] == 1) ==> ((R[NW#input] - I[NW#input]) == 1);
  assert {:msg "167.15: Action at 53.2 ('send_header') for actor instance 'a' might not preserve the channel invariant (#56)"} ((M[NW#St][R[NW#St]] == 1) || (M[NW#St][R[NW#St]] == 2)) ==> ((C[NW#data] - I[NW#data]) == AT#Bv2Int(M[NW#octet_index][R[NW#octet_index]]));
  assert {:msg "168.15: Action at 53.2 ('send_header') for actor instance 'a' might not preserve the channel invariant (#57)"} (M[NW#St][R[NW#St]] == 2) ==> ((R[NW#input] - I[NW#input]) == ((C[NW#data] - I[NW#data]) - 5));
  assert {:msg "170.15: Action at 53.2 ('send_header') for actor instance 'a' might not preserve the channel invariant (#58)"} (M[NW#St][R[NW#St]] == 0) <==> (((R[NW#input] - I[NW#input]) == 0) || ((R[NW#input] - I[NW#input]) == 2));
  assert {:msg "172.15: Action at 53.2 ('send_header') for actor instance 'a' might not preserve the channel invariant (#59)"} ((R[NW#input] - I[NW#input]) == 0) ==> ((C[NW#len] - I[NW#len]) == 0);
  assert {:msg "173.15: Action at 53.2 ('send_header') for actor instance 'a' might not preserve the channel invariant (#60)"} ((R[NW#input] - I[NW#input]) > 0) ==> (M[NW#octet_count][R[NW#octet_count]] == AT#BvAdd8(M[NW#input][I[NW#input]], 6bv8));
  assert {:msg "175.15: Action at 53.2 ('send_header') for actor instance 'a' might not preserve the channel invariant (#61)"} ((R[NW#input] - I[NW#input]) > 0) ==> ((C[NW#len] - I[NW#len]) == 1);
}
procedure NW##headerAdd#send_length#9()
  modifies C, R, M, I, H;
{
  var NW#a: Actor;
  var NW#input: Chan (bv8);
  var NW#octet_count: Chan (bv8);
  var NW#octet_index: Chan (bv8);
  var NW#St: Chan (int);
  var NW#data: Chan (bv8);
  var NW#len: Chan (bv8);
  var AV#a#octet_count: bv8;
  var AV#a#octet_index: bv8;
  var AV#a#HEADER_LEN: int;
  var AV#a#Header: Map (bv8) (bv8);
  var AV#a#data_out: bv8;
  var octet_index_in#octet_index: bv8;
  var octet_count_in#octet_count: bv8;
  var St_in#St: int;
  assume (NW#input != NW#octet_count) && (NW#input != NW#octet_index) && (NW#input != NW#data) && (NW#input != NW#len) && (NW#octet_count != NW#octet_index) && (NW#octet_count != NW#data) && (NW#octet_count != NW#len) && (NW#octet_index != NW#data) && (NW#octet_index != NW#len) && (NW#data != NW#len);
  assume 0 <= I[NW#input];
  assume I[NW#input] <= R[NW#input];
  assume R[NW#input] <= C[NW#input];
  assume 0 <= I[NW#octet_count];
  assume I[NW#octet_count] <= R[NW#octet_count];
  assume R[NW#octet_count] <= C[NW#octet_count];
  assume 0 <= I[NW#octet_index];
  assume I[NW#octet_index] <= R[NW#octet_index];
  assume R[NW#octet_index] <= C[NW#octet_index];
  assume 0 <= I[NW#St];
  assume I[NW#St] <= R[NW#St];
  assume R[NW#St] <= C[NW#St];
  assume 0 <= I[NW#data];
  assume I[NW#data] <= R[NW#data];
  assume R[NW#data] <= C[NW#data];
  assume I[NW#data] == R[NW#data];
  assume 0 <= I[NW#len];
  assume I[NW#len] <= R[NW#len];
  assume R[NW#len] <= C[NW#len];
  assume I[NW#len] == R[NW#len];
  assume ((C[NW#octet_count] - R[NW#octet_count]) == 1) && ((C[NW#octet_index] - R[NW#octet_index]) == 1) && ((C[NW#St] - R[NW#St]) == 1);
  assume AT#BvUle8(0bv8, M[NW#octet_index][R[NW#octet_index]]) && AT#BvUle8(M[NW#octet_index][R[NW#octet_index]], M[NW#octet_count][R[NW#octet_count]]);
  assume (0 <= M[NW#St][R[NW#St]]) && (M[NW#St][R[NW#St]] <= 2);
  assume (C[NW#input] - I[NW#input]) <= 2;
  assume ((C[NW#input] - I[NW#input]) > 0) ==> (M[NW#input][I[NW#input]] == 1bv8);
  assume (M[NW#St][R[NW#St]] == 0) ==> (M[NW#octet_index][R[NW#octet_index]] == M[NW#octet_count][R[NW#octet_count]]);
  assume (M[NW#St][R[NW#St]] == 1) ==> AT#BvUle8(0bv8, M[NW#octet_index][R[NW#octet_index]]) && AT#BvUle8(M[NW#octet_index][R[NW#octet_index]], 5bv8);
  assume (M[NW#St][R[NW#St]] == 2) ==> AT#BvUle8(6bv8, M[NW#octet_index][R[NW#octet_index]]) && AT#BvUlt8(M[NW#octet_index][R[NW#octet_index]], M[NW#octet_count][R[NW#octet_count]]);
  assume (M[NW#St][R[NW#St]] == 0) && ((R[NW#input] - I[NW#input]) == 0) ==> ((C[NW#data] - I[NW#data]) == 0);
  assume (M[NW#St][R[NW#St]] == 0) && ((R[NW#input] - I[NW#input]) > 0) ==> ((C[NW#data] - I[NW#data]) == AT#Bv2Int(M[NW#octet_count][R[NW#octet_count]]));
  assume (M[NW#St][R[NW#St]] == 1) ==> ((R[NW#input] - I[NW#input]) == 1);
  assume ((M[NW#St][R[NW#St]] == 1) || (M[NW#St][R[NW#St]] == 2)) ==> ((C[NW#data] - I[NW#data]) == AT#Bv2Int(M[NW#octet_index][R[NW#octet_index]]));
  assume (M[NW#St][R[NW#St]] == 2) ==> ((R[NW#input] - I[NW#input]) == ((C[NW#data] - I[NW#data]) - 5));
  assume (M[NW#St][R[NW#St]] == 0) <==> (((R[NW#input] - I[NW#input]) == 0) || ((R[NW#input] - I[NW#input]) == 2));
  assume ((R[NW#input] - I[NW#input]) == 0) ==> ((C[NW#len] - I[NW#len]) == 0);
  assume ((R[NW#input] - I[NW#input]) > 0) ==> (M[NW#octet_count][R[NW#octet_count]] == AT#BvAdd8(M[NW#input][I[NW#input]], 6bv8));
  assume ((R[NW#input] - I[NW#input]) > 0) ==> ((C[NW#len] - I[NW#len]) == 1);
  assume M[NW#input][I[NW#input]] == 1bv8;
  assume (1 <= (C[NW#octet_index] - R[NW#octet_index])) && (1 <= (C[NW#octet_count] - R[NW#octet_count])) && (1 <= (C[NW#St] - R[NW#St])) && (M[NW#octet_index][R[NW#octet_index]] == 5bv8) && (M[NW#St][R[NW#St]] == 1);
  octet_index_in#octet_index := M[NW#octet_index][R[NW#octet_index]];
  R[NW#octet_index] := R[NW#octet_index] + 1;
  octet_count_in#octet_count := M[NW#octet_count][R[NW#octet_count]];
  R[NW#octet_count] := R[NW#octet_count] + 1;
  St_in#St := M[NW#St][R[NW#St]];
  R[NW#St] := R[NW#St] + 1;
  M[NW#St][C[NW#St]] := 2;
  C[NW#St] := C[NW#St] + 1;
  M[NW#octet_index][C[NW#octet_index]] := AT#BvAdd8(octet_index_in#octet_index, 1bv8);
  C[NW#octet_index] := C[NW#octet_index] + 1;
  M[NW#octet_count][C[NW#octet_count]] := octet_count_in#octet_count;
  C[NW#octet_count] := C[NW#octet_count] + 1;
  M[NW#data][C[NW#data]] := AT#BvSub8(AT#BvSub8(octet_count_in#octet_count, 5bv8), 1bv8);
  C[NW#data] := C[NW#data] + 1;
  assert {:msg "148.15: Action at 71.2 ('send_length') for actor instance 'a' might not preserve the channel invariant (#62)"} ((C[NW#octet_count] - R[NW#octet_count]) == 1) && ((C[NW#octet_index] - R[NW#octet_index]) == 1) && ((C[NW#St] - R[NW#St]) == 1);
  assert {:msg "151.15: Action at 71.2 ('send_length') for actor instance 'a' might not preserve the channel invariant (#63)"} AT#BvUle8(0bv8, M[NW#octet_index][R[NW#octet_index]]) && AT#BvUle8(M[NW#octet_index][R[NW#octet_index]], M[NW#octet_count][R[NW#octet_count]]);
  assert {:msg "154.15: Action at 71.2 ('send_length') for actor instance 'a' might not preserve the channel invariant (#64)"} (0 <= M[NW#St][R[NW#St]]) && (M[NW#St][R[NW#St]] <= 2);
  assert {:msg "156.15: Action at 71.2 ('send_length') for actor instance 'a' might not preserve the channel invariant (#65)"} (C[NW#input] - I[NW#input]) <= 2;
  assert {:msg "157.15: Action at 71.2 ('send_length') for actor instance 'a' might not preserve the channel invariant (#66)"} ((C[NW#input] - I[NW#input]) > 0) ==> (M[NW#input][I[NW#input]] == 1bv8);
  assert {:msg "159.15: Action at 71.2 ('send_length') for actor instance 'a' might not preserve the channel invariant (#67)"} (M[NW#St][R[NW#St]] == 0) ==> (M[NW#octet_index][R[NW#octet_index]] == M[NW#octet_count][R[NW#octet_count]]);
  assert {:msg "160.15: Action at 71.2 ('send_length') for actor instance 'a' might not preserve the channel invariant (#68)"} (M[NW#St][R[NW#St]] == 1) ==> AT#BvUle8(0bv8, M[NW#octet_index][R[NW#octet_index]]) && AT#BvUle8(M[NW#octet_index][R[NW#octet_index]], 5bv8);
  assert {:msg "161.15: Action at 71.2 ('send_length') for actor instance 'a' might not preserve the channel invariant (#69)"} (M[NW#St][R[NW#St]] == 2) ==> AT#BvUle8(6bv8, M[NW#octet_index][R[NW#octet_index]]) && AT#BvUlt8(M[NW#octet_index][R[NW#octet_index]], M[NW#octet_count][R[NW#octet_count]]);
  assert {:msg "163.15: Action at 71.2 ('send_length') for actor instance 'a' might not preserve the channel invariant (#70)"} (M[NW#St][R[NW#St]] == 0) && ((R[NW#input] - I[NW#input]) == 0) ==> ((C[NW#data] - I[NW#data]) == 0);
  assert {:msg "164.15: Action at 71.2 ('send_length') for actor instance 'a' might not preserve the channel invariant (#71)"} (M[NW#St][R[NW#St]] == 0) && ((R[NW#input] - I[NW#input]) > 0) ==> ((C[NW#data] - I[NW#data]) == AT#Bv2Int(M[NW#octet_count][R[NW#octet_count]]));
  assert {:msg "166.15: Action at 71.2 ('send_length') for actor instance 'a' might not preserve the channel invariant (#72)"} (M[NW#St][R[NW#St]] == 1) ==> ((R[NW#input] - I[NW#input]) == 1);
  assert {:msg "167.15: Action at 71.2 ('send_length') for actor instance 'a' might not preserve the channel invariant (#73)"} ((M[NW#St][R[NW#St]] == 1) || (M[NW#St][R[NW#St]] == 2)) ==> ((C[NW#data] - I[NW#data]) == AT#Bv2Int(M[NW#octet_index][R[NW#octet_index]]));
  assert {:msg "168.15: Action at 71.2 ('send_length') for actor instance 'a' might not preserve the channel invariant (#74)"} (M[NW#St][R[NW#St]] == 2) ==> ((R[NW#input] - I[NW#input]) == ((C[NW#data] - I[NW#data]) - 5));
  assert {:msg "170.15: Action at 71.2 ('send_length') for actor instance 'a' might not preserve the channel invariant (#75)"} (M[NW#St][R[NW#St]] == 0) <==> (((R[NW#input] - I[NW#input]) == 0) || ((R[NW#input] - I[NW#input]) == 2));
  assert {:msg "172.15: Action at 71.2 ('send_length') for actor instance 'a' might not preserve the channel invariant (#76)"} ((R[NW#input] - I[NW#input]) == 0) ==> ((C[NW#len] - I[NW#len]) == 0);
  assert {:msg "173.15: Action at 71.2 ('send_length') for actor instance 'a' might not preserve the channel invariant (#77)"} ((R[NW#input] - I[NW#input]) > 0) ==> (M[NW#octet_count][R[NW#octet_count]] == AT#BvAdd8(M[NW#input][I[NW#input]], 6bv8));
  assert {:msg "175.15: Action at 71.2 ('send_length') for actor instance 'a' might not preserve the channel invariant (#78)"} ((R[NW#input] - I[NW#input]) > 0) ==> ((C[NW#len] - I[NW#len]) == 1);
}
procedure NW##headerAdd#send_payload_octet#10()
  modifies C, R, M, I, H;
{
  var NW#a: Actor;
  var NW#input: Chan (bv8);
  var NW#octet_count: Chan (bv8);
  var NW#octet_index: Chan (bv8);
  var NW#St: Chan (int);
  var NW#data: Chan (bv8);
  var NW#len: Chan (bv8);
  var AV#a#octet_count: bv8;
  var AV#a#octet_index: bv8;
  var AV#a#HEADER_LEN: int;
  var AV#a#Header: Map (bv8) (bv8);
  var AV#a#data_out: bv8;
  var pl_bits#bits_in: bv8;
  var octet_index_in#octet_index: bv8;
  var octet_count_in#octet_count: bv8;
  var St_in#St: int;
  assume (NW#input != NW#octet_count) && (NW#input != NW#octet_index) && (NW#input != NW#data) && (NW#input != NW#len) && (NW#octet_count != NW#octet_index) && (NW#octet_count != NW#data) && (NW#octet_count != NW#len) && (NW#octet_index != NW#data) && (NW#octet_index != NW#len) && (NW#data != NW#len);
  assume 0 <= I[NW#input];
  assume I[NW#input] <= R[NW#input];
  assume R[NW#input] <= C[NW#input];
  assume 0 <= I[NW#octet_count];
  assume I[NW#octet_count] <= R[NW#octet_count];
  assume R[NW#octet_count] <= C[NW#octet_count];
  assume 0 <= I[NW#octet_index];
  assume I[NW#octet_index] <= R[NW#octet_index];
  assume R[NW#octet_index] <= C[NW#octet_index];
  assume 0 <= I[NW#St];
  assume I[NW#St] <= R[NW#St];
  assume R[NW#St] <= C[NW#St];
  assume 0 <= I[NW#data];
  assume I[NW#data] <= R[NW#data];
  assume R[NW#data] <= C[NW#data];
  assume I[NW#data] == R[NW#data];
  assume 0 <= I[NW#len];
  assume I[NW#len] <= R[NW#len];
  assume R[NW#len] <= C[NW#len];
  assume I[NW#len] == R[NW#len];
  assume ((C[NW#octet_count] - R[NW#octet_count]) == 1) && ((C[NW#octet_index] - R[NW#octet_index]) == 1) && ((C[NW#St] - R[NW#St]) == 1);
  assume AT#BvUle8(0bv8, M[NW#octet_index][R[NW#octet_index]]) && AT#BvUle8(M[NW#octet_index][R[NW#octet_index]], M[NW#octet_count][R[NW#octet_count]]);
  assume (0 <= M[NW#St][R[NW#St]]) && (M[NW#St][R[NW#St]] <= 2);
  assume (C[NW#input] - I[NW#input]) <= 2;
  assume ((C[NW#input] - I[NW#input]) > 0) ==> (M[NW#input][I[NW#input]] == 1bv8);
  assume (M[NW#St][R[NW#St]] == 0) ==> (M[NW#octet_index][R[NW#octet_index]] == M[NW#octet_count][R[NW#octet_count]]);
  assume (M[NW#St][R[NW#St]] == 1) ==> AT#BvUle8(0bv8, M[NW#octet_index][R[NW#octet_index]]) && AT#BvUle8(M[NW#octet_index][R[NW#octet_index]], 5bv8);
  assume (M[NW#St][R[NW#St]] == 2) ==> AT#BvUle8(6bv8, M[NW#octet_index][R[NW#octet_index]]) && AT#BvUlt8(M[NW#octet_index][R[NW#octet_index]], M[NW#octet_count][R[NW#octet_count]]);
  assume (M[NW#St][R[NW#St]] == 0) && ((R[NW#input] - I[NW#input]) == 0) ==> ((C[NW#data] - I[NW#data]) == 0);
  assume (M[NW#St][R[NW#St]] == 0) && ((R[NW#input] - I[NW#input]) > 0) ==> ((C[NW#data] - I[NW#data]) == AT#Bv2Int(M[NW#octet_count][R[NW#octet_count]]));
  assume (M[NW#St][R[NW#St]] == 1) ==> ((R[NW#input] - I[NW#input]) == 1);
  assume ((M[NW#St][R[NW#St]] == 1) || (M[NW#St][R[NW#St]] == 2)) ==> ((C[NW#data] - I[NW#data]) == AT#Bv2Int(M[NW#octet_index][R[NW#octet_index]]));
  assume (M[NW#St][R[NW#St]] == 2) ==> ((R[NW#input] - I[NW#input]) == ((C[NW#data] - I[NW#data]) - 5));
  assume (M[NW#St][R[NW#St]] == 0) <==> (((R[NW#input] - I[NW#input]) == 0) || ((R[NW#input] - I[NW#input]) == 2));
  assume ((R[NW#input] - I[NW#input]) == 0) ==> ((C[NW#len] - I[NW#len]) == 0);
  assume ((R[NW#input] - I[NW#input]) > 0) ==> (M[NW#octet_count][R[NW#octet_count]] == AT#BvAdd8(M[NW#input][I[NW#input]], 6bv8));
  assume ((R[NW#input] - I[NW#input]) > 0) ==> ((C[NW#len] - I[NW#len]) == 1);
  assume M[NW#input][I[NW#input]] == 1bv8;
  assume (1 <= (C[NW#input] - R[NW#input])) && (1 <= (C[NW#octet_index] - R[NW#octet_index])) && (1 <= (C[NW#octet_count] - R[NW#octet_count])) && (1 <= (C[NW#St] - R[NW#St])) && AT#BvUlt8(M[NW#octet_index][R[NW#octet_index]], M[NW#octet_count][R[NW#octet_count]]) && (M[NW#St][R[NW#St]] == 2);
  pl_bits#bits_in := M[NW#input][R[NW#input]];
  R[NW#input] := R[NW#input] + 1;
  octet_index_in#octet_index := M[NW#octet_index][R[NW#octet_index]];
  R[NW#octet_index] := R[NW#octet_index] + 1;
  octet_count_in#octet_count := M[NW#octet_count][R[NW#octet_count]];
  R[NW#octet_count] := R[NW#octet_count] + 1;
  St_in#St := M[NW#St][R[NW#St]];
  R[NW#St] := R[NW#St] + 1;
  M[NW#St][C[NW#St]] := (if AT#BvAdd8(octet_index_in#octet_index, 1bv8) == octet_count_in#octet_count then 0 else 2);
  C[NW#St] := C[NW#St] + 1;
  M[NW#octet_index][C[NW#octet_index]] := AT#BvAdd8(octet_index_in#octet_index, 1bv8);
  C[NW#octet_index] := C[NW#octet_index] + 1;
  M[NW#octet_count][C[NW#octet_count]] := octet_count_in#octet_count;
  C[NW#octet_count] := C[NW#octet_count] + 1;
  M[NW#data][C[NW#data]] := pl_bits#bits_in;
  C[NW#data] := C[NW#data] + 1;
  assert {:msg "148.15: Action at 87.2 ('send_payload_octet') for actor instance 'a' might not preserve the channel invariant (#79)"} ((C[NW#octet_count] - R[NW#octet_count]) == 1) && ((C[NW#octet_index] - R[NW#octet_index]) == 1) && ((C[NW#St] - R[NW#St]) == 1);
  assert {:msg "151.15: Action at 87.2 ('send_payload_octet') for actor instance 'a' might not preserve the channel invariant (#80)"} AT#BvUle8(0bv8, M[NW#octet_index][R[NW#octet_index]]) && AT#BvUle8(M[NW#octet_index][R[NW#octet_index]], M[NW#octet_count][R[NW#octet_count]]);
  assert {:msg "154.15: Action at 87.2 ('send_payload_octet') for actor instance 'a' might not preserve the channel invariant (#81)"} (0 <= M[NW#St][R[NW#St]]) && (M[NW#St][R[NW#St]] <= 2);
  assert {:msg "156.15: Action at 87.2 ('send_payload_octet') for actor instance 'a' might not preserve the channel invariant (#82)"} (C[NW#input] - I[NW#input]) <= 2;
  assert {:msg "157.15: Action at 87.2 ('send_payload_octet') for actor instance 'a' might not preserve the channel invariant (#83)"} ((C[NW#input] - I[NW#input]) > 0) ==> (M[NW#input][I[NW#input]] == 1bv8);
  assert {:msg "159.15: Action at 87.2 ('send_payload_octet') for actor instance 'a' might not preserve the channel invariant (#84)"} (M[NW#St][R[NW#St]] == 0) ==> (M[NW#octet_index][R[NW#octet_index]] == M[NW#octet_count][R[NW#octet_count]]);
  assert {:msg "160.15: Action at 87.2 ('send_payload_octet') for actor instance 'a' might not preserve the channel invariant (#85)"} (M[NW#St][R[NW#St]] == 1) ==> AT#BvUle8(0bv8, M[NW#octet_index][R[NW#octet_index]]) && AT#BvUle8(M[NW#octet_index][R[NW#octet_index]], 5bv8);
  assert {:msg "161.15: Action at 87.2 ('send_payload_octet') for actor instance 'a' might not preserve the channel invariant (#86)"} (M[NW#St][R[NW#St]] == 2) ==> AT#BvUle8(6bv8, M[NW#octet_index][R[NW#octet_index]]) && AT#BvUlt8(M[NW#octet_index][R[NW#octet_index]], M[NW#octet_count][R[NW#octet_count]]);
  assert {:msg "163.15: Action at 87.2 ('send_payload_octet') for actor instance 'a' might not preserve the channel invariant (#87)"} (M[NW#St][R[NW#St]] == 0) && ((R[NW#input] - I[NW#input]) == 0) ==> ((C[NW#data] - I[NW#data]) == 0);
  assert {:msg "164.15: Action at 87.2 ('send_payload_octet') for actor instance 'a' might not preserve the channel invariant (#88)"} (M[NW#St][R[NW#St]] == 0) && ((R[NW#input] - I[NW#input]) > 0) ==> ((C[NW#data] - I[NW#data]) == AT#Bv2Int(M[NW#octet_count][R[NW#octet_count]]));
  assert {:msg "166.15: Action at 87.2 ('send_payload_octet') for actor instance 'a' might not preserve the channel invariant (#89)"} (M[NW#St][R[NW#St]] == 1) ==> ((R[NW#input] - I[NW#input]) == 1);
  assert {:msg "167.15: Action at 87.2 ('send_payload_octet') for actor instance 'a' might not preserve the channel invariant (#90)"} ((M[NW#St][R[NW#St]] == 1) || (M[NW#St][R[NW#St]] == 2)) ==> ((C[NW#data] - I[NW#data]) == AT#Bv2Int(M[NW#octet_index][R[NW#octet_index]]));
  assert {:msg "168.15: Action at 87.2 ('send_payload_octet') for actor instance 'a' might not preserve the channel invariant (#91)"} (M[NW#St][R[NW#St]] == 2) ==> ((R[NW#input] - I[NW#input]) == ((C[NW#data] - I[NW#data]) - 5));
  assert {:msg "170.15: Action at 87.2 ('send_payload_octet') for actor instance 'a' might not preserve the channel invariant (#92)"} (M[NW#St][R[NW#St]] == 0) <==> (((R[NW#input] - I[NW#input]) == 0) || ((R[NW#input] - I[NW#input]) == 2));
  assert {:msg "172.15: Action at 87.2 ('send_payload_octet') for actor instance 'a' might not preserve the channel invariant (#93)"} ((R[NW#input] - I[NW#input]) == 0) ==> ((C[NW#len] - I[NW#len]) == 0);
  assert {:msg "173.15: Action at 87.2 ('send_payload_octet') for actor instance 'a' might not preserve the channel invariant (#94)"} ((R[NW#input] - I[NW#input]) > 0) ==> (M[NW#octet_count][R[NW#octet_count]] == AT#BvAdd8(M[NW#input][I[NW#input]], 6bv8));
  assert {:msg "175.15: Action at 87.2 ('send_payload_octet') for actor instance 'a' might not preserve the channel invariant (#95)"} ((R[NW#input] - I[NW#input]) > 0) ==> ((C[NW#len] - I[NW#len]) == 1);
}
procedure NW#anon$1#input#pl_bits#11()
  modifies C, R, M, I, H;
{
  var NW#a: Actor;
  var NW#input: Chan (bv8);
  var NW#octet_count: Chan (bv8);
  var NW#octet_index: Chan (bv8);
  var NW#St: Chan (int);
  var NW#data: Chan (bv8);
  var NW#len: Chan (bv8);
  var AV#a#octet_count: bv8;
  var AV#a#octet_index: bv8;
  var AV#a#HEADER_LEN: int;
  var AV#a#Header: Map (bv8) (bv8);
  var AV#a#data_out: bv8;
  assume (NW#input != NW#octet_count) && (NW#input != NW#octet_index) && (NW#input != NW#data) && (NW#input != NW#len) && (NW#octet_count != NW#octet_index) && (NW#octet_count != NW#data) && (NW#octet_count != NW#len) && (NW#octet_index != NW#data) && (NW#octet_index != NW#len) && (NW#data != NW#len);
  assume 0 <= I[NW#input];
  assume I[NW#input] <= R[NW#input];
  assume R[NW#input] <= C[NW#input];
  assume 0 <= I[NW#octet_count];
  assume I[NW#octet_count] <= R[NW#octet_count];
  assume R[NW#octet_count] <= C[NW#octet_count];
  assume 0 <= I[NW#octet_index];
  assume I[NW#octet_index] <= R[NW#octet_index];
  assume R[NW#octet_index] <= C[NW#octet_index];
  assume 0 <= I[NW#St];
  assume I[NW#St] <= R[NW#St];
  assume R[NW#St] <= C[NW#St];
  assume 0 <= I[NW#data];
  assume I[NW#data] <= R[NW#data];
  assume R[NW#data] <= C[NW#data];
  assume I[NW#data] == R[NW#data];
  assume 0 <= I[NW#len];
  assume I[NW#len] <= R[NW#len];
  assume R[NW#len] <= C[NW#len];
  assume I[NW#len] == R[NW#len];
  assume (C[NW#input] - I[NW#input]) < 2;
  assume ((C[NW#octet_count] - R[NW#octet_count]) == 1) && ((C[NW#octet_index] - R[NW#octet_index]) == 1) && ((C[NW#St] - R[NW#St]) == 1);
  assume AT#BvUle8(0bv8, M[NW#octet_index][R[NW#octet_index]]) && AT#BvUle8(M[NW#octet_index][R[NW#octet_index]], M[NW#octet_count][R[NW#octet_count]]);
  assume (0 <= M[NW#St][R[NW#St]]) && (M[NW#St][R[NW#St]] <= 2);
  assume (C[NW#input] - I[NW#input]) <= 2;
  assume ((C[NW#input] - I[NW#input]) > 0) ==> (M[NW#input][I[NW#input]] == 1bv8);
  assume (M[NW#St][R[NW#St]] == 0) ==> (M[NW#octet_index][R[NW#octet_index]] == M[NW#octet_count][R[NW#octet_count]]);
  assume (M[NW#St][R[NW#St]] == 1) ==> AT#BvUle8(0bv8, M[NW#octet_index][R[NW#octet_index]]) && AT#BvUle8(M[NW#octet_index][R[NW#octet_index]], 5bv8);
  assume (M[NW#St][R[NW#St]] == 2) ==> AT#BvUle8(6bv8, M[NW#octet_index][R[NW#octet_index]]) && AT#BvUlt8(M[NW#octet_index][R[NW#octet_index]], M[NW#octet_count][R[NW#octet_count]]);
  assume (M[NW#St][R[NW#St]] == 0) && ((R[NW#input] - I[NW#input]) == 0) ==> ((C[NW#data] - I[NW#data]) == 0);
  assume (M[NW#St][R[NW#St]] == 0) && ((R[NW#input] - I[NW#input]) > 0) ==> ((C[NW#data] - I[NW#data]) == AT#Bv2Int(M[NW#octet_count][R[NW#octet_count]]));
  assume (M[NW#St][R[NW#St]] == 1) ==> ((R[NW#input] - I[NW#input]) == 1);
  assume ((M[NW#St][R[NW#St]] == 1) || (M[NW#St][R[NW#St]] == 2)) ==> ((C[NW#data] - I[NW#data]) == AT#Bv2Int(M[NW#octet_index][R[NW#octet_index]]));
  assume (M[NW#St][R[NW#St]] == 2) ==> ((R[NW#input] - I[NW#input]) == ((C[NW#data] - I[NW#data]) - 5));
  assume (M[NW#St][R[NW#St]] == 0) <==> (((R[NW#input] - I[NW#input]) == 0) || ((R[NW#input] - I[NW#input]) == 2));
  assume ((R[NW#input] - I[NW#input]) == 0) ==> ((C[NW#len] - I[NW#len]) == 0);
  assume ((R[NW#input] - I[NW#input]) > 0) ==> (M[NW#octet_count][R[NW#octet_count]] == AT#BvAdd8(M[NW#input][I[NW#input]], 6bv8));
  assume ((R[NW#input] - I[NW#input]) > 0) ==> ((C[NW#len] - I[NW#len]) == 1);
  assume M[NW#input][I[NW#input]] == 1bv8;
  C[NW#input] := C[NW#input] + 1;
  assume M[NW#input][I[NW#input]] == 1bv8;
  assert {:msg "148.15: Channel invariant might be falsified by network input (#96)"} ((C[NW#octet_count] - R[NW#octet_count]) == 1) && ((C[NW#octet_index] - R[NW#octet_index]) == 1) && ((C[NW#St] - R[NW#St]) == 1);
  assert {:msg "151.15: Channel invariant might be falsified by network input (#97)"} AT#BvUle8(0bv8, M[NW#octet_index][R[NW#octet_index]]) && AT#BvUle8(M[NW#octet_index][R[NW#octet_index]], M[NW#octet_count][R[NW#octet_count]]);
  assert {:msg "154.15: Channel invariant might be falsified by network input (#98)"} (0 <= M[NW#St][R[NW#St]]) && (M[NW#St][R[NW#St]] <= 2);
  assert {:msg "156.15: Channel invariant might be falsified by network input (#99)"} (C[NW#input] - I[NW#input]) <= 2;
  assert {:msg "157.15: Channel invariant might be falsified by network input (#100)"} ((C[NW#input] - I[NW#input]) > 0) ==> (M[NW#input][I[NW#input]] == 1bv8);
  assert {:msg "159.15: Channel invariant might be falsified by network input (#101)"} (M[NW#St][R[NW#St]] == 0) ==> (M[NW#octet_index][R[NW#octet_index]] == M[NW#octet_count][R[NW#octet_count]]);
  assert {:msg "160.15: Channel invariant might be falsified by network input (#102)"} (M[NW#St][R[NW#St]] == 1) ==> AT#BvUle8(0bv8, M[NW#octet_index][R[NW#octet_index]]) && AT#BvUle8(M[NW#octet_index][R[NW#octet_index]], 5bv8);
  assert {:msg "161.15: Channel invariant might be falsified by network input (#103)"} (M[NW#St][R[NW#St]] == 2) ==> AT#BvUle8(6bv8, M[NW#octet_index][R[NW#octet_index]]) && AT#BvUlt8(M[NW#octet_index][R[NW#octet_index]], M[NW#octet_count][R[NW#octet_count]]);
  assert {:msg "163.15: Channel invariant might be falsified by network input (#104)"} (M[NW#St][R[NW#St]] == 0) && ((R[NW#input] - I[NW#input]) == 0) ==> ((C[NW#data] - I[NW#data]) == 0);
  assert {:msg "164.15: Channel invariant might be falsified by network input (#105)"} (M[NW#St][R[NW#St]] == 0) && ((R[NW#input] - I[NW#input]) > 0) ==> ((C[NW#data] - I[NW#data]) == AT#Bv2Int(M[NW#octet_count][R[NW#octet_count]]));
  assert {:msg "166.15: Channel invariant might be falsified by network input (#106)"} (M[NW#St][R[NW#St]] == 1) ==> ((R[NW#input] - I[NW#input]) == 1);
  assert {:msg "167.15: Channel invariant might be falsified by network input (#107)"} ((M[NW#St][R[NW#St]] == 1) || (M[NW#St][R[NW#St]] == 2)) ==> ((C[NW#data] - I[NW#data]) == AT#Bv2Int(M[NW#octet_index][R[NW#octet_index]]));
  assert {:msg "168.15: Channel invariant might be falsified by network input (#108)"} (M[NW#St][R[NW#St]] == 2) ==> ((R[NW#input] - I[NW#input]) == ((C[NW#data] - I[NW#data]) - 5));
  assert {:msg "170.15: Channel invariant might be falsified by network input (#109)"} (M[NW#St][R[NW#St]] == 0) <==> (((R[NW#input] - I[NW#input]) == 0) || ((R[NW#input] - I[NW#input]) == 2));
  assert {:msg "172.15: Channel invariant might be falsified by network input (#110)"} ((R[NW#input] - I[NW#input]) == 0) ==> ((C[NW#len] - I[NW#len]) == 0);
  assert {:msg "173.15: Channel invariant might be falsified by network input (#111)"} ((R[NW#input] - I[NW#input]) > 0) ==> (M[NW#octet_count][R[NW#octet_count]] == AT#BvAdd8(M[NW#input][I[NW#input]], 6bv8));
  assert {:msg "175.15: Channel invariant might be falsified by network input (#112)"} ((R[NW#input] - I[NW#input]) > 0) ==> ((C[NW#len] - I[NW#len]) == 1);
  assert {:msg "135.14: Channel invariant might be falsified by network input (#113)"} M[NW#input][I[NW#input]] == 1bv8;
}
procedure NW#anon$1#exit#12()
  modifies C, R, M, I, H;
{
  var NW#a: Actor;
  var NW#input: Chan (bv8);
  var NW#octet_count: Chan (bv8);
  var NW#octet_index: Chan (bv8);
  var NW#St: Chan (int);
  var NW#data: Chan (bv8);
  var NW#len: Chan (bv8);
  var AV#a#octet_count: bv8;
  var AV#a#octet_index: bv8;
  var AV#a#HEADER_LEN: int;
  var AV#a#Header: Map (bv8) (bv8);
  var AV#a#data_out: bv8;
  assume (NW#input != NW#octet_count) && (NW#input != NW#octet_index) && (NW#input != NW#data) && (NW#input != NW#len) && (NW#octet_count != NW#octet_index) && (NW#octet_count != NW#data) && (NW#octet_count != NW#len) && (NW#octet_index != NW#data) && (NW#octet_index != NW#len) && (NW#data != NW#len);
  assume 0 <= I[NW#input];
  assume I[NW#input] <= R[NW#input];
  assume R[NW#input] <= C[NW#input];
  assume 0 <= I[NW#octet_count];
  assume I[NW#octet_count] <= R[NW#octet_count];
  assume R[NW#octet_count] <= C[NW#octet_count];
  assume 0 <= I[NW#octet_index];
  assume I[NW#octet_index] <= R[NW#octet_index];
  assume R[NW#octet_index] <= C[NW#octet_index];
  assume 0 <= I[NW#St];
  assume I[NW#St] <= R[NW#St];
  assume R[NW#St] <= C[NW#St];
  assume 0 <= I[NW#data];
  assume I[NW#data] <= R[NW#data];
  assume R[NW#data] <= C[NW#data];
  assume I[NW#data] == R[NW#data];
  assume 0 <= I[NW#len];
  assume I[NW#len] <= R[NW#len];
  assume R[NW#len] <= C[NW#len];
  assume I[NW#len] == R[NW#len];
  assume ((C[NW#octet_count] - R[NW#octet_count]) == 1) && ((C[NW#octet_index] - R[NW#octet_index]) == 1) && ((C[NW#St] - R[NW#St]) == 1);
  assume AT#BvUle8(0bv8, M[NW#octet_index][R[NW#octet_index]]) && AT#BvUle8(M[NW#octet_index][R[NW#octet_index]], M[NW#octet_count][R[NW#octet_count]]);
  assume (0 <= M[NW#St][R[NW#St]]) && (M[NW#St][R[NW#St]] <= 2);
  assume (C[NW#input] - I[NW#input]) <= 2;
  assume ((C[NW#input] - I[NW#input]) > 0) ==> (M[NW#input][I[NW#input]] == 1bv8);
  assume (M[NW#St][R[NW#St]] == 0) ==> (M[NW#octet_index][R[NW#octet_index]] == M[NW#octet_count][R[NW#octet_count]]);
  assume (M[NW#St][R[NW#St]] == 1) ==> AT#BvUle8(0bv8, M[NW#octet_index][R[NW#octet_index]]) && AT#BvUle8(M[NW#octet_index][R[NW#octet_index]], 5bv8);
  assume (M[NW#St][R[NW#St]] == 2) ==> AT#BvUle8(6bv8, M[NW#octet_index][R[NW#octet_index]]) && AT#BvUlt8(M[NW#octet_index][R[NW#octet_index]], M[NW#octet_count][R[NW#octet_count]]);
  assume (M[NW#St][R[NW#St]] == 0) && ((R[NW#input] - I[NW#input]) == 0) ==> ((C[NW#data] - I[NW#data]) == 0);
  assume (M[NW#St][R[NW#St]] == 0) && ((R[NW#input] - I[NW#input]) > 0) ==> ((C[NW#data] - I[NW#data]) == AT#Bv2Int(M[NW#octet_count][R[NW#octet_count]]));
  assume (M[NW#St][R[NW#St]] == 1) ==> ((R[NW#input] - I[NW#input]) == 1);
  assume ((M[NW#St][R[NW#St]] == 1) || (M[NW#St][R[NW#St]] == 2)) ==> ((C[NW#data] - I[NW#data]) == AT#Bv2Int(M[NW#octet_index][R[NW#octet_index]]));
  assume (M[NW#St][R[NW#St]] == 2) ==> ((R[NW#input] - I[NW#input]) == ((C[NW#data] - I[NW#data]) - 5));
  assume (M[NW#St][R[NW#St]] == 0) <==> (((R[NW#input] - I[NW#input]) == 0) || ((R[NW#input] - I[NW#input]) == 2));
  assume ((R[NW#input] - I[NW#input]) == 0) ==> ((C[NW#len] - I[NW#len]) == 0);
  assume ((R[NW#input] - I[NW#input]) > 0) ==> (M[NW#octet_count][R[NW#octet_count]] == AT#BvAdd8(M[NW#input][I[NW#input]], 6bv8));
  assume ((R[NW#input] - I[NW#input]) > 0) ==> ((C[NW#len] - I[NW#len]) == 1);
  assume M[NW#input][I[NW#input]] == 1bv8;
  assume (C[NW#input] - I[NW#input]) == 2;
  assume M[NW#input][I[NW#input]] == 1bv8;
  assume !((1 <= (C[NW#input] - R[NW#input])) && (1 <= (C[NW#octet_index] - R[NW#octet_index])) && (1 <= (C[NW#octet_count] - R[NW#octet_count])) && (1 <= (C[NW#St] - R[NW#St])) && (M[NW#St][R[NW#St]] == 0));
  assume !((1 <= (C[NW#octet_index] - R[NW#octet_index])) && (1 <= (C[NW#octet_count] - R[NW#octet_count])) && (1 <= (C[NW#St] - R[NW#St])) && AT#BvUlt8(M[NW#octet_index][R[NW#octet_index]], 5bv8) && (M[NW#St][R[NW#St]] == 1));
  assume !((1 <= (C[NW#octet_index] - R[NW#octet_index])) && (1 <= (C[NW#octet_count] - R[NW#octet_count])) && (1 <= (C[NW#St] - R[NW#St])) && (M[NW#octet_index][R[NW#octet_index]] == 5bv8) && (M[NW#St][R[NW#St]] == 1));
  assume !((1 <= (C[NW#input] - R[NW#input])) && (1 <= (C[NW#octet_index] - R[NW#octet_index])) && (1 <= (C[NW#octet_count] - R[NW#octet_count])) && (1 <= (C[NW#St] - R[NW#St])) && AT#BvUlt8(M[NW#octet_index][R[NW#octet_index]], M[NW#octet_count][R[NW#octet_count]]) && (M[NW#St][R[NW#St]] == 2));
  R[NW#data] := R[NW#data] + 7;
  R[NW#len] := R[NW#len] + 1;
  I := R;
  assert {:msg "148.15: The network might not preserve the channel invariant (#114)"} ((C[NW#octet_count] - R[NW#octet_count]) == 1) && ((C[NW#octet_index] - R[NW#octet_index]) == 1) && ((C[NW#St] - R[NW#St]) == 1);
  assert {:msg "151.15: The network might not preserve the channel invariant (#115)"} AT#BvUle8(0bv8, M[NW#octet_index][R[NW#octet_index]]) && AT#BvUle8(M[NW#octet_index][R[NW#octet_index]], M[NW#octet_count][R[NW#octet_count]]);
  assert {:msg "154.15: The network might not preserve the channel invariant (#116)"} (0 <= M[NW#St][R[NW#St]]) && (M[NW#St][R[NW#St]] <= 2);
  assert {:msg "156.15: The network might not preserve the channel invariant (#117)"} (C[NW#input] - I[NW#input]) <= 2;
  assert {:msg "157.15: The network might not preserve the channel invariant (#118)"} ((C[NW#input] - I[NW#input]) > 0) ==> (M[NW#input][I[NW#input]] == 1bv8);
  assert {:msg "159.15: The network might not preserve the channel invariant (#119)"} (M[NW#St][R[NW#St]] == 0) ==> (M[NW#octet_index][R[NW#octet_index]] == M[NW#octet_count][R[NW#octet_count]]);
  assert {:msg "160.15: The network might not preserve the channel invariant (#120)"} (M[NW#St][R[NW#St]] == 1) ==> AT#BvUle8(0bv8, M[NW#octet_index][R[NW#octet_index]]) && AT#BvUle8(M[NW#octet_index][R[NW#octet_index]], 5bv8);
  assert {:msg "161.15: The network might not preserve the channel invariant (#121)"} (M[NW#St][R[NW#St]] == 2) ==> AT#BvUle8(6bv8, M[NW#octet_index][R[NW#octet_index]]) && AT#BvUlt8(M[NW#octet_index][R[NW#octet_index]], M[NW#octet_count][R[NW#octet_count]]);
  assert {:msg "163.15: The network might not preserve the channel invariant (#122)"} (M[NW#St][R[NW#St]] == 0) && ((R[NW#input] - I[NW#input]) == 0) ==> ((C[NW#data] - I[NW#data]) == 0);
  assert {:msg "164.15: The network might not preserve the channel invariant (#123)"} (M[NW#St][R[NW#St]] == 0) && ((R[NW#input] - I[NW#input]) > 0) ==> ((C[NW#data] - I[NW#data]) == AT#Bv2Int(M[NW#octet_count][R[NW#octet_count]]));
  assert {:msg "166.15: The network might not preserve the channel invariant (#124)"} (M[NW#St][R[NW#St]] == 1) ==> ((R[NW#input] - I[NW#input]) == 1);
  assert {:msg "167.15: The network might not preserve the channel invariant (#125)"} ((M[NW#St][R[NW#St]] == 1) || (M[NW#St][R[NW#St]] == 2)) ==> ((C[NW#data] - I[NW#data]) == AT#Bv2Int(M[NW#octet_index][R[NW#octet_index]]));
  assert {:msg "168.15: The network might not preserve the channel invariant (#126)"} (M[NW#St][R[NW#St]] == 2) ==> ((R[NW#input] - I[NW#input]) == ((C[NW#data] - I[NW#data]) - 5));
  assert {:msg "170.15: The network might not preserve the channel invariant (#127)"} (M[NW#St][R[NW#St]] == 0) <==> (((R[NW#input] - I[NW#input]) == 0) || ((R[NW#input] - I[NW#input]) == 2));
  assert {:msg "172.15: The network might not preserve the channel invariant (#128)"} ((R[NW#input] - I[NW#input]) == 0) ==> ((C[NW#len] - I[NW#len]) == 0);
  assert {:msg "173.15: The network might not preserve the channel invariant (#129)"} ((R[NW#input] - I[NW#input]) > 0) ==> (M[NW#octet_count][R[NW#octet_count]] == AT#BvAdd8(M[NW#input][I[NW#input]], 6bv8));
  assert {:msg "175.15: The network might not preserve the channel invariant (#130)"} ((R[NW#input] - I[NW#input]) > 0) ==> ((C[NW#len] - I[NW#len]) == 1);
  assert {:msg "144.13: The network might not preserve the network invariant (#131)"} ((C[NW#octet_count] - R[NW#octet_count]) == 1) && ((C[NW#octet_index] - R[NW#octet_index]) == 1) && ((C[NW#St] - R[NW#St]) == 1);
  assert {:msg "145.13: The network might not preserve the network invariant (#132)"} (M[NW#St][R[NW#St]] == 0) && (M[NW#octet_index][R[NW#octet_index]] == M[NW#octet_count][R[NW#octet_count]]);
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel input (#133)"} (C[NW#input] - R[NW#input]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel data (#134)"} (C[NW#data] - R[NW#data]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel len (#135)"} (C[NW#len] - R[NW#len]) == 0;
}

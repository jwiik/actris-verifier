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

procedure headerAdd#init#0()
  modifies C, R, M, I, H;
{
  var pl_bits: Chan (bv8);
  var data: Chan (bv8);
  var len: Chan (bv8);
  var octet_count: bv8;
  var octet_index: bv8;
  var HEADER_LEN: int;
  var Header: Map (bv8) (bv8);
  var data_out: bv8;
  var St: int;
  assume (pl_bits != data) && (pl_bits != len) && (data != len);
  assume R[pl_bits] == 0;
  assume C[data] == 0;
  assume C[len] == 0;
  octet_index := 0bv8;
  octet_count := 14bv8;
  St := 0;
  assert {:msg "25.12: Initialization might not establish the invariant (#0)"} AT#BvUle8(0bv8, octet_index);
  assert {:msg "26.12: Initialization might not establish the invariant (#1)"} AT#BvUle8(octet_index, octet_count);
  assert {:msg "27.12: Initialization might not establish the invariant (#2)"} octet_count == 14bv8;
  assert {:msg "29.12: Initialization might not establish the invariant (#3)"} (St == 1) ==> AT#BvUle8(octet_index, 5bv8);
  assert {:msg "30.12: Initialization might not establish the invariant (#4)"} (St == 2) ==> AT#BvUlt8(5bv8, octet_index);
  assert {:msg "31.12: Initialization might not establish the invariant (#5)"} (0 <= St) && (St <= 2);
}
procedure headerAdd#get_data_len#1()
  modifies C, R, M, I, H;
{
  var pl_bits: Chan (bv8);
  var data: Chan (bv8);
  var len: Chan (bv8);
  var octet_count: bv8;
  var octet_index: bv8;
  var HEADER_LEN: int;
  var Header: Map (bv8) (bv8);
  var data_out: bv8;
  var St: int;
  var pl_bits#0: bv8;
  assume (pl_bits != data) && (pl_bits != len) && (data != len);
  assume 0 <= R[pl_bits];
  assume 0 <= C[data];
  assume 0 <= C[len];
  assume AT#BvUle8(0bv8, octet_index);
  assume AT#BvUle8(octet_index, octet_count);
  assume octet_count == 14bv8;
  assume (St == 1) ==> AT#BvUle8(octet_index, 5bv8);
  assume (St == 2) ==> AT#BvUlt8(5bv8, octet_index);
  assume (0 <= St) && (St <= 2);
  pl_bits#0 := M[pl_bits][R[pl_bits]];
  R[pl_bits] := R[pl_bits] + 1;
  assume pl_bits#0 == 8bv8;
  assume St == 0;
  octet_index := 0bv8;
  octet_count := AT#BvAdd8(AT#BvAdd8(pl_bits#0, 5bv8), 1bv8);
  St := 1;
  M[len][C[len]] := octet_count;
  C[len] := C[len] + 1;
  assert {:msg "25.12: Action at 46.2 might not preserve invariant (#6)"} AT#BvUle8(0bv8, octet_index);
  assert {:msg "26.12: Action at 46.2 might not preserve invariant (#7)"} AT#BvUle8(octet_index, octet_count);
  assert {:msg "27.12: Action at 46.2 might not preserve invariant (#8)"} octet_count == 14bv8;
  assert {:msg "29.12: Action at 46.2 might not preserve invariant (#9)"} (St == 1) ==> AT#BvUle8(octet_index, 5bv8);
  assert {:msg "30.12: Action at 46.2 might not preserve invariant (#10)"} (St == 2) ==> AT#BvUlt8(5bv8, octet_index);
  assert {:msg "31.12: Action at 46.2 might not preserve invariant (#11)"} (0 <= St) && (St <= 2);
}
procedure headerAdd#send_header#2()
  modifies C, R, M, I, H;
{
  var pl_bits: Chan (bv8);
  var data: Chan (bv8);
  var len: Chan (bv8);
  var octet_count: bv8;
  var octet_index: bv8;
  var HEADER_LEN: int;
  var Header: Map (bv8) (bv8);
  var data_out: bv8;
  var St: int;
  var pl_bits#0: bv8;
  assume (pl_bits != data) && (pl_bits != len) && (data != len);
  assume 0 <= R[pl_bits];
  assume 0 <= C[data];
  assume 0 <= C[len];
  assume AT#BvUle8(0bv8, octet_index);
  assume AT#BvUle8(octet_index, octet_count);
  assume octet_count == 14bv8;
  assume (St == 1) ==> AT#BvUle8(octet_index, 5bv8);
  assume (St == 2) ==> AT#BvUlt8(5bv8, octet_index);
  assume (0 <= St) && (St <= 2);
  assume AT#BvUlt8(octet_index, 5bv8) && (St == 1);
  data_out := Map#Select(Header, octet_index);
  octet_index := AT#BvAdd8(octet_index, 1bv8);
  St := 1;
  M[data][C[data]] := data_out;
  C[data] := C[data] + 1;
  assert {:msg "25.12: Action at 57.2 might not preserve invariant (#12)"} AT#BvUle8(0bv8, octet_index);
  assert {:msg "26.12: Action at 57.2 might not preserve invariant (#13)"} AT#BvUle8(octet_index, octet_count);
  assert {:msg "27.12: Action at 57.2 might not preserve invariant (#14)"} octet_count == 14bv8;
  assert {:msg "29.12: Action at 57.2 might not preserve invariant (#15)"} (St == 1) ==> AT#BvUle8(octet_index, 5bv8);
  assert {:msg "30.12: Action at 57.2 might not preserve invariant (#16)"} (St == 2) ==> AT#BvUlt8(5bv8, octet_index);
  assert {:msg "31.12: Action at 57.2 might not preserve invariant (#17)"} (0 <= St) && (St <= 2);
}
procedure headerAdd#send_length#3()
  modifies C, R, M, I, H;
{
  var pl_bits: Chan (bv8);
  var data: Chan (bv8);
  var len: Chan (bv8);
  var octet_count: bv8;
  var octet_index: bv8;
  var HEADER_LEN: int;
  var Header: Map (bv8) (bv8);
  var data_out: bv8;
  var St: int;
  var pl_bits#0: bv8;
  assume (pl_bits != data) && (pl_bits != len) && (data != len);
  assume 0 <= R[pl_bits];
  assume 0 <= C[data];
  assume 0 <= C[len];
  assume AT#BvUle8(0bv8, octet_index);
  assume AT#BvUle8(octet_index, octet_count);
  assume octet_count == 14bv8;
  assume (St == 1) ==> AT#BvUle8(octet_index, 5bv8);
  assume (St == 2) ==> AT#BvUlt8(5bv8, octet_index);
  assume (0 <= St) && (St <= 2);
  assume !(true && AT#BvUlt8(octet_index, 5bv8) && (St == 1));
  assume (octet_index == 5bv8) && (St == 1);
  octet_index := AT#BvAdd8(octet_index, 1bv8);
  St := 2;
  M[data][C[data]] := AT#BvSub8(AT#BvSub8(octet_count, 5bv8), 1bv8);
  C[data] := C[data] + 1;
  assert {:msg "25.12: Action at 69.2 might not preserve invariant (#18)"} AT#BvUle8(0bv8, octet_index);
  assert {:msg "26.12: Action at 69.2 might not preserve invariant (#19)"} AT#BvUle8(octet_index, octet_count);
  assert {:msg "27.12: Action at 69.2 might not preserve invariant (#20)"} octet_count == 14bv8;
  assert {:msg "29.12: Action at 69.2 might not preserve invariant (#21)"} (St == 1) ==> AT#BvUle8(octet_index, 5bv8);
  assert {:msg "30.12: Action at 69.2 might not preserve invariant (#22)"} (St == 2) ==> AT#BvUlt8(5bv8, octet_index);
  assert {:msg "31.12: Action at 69.2 might not preserve invariant (#23)"} (0 <= St) && (St <= 2);
}
procedure headerAdd#send_payload_octet#4()
  modifies C, R, M, I, H;
{
  var pl_bits: Chan (bv8);
  var data: Chan (bv8);
  var len: Chan (bv8);
  var octet_count: bv8;
  var octet_index: bv8;
  var HEADER_LEN: int;
  var Header: Map (bv8) (bv8);
  var data_out: bv8;
  var St: int;
  var pl_bits#0: bv8;
  assume (pl_bits != data) && (pl_bits != len) && (data != len);
  assume 0 <= R[pl_bits];
  assume 0 <= C[data];
  assume 0 <= C[len];
  assume AT#BvUle8(0bv8, octet_index);
  assume AT#BvUle8(octet_index, octet_count);
  assume octet_count == 14bv8;
  assume (St == 1) ==> AT#BvUle8(octet_index, 5bv8);
  assume (St == 2) ==> AT#BvUlt8(5bv8, octet_index);
  assume (0 <= St) && (St <= 2);
  pl_bits#0 := M[pl_bits][R[pl_bits]];
  R[pl_bits] := R[pl_bits] + 1;
  assume AT#BvUlt8(octet_index, octet_count) && (St == 2);
  octet_index := AT#BvAdd8(octet_index, 1bv8);
  St := 2;
  M[data][C[data]] := pl_bits#0;
  C[data] := C[data] + 1;
  assert {:msg "25.12: Action at 80.2 might not preserve invariant (#24)"} AT#BvUle8(0bv8, octet_index);
  assert {:msg "26.12: Action at 80.2 might not preserve invariant (#25)"} AT#BvUle8(octet_index, octet_count);
  assert {:msg "27.12: Action at 80.2 might not preserve invariant (#26)"} octet_count == 14bv8;
  assert {:msg "29.12: Action at 80.2 might not preserve invariant (#27)"} (St == 1) ==> AT#BvUle8(octet_index, 5bv8);
  assert {:msg "30.12: Action at 80.2 might not preserve invariant (#28)"} (St == 2) ==> AT#BvUlt8(5bv8, octet_index);
  assert {:msg "31.12: Action at 80.2 might not preserve invariant (#29)"} (0 <= St) && (St <= 2);
}
procedure headerAdd#done#5()
  modifies C, R, M, I, H;
{
  var pl_bits: Chan (bv8);
  var data: Chan (bv8);
  var len: Chan (bv8);
  var octet_count: bv8;
  var octet_index: bv8;
  var HEADER_LEN: int;
  var Header: Map (bv8) (bv8);
  var data_out: bv8;
  var St: int;
  var pl_bits#0: bv8;
  assume (pl_bits != data) && (pl_bits != len) && (data != len);
  assume 0 <= R[pl_bits];
  assume 0 <= C[data];
  assume 0 <= C[len];
  assume AT#BvUle8(0bv8, octet_index);
  assume AT#BvUle8(octet_index, octet_count);
  assume octet_count == 14bv8;
  assume (St == 1) ==> AT#BvUle8(octet_index, 5bv8);
  assume (St == 2) ==> AT#BvUlt8(5bv8, octet_index);
  assume (0 <= St) && (St <= 2);
  assume !((1 <= (C[pl_bits] - R[pl_bits])) && AT#BvUlt8(octet_index, octet_count) && (St == 2));
  assume (octet_index == octet_count) && (St == 2);
  St := 0;
  assert {:msg "25.12: Action at 91.2 might not preserve invariant (#30)"} AT#BvUle8(0bv8, octet_index);
  assert {:msg "26.12: Action at 91.2 might not preserve invariant (#31)"} AT#BvUle8(octet_index, octet_count);
  assert {:msg "27.12: Action at 91.2 might not preserve invariant (#32)"} octet_count == 14bv8;
  assert {:msg "29.12: Action at 91.2 might not preserve invariant (#33)"} (St == 1) ==> AT#BvUle8(octet_index, 5bv8);
  assert {:msg "30.12: Action at 91.2 might not preserve invariant (#34)"} (St == 2) ==> AT#BvUlt8(5bv8, octet_index);
  assert {:msg "31.12: Action at 91.2 might not preserve invariant (#35)"} (0 <= St) && (St <= 2);
}
procedure headerAdd##GuardWD#6()
  modifies C, R, M, I, H;
{
  var pl_bits: Chan (bv8);
  var data: Chan (bv8);
  var len: Chan (bv8);
  var octet_count: bv8;
  var octet_index: bv8;
  var HEADER_LEN: int;
  var Header: Map (bv8) (bv8);
  var data_out: bv8;
  var St: int;
  var pl_bits#0: bv8;
  assume (pl_bits != data) && (pl_bits != len) && (data != len);
  assert {:msg "1.1: The actions 'done' and 'get_data_len' of actor 'headerAdd' might not have mutually exclusive guards (#36)"} !(true && (!((1 <= (C[pl_bits] - R[pl_bits])) && AT#BvUlt8(octet_index, octet_count) && (St == 2))) && true && (octet_index == octet_count) && (St == 2) && true && (1 <= (C[pl_bits] - R[pl_bits])) && (St == 0));
  assert {:msg "1.1: The actions 'done' and 'send_length' of actor 'headerAdd' might not have mutually exclusive guards (#37)"} !(true && (!((1 <= (C[pl_bits] - R[pl_bits])) && AT#BvUlt8(octet_index, octet_count) && (St == 2))) && true && (octet_index == octet_count) && (St == 2) && true && (!(true && AT#BvUlt8(octet_index, 5bv8) && (St == 1))) && true && (octet_index == 5bv8) && (St == 1));
  assert {:msg "1.1: The actions 'done' and 'send_header' of actor 'headerAdd' might not have mutually exclusive guards (#38)"} !(true && (!((1 <= (C[pl_bits] - R[pl_bits])) && AT#BvUlt8(octet_index, octet_count) && (St == 2))) && true && (octet_index == octet_count) && (St == 2) && true && true && AT#BvUlt8(octet_index, 5bv8) && (St == 1));
  assert {:msg "1.1: The actions 'done' and 'send_payload_octet' of actor 'headerAdd' might not have mutually exclusive guards (#39)"} !(true && (!((1 <= (C[pl_bits] - R[pl_bits])) && AT#BvUlt8(octet_index, octet_count) && (St == 2))) && true && (octet_index == octet_count) && (St == 2) && true && (1 <= (C[pl_bits] - R[pl_bits])) && AT#BvUlt8(octet_index, octet_count) && (St == 2));
  assert {:msg "1.1: The actions 'get_data_len' and 'send_length' of actor 'headerAdd' might not have mutually exclusive guards (#40)"} !(true && (1 <= (C[pl_bits] - R[pl_bits])) && (St == 0) && true && (!(true && AT#BvUlt8(octet_index, 5bv8) && (St == 1))) && true && (octet_index == 5bv8) && (St == 1));
  assert {:msg "1.1: The actions 'get_data_len' and 'send_header' of actor 'headerAdd' might not have mutually exclusive guards (#41)"} !(true && (1 <= (C[pl_bits] - R[pl_bits])) && (St == 0) && true && true && AT#BvUlt8(octet_index, 5bv8) && (St == 1));
  assert {:msg "1.1: The actions 'get_data_len' and 'send_payload_octet' of actor 'headerAdd' might not have mutually exclusive guards (#42)"} !(true && (1 <= (C[pl_bits] - R[pl_bits])) && (St == 0) && true && (1 <= (C[pl_bits] - R[pl_bits])) && AT#BvUlt8(octet_index, octet_count) && (St == 2));
  assert {:msg "1.1: The actions 'send_length' and 'send_header' of actor 'headerAdd' might not have mutually exclusive guards (#43)"} !(true && (!(true && AT#BvUlt8(octet_index, 5bv8) && (St == 1))) && true && (octet_index == 5bv8) && (St == 1) && true && true && AT#BvUlt8(octet_index, 5bv8) && (St == 1));
  assert {:msg "1.1: The actions 'send_length' and 'send_payload_octet' of actor 'headerAdd' might not have mutually exclusive guards (#44)"} !(true && (!(true && AT#BvUlt8(octet_index, 5bv8) && (St == 1))) && true && (octet_index == 5bv8) && (St == 1) && true && (1 <= (C[pl_bits] - R[pl_bits])) && AT#BvUlt8(octet_index, octet_count) && (St == 2));
  assert {:msg "1.1: The actions 'send_header' and 'send_payload_octet' of actor 'headerAdd' might not have mutually exclusive guards (#45)"} !(true && true && AT#BvUlt8(octet_index, 5bv8) && (St == 1) && true && (1 <= (C[pl_bits] - R[pl_bits])) && AT#BvUlt8(octet_index, octet_count) && (St == 2));
}
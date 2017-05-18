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

// ---------------------------------------------------------------
// -- Integer division and modulo --------------------------------
// ---------------------------------------------------------------
function AT#Abs(x: int): int { if 0 <= x then x else -x }
function AT#Div(int, int): int;
function AT#Mod(int, int): int;
axiom (forall a,b: int :: AT#Div(a,b)*b + AT#Mod(a,b) == a);
axiom (forall a,b: int :: 0 <= AT#Mod(a,b) && AT#Mod(a,b) < AT#Abs(b));

// ---------------------------------------------------------------
// -- Bit vector operations --------------------------------------
// ---------------------------------------------------------------
// Size: 8
function {:bvbuiltin "bvand"} AT#BvAnd8(a: bv8, b: bv8): bv8;
function {:bvbuiltin "bvor"} AT#BvOr8(a: bv8, b: bv8): bv8;
function {:bvbuiltin "bvnot"} AT#BvNot8(a: bv8): bv8;
function {:bvbuiltin "bvneg"} AT#BvNeg8(a: bv8): bv8;
function {:bvbuiltin "bvadd"} AT#BvAdd8(a: bv8, b: bv8): bv8;
function {:bvbuiltin "bvsub"} AT#BvSub8(a: bv8, b: bv8): bv8;
function {:bvbuiltin "bvmul"} AT#BvMul8(a: bv8, b: bv8): bv8;
function {:bvbuiltin "bvsdiv"} AT#BvSdiv8(a: bv8, b: bv8): bv8;
function {:bvbuiltin "bvudiv"} AT#BvUdiv8(a: bv8, b: bv8): bv8;
function {:bvbuiltin "bvshl"} AT#BvShl8(bv8,bv8): bv8;
function {:bvbuiltin "bvlshr"} AT#BvLshr8(bv8,bv8): bv8;
function {:bvbuiltin "bvashr"} AT#BvAshr8(bv8,bv8): bv8;
function {:bvbuiltin "bvule"} AT#BvUle8(a: bv8, b: bv8): bool;
function {:bvbuiltin "bvult"} AT#BvUlt8(a: bv8, b: bv8): bool;
function {:bvbuiltin "bvuge"} AT#BvUge8(a: bv8, b: bv8): bool;
function {:bvbuiltin "bvugt"} AT#BvUgt8(a: bv8, b: bv8): bool;
function {:bvbuiltin "bvsle"} AT#BvSle8(a: bv8, b: bv8): bool;
function {:bvbuiltin "bvslt"} AT#BvSlt8(a: bv8, b: bv8): bool;
function {:bvbuiltin "bvsge"} AT#BvSge8(a: bv8, b: bv8): bool;
function {:bvbuiltin "bvsgt"} AT#BvSgt8(a: bv8, b: bv8): bool;
function AT#BvXor8(a: bv8, b: bv8): bv8;
function AT#BvAbs8(a: bv8): bv8;

axiom (forall a,b: bv8 :: AT#BvXor8(a,b) == AT#BvAnd8(AT#BvOr8(a,b), AT#BvNot8(AT#BvAnd8(a,b))) );
axiom (forall a,b: bv8 :: AT#BvAbs8(a) == (if AT#BvSle8(0bv8,a) then a else AT#BvNeg8(a)) );

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
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

procedure DCSplit#init#0()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var IN: Chan (bv13);
  var DC: Chan (bv13);
  var AC: Chan (bv13);
  var anon$0: int;
  var count: bv8;
  assume (IN != DC) && (IN != AC) && (DC != AC);
  assume anon$0 == 0;
  assume Mode#[this#] == anon$0;
  assume (I#[IN] == 0) && (R#[IN] == 0) && (C#[IN] == 0);
  assume (I#[DC] == 0) && (R#[DC] == 0) && (C#[DC] == 0);
  assume (I#[AC] == 0) && (R#[AC] == 0) && (C#[AC] == 0);
  count := 0bv8;
  assert {:msg "DCSplit.cal(51.12): Initialization might not establish the invariant (#0)"} AT#BvSle8(0bv8, count) && AT#BvSlt8(count, 64bv8);
  assert {:msg "DCSplit.cal(52.12): Initialization might not establish the invariant (#1)"} AT#Mod(R#[IN] - I#[IN], 64) == AT#Bv2Int8(count);
  assert {:msg "DCSplit.cal(53.12): Initialization might not establish the invariant (#2)"} ((R#[IN] - I#[IN]) == 0) ==> ((C#[DC] - I#[DC]) == 0);
  assert {:msg "DCSplit.cal(54.12): Initialization might not establish the invariant (#3)"} ((R#[IN] - I#[IN]) < 2) ==> ((C#[AC] - I#[AC]) == 0);
  assert {:msg "DCSplit.cal(55.12): Initialization might not establish the invariant (#4)"} ((R#[IN] - I#[IN]) > 0) ==> ((C#[DC] - I#[DC]) == 1) && (M#[DC][I#[DC]] == M#[IN][I#[IN]]);
  assert {:msg "DCSplit.cal(56.12): Initialization might not establish the invariant (#5)"} ((R#[IN] - I#[IN]) > 0) ==> ((C#[AC] - I#[AC]) == ((R#[IN] - I#[IN]) - 1));
  assert {:msg "Initialization might not establish the invariant (#6)"} (Mode#[this#] == anon$0) ==> ((C#[IN] - I#[IN]) <= 64);
}
procedure DCSplit#dc#1()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var IN: Chan (bv13);
  var DC: Chan (bv13);
  var AC: Chan (bv13);
  var anon$0: int;
  var count: bv8;
  var IN#0: bv13;
  assume (IN != DC) && (IN != AC) && (DC != AC);
  assume anon$0 == 0;
  assume Mode#[this#] == anon$0;
  assume (0 <= I#[IN]) && (I#[IN] <= R#[IN]) && (R#[IN] <= C#[IN]);
  assume (0 <= I#[DC]) && (I#[DC] <= R#[DC]) && (R#[DC] <= C#[DC]);
  assume (0 <= I#[AC]) && (I#[AC] <= R#[AC]) && (R#[AC] <= C#[AC]);
  assume AT#BvSle8(0bv8, count) && AT#BvSlt8(count, 64bv8);
  assume AT#Mod(R#[IN] - I#[IN], 64) == AT#Bv2Int8(count);
  assume ((R#[IN] - I#[IN]) == 0) ==> ((C#[DC] - I#[DC]) == 0);
  assume ((R#[IN] - I#[IN]) < 2) ==> ((C#[AC] - I#[AC]) == 0);
  assume ((R#[IN] - I#[IN]) > 0) ==> ((C#[DC] - I#[DC]) == 1) && (M#[DC][I#[DC]] == M#[IN][I#[IN]]);
  assume ((R#[IN] - I#[IN]) > 0) ==> ((C#[AC] - I#[AC]) == ((R#[IN] - I#[IN]) - 1));
  assume (Mode#[this#] == anon$0) ==> ((C#[IN] - I#[IN]) <= 64);
  assume 1 <= (C#[IN] - R#[IN]);
  IN#0 := M#[IN][R#[IN]];
  R#[IN] := R#[IN] + 1;
  assume count == 0bv8;
  count := 1bv8;
  M#[DC][C#[DC]] := IN#0;
  C#[DC] := C#[DC] + 1;
  assert {:msg "DCSplit.cal(51.12): Action 'dc' at DCSplit.cal(58.2) might not preserve the invariant (#7)"} AT#BvSle8(0bv8, count) && AT#BvSlt8(count, 64bv8);
  assert {:msg "DCSplit.cal(52.12): Action 'dc' at DCSplit.cal(58.2) might not preserve the invariant (#8)"} AT#Mod(R#[IN] - I#[IN], 64) == AT#Bv2Int8(count);
  assert {:msg "DCSplit.cal(53.12): Action 'dc' at DCSplit.cal(58.2) might not preserve the invariant (#9)"} ((R#[IN] - I#[IN]) == 0) ==> ((C#[DC] - I#[DC]) == 0);
  assert {:msg "DCSplit.cal(54.12): Action 'dc' at DCSplit.cal(58.2) might not preserve the invariant (#10)"} ((R#[IN] - I#[IN]) < 2) ==> ((C#[AC] - I#[AC]) == 0);
  assert {:msg "DCSplit.cal(55.12): Action 'dc' at DCSplit.cal(58.2) might not preserve the invariant (#11)"} ((R#[IN] - I#[IN]) > 0) ==> ((C#[DC] - I#[DC]) == 1) && (M#[DC][I#[DC]] == M#[IN][I#[IN]]);
  assert {:msg "DCSplit.cal(56.12): Action 'dc' at DCSplit.cal(58.2) might not preserve the invariant (#12)"} ((R#[IN] - I#[IN]) > 0) ==> ((C#[AC] - I#[AC]) == ((R#[IN] - I#[IN]) - 1));
  assert {:msg "Action 'dc' at DCSplit.cal(58.2) might not preserve the invariant (#13)"} (Mode#[this#] == anon$0) ==> ((C#[IN] - I#[IN]) <= 64);
}
procedure DCSplit#ac#2()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var IN: Chan (bv13);
  var DC: Chan (bv13);
  var AC: Chan (bv13);
  var anon$0: int;
  var count: bv8;
  var IN#0: bv13;
  assume (IN != DC) && (IN != AC) && (DC != AC);
  assume anon$0 == 0;
  assume Mode#[this#] == anon$0;
  assume (0 <= I#[IN]) && (I#[IN] <= R#[IN]) && (R#[IN] <= C#[IN]);
  assume (0 <= I#[DC]) && (I#[DC] <= R#[DC]) && (R#[DC] <= C#[DC]);
  assume (0 <= I#[AC]) && (I#[AC] <= R#[AC]) && (R#[AC] <= C#[AC]);
  assume AT#BvSle8(0bv8, count) && AT#BvSlt8(count, 64bv8);
  assume AT#Mod(R#[IN] - I#[IN], 64) == AT#Bv2Int8(count);
  assume ((R#[IN] - I#[IN]) == 0) ==> ((C#[DC] - I#[DC]) == 0);
  assume ((R#[IN] - I#[IN]) < 2) ==> ((C#[AC] - I#[AC]) == 0);
  assume ((R#[IN] - I#[IN]) > 0) ==> ((C#[DC] - I#[DC]) == 1) && (M#[DC][I#[DC]] == M#[IN][I#[IN]]);
  assume ((R#[IN] - I#[IN]) > 0) ==> ((C#[AC] - I#[AC]) == ((R#[IN] - I#[IN]) - 1));
  assume (Mode#[this#] == anon$0) ==> ((C#[IN] - I#[IN]) <= 64);
  assume 1 <= (C#[IN] - R#[IN]);
  IN#0 := M#[IN][R#[IN]];
  R#[IN] := R#[IN] + 1;
  assume !(count == 0bv8);
  assume true;
  count := AT#BvAnd8(AT#BvAdd8(count, 1bv8), 63bv8);
  M#[AC][C#[AC]] := IN#0;
  C#[AC] := C#[AC] + 1;
  assert {:msg "DCSplit.cal(51.12): Action 'ac' at DCSplit.cal(65.2) might not preserve the invariant (#14)"} AT#BvSle8(0bv8, count) && AT#BvSlt8(count, 64bv8);
  assert {:msg "DCSplit.cal(52.12): Action 'ac' at DCSplit.cal(65.2) might not preserve the invariant (#15)"} AT#Mod(R#[IN] - I#[IN], 64) == AT#Bv2Int8(count);
  assert {:msg "DCSplit.cal(53.12): Action 'ac' at DCSplit.cal(65.2) might not preserve the invariant (#16)"} ((R#[IN] - I#[IN]) == 0) ==> ((C#[DC] - I#[DC]) == 0);
  assert {:msg "DCSplit.cal(54.12): Action 'ac' at DCSplit.cal(65.2) might not preserve the invariant (#17)"} ((R#[IN] - I#[IN]) < 2) ==> ((C#[AC] - I#[AC]) == 0);
  assert {:msg "DCSplit.cal(55.12): Action 'ac' at DCSplit.cal(65.2) might not preserve the invariant (#18)"} ((R#[IN] - I#[IN]) > 0) ==> ((C#[DC] - I#[DC]) == 1) && (M#[DC][I#[DC]] == M#[IN][I#[IN]]);
  assert {:msg "DCSplit.cal(56.12): Action 'ac' at DCSplit.cal(65.2) might not preserve the invariant (#19)"} ((R#[IN] - I#[IN]) > 0) ==> ((C#[AC] - I#[AC]) == ((R#[IN] - I#[IN]) - 1));
  assert {:msg "Action 'ac' at DCSplit.cal(65.2) might not preserve the invariant (#20)"} (Mode#[this#] == anon$0) ==> ((C#[IN] - I#[IN]) <= 64);
}
procedure DCSplit##GuardWD#3()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var IN: Chan (bv13);
  var DC: Chan (bv13);
  var AC: Chan (bv13);
  var anon$0: int;
  var count: bv8;
  var IN#0: bv13;
  assume (IN != DC) && (IN != AC) && (DC != AC);
  assume anon$0 == 0;
  assume Mode#[this#] == anon$0;
  assume (0 <= I#[IN]) && (I#[IN] <= R#[IN]) && (R#[IN] <= C#[IN]);
  assume (0 <= I#[DC]) && (I#[DC] <= R#[DC]) && (R#[DC] <= C#[DC]);
  assume (0 <= I#[AC]) && (I#[AC] <= R#[AC]) && (R#[AC] <= C#[AC]);
  assume AT#BvSle8(0bv8, count) && AT#BvSlt8(count, 64bv8);
  assume AT#Mod(R#[IN] - I#[IN], 64) == AT#Bv2Int8(count);
  assume ((R#[IN] - I#[IN]) == 0) ==> ((C#[DC] - I#[DC]) == 0);
  assume ((R#[IN] - I#[IN]) < 2) ==> ((C#[AC] - I#[AC]) == 0);
  assume ((R#[IN] - I#[IN]) > 0) ==> ((C#[DC] - I#[DC]) == 1) && (M#[DC][I#[DC]] == M#[IN][I#[IN]]);
  assume ((R#[IN] - I#[IN]) > 0) ==> ((C#[AC] - I#[AC]) == ((R#[IN] - I#[IN]) - 1));
  assume (Mode#[this#] == anon$0) ==> ((C#[IN] - I#[IN]) <= 64);
  assert {:msg "The actions 'dc' and 'ac' of actor 'DCSplit' might not have mutually exclusive guards (#21)"} !(true && (1 <= (C#[IN] - R#[IN])) && (count == 0bv8) && true && (!((1 <= (C#[IN] - R#[IN])) && (count == 0bv8))) && (1 <= (C#[IN] - R#[IN])) && true);
}
procedure DCSplit#contract#anon$0#input#4()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var IN: Chan (bv13);
  var DC: Chan (bv13);
  var AC: Chan (bv13);
  var anon$0: int;
  var count: bv8;
  assume (IN != DC) && (IN != AC) && (DC != AC);
  assume anon$0 == 0;
  assume Mode#[this#] == anon$0;
  assume (0 <= I#[IN]) && (I#[IN] <= R#[IN]) && (R#[IN] <= C#[IN]);
  assume (0 <= I#[DC]) && (I#[DC] <= R#[DC]) && (R#[DC] <= C#[DC]);
  assume (0 <= I#[AC]) && (I#[AC] <= R#[AC]) && (R#[AC] <= C#[AC]);
  assume Mode#[this#] == anon$0;
  assume R#[DC] == I#[DC];
  assume R#[AC] == I#[AC];
  assume AT#BvSle8(0bv8, count) && AT#BvSlt8(count, 64bv8);
  assume AT#Mod(R#[IN] - I#[IN], 64) == AT#Bv2Int8(count);
  assume ((R#[IN] - I#[IN]) == 0) ==> ((C#[DC] - I#[DC]) == 0);
  assume ((R#[IN] - I#[IN]) < 2) ==> ((C#[AC] - I#[AC]) == 0);
  assume ((R#[IN] - I#[IN]) > 0) ==> ((C#[DC] - I#[DC]) == 1) && (M#[DC][I#[DC]] == M#[IN][I#[IN]]);
  assume ((R#[IN] - I#[IN]) > 0) ==> ((C#[AC] - I#[AC]) == ((R#[IN] - I#[IN]) - 1));
  assume (Mode#[this#] == anon$0) ==> ((C#[IN] - I#[IN]) <= 64);
  assume (C#[IN] - I#[IN]) < 64;
  C#[IN] := C#[IN] + 1;
  assert {:msg "DCSplit.cal(51.12): Invariant might be falsified by actor input (#22)"} AT#BvSle8(0bv8, count) && AT#BvSlt8(count, 64bv8);
  assert {:msg "DCSplit.cal(52.12): Invariant might be falsified by actor input (#23)"} AT#Mod(R#[IN] - I#[IN], 64) == AT#Bv2Int8(count);
  assert {:msg "DCSplit.cal(53.12): Invariant might be falsified by actor input (#24)"} ((R#[IN] - I#[IN]) == 0) ==> ((C#[DC] - I#[DC]) == 0);
  assert {:msg "DCSplit.cal(54.12): Invariant might be falsified by actor input (#25)"} ((R#[IN] - I#[IN]) < 2) ==> ((C#[AC] - I#[AC]) == 0);
  assert {:msg "DCSplit.cal(55.12): Invariant might be falsified by actor input (#26)"} ((R#[IN] - I#[IN]) > 0) ==> ((C#[DC] - I#[DC]) == 1) && (M#[DC][I#[DC]] == M#[IN][I#[IN]]);
  assert {:msg "DCSplit.cal(56.12): Invariant might be falsified by actor input (#27)"} ((R#[IN] - I#[IN]) > 0) ==> ((C#[AC] - I#[AC]) == ((R#[IN] - I#[IN]) - 1));
  assert {:msg "Invariant might be falsified by actor input (#28)"} (Mode#[this#] == anon$0) ==> ((C#[IN] - I#[IN]) <= 64);
}
procedure DCSplit#contract#anon$0#exit#5()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var IN: Chan (bv13);
  var DC: Chan (bv13);
  var AC: Chan (bv13);
  var anon$0: int;
  var count: bv8;
  assume (IN != DC) && (IN != AC) && (DC != AC);
  assume anon$0 == 0;
  assume Mode#[this#] == anon$0;
  assume (0 <= I#[IN]) && (I#[IN] <= R#[IN]) && (R#[IN] <= C#[IN]);
  assume (0 <= I#[DC]) && (I#[DC] <= R#[DC]) && (R#[DC] <= C#[DC]);
  assume (0 <= I#[AC]) && (I#[AC] <= R#[AC]) && (R#[AC] <= C#[AC]);
  assume Mode#[this#] == anon$0;
  assume R#[DC] == I#[DC];
  assume R#[AC] == I#[AC];
  assume AT#BvSle8(0bv8, count) && AT#BvSlt8(count, 64bv8);
  assume AT#Mod(R#[IN] - I#[IN], 64) == AT#Bv2Int8(count);
  assume ((R#[IN] - I#[IN]) == 0) ==> ((C#[DC] - I#[DC]) == 0);
  assume ((R#[IN] - I#[IN]) < 2) ==> ((C#[AC] - I#[AC]) == 0);
  assume ((R#[IN] - I#[IN]) > 0) ==> ((C#[DC] - I#[DC]) == 1) && (M#[DC][I#[DC]] == M#[IN][I#[IN]]);
  assume ((R#[IN] - I#[IN]) > 0) ==> ((C#[AC] - I#[AC]) == ((R#[IN] - I#[IN]) - 1));
  assume (Mode#[this#] == anon$0) ==> ((C#[IN] - I#[IN]) <= 64);
  assume (C#[IN] - I#[IN]) == 64;
  assume !(true && (1 <= (C#[IN] - R#[IN])) && (count == 0bv8));
  assume !(true && (!((1 <= (C#[IN] - R#[IN])) && (count == 0bv8))) && (1 <= (C#[IN] - R#[IN])) && true);
  assert {:msg "DCSplit.cal(47.2): The correct number of tokens might not be produced on output 'DC' with contract 'anon$0' (#29)"} (C#[DC] - I#[DC]) == 1;
  assert {:msg "DCSplit.cal(47.2): The correct number of tokens might not be produced on output 'AC' with contract 'anon$0' (#30)"} (C#[AC] - I#[AC]) == 63;
  assert {:msg "DCSplit.cal(48.12): Contract action postcondition might not hold (#31)"} M#[DC][I#[DC]] == M#[IN][I#[IN]];
  R#[DC] := R#[DC] + 1;
  R#[AC] := R#[AC] + 63;
  I# := R#;
  assert {:msg "DCSplit.cal(51.12): The actor might not preserve the invariant with contract 'anon$0' at DCSplit.cal(47.2) (#32)"} AT#BvSle8(0bv8, count) && AT#BvSlt8(count, 64bv8);
  assert {:msg "DCSplit.cal(52.12): The actor might not preserve the invariant with contract 'anon$0' at DCSplit.cal(47.2) (#33)"} AT#Mod(R#[IN] - I#[IN], 64) == AT#Bv2Int8(count);
  assert {:msg "DCSplit.cal(53.12): The actor might not preserve the invariant with contract 'anon$0' at DCSplit.cal(47.2) (#34)"} ((R#[IN] - I#[IN]) == 0) ==> ((C#[DC] - I#[DC]) == 0);
  assert {:msg "DCSplit.cal(54.12): The actor might not preserve the invariant with contract 'anon$0' at DCSplit.cal(47.2) (#35)"} ((R#[IN] - I#[IN]) < 2) ==> ((C#[AC] - I#[AC]) == 0);
  assert {:msg "DCSplit.cal(55.12): The actor might not preserve the invariant with contract 'anon$0' at DCSplit.cal(47.2) (#36)"} ((R#[IN] - I#[IN]) > 0) ==> ((C#[DC] - I#[DC]) == 1) && (M#[DC][I#[DC]] == M#[IN][I#[IN]]);
  assert {:msg "DCSplit.cal(56.12): The actor might not preserve the invariant with contract 'anon$0' at DCSplit.cal(47.2) (#37)"} ((R#[IN] - I#[IN]) > 0) ==> ((C#[AC] - I#[AC]) == ((R#[IN] - I#[IN]) - 1));
  assert {:msg "The actor might not preserve the invariant with contract 'anon$0' at DCSplit.cal(47.2) (#38)"} (Mode#[this#] == anon$0) ==> ((C#[IN] - I#[IN]) <= 64);
}
procedure DCSplit##GuardWD#6()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var IN: Chan (bv13);
  var DC: Chan (bv13);
  var AC: Chan (bv13);
  var anon$0: int;
  var count: bv8;
  assume (IN != DC) && (IN != AC) && (DC != AC);
  assume anon$0 == 0;
  assume Mode#[this#] == anon$0;
  assume (0 <= I#[IN]) && (I#[IN] <= R#[IN]) && (R#[IN] <= C#[IN]);
  assume (0 <= I#[DC]) && (I#[DC] <= R#[DC]) && (R#[DC] <= C#[DC]);
  assume (0 <= I#[AC]) && (I#[AC] <= R#[AC]) && (R#[AC] <= C#[AC]);
  assume AT#BvSle8(0bv8, count) && AT#BvSlt8(count, 64bv8);
  assume AT#Mod(R#[IN] - I#[IN], 64) == AT#Bv2Int8(count);
  assume ((R#[IN] - I#[IN]) == 0) ==> ((C#[DC] - I#[DC]) == 0);
  assume ((R#[IN] - I#[IN]) < 2) ==> ((C#[AC] - I#[AC]) == 0);
  assume ((R#[IN] - I#[IN]) > 0) ==> ((C#[DC] - I#[DC]) == 1) && (M#[DC][I#[DC]] == M#[IN][I#[IN]]);
  assume ((R#[IN] - I#[IN]) > 0) ==> ((C#[AC] - I#[AC]) == ((R#[IN] - I#[IN]) - 1));
  assume (Mode#[this#] == anon$0) ==> ((C#[IN] - I#[IN]) <= 64);
}

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
// -- Axiomatisation for map data type ---------------------------
// ---------------------------------------------------------------
type Map a b;
function List#Empty<U>(U): Map int U;
function Map#Empty<T,U>(T, U): Map T U;
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
// -- Bit vector operations --------------------------------------
// ---------------------------------------------------------------
// Size: 3
function {:bvbuiltin "bvand"} AT#BvAnd3(a: bv3, b: bv3): bv3;
function {:bvbuiltin "bvor"} AT#BvOr3(a: bv3, b: bv3): bv3;
function {:bvbuiltin "bvnot"} AT#BvNot3(a: bv3): bv3;
function {:bvbuiltin "bvneg"} AT#BvNeg3(a: bv3): bv3;
function {:bvbuiltin "bvadd"} AT#BvAdd3(a: bv3, b: bv3): bv3;
function {:bvbuiltin "bvsub"} AT#BvSub3(a: bv3, b: bv3): bv3;
function {:bvbuiltin "bvmul"} AT#BvMul3(a: bv3, b: bv3): bv3;
function {:bvbuiltin "bvsdiv"} AT#BvSdiv3(a: bv3, b: bv3): bv3;
function {:bvbuiltin "bvudiv"} AT#BvUdiv3(a: bv3, b: bv3): bv3;
function {:bvbuiltin "bvshl"} AT#BvShl3(bv3,bv3): bv3;
function {:bvbuiltin "bvlshr"} AT#BvLshr3(bv3,bv3): bv3;
function {:bvbuiltin "bvashr"} AT#BvAshr3(bv3,bv3): bv3;
function {:bvbuiltin "bvule"} AT#BvUle3(a: bv3, b: bv3): bool;
function {:bvbuiltin "bvult"} AT#BvUlt3(a: bv3, b: bv3): bool;
function {:bvbuiltin "bvuge"} AT#BvUge3(a: bv3, b: bv3): bool;
function {:bvbuiltin "bvugt"} AT#BvUgt3(a: bv3, b: bv3): bool;
function {:bvbuiltin "bvsle"} AT#BvSle3(a: bv3, b: bv3): bool;
function {:bvbuiltin "bvslt"} AT#BvSlt3(a: bv3, b: bv3): bool;
function {:bvbuiltin "bvsge"} AT#BvSge3(a: bv3, b: bv3): bool;
function {:bvbuiltin "bvsgt"} AT#BvSgt3(a: bv3, b: bv3): bool;
function AT#BvXor3(a: bv3, b: bv3): bv3;
function AT#BvAbs3(a: bv3): bv3;

axiom (forall a,b: bv3 :: AT#BvXor3(a,b) == AT#BvAnd3(AT#BvOr3(a,b), AT#BvNot3(AT#BvAnd3(a,b))) );
axiom (forall a,b: bv3 :: AT#BvAbs3(a) == (if AT#BvSle3(0bv3,a) then a else AT#BvNeg3(a)) );

// ---------------------------------------------------------------
// -- Bit vector operations --------------------------------------
// ---------------------------------------------------------------
// Size: 9
function {:bvbuiltin "bvand"} AT#BvAnd9(a: bv9, b: bv9): bv9;
function {:bvbuiltin "bvor"} AT#BvOr9(a: bv9, b: bv9): bv9;
function {:bvbuiltin "bvnot"} AT#BvNot9(a: bv9): bv9;
function {:bvbuiltin "bvneg"} AT#BvNeg9(a: bv9): bv9;
function {:bvbuiltin "bvadd"} AT#BvAdd9(a: bv9, b: bv9): bv9;
function {:bvbuiltin "bvsub"} AT#BvSub9(a: bv9, b: bv9): bv9;
function {:bvbuiltin "bvmul"} AT#BvMul9(a: bv9, b: bv9): bv9;
function {:bvbuiltin "bvsdiv"} AT#BvSdiv9(a: bv9, b: bv9): bv9;
function {:bvbuiltin "bvudiv"} AT#BvUdiv9(a: bv9, b: bv9): bv9;
function {:bvbuiltin "bvshl"} AT#BvShl9(bv9,bv9): bv9;
function {:bvbuiltin "bvlshr"} AT#BvLshr9(bv9,bv9): bv9;
function {:bvbuiltin "bvashr"} AT#BvAshr9(bv9,bv9): bv9;
function {:bvbuiltin "bvule"} AT#BvUle9(a: bv9, b: bv9): bool;
function {:bvbuiltin "bvult"} AT#BvUlt9(a: bv9, b: bv9): bool;
function {:bvbuiltin "bvuge"} AT#BvUge9(a: bv9, b: bv9): bool;
function {:bvbuiltin "bvugt"} AT#BvUgt9(a: bv9, b: bv9): bool;
function {:bvbuiltin "bvsle"} AT#BvSle9(a: bv9, b: bv9): bool;
function {:bvbuiltin "bvslt"} AT#BvSlt9(a: bv9, b: bv9): bool;
function {:bvbuiltin "bvsge"} AT#BvSge9(a: bv9, b: bv9): bool;
function {:bvbuiltin "bvsgt"} AT#BvSgt9(a: bv9, b: bv9): bool;
function AT#BvXor9(a: bv9, b: bv9): bv9;
function AT#BvAbs9(a: bv9): bv9;

axiom (forall a,b: bv9 :: AT#BvXor9(a,b) == AT#BvAnd9(AT#BvOr9(a,b), AT#BvNot9(AT#BvAnd9(a,b))) );
axiom (forall a,b: bv9 :: AT#BvAbs9(a) == (if AT#BvSle9(0bv9,a) then a else AT#BvNeg9(a)) );

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

function Algo_IS_simple#wa() returns (out: bv7);
function Algo_IS_simple#ra(address: bv7) returns (out: bv7);
procedure Algo_IS_simple#init#0()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var AC_PRED_DIR: Chan (bv3);
  var QFS_AC: Chan (bv13);
  var PQF_AC: Chan (bv13);
  var Skip: int;
  var Main: int;
  var St#: int;
  var write: int;
  var read: int;
  var rest: int;
  var Scanmode: Map (bv9) (bv7);
  var count: bv8;
  var addr: bv9;
  var add_buf: bv3;
  var buf: Map (bv7) (bv13);
  var half_: bool;
  assume QFS_AC != PQF_AC;
  assume Skip == 0;
  assume Main == 1;
  assume (Mode#[this#] == Skip) || (Mode#[this#] == Main);
  assume write == 2;
  assume read == 1;
  assume rest == 0;
  assume Scanmode == Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Empty(0bv9, 0bv7), 0bv9, 0bv7), 1bv9, 1bv7), 2bv9, 5bv7), 3bv9, 6bv7), 4bv9, 14bv7), 5bv9, 15bv7), 6bv9, 27bv7), 7bv9, 28bv7), 8bv9, 2bv7), 9bv9, 4bv7), 10bv9, 7bv7), 11bv9, 13bv7), 12bv9, 16bv7), 13bv9, 26bv7), 14bv9, 29bv7), 15bv9, 42bv7), 16bv9, 3bv7), 17bv9, 8bv7), 18bv9, 12bv7), 19bv9, 17bv7), 20bv9, 25bv7), 21bv9, 30bv7), 22bv9, 41bv7), 23bv9, 43bv7), 24bv9, 9bv7), 25bv9, 11bv7), 26bv9, 18bv7), 27bv9, 24bv7), 28bv9, 31bv7), 29bv9, 40bv7), 30bv9, 44bv7), 31bv9, 53bv7), 32bv9, 10bv7), 33bv9, 19bv7), 34bv9, 23bv7), 35bv9, 32bv7), 36bv9, 39bv7), 37bv9, 45bv7), 38bv9, 52bv7), 39bv9, 54bv7), 40bv9, 20bv7), 41bv9, 22bv7), 42bv9, 33bv7), 43bv9, 38bv7), 44bv9, 46bv7), 45bv9, 51bv7), 46bv9, 55bv7), 47bv9, 60bv7), 48bv9, 21bv7), 49bv9, 34bv7), 50bv9, 37bv7), 51bv9, 47bv7), 52bv9, 50bv7), 53bv9, 56bv7), 54bv9, 59bv7), 55bv9, 61bv7), 56bv9, 35bv7), 57bv9, 36bv7), 58bv9, 48bv7), 59bv9, 49bv7), 60bv9, 57bv7), 61bv9, 58bv7), 62bv9, 62bv7), 63bv9, 63bv7), 64bv9, 0bv7), 65bv9, 4bv7), 66bv9, 6bv7), 67bv9, 20bv7), 68bv9, 22bv7), 69bv9, 36bv7), 70bv9, 38bv7), 71bv9, 52bv7), 72bv9, 1bv7), 73bv9, 5bv7), 74bv9, 7bv7), 75bv9, 21bv7), 76bv9, 23bv7), 77bv9, 37bv7), 78bv9, 39bv7), 79bv9, 53bv7), 80bv9, 2bv7), 81bv9, 8bv7), 82bv9, 19bv7), 83bv9, 24bv7), 84bv9, 34bv7), 85bv9, 40bv7), 86bv9, 50bv7), 87bv9, 54bv7), 88bv9, 3bv7), 89bv9, 9bv7), 90bv9, 18bv7), 91bv9, 25bv7), 92bv9, 35bv7), 93bv9, 41bv7), 94bv9, 51bv7), 95bv9, 55bv7), 96bv9, 10bv7), 97bv9, 17bv7), 98bv9, 26bv7), 99bv9, 30bv7), 100bv9, 42bv7), 101bv9, 46bv7), 102bv9, 56bv7), 103bv9, 60bv7), 104bv9, 11bv7), 105bv9, 16bv7), 106bv9, 27bv7), 107bv9, 31bv7), 108bv9, 43bv7), 109bv9, 47bv7), 110bv9, 57bv7), 111bv9, 61bv7), 112bv9, 12bv7), 113bv9, 15bv7), 114bv9, 28bv7), 115bv9, 32bv7), 116bv9, 44bv7), 117bv9, 48bv7), 118bv9, 58bv7), 119bv9, 62bv7), 120bv9, 13bv7), 121bv9, 14bv7), 122bv9, 29bv7), 123bv9, 33bv7), 124bv9, 45bv7), 125bv9, 49bv7), 126bv9, 59bv7), 127bv9, 63bv7), 128bv9, 0bv7), 129bv9, 1bv7), 130bv9, 2bv7), 131bv9, 3bv7), 132bv9, 10bv7), 133bv9, 11bv7), 134bv9, 12bv7), 135bv9, 13bv7), 136bv9, 4bv7), 137bv9, 5bv7), 138bv9, 8bv7), 139bv9, 9bv7), 140bv9, 17bv7), 141bv9, 16bv7), 142bv9, 15bv7), 143bv9, 14bv7), 144bv9, 6bv7), 145bv9, 7bv7), 146bv9, 19bv7), 147bv9, 18bv7), 148bv9, 26bv7), 149bv9, 27bv7), 150bv9, 28bv7), 151bv9, 29bv7), 152bv9, 20bv7), 153bv9, 21bv7), 154bv9, 24bv7), 155bv9, 25bv7), 156bv9, 30bv7), 157bv9, 31bv7), 158bv9, 32bv7), 159bv9, 33bv7), 160bv9, 22bv7), 161bv9, 23bv7), 162bv9, 34bv7), 163bv9, 35bv7), 164bv9, 42bv7), 165bv9, 43bv7), 166bv9, 44bv7), 167bv9, 45bv7), 168bv9, 36bv7), 169bv9, 37bv7), 170bv9, 40bv7), 171bv9, 41bv7), 172bv9, 46bv7), 173bv9, 47bv7), 174bv9, 48bv7), 175bv9, 49bv7), 176bv9, 38bv7), 177bv9, 39bv7), 178bv9, 50bv7), 179bv9, 51bv7), 180bv9, 56bv7), 181bv9, 57bv7), 182bv9, 58bv7), 183bv9, 59bv7), 184bv9, 52bv7), 185bv9, 53bv7), 186bv9, 54bv7), 187bv9, 55bv7), 188bv9, 60bv7), 189bv9, 61bv7), 190bv9, 62bv7), 191bv9, 63bv7);
  assume (I#[AC_PRED_DIR] == 0) && (R#[AC_PRED_DIR] == 0) && (C#[AC_PRED_DIR] == 0);
  assume (I#[QFS_AC] == 0) && (R#[QFS_AC] == 0) && (C#[QFS_AC] == 0);
  assume (I#[PQF_AC] == 0) && (R#[PQF_AC] == 0) && (C#[PQF_AC] == 0);
  count := 1bv8;
  half_ := false;
  St# := rest;
  assert {:msg "Algo_IS_simple.cal(123.3): Initialization might not establish the invariant (#0)"} ((St# == rest) || (St# == read)) || (St# == write);
  assert {:msg "Algo_IS_simple.cal(36.13): Initialization might not establish the invariant (#1)"} AT#BvSle8(1bv8, count) && AT#BvSle8(count, 64bv8);
  assert {:msg "Algo_IS_simple.cal(37.13): Initialization might not establish the invariant (#2)"} (St# == rest) ==> (count == 1bv8);
  assert {:msg "Algo_IS_simple.cal(39.13): Initialization might not establish the invariant (#3)"} (Mode#[this#] == Skip) && ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) > 0) ==> AT#BvSlt3(M#[AC_PRED_DIR][I#[AC_PRED_DIR]], 0bv3);
  assert {:msg "Algo_IS_simple.cal(40.13): Initialization might not establish the invariant (#4)"} (Mode#[this#] == Skip) ==> (St# == rest);
  assert {:msg "Algo_IS_simple.cal(41.13): Initialization might not establish the invariant (#5)"} (Mode#[this#] == Skip) ==> ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assert {:msg "Algo_IS_simple.cal(43.13): Initialization might not establish the invariant (#6)"} (Mode#[this#] == Main) && ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) > 0) ==> AT#BvSge3(M#[AC_PRED_DIR][I#[AC_PRED_DIR]], 0bv3);
  assert {:msg "Algo_IS_simple.cal(44.13): Initialization might not establish the invariant (#7)"} (Mode#[this#] == Main) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 0) ==> (St# == rest);
  assert {:msg "Algo_IS_simple.cal(45.13): Initialization might not establish the invariant (#8)"} (Mode#[this#] == Main) && (St# == rest) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 0) ==> ((R#[QFS_AC] - I#[QFS_AC]) == 0) && ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assert {:msg "Algo_IS_simple.cal(46.13): Initialization might not establish the invariant (#9)"} (Mode#[this#] == Main) && (St# == read) ==> ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) && ((R#[QFS_AC] - I#[QFS_AC]) == (AT#Bv2Int8(count) - 1)) && ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assert {:msg "Algo_IS_simple.cal(47.13): Initialization might not establish the invariant (#10)"} (Mode#[this#] == Main) && (St# == write) ==> ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) && ((R#[QFS_AC] - I#[QFS_AC]) == 63) && ((C#[PQF_AC] - I#[PQF_AC]) == (AT#Bv2Int8(count) - 1));
  assert {:msg "Algo_IS_simple.cal(48.13): Initialization might not establish the invariant (#11)"} (Mode#[this#] == Main) && (St# == rest) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) ==> ((R#[QFS_AC] - I#[QFS_AC]) == 63) && ((C#[PQF_AC] - I#[PQF_AC]) == 63);
  assert {:msg "Initialization might not establish the invariant (#12)"} (Mode#[this#] == Skip) ==> ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) <= 1) && ((C#[QFS_AC] - I#[QFS_AC]) == 0);
  assert {:msg "Initialization might not establish the invariant (#13)"} (Mode#[this#] == Main) ==> ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) <= 1) && ((C#[QFS_AC] - I#[QFS_AC]) <= 63);
}
procedure Algo_IS_simple#skip#1()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var AC_PRED_DIR: Chan (bv3);
  var QFS_AC: Chan (bv13);
  var PQF_AC: Chan (bv13);
  var Skip: int;
  var Main: int;
  var St#: int;
  var write: int;
  var read: int;
  var rest: int;
  var Scanmode: Map (bv9) (bv7);
  var count: bv8;
  var addr: bv9;
  var add_buf: bv3;
  var buf: Map (bv7) (bv13);
  var half_: bool;
  var AC_PRED_DIR#0: bv3;
  var QFS_AC#0: bv13;
  assume QFS_AC != PQF_AC;
  assume Skip == 0;
  assume Main == 1;
  assume (Mode#[this#] == Skip) || (Mode#[this#] == Main);
  assume write == 2;
  assume read == 1;
  assume rest == 0;
  assume Scanmode == Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Empty(0bv9, 0bv7), 0bv9, 0bv7), 1bv9, 1bv7), 2bv9, 5bv7), 3bv9, 6bv7), 4bv9, 14bv7), 5bv9, 15bv7), 6bv9, 27bv7), 7bv9, 28bv7), 8bv9, 2bv7), 9bv9, 4bv7), 10bv9, 7bv7), 11bv9, 13bv7), 12bv9, 16bv7), 13bv9, 26bv7), 14bv9, 29bv7), 15bv9, 42bv7), 16bv9, 3bv7), 17bv9, 8bv7), 18bv9, 12bv7), 19bv9, 17bv7), 20bv9, 25bv7), 21bv9, 30bv7), 22bv9, 41bv7), 23bv9, 43bv7), 24bv9, 9bv7), 25bv9, 11bv7), 26bv9, 18bv7), 27bv9, 24bv7), 28bv9, 31bv7), 29bv9, 40bv7), 30bv9, 44bv7), 31bv9, 53bv7), 32bv9, 10bv7), 33bv9, 19bv7), 34bv9, 23bv7), 35bv9, 32bv7), 36bv9, 39bv7), 37bv9, 45bv7), 38bv9, 52bv7), 39bv9, 54bv7), 40bv9, 20bv7), 41bv9, 22bv7), 42bv9, 33bv7), 43bv9, 38bv7), 44bv9, 46bv7), 45bv9, 51bv7), 46bv9, 55bv7), 47bv9, 60bv7), 48bv9, 21bv7), 49bv9, 34bv7), 50bv9, 37bv7), 51bv9, 47bv7), 52bv9, 50bv7), 53bv9, 56bv7), 54bv9, 59bv7), 55bv9, 61bv7), 56bv9, 35bv7), 57bv9, 36bv7), 58bv9, 48bv7), 59bv9, 49bv7), 60bv9, 57bv7), 61bv9, 58bv7), 62bv9, 62bv7), 63bv9, 63bv7), 64bv9, 0bv7), 65bv9, 4bv7), 66bv9, 6bv7), 67bv9, 20bv7), 68bv9, 22bv7), 69bv9, 36bv7), 70bv9, 38bv7), 71bv9, 52bv7), 72bv9, 1bv7), 73bv9, 5bv7), 74bv9, 7bv7), 75bv9, 21bv7), 76bv9, 23bv7), 77bv9, 37bv7), 78bv9, 39bv7), 79bv9, 53bv7), 80bv9, 2bv7), 81bv9, 8bv7), 82bv9, 19bv7), 83bv9, 24bv7), 84bv9, 34bv7), 85bv9, 40bv7), 86bv9, 50bv7), 87bv9, 54bv7), 88bv9, 3bv7), 89bv9, 9bv7), 90bv9, 18bv7), 91bv9, 25bv7), 92bv9, 35bv7), 93bv9, 41bv7), 94bv9, 51bv7), 95bv9, 55bv7), 96bv9, 10bv7), 97bv9, 17bv7), 98bv9, 26bv7), 99bv9, 30bv7), 100bv9, 42bv7), 101bv9, 46bv7), 102bv9, 56bv7), 103bv9, 60bv7), 104bv9, 11bv7), 105bv9, 16bv7), 106bv9, 27bv7), 107bv9, 31bv7), 108bv9, 43bv7), 109bv9, 47bv7), 110bv9, 57bv7), 111bv9, 61bv7), 112bv9, 12bv7), 113bv9, 15bv7), 114bv9, 28bv7), 115bv9, 32bv7), 116bv9, 44bv7), 117bv9, 48bv7), 118bv9, 58bv7), 119bv9, 62bv7), 120bv9, 13bv7), 121bv9, 14bv7), 122bv9, 29bv7), 123bv9, 33bv7), 124bv9, 45bv7), 125bv9, 49bv7), 126bv9, 59bv7), 127bv9, 63bv7), 128bv9, 0bv7), 129bv9, 1bv7), 130bv9, 2bv7), 131bv9, 3bv7), 132bv9, 10bv7), 133bv9, 11bv7), 134bv9, 12bv7), 135bv9, 13bv7), 136bv9, 4bv7), 137bv9, 5bv7), 138bv9, 8bv7), 139bv9, 9bv7), 140bv9, 17bv7), 141bv9, 16bv7), 142bv9, 15bv7), 143bv9, 14bv7), 144bv9, 6bv7), 145bv9, 7bv7), 146bv9, 19bv7), 147bv9, 18bv7), 148bv9, 26bv7), 149bv9, 27bv7), 150bv9, 28bv7), 151bv9, 29bv7), 152bv9, 20bv7), 153bv9, 21bv7), 154bv9, 24bv7), 155bv9, 25bv7), 156bv9, 30bv7), 157bv9, 31bv7), 158bv9, 32bv7), 159bv9, 33bv7), 160bv9, 22bv7), 161bv9, 23bv7), 162bv9, 34bv7), 163bv9, 35bv7), 164bv9, 42bv7), 165bv9, 43bv7), 166bv9, 44bv7), 167bv9, 45bv7), 168bv9, 36bv7), 169bv9, 37bv7), 170bv9, 40bv7), 171bv9, 41bv7), 172bv9, 46bv7), 173bv9, 47bv7), 174bv9, 48bv7), 175bv9, 49bv7), 176bv9, 38bv7), 177bv9, 39bv7), 178bv9, 50bv7), 179bv9, 51bv7), 180bv9, 56bv7), 181bv9, 57bv7), 182bv9, 58bv7), 183bv9, 59bv7), 184bv9, 52bv7), 185bv9, 53bv7), 186bv9, 54bv7), 187bv9, 55bv7), 188bv9, 60bv7), 189bv9, 61bv7), 190bv9, 62bv7), 191bv9, 63bv7);
  assume (0 <= I#[AC_PRED_DIR]) && (I#[AC_PRED_DIR] <= R#[AC_PRED_DIR]) && (R#[AC_PRED_DIR] <= C#[AC_PRED_DIR]);
  assume (0 <= I#[QFS_AC]) && (I#[QFS_AC] <= R#[QFS_AC]) && (R#[QFS_AC] <= C#[QFS_AC]);
  assume (0 <= I#[PQF_AC]) && (I#[PQF_AC] <= R#[PQF_AC]) && (R#[PQF_AC] <= C#[PQF_AC]);
  assume ((St# == rest) || (St# == read)) || (St# == write);
  assume AT#BvSle8(1bv8, count) && AT#BvSle8(count, 64bv8);
  assume (St# == rest) ==> (count == 1bv8);
  assume (Mode#[this#] == Skip) && ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) > 0) ==> AT#BvSlt3(M#[AC_PRED_DIR][I#[AC_PRED_DIR]], 0bv3);
  assume (Mode#[this#] == Skip) ==> (St# == rest);
  assume (Mode#[this#] == Skip) ==> ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assume (Mode#[this#] == Main) && ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) > 0) ==> AT#BvSge3(M#[AC_PRED_DIR][I#[AC_PRED_DIR]], 0bv3);
  assume (Mode#[this#] == Main) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 0) ==> (St# == rest);
  assume (Mode#[this#] == Main) && (St# == rest) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 0) ==> ((R#[QFS_AC] - I#[QFS_AC]) == 0) && ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assume (Mode#[this#] == Main) && (St# == read) ==> ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) && ((R#[QFS_AC] - I#[QFS_AC]) == (AT#Bv2Int8(count) - 1)) && ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assume (Mode#[this#] == Main) && (St# == write) ==> ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) && ((R#[QFS_AC] - I#[QFS_AC]) == 63) && ((C#[PQF_AC] - I#[PQF_AC]) == (AT#Bv2Int8(count) - 1));
  assume (Mode#[this#] == Main) && (St# == rest) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) ==> ((R#[QFS_AC] - I#[QFS_AC]) == 63) && ((C#[PQF_AC] - I#[PQF_AC]) == 63);
  assume (Mode#[this#] == Skip) ==> ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) <= 1) && ((C#[QFS_AC] - I#[QFS_AC]) == 0);
  assume (Mode#[this#] == Main) ==> ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) <= 1) && ((C#[QFS_AC] - I#[QFS_AC]) <= 63);
  assume 1 <= (C#[AC_PRED_DIR] - R#[AC_PRED_DIR]);
  AC_PRED_DIR#0 := M#[AC_PRED_DIR][R#[AC_PRED_DIR]];
  R#[AC_PRED_DIR] := R#[AC_PRED_DIR] + 1;
  assume AT#BvSlt3(AC_PRED_DIR#0, 0bv3) && (St# == rest);
  St# := rest;
  assert {:msg "Algo_IS_simple.cal(123.3): Action 'skip' at <unknown_file>(-1.-1) might not preserve the invariant (#14)"} ((St# == rest) || (St# == read)) || (St# == write);
  assert {:msg "Algo_IS_simple.cal(36.13): Action 'skip' at <unknown_file>(-1.-1) might not preserve the invariant (#15)"} AT#BvSle8(1bv8, count) && AT#BvSle8(count, 64bv8);
  assert {:msg "Algo_IS_simple.cal(37.13): Action 'skip' at <unknown_file>(-1.-1) might not preserve the invariant (#16)"} (St# == rest) ==> (count == 1bv8);
  assert {:msg "Algo_IS_simple.cal(39.13): Action 'skip' at <unknown_file>(-1.-1) might not preserve the invariant (#17)"} (Mode#[this#] == Skip) && ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) > 0) ==> AT#BvSlt3(M#[AC_PRED_DIR][I#[AC_PRED_DIR]], 0bv3);
  assert {:msg "Algo_IS_simple.cal(40.13): Action 'skip' at <unknown_file>(-1.-1) might not preserve the invariant (#18)"} (Mode#[this#] == Skip) ==> (St# == rest);
  assert {:msg "Algo_IS_simple.cal(41.13): Action 'skip' at <unknown_file>(-1.-1) might not preserve the invariant (#19)"} (Mode#[this#] == Skip) ==> ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assert {:msg "Algo_IS_simple.cal(43.13): Action 'skip' at <unknown_file>(-1.-1) might not preserve the invariant (#20)"} (Mode#[this#] == Main) && ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) > 0) ==> AT#BvSge3(M#[AC_PRED_DIR][I#[AC_PRED_DIR]], 0bv3);
  assert {:msg "Algo_IS_simple.cal(44.13): Action 'skip' at <unknown_file>(-1.-1) might not preserve the invariant (#21)"} (Mode#[this#] == Main) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 0) ==> (St# == rest);
  assert {:msg "Algo_IS_simple.cal(45.13): Action 'skip' at <unknown_file>(-1.-1) might not preserve the invariant (#22)"} (Mode#[this#] == Main) && (St# == rest) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 0) ==> ((R#[QFS_AC] - I#[QFS_AC]) == 0) && ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assert {:msg "Algo_IS_simple.cal(46.13): Action 'skip' at <unknown_file>(-1.-1) might not preserve the invariant (#23)"} (Mode#[this#] == Main) && (St# == read) ==> ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) && ((R#[QFS_AC] - I#[QFS_AC]) == (AT#Bv2Int8(count) - 1)) && ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assert {:msg "Algo_IS_simple.cal(47.13): Action 'skip' at <unknown_file>(-1.-1) might not preserve the invariant (#24)"} (Mode#[this#] == Main) && (St# == write) ==> ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) && ((R#[QFS_AC] - I#[QFS_AC]) == 63) && ((C#[PQF_AC] - I#[PQF_AC]) == (AT#Bv2Int8(count) - 1));
  assert {:msg "Algo_IS_simple.cal(48.13): Action 'skip' at <unknown_file>(-1.-1) might not preserve the invariant (#25)"} (Mode#[this#] == Main) && (St# == rest) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) ==> ((R#[QFS_AC] - I#[QFS_AC]) == 63) && ((C#[PQF_AC] - I#[PQF_AC]) == 63);
  assert {:msg "Action 'skip' at <unknown_file>(-1.-1) might not preserve the invariant (#26)"} (Mode#[this#] == Skip) ==> ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) <= 1) && ((C#[QFS_AC] - I#[QFS_AC]) == 0);
  assert {:msg "Action 'skip' at <unknown_file>(-1.-1) might not preserve the invariant (#27)"} (Mode#[this#] == Main) ==> ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) <= 1) && ((C#[QFS_AC] - I#[QFS_AC]) <= 63);
}
procedure Algo_IS_simple#start#2()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var AC_PRED_DIR: Chan (bv3);
  var QFS_AC: Chan (bv13);
  var PQF_AC: Chan (bv13);
  var Skip: int;
  var Main: int;
  var St#: int;
  var write: int;
  var read: int;
  var rest: int;
  var Scanmode: Map (bv9) (bv7);
  var count: bv8;
  var addr: bv9;
  var add_buf: bv3;
  var buf: Map (bv7) (bv13);
  var half_: bool;
  var AC_PRED_DIR#0: bv3;
  var QFS_AC#0: bv13;
  assume QFS_AC != PQF_AC;
  assume Skip == 0;
  assume Main == 1;
  assume (Mode#[this#] == Skip) || (Mode#[this#] == Main);
  assume write == 2;
  assume read == 1;
  assume rest == 0;
  assume Scanmode == Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Empty(0bv9, 0bv7), 0bv9, 0bv7), 1bv9, 1bv7), 2bv9, 5bv7), 3bv9, 6bv7), 4bv9, 14bv7), 5bv9, 15bv7), 6bv9, 27bv7), 7bv9, 28bv7), 8bv9, 2bv7), 9bv9, 4bv7), 10bv9, 7bv7), 11bv9, 13bv7), 12bv9, 16bv7), 13bv9, 26bv7), 14bv9, 29bv7), 15bv9, 42bv7), 16bv9, 3bv7), 17bv9, 8bv7), 18bv9, 12bv7), 19bv9, 17bv7), 20bv9, 25bv7), 21bv9, 30bv7), 22bv9, 41bv7), 23bv9, 43bv7), 24bv9, 9bv7), 25bv9, 11bv7), 26bv9, 18bv7), 27bv9, 24bv7), 28bv9, 31bv7), 29bv9, 40bv7), 30bv9, 44bv7), 31bv9, 53bv7), 32bv9, 10bv7), 33bv9, 19bv7), 34bv9, 23bv7), 35bv9, 32bv7), 36bv9, 39bv7), 37bv9, 45bv7), 38bv9, 52bv7), 39bv9, 54bv7), 40bv9, 20bv7), 41bv9, 22bv7), 42bv9, 33bv7), 43bv9, 38bv7), 44bv9, 46bv7), 45bv9, 51bv7), 46bv9, 55bv7), 47bv9, 60bv7), 48bv9, 21bv7), 49bv9, 34bv7), 50bv9, 37bv7), 51bv9, 47bv7), 52bv9, 50bv7), 53bv9, 56bv7), 54bv9, 59bv7), 55bv9, 61bv7), 56bv9, 35bv7), 57bv9, 36bv7), 58bv9, 48bv7), 59bv9, 49bv7), 60bv9, 57bv7), 61bv9, 58bv7), 62bv9, 62bv7), 63bv9, 63bv7), 64bv9, 0bv7), 65bv9, 4bv7), 66bv9, 6bv7), 67bv9, 20bv7), 68bv9, 22bv7), 69bv9, 36bv7), 70bv9, 38bv7), 71bv9, 52bv7), 72bv9, 1bv7), 73bv9, 5bv7), 74bv9, 7bv7), 75bv9, 21bv7), 76bv9, 23bv7), 77bv9, 37bv7), 78bv9, 39bv7), 79bv9, 53bv7), 80bv9, 2bv7), 81bv9, 8bv7), 82bv9, 19bv7), 83bv9, 24bv7), 84bv9, 34bv7), 85bv9, 40bv7), 86bv9, 50bv7), 87bv9, 54bv7), 88bv9, 3bv7), 89bv9, 9bv7), 90bv9, 18bv7), 91bv9, 25bv7), 92bv9, 35bv7), 93bv9, 41bv7), 94bv9, 51bv7), 95bv9, 55bv7), 96bv9, 10bv7), 97bv9, 17bv7), 98bv9, 26bv7), 99bv9, 30bv7), 100bv9, 42bv7), 101bv9, 46bv7), 102bv9, 56bv7), 103bv9, 60bv7), 104bv9, 11bv7), 105bv9, 16bv7), 106bv9, 27bv7), 107bv9, 31bv7), 108bv9, 43bv7), 109bv9, 47bv7), 110bv9, 57bv7), 111bv9, 61bv7), 112bv9, 12bv7), 113bv9, 15bv7), 114bv9, 28bv7), 115bv9, 32bv7), 116bv9, 44bv7), 117bv9, 48bv7), 118bv9, 58bv7), 119bv9, 62bv7), 120bv9, 13bv7), 121bv9, 14bv7), 122bv9, 29bv7), 123bv9, 33bv7), 124bv9, 45bv7), 125bv9, 49bv7), 126bv9, 59bv7), 127bv9, 63bv7), 128bv9, 0bv7), 129bv9, 1bv7), 130bv9, 2bv7), 131bv9, 3bv7), 132bv9, 10bv7), 133bv9, 11bv7), 134bv9, 12bv7), 135bv9, 13bv7), 136bv9, 4bv7), 137bv9, 5bv7), 138bv9, 8bv7), 139bv9, 9bv7), 140bv9, 17bv7), 141bv9, 16bv7), 142bv9, 15bv7), 143bv9, 14bv7), 144bv9, 6bv7), 145bv9, 7bv7), 146bv9, 19bv7), 147bv9, 18bv7), 148bv9, 26bv7), 149bv9, 27bv7), 150bv9, 28bv7), 151bv9, 29bv7), 152bv9, 20bv7), 153bv9, 21bv7), 154bv9, 24bv7), 155bv9, 25bv7), 156bv9, 30bv7), 157bv9, 31bv7), 158bv9, 32bv7), 159bv9, 33bv7), 160bv9, 22bv7), 161bv9, 23bv7), 162bv9, 34bv7), 163bv9, 35bv7), 164bv9, 42bv7), 165bv9, 43bv7), 166bv9, 44bv7), 167bv9, 45bv7), 168bv9, 36bv7), 169bv9, 37bv7), 170bv9, 40bv7), 171bv9, 41bv7), 172bv9, 46bv7), 173bv9, 47bv7), 174bv9, 48bv7), 175bv9, 49bv7), 176bv9, 38bv7), 177bv9, 39bv7), 178bv9, 50bv7), 179bv9, 51bv7), 180bv9, 56bv7), 181bv9, 57bv7), 182bv9, 58bv7), 183bv9, 59bv7), 184bv9, 52bv7), 185bv9, 53bv7), 186bv9, 54bv7), 187bv9, 55bv7), 188bv9, 60bv7), 189bv9, 61bv7), 190bv9, 62bv7), 191bv9, 63bv7);
  assume (0 <= I#[AC_PRED_DIR]) && (I#[AC_PRED_DIR] <= R#[AC_PRED_DIR]) && (R#[AC_PRED_DIR] <= C#[AC_PRED_DIR]);
  assume (0 <= I#[QFS_AC]) && (I#[QFS_AC] <= R#[QFS_AC]) && (R#[QFS_AC] <= C#[QFS_AC]);
  assume (0 <= I#[PQF_AC]) && (I#[PQF_AC] <= R#[PQF_AC]) && (R#[PQF_AC] <= C#[PQF_AC]);
  assume ((St# == rest) || (St# == read)) || (St# == write);
  assume AT#BvSle8(1bv8, count) && AT#BvSle8(count, 64bv8);
  assume (St# == rest) ==> (count == 1bv8);
  assume (Mode#[this#] == Skip) && ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) > 0) ==> AT#BvSlt3(M#[AC_PRED_DIR][I#[AC_PRED_DIR]], 0bv3);
  assume (Mode#[this#] == Skip) ==> (St# == rest);
  assume (Mode#[this#] == Skip) ==> ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assume (Mode#[this#] == Main) && ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) > 0) ==> AT#BvSge3(M#[AC_PRED_DIR][I#[AC_PRED_DIR]], 0bv3);
  assume (Mode#[this#] == Main) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 0) ==> (St# == rest);
  assume (Mode#[this#] == Main) && (St# == rest) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 0) ==> ((R#[QFS_AC] - I#[QFS_AC]) == 0) && ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assume (Mode#[this#] == Main) && (St# == read) ==> ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) && ((R#[QFS_AC] - I#[QFS_AC]) == (AT#Bv2Int8(count) - 1)) && ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assume (Mode#[this#] == Main) && (St# == write) ==> ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) && ((R#[QFS_AC] - I#[QFS_AC]) == 63) && ((C#[PQF_AC] - I#[PQF_AC]) == (AT#Bv2Int8(count) - 1));
  assume (Mode#[this#] == Main) && (St# == rest) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) ==> ((R#[QFS_AC] - I#[QFS_AC]) == 63) && ((C#[PQF_AC] - I#[PQF_AC]) == 63);
  assume (Mode#[this#] == Skip) ==> ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) <= 1) && ((C#[QFS_AC] - I#[QFS_AC]) == 0);
  assume (Mode#[this#] == Main) ==> ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) <= 1) && ((C#[QFS_AC] - I#[QFS_AC]) <= 63);
  assume 1 <= (C#[AC_PRED_DIR] - R#[AC_PRED_DIR]);
  AC_PRED_DIR#0 := M#[AC_PRED_DIR][R#[AC_PRED_DIR]];
  R#[AC_PRED_DIR] := R#[AC_PRED_DIR] + 1;
  assume !(AT#BvSlt3(AC_PRED_DIR#0, 0bv3) && (St# == rest));
  assume AT#BvSge3(AC_PRED_DIR#0, 0bv3) && (St# == rest);
  add_buf := AC_PRED_DIR#0;
  St# := read;
  assert {:msg "Algo_IS_simple.cal(123.3): Action 'start' at <unknown_file>(-1.-1) might not preserve the invariant (#28)"} ((St# == rest) || (St# == read)) || (St# == write);
  assert {:msg "Algo_IS_simple.cal(36.13): Action 'start' at <unknown_file>(-1.-1) might not preserve the invariant (#29)"} AT#BvSle8(1bv8, count) && AT#BvSle8(count, 64bv8);
  assert {:msg "Algo_IS_simple.cal(37.13): Action 'start' at <unknown_file>(-1.-1) might not preserve the invariant (#30)"} (St# == rest) ==> (count == 1bv8);
  assert {:msg "Algo_IS_simple.cal(39.13): Action 'start' at <unknown_file>(-1.-1) might not preserve the invariant (#31)"} (Mode#[this#] == Skip) && ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) > 0) ==> AT#BvSlt3(M#[AC_PRED_DIR][I#[AC_PRED_DIR]], 0bv3);
  assert {:msg "Algo_IS_simple.cal(40.13): Action 'start' at <unknown_file>(-1.-1) might not preserve the invariant (#32)"} (Mode#[this#] == Skip) ==> (St# == rest);
  assert {:msg "Algo_IS_simple.cal(41.13): Action 'start' at <unknown_file>(-1.-1) might not preserve the invariant (#33)"} (Mode#[this#] == Skip) ==> ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assert {:msg "Algo_IS_simple.cal(43.13): Action 'start' at <unknown_file>(-1.-1) might not preserve the invariant (#34)"} (Mode#[this#] == Main) && ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) > 0) ==> AT#BvSge3(M#[AC_PRED_DIR][I#[AC_PRED_DIR]], 0bv3);
  assert {:msg "Algo_IS_simple.cal(44.13): Action 'start' at <unknown_file>(-1.-1) might not preserve the invariant (#35)"} (Mode#[this#] == Main) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 0) ==> (St# == rest);
  assert {:msg "Algo_IS_simple.cal(45.13): Action 'start' at <unknown_file>(-1.-1) might not preserve the invariant (#36)"} (Mode#[this#] == Main) && (St# == rest) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 0) ==> ((R#[QFS_AC] - I#[QFS_AC]) == 0) && ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assert {:msg "Algo_IS_simple.cal(46.13): Action 'start' at <unknown_file>(-1.-1) might not preserve the invariant (#37)"} (Mode#[this#] == Main) && (St# == read) ==> ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) && ((R#[QFS_AC] - I#[QFS_AC]) == (AT#Bv2Int8(count) - 1)) && ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assert {:msg "Algo_IS_simple.cal(47.13): Action 'start' at <unknown_file>(-1.-1) might not preserve the invariant (#38)"} (Mode#[this#] == Main) && (St# == write) ==> ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) && ((R#[QFS_AC] - I#[QFS_AC]) == 63) && ((C#[PQF_AC] - I#[PQF_AC]) == (AT#Bv2Int8(count) - 1));
  assert {:msg "Algo_IS_simple.cal(48.13): Action 'start' at <unknown_file>(-1.-1) might not preserve the invariant (#39)"} (Mode#[this#] == Main) && (St# == rest) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) ==> ((R#[QFS_AC] - I#[QFS_AC]) == 63) && ((C#[PQF_AC] - I#[PQF_AC]) == 63);
  assert {:msg "Action 'start' at <unknown_file>(-1.-1) might not preserve the invariant (#40)"} (Mode#[this#] == Skip) ==> ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) <= 1) && ((C#[QFS_AC] - I#[QFS_AC]) == 0);
  assert {:msg "Action 'start' at <unknown_file>(-1.-1) might not preserve the invariant (#41)"} (Mode#[this#] == Main) ==> ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) <= 1) && ((C#[QFS_AC] - I#[QFS_AC]) <= 63);
}
procedure Algo_IS_simple#done#3()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var AC_PRED_DIR: Chan (bv3);
  var QFS_AC: Chan (bv13);
  var PQF_AC: Chan (bv13);
  var Skip: int;
  var Main: int;
  var St#: int;
  var write: int;
  var read: int;
  var rest: int;
  var Scanmode: Map (bv9) (bv7);
  var count: bv8;
  var addr: bv9;
  var add_buf: bv3;
  var buf: Map (bv7) (bv13);
  var half_: bool;
  var AC_PRED_DIR#0: bv3;
  var QFS_AC#0: bv13;
  assume QFS_AC != PQF_AC;
  assume Skip == 0;
  assume Main == 1;
  assume (Mode#[this#] == Skip) || (Mode#[this#] == Main);
  assume write == 2;
  assume read == 1;
  assume rest == 0;
  assume Scanmode == Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Empty(0bv9, 0bv7), 0bv9, 0bv7), 1bv9, 1bv7), 2bv9, 5bv7), 3bv9, 6bv7), 4bv9, 14bv7), 5bv9, 15bv7), 6bv9, 27bv7), 7bv9, 28bv7), 8bv9, 2bv7), 9bv9, 4bv7), 10bv9, 7bv7), 11bv9, 13bv7), 12bv9, 16bv7), 13bv9, 26bv7), 14bv9, 29bv7), 15bv9, 42bv7), 16bv9, 3bv7), 17bv9, 8bv7), 18bv9, 12bv7), 19bv9, 17bv7), 20bv9, 25bv7), 21bv9, 30bv7), 22bv9, 41bv7), 23bv9, 43bv7), 24bv9, 9bv7), 25bv9, 11bv7), 26bv9, 18bv7), 27bv9, 24bv7), 28bv9, 31bv7), 29bv9, 40bv7), 30bv9, 44bv7), 31bv9, 53bv7), 32bv9, 10bv7), 33bv9, 19bv7), 34bv9, 23bv7), 35bv9, 32bv7), 36bv9, 39bv7), 37bv9, 45bv7), 38bv9, 52bv7), 39bv9, 54bv7), 40bv9, 20bv7), 41bv9, 22bv7), 42bv9, 33bv7), 43bv9, 38bv7), 44bv9, 46bv7), 45bv9, 51bv7), 46bv9, 55bv7), 47bv9, 60bv7), 48bv9, 21bv7), 49bv9, 34bv7), 50bv9, 37bv7), 51bv9, 47bv7), 52bv9, 50bv7), 53bv9, 56bv7), 54bv9, 59bv7), 55bv9, 61bv7), 56bv9, 35bv7), 57bv9, 36bv7), 58bv9, 48bv7), 59bv9, 49bv7), 60bv9, 57bv7), 61bv9, 58bv7), 62bv9, 62bv7), 63bv9, 63bv7), 64bv9, 0bv7), 65bv9, 4bv7), 66bv9, 6bv7), 67bv9, 20bv7), 68bv9, 22bv7), 69bv9, 36bv7), 70bv9, 38bv7), 71bv9, 52bv7), 72bv9, 1bv7), 73bv9, 5bv7), 74bv9, 7bv7), 75bv9, 21bv7), 76bv9, 23bv7), 77bv9, 37bv7), 78bv9, 39bv7), 79bv9, 53bv7), 80bv9, 2bv7), 81bv9, 8bv7), 82bv9, 19bv7), 83bv9, 24bv7), 84bv9, 34bv7), 85bv9, 40bv7), 86bv9, 50bv7), 87bv9, 54bv7), 88bv9, 3bv7), 89bv9, 9bv7), 90bv9, 18bv7), 91bv9, 25bv7), 92bv9, 35bv7), 93bv9, 41bv7), 94bv9, 51bv7), 95bv9, 55bv7), 96bv9, 10bv7), 97bv9, 17bv7), 98bv9, 26bv7), 99bv9, 30bv7), 100bv9, 42bv7), 101bv9, 46bv7), 102bv9, 56bv7), 103bv9, 60bv7), 104bv9, 11bv7), 105bv9, 16bv7), 106bv9, 27bv7), 107bv9, 31bv7), 108bv9, 43bv7), 109bv9, 47bv7), 110bv9, 57bv7), 111bv9, 61bv7), 112bv9, 12bv7), 113bv9, 15bv7), 114bv9, 28bv7), 115bv9, 32bv7), 116bv9, 44bv7), 117bv9, 48bv7), 118bv9, 58bv7), 119bv9, 62bv7), 120bv9, 13bv7), 121bv9, 14bv7), 122bv9, 29bv7), 123bv9, 33bv7), 124bv9, 45bv7), 125bv9, 49bv7), 126bv9, 59bv7), 127bv9, 63bv7), 128bv9, 0bv7), 129bv9, 1bv7), 130bv9, 2bv7), 131bv9, 3bv7), 132bv9, 10bv7), 133bv9, 11bv7), 134bv9, 12bv7), 135bv9, 13bv7), 136bv9, 4bv7), 137bv9, 5bv7), 138bv9, 8bv7), 139bv9, 9bv7), 140bv9, 17bv7), 141bv9, 16bv7), 142bv9, 15bv7), 143bv9, 14bv7), 144bv9, 6bv7), 145bv9, 7bv7), 146bv9, 19bv7), 147bv9, 18bv7), 148bv9, 26bv7), 149bv9, 27bv7), 150bv9, 28bv7), 151bv9, 29bv7), 152bv9, 20bv7), 153bv9, 21bv7), 154bv9, 24bv7), 155bv9, 25bv7), 156bv9, 30bv7), 157bv9, 31bv7), 158bv9, 32bv7), 159bv9, 33bv7), 160bv9, 22bv7), 161bv9, 23bv7), 162bv9, 34bv7), 163bv9, 35bv7), 164bv9, 42bv7), 165bv9, 43bv7), 166bv9, 44bv7), 167bv9, 45bv7), 168bv9, 36bv7), 169bv9, 37bv7), 170bv9, 40bv7), 171bv9, 41bv7), 172bv9, 46bv7), 173bv9, 47bv7), 174bv9, 48bv7), 175bv9, 49bv7), 176bv9, 38bv7), 177bv9, 39bv7), 178bv9, 50bv7), 179bv9, 51bv7), 180bv9, 56bv7), 181bv9, 57bv7), 182bv9, 58bv7), 183bv9, 59bv7), 184bv9, 52bv7), 185bv9, 53bv7), 186bv9, 54bv7), 187bv9, 55bv7), 188bv9, 60bv7), 189bv9, 61bv7), 190bv9, 62bv7), 191bv9, 63bv7);
  assume (0 <= I#[AC_PRED_DIR]) && (I#[AC_PRED_DIR] <= R#[AC_PRED_DIR]) && (R#[AC_PRED_DIR] <= C#[AC_PRED_DIR]);
  assume (0 <= I#[QFS_AC]) && (I#[QFS_AC] <= R#[QFS_AC]) && (R#[QFS_AC] <= C#[QFS_AC]);
  assume (0 <= I#[PQF_AC]) && (I#[PQF_AC] <= R#[PQF_AC]) && (R#[PQF_AC] <= C#[PQF_AC]);
  assume ((St# == rest) || (St# == read)) || (St# == write);
  assume AT#BvSle8(1bv8, count) && AT#BvSle8(count, 64bv8);
  assume (St# == rest) ==> (count == 1bv8);
  assume (Mode#[this#] == Skip) && ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) > 0) ==> AT#BvSlt3(M#[AC_PRED_DIR][I#[AC_PRED_DIR]], 0bv3);
  assume (Mode#[this#] == Skip) ==> (St# == rest);
  assume (Mode#[this#] == Skip) ==> ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assume (Mode#[this#] == Main) && ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) > 0) ==> AT#BvSge3(M#[AC_PRED_DIR][I#[AC_PRED_DIR]], 0bv3);
  assume (Mode#[this#] == Main) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 0) ==> (St# == rest);
  assume (Mode#[this#] == Main) && (St# == rest) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 0) ==> ((R#[QFS_AC] - I#[QFS_AC]) == 0) && ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assume (Mode#[this#] == Main) && (St# == read) ==> ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) && ((R#[QFS_AC] - I#[QFS_AC]) == (AT#Bv2Int8(count) - 1)) && ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assume (Mode#[this#] == Main) && (St# == write) ==> ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) && ((R#[QFS_AC] - I#[QFS_AC]) == 63) && ((C#[PQF_AC] - I#[PQF_AC]) == (AT#Bv2Int8(count) - 1));
  assume (Mode#[this#] == Main) && (St# == rest) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) ==> ((R#[QFS_AC] - I#[QFS_AC]) == 63) && ((C#[PQF_AC] - I#[PQF_AC]) == 63);
  assume (Mode#[this#] == Skip) ==> ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) <= 1) && ((C#[QFS_AC] - I#[QFS_AC]) == 0);
  assume (Mode#[this#] == Main) ==> ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) <= 1) && ((C#[QFS_AC] - I#[QFS_AC]) <= 63);
  assume true;
  assume (count == 64bv8) && ((St# == read) || (St# == write));
  count := 1bv8;
  half_ := !half_;
  addr := (if add_buf == 0bv3 then 0bv9 else (if add_buf == 1bv3 then 64bv9 else 128bv9));
  if (St# == read) {
    St# := write;
  } else {
    if (St# == write) {
      St# := rest;
    }
  }
  assert {:msg "Algo_IS_simple.cal(123.3): Action 'done' at <unknown_file>(-1.-1) might not preserve the invariant (#42)"} ((St# == rest) || (St# == read)) || (St# == write);
  assert {:msg "Algo_IS_simple.cal(36.13): Action 'done' at <unknown_file>(-1.-1) might not preserve the invariant (#43)"} AT#BvSle8(1bv8, count) && AT#BvSle8(count, 64bv8);
  assert {:msg "Algo_IS_simple.cal(37.13): Action 'done' at <unknown_file>(-1.-1) might not preserve the invariant (#44)"} (St# == rest) ==> (count == 1bv8);
  assert {:msg "Algo_IS_simple.cal(39.13): Action 'done' at <unknown_file>(-1.-1) might not preserve the invariant (#45)"} (Mode#[this#] == Skip) && ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) > 0) ==> AT#BvSlt3(M#[AC_PRED_DIR][I#[AC_PRED_DIR]], 0bv3);
  assert {:msg "Algo_IS_simple.cal(40.13): Action 'done' at <unknown_file>(-1.-1) might not preserve the invariant (#46)"} (Mode#[this#] == Skip) ==> (St# == rest);
  assert {:msg "Algo_IS_simple.cal(41.13): Action 'done' at <unknown_file>(-1.-1) might not preserve the invariant (#47)"} (Mode#[this#] == Skip) ==> ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assert {:msg "Algo_IS_simple.cal(43.13): Action 'done' at <unknown_file>(-1.-1) might not preserve the invariant (#48)"} (Mode#[this#] == Main) && ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) > 0) ==> AT#BvSge3(M#[AC_PRED_DIR][I#[AC_PRED_DIR]], 0bv3);
  assert {:msg "Algo_IS_simple.cal(44.13): Action 'done' at <unknown_file>(-1.-1) might not preserve the invariant (#49)"} (Mode#[this#] == Main) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 0) ==> (St# == rest);
  assert {:msg "Algo_IS_simple.cal(45.13): Action 'done' at <unknown_file>(-1.-1) might not preserve the invariant (#50)"} (Mode#[this#] == Main) && (St# == rest) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 0) ==> ((R#[QFS_AC] - I#[QFS_AC]) == 0) && ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assert {:msg "Algo_IS_simple.cal(46.13): Action 'done' at <unknown_file>(-1.-1) might not preserve the invariant (#51)"} (Mode#[this#] == Main) && (St# == read) ==> ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) && ((R#[QFS_AC] - I#[QFS_AC]) == (AT#Bv2Int8(count) - 1)) && ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assert {:msg "Algo_IS_simple.cal(47.13): Action 'done' at <unknown_file>(-1.-1) might not preserve the invariant (#52)"} (Mode#[this#] == Main) && (St# == write) ==> ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) && ((R#[QFS_AC] - I#[QFS_AC]) == 63) && ((C#[PQF_AC] - I#[PQF_AC]) == (AT#Bv2Int8(count) - 1));
  assert {:msg "Algo_IS_simple.cal(48.13): Action 'done' at <unknown_file>(-1.-1) might not preserve the invariant (#53)"} (Mode#[this#] == Main) && (St# == rest) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) ==> ((R#[QFS_AC] - I#[QFS_AC]) == 63) && ((C#[PQF_AC] - I#[PQF_AC]) == 63);
  assert {:msg "Action 'done' at <unknown_file>(-1.-1) might not preserve the invariant (#54)"} (Mode#[this#] == Skip) ==> ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) <= 1) && ((C#[QFS_AC] - I#[QFS_AC]) == 0);
  assert {:msg "Action 'done' at <unknown_file>(-1.-1) might not preserve the invariant (#55)"} (Mode#[this#] == Main) ==> ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) <= 1) && ((C#[QFS_AC] - I#[QFS_AC]) <= 63);
}
procedure Algo_IS_simple#read_only#4()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var AC_PRED_DIR: Chan (bv3);
  var QFS_AC: Chan (bv13);
  var PQF_AC: Chan (bv13);
  var Skip: int;
  var Main: int;
  var St#: int;
  var write: int;
  var read: int;
  var rest: int;
  var Scanmode: Map (bv9) (bv7);
  var count: bv8;
  var addr: bv9;
  var add_buf: bv3;
  var buf: Map (bv7) (bv13);
  var half_: bool;
  var AC_PRED_DIR#0: bv3;
  var QFS_AC#0: bv13;
  assume QFS_AC != PQF_AC;
  assume Skip == 0;
  assume Main == 1;
  assume (Mode#[this#] == Skip) || (Mode#[this#] == Main);
  assume write == 2;
  assume read == 1;
  assume rest == 0;
  assume Scanmode == Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Empty(0bv9, 0bv7), 0bv9, 0bv7), 1bv9, 1bv7), 2bv9, 5bv7), 3bv9, 6bv7), 4bv9, 14bv7), 5bv9, 15bv7), 6bv9, 27bv7), 7bv9, 28bv7), 8bv9, 2bv7), 9bv9, 4bv7), 10bv9, 7bv7), 11bv9, 13bv7), 12bv9, 16bv7), 13bv9, 26bv7), 14bv9, 29bv7), 15bv9, 42bv7), 16bv9, 3bv7), 17bv9, 8bv7), 18bv9, 12bv7), 19bv9, 17bv7), 20bv9, 25bv7), 21bv9, 30bv7), 22bv9, 41bv7), 23bv9, 43bv7), 24bv9, 9bv7), 25bv9, 11bv7), 26bv9, 18bv7), 27bv9, 24bv7), 28bv9, 31bv7), 29bv9, 40bv7), 30bv9, 44bv7), 31bv9, 53bv7), 32bv9, 10bv7), 33bv9, 19bv7), 34bv9, 23bv7), 35bv9, 32bv7), 36bv9, 39bv7), 37bv9, 45bv7), 38bv9, 52bv7), 39bv9, 54bv7), 40bv9, 20bv7), 41bv9, 22bv7), 42bv9, 33bv7), 43bv9, 38bv7), 44bv9, 46bv7), 45bv9, 51bv7), 46bv9, 55bv7), 47bv9, 60bv7), 48bv9, 21bv7), 49bv9, 34bv7), 50bv9, 37bv7), 51bv9, 47bv7), 52bv9, 50bv7), 53bv9, 56bv7), 54bv9, 59bv7), 55bv9, 61bv7), 56bv9, 35bv7), 57bv9, 36bv7), 58bv9, 48bv7), 59bv9, 49bv7), 60bv9, 57bv7), 61bv9, 58bv7), 62bv9, 62bv7), 63bv9, 63bv7), 64bv9, 0bv7), 65bv9, 4bv7), 66bv9, 6bv7), 67bv9, 20bv7), 68bv9, 22bv7), 69bv9, 36bv7), 70bv9, 38bv7), 71bv9, 52bv7), 72bv9, 1bv7), 73bv9, 5bv7), 74bv9, 7bv7), 75bv9, 21bv7), 76bv9, 23bv7), 77bv9, 37bv7), 78bv9, 39bv7), 79bv9, 53bv7), 80bv9, 2bv7), 81bv9, 8bv7), 82bv9, 19bv7), 83bv9, 24bv7), 84bv9, 34bv7), 85bv9, 40bv7), 86bv9, 50bv7), 87bv9, 54bv7), 88bv9, 3bv7), 89bv9, 9bv7), 90bv9, 18bv7), 91bv9, 25bv7), 92bv9, 35bv7), 93bv9, 41bv7), 94bv9, 51bv7), 95bv9, 55bv7), 96bv9, 10bv7), 97bv9, 17bv7), 98bv9, 26bv7), 99bv9, 30bv7), 100bv9, 42bv7), 101bv9, 46bv7), 102bv9, 56bv7), 103bv9, 60bv7), 104bv9, 11bv7), 105bv9, 16bv7), 106bv9, 27bv7), 107bv9, 31bv7), 108bv9, 43bv7), 109bv9, 47bv7), 110bv9, 57bv7), 111bv9, 61bv7), 112bv9, 12bv7), 113bv9, 15bv7), 114bv9, 28bv7), 115bv9, 32bv7), 116bv9, 44bv7), 117bv9, 48bv7), 118bv9, 58bv7), 119bv9, 62bv7), 120bv9, 13bv7), 121bv9, 14bv7), 122bv9, 29bv7), 123bv9, 33bv7), 124bv9, 45bv7), 125bv9, 49bv7), 126bv9, 59bv7), 127bv9, 63bv7), 128bv9, 0bv7), 129bv9, 1bv7), 130bv9, 2bv7), 131bv9, 3bv7), 132bv9, 10bv7), 133bv9, 11bv7), 134bv9, 12bv7), 135bv9, 13bv7), 136bv9, 4bv7), 137bv9, 5bv7), 138bv9, 8bv7), 139bv9, 9bv7), 140bv9, 17bv7), 141bv9, 16bv7), 142bv9, 15bv7), 143bv9, 14bv7), 144bv9, 6bv7), 145bv9, 7bv7), 146bv9, 19bv7), 147bv9, 18bv7), 148bv9, 26bv7), 149bv9, 27bv7), 150bv9, 28bv7), 151bv9, 29bv7), 152bv9, 20bv7), 153bv9, 21bv7), 154bv9, 24bv7), 155bv9, 25bv7), 156bv9, 30bv7), 157bv9, 31bv7), 158bv9, 32bv7), 159bv9, 33bv7), 160bv9, 22bv7), 161bv9, 23bv7), 162bv9, 34bv7), 163bv9, 35bv7), 164bv9, 42bv7), 165bv9, 43bv7), 166bv9, 44bv7), 167bv9, 45bv7), 168bv9, 36bv7), 169bv9, 37bv7), 170bv9, 40bv7), 171bv9, 41bv7), 172bv9, 46bv7), 173bv9, 47bv7), 174bv9, 48bv7), 175bv9, 49bv7), 176bv9, 38bv7), 177bv9, 39bv7), 178bv9, 50bv7), 179bv9, 51bv7), 180bv9, 56bv7), 181bv9, 57bv7), 182bv9, 58bv7), 183bv9, 59bv7), 184bv9, 52bv7), 185bv9, 53bv7), 186bv9, 54bv7), 187bv9, 55bv7), 188bv9, 60bv7), 189bv9, 61bv7), 190bv9, 62bv7), 191bv9, 63bv7);
  assume (0 <= I#[AC_PRED_DIR]) && (I#[AC_PRED_DIR] <= R#[AC_PRED_DIR]) && (R#[AC_PRED_DIR] <= C#[AC_PRED_DIR]);
  assume (0 <= I#[QFS_AC]) && (I#[QFS_AC] <= R#[QFS_AC]) && (R#[QFS_AC] <= C#[QFS_AC]);
  assume (0 <= I#[PQF_AC]) && (I#[PQF_AC] <= R#[PQF_AC]) && (R#[PQF_AC] <= C#[PQF_AC]);
  assume ((St# == rest) || (St# == read)) || (St# == write);
  assume AT#BvSle8(1bv8, count) && AT#BvSle8(count, 64bv8);
  assume (St# == rest) ==> (count == 1bv8);
  assume (Mode#[this#] == Skip) && ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) > 0) ==> AT#BvSlt3(M#[AC_PRED_DIR][I#[AC_PRED_DIR]], 0bv3);
  assume (Mode#[this#] == Skip) ==> (St# == rest);
  assume (Mode#[this#] == Skip) ==> ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assume (Mode#[this#] == Main) && ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) > 0) ==> AT#BvSge3(M#[AC_PRED_DIR][I#[AC_PRED_DIR]], 0bv3);
  assume (Mode#[this#] == Main) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 0) ==> (St# == rest);
  assume (Mode#[this#] == Main) && (St# == rest) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 0) ==> ((R#[QFS_AC] - I#[QFS_AC]) == 0) && ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assume (Mode#[this#] == Main) && (St# == read) ==> ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) && ((R#[QFS_AC] - I#[QFS_AC]) == (AT#Bv2Int8(count) - 1)) && ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assume (Mode#[this#] == Main) && (St# == write) ==> ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) && ((R#[QFS_AC] - I#[QFS_AC]) == 63) && ((C#[PQF_AC] - I#[PQF_AC]) == (AT#Bv2Int8(count) - 1));
  assume (Mode#[this#] == Main) && (St# == rest) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) ==> ((R#[QFS_AC] - I#[QFS_AC]) == 63) && ((C#[PQF_AC] - I#[PQF_AC]) == 63);
  assume (Mode#[this#] == Skip) ==> ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) <= 1) && ((C#[QFS_AC] - I#[QFS_AC]) == 0);
  assume (Mode#[this#] == Main) ==> ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) <= 1) && ((C#[QFS_AC] - I#[QFS_AC]) <= 63);
  assume 1 <= (C#[QFS_AC] - R#[QFS_AC]);
  QFS_AC#0 := M#[QFS_AC][R#[QFS_AC]];
  R#[QFS_AC] := R#[QFS_AC] + 1;
  assume !((count == 64bv8) && ((St# == read) || (St# == write)));
  assume AT#BvSlt8(count, 64bv8) && (St# == read);
  buf := Map#Store(buf, Algo_IS_simple#wa(), QFS_AC#0);
  count := AT#BvAdd8(count, 1bv8);
  St# := read;
  assert {:msg "Algo_IS_simple.cal(123.3): Action 'read_only' at <unknown_file>(-1.-1) might not preserve the invariant (#56)"} ((St# == rest) || (St# == read)) || (St# == write);
  assert {:msg "Algo_IS_simple.cal(36.13): Action 'read_only' at <unknown_file>(-1.-1) might not preserve the invariant (#57)"} AT#BvSle8(1bv8, count) && AT#BvSle8(count, 64bv8);
  assert {:msg "Algo_IS_simple.cal(37.13): Action 'read_only' at <unknown_file>(-1.-1) might not preserve the invariant (#58)"} (St# == rest) ==> (count == 1bv8);
  assert {:msg "Algo_IS_simple.cal(39.13): Action 'read_only' at <unknown_file>(-1.-1) might not preserve the invariant (#59)"} (Mode#[this#] == Skip) && ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) > 0) ==> AT#BvSlt3(M#[AC_PRED_DIR][I#[AC_PRED_DIR]], 0bv3);
  assert {:msg "Algo_IS_simple.cal(40.13): Action 'read_only' at <unknown_file>(-1.-1) might not preserve the invariant (#60)"} (Mode#[this#] == Skip) ==> (St# == rest);
  assert {:msg "Algo_IS_simple.cal(41.13): Action 'read_only' at <unknown_file>(-1.-1) might not preserve the invariant (#61)"} (Mode#[this#] == Skip) ==> ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assert {:msg "Algo_IS_simple.cal(43.13): Action 'read_only' at <unknown_file>(-1.-1) might not preserve the invariant (#62)"} (Mode#[this#] == Main) && ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) > 0) ==> AT#BvSge3(M#[AC_PRED_DIR][I#[AC_PRED_DIR]], 0bv3);
  assert {:msg "Algo_IS_simple.cal(44.13): Action 'read_only' at <unknown_file>(-1.-1) might not preserve the invariant (#63)"} (Mode#[this#] == Main) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 0) ==> (St# == rest);
  assert {:msg "Algo_IS_simple.cal(45.13): Action 'read_only' at <unknown_file>(-1.-1) might not preserve the invariant (#64)"} (Mode#[this#] == Main) && (St# == rest) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 0) ==> ((R#[QFS_AC] - I#[QFS_AC]) == 0) && ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assert {:msg "Algo_IS_simple.cal(46.13): Action 'read_only' at <unknown_file>(-1.-1) might not preserve the invariant (#65)"} (Mode#[this#] == Main) && (St# == read) ==> ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) && ((R#[QFS_AC] - I#[QFS_AC]) == (AT#Bv2Int8(count) - 1)) && ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assert {:msg "Algo_IS_simple.cal(47.13): Action 'read_only' at <unknown_file>(-1.-1) might not preserve the invariant (#66)"} (Mode#[this#] == Main) && (St# == write) ==> ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) && ((R#[QFS_AC] - I#[QFS_AC]) == 63) && ((C#[PQF_AC] - I#[PQF_AC]) == (AT#Bv2Int8(count) - 1));
  assert {:msg "Algo_IS_simple.cal(48.13): Action 'read_only' at <unknown_file>(-1.-1) might not preserve the invariant (#67)"} (Mode#[this#] == Main) && (St# == rest) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) ==> ((R#[QFS_AC] - I#[QFS_AC]) == 63) && ((C#[PQF_AC] - I#[PQF_AC]) == 63);
  assert {:msg "Action 'read_only' at <unknown_file>(-1.-1) might not preserve the invariant (#68)"} (Mode#[this#] == Skip) ==> ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) <= 1) && ((C#[QFS_AC] - I#[QFS_AC]) == 0);
  assert {:msg "Action 'read_only' at <unknown_file>(-1.-1) might not preserve the invariant (#69)"} (Mode#[this#] == Main) ==> ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) <= 1) && ((C#[QFS_AC] - I#[QFS_AC]) <= 63);
}
procedure Algo_IS_simple#write_only#5()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var AC_PRED_DIR: Chan (bv3);
  var QFS_AC: Chan (bv13);
  var PQF_AC: Chan (bv13);
  var Skip: int;
  var Main: int;
  var St#: int;
  var write: int;
  var read: int;
  var rest: int;
  var Scanmode: Map (bv9) (bv7);
  var count: bv8;
  var addr: bv9;
  var add_buf: bv3;
  var buf: Map (bv7) (bv13);
  var half_: bool;
  var AC_PRED_DIR#0: bv3;
  var QFS_AC#0: bv13;
  assume QFS_AC != PQF_AC;
  assume Skip == 0;
  assume Main == 1;
  assume (Mode#[this#] == Skip) || (Mode#[this#] == Main);
  assume write == 2;
  assume read == 1;
  assume rest == 0;
  assume Scanmode == Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Empty(0bv9, 0bv7), 0bv9, 0bv7), 1bv9, 1bv7), 2bv9, 5bv7), 3bv9, 6bv7), 4bv9, 14bv7), 5bv9, 15bv7), 6bv9, 27bv7), 7bv9, 28bv7), 8bv9, 2bv7), 9bv9, 4bv7), 10bv9, 7bv7), 11bv9, 13bv7), 12bv9, 16bv7), 13bv9, 26bv7), 14bv9, 29bv7), 15bv9, 42bv7), 16bv9, 3bv7), 17bv9, 8bv7), 18bv9, 12bv7), 19bv9, 17bv7), 20bv9, 25bv7), 21bv9, 30bv7), 22bv9, 41bv7), 23bv9, 43bv7), 24bv9, 9bv7), 25bv9, 11bv7), 26bv9, 18bv7), 27bv9, 24bv7), 28bv9, 31bv7), 29bv9, 40bv7), 30bv9, 44bv7), 31bv9, 53bv7), 32bv9, 10bv7), 33bv9, 19bv7), 34bv9, 23bv7), 35bv9, 32bv7), 36bv9, 39bv7), 37bv9, 45bv7), 38bv9, 52bv7), 39bv9, 54bv7), 40bv9, 20bv7), 41bv9, 22bv7), 42bv9, 33bv7), 43bv9, 38bv7), 44bv9, 46bv7), 45bv9, 51bv7), 46bv9, 55bv7), 47bv9, 60bv7), 48bv9, 21bv7), 49bv9, 34bv7), 50bv9, 37bv7), 51bv9, 47bv7), 52bv9, 50bv7), 53bv9, 56bv7), 54bv9, 59bv7), 55bv9, 61bv7), 56bv9, 35bv7), 57bv9, 36bv7), 58bv9, 48bv7), 59bv9, 49bv7), 60bv9, 57bv7), 61bv9, 58bv7), 62bv9, 62bv7), 63bv9, 63bv7), 64bv9, 0bv7), 65bv9, 4bv7), 66bv9, 6bv7), 67bv9, 20bv7), 68bv9, 22bv7), 69bv9, 36bv7), 70bv9, 38bv7), 71bv9, 52bv7), 72bv9, 1bv7), 73bv9, 5bv7), 74bv9, 7bv7), 75bv9, 21bv7), 76bv9, 23bv7), 77bv9, 37bv7), 78bv9, 39bv7), 79bv9, 53bv7), 80bv9, 2bv7), 81bv9, 8bv7), 82bv9, 19bv7), 83bv9, 24bv7), 84bv9, 34bv7), 85bv9, 40bv7), 86bv9, 50bv7), 87bv9, 54bv7), 88bv9, 3bv7), 89bv9, 9bv7), 90bv9, 18bv7), 91bv9, 25bv7), 92bv9, 35bv7), 93bv9, 41bv7), 94bv9, 51bv7), 95bv9, 55bv7), 96bv9, 10bv7), 97bv9, 17bv7), 98bv9, 26bv7), 99bv9, 30bv7), 100bv9, 42bv7), 101bv9, 46bv7), 102bv9, 56bv7), 103bv9, 60bv7), 104bv9, 11bv7), 105bv9, 16bv7), 106bv9, 27bv7), 107bv9, 31bv7), 108bv9, 43bv7), 109bv9, 47bv7), 110bv9, 57bv7), 111bv9, 61bv7), 112bv9, 12bv7), 113bv9, 15bv7), 114bv9, 28bv7), 115bv9, 32bv7), 116bv9, 44bv7), 117bv9, 48bv7), 118bv9, 58bv7), 119bv9, 62bv7), 120bv9, 13bv7), 121bv9, 14bv7), 122bv9, 29bv7), 123bv9, 33bv7), 124bv9, 45bv7), 125bv9, 49bv7), 126bv9, 59bv7), 127bv9, 63bv7), 128bv9, 0bv7), 129bv9, 1bv7), 130bv9, 2bv7), 131bv9, 3bv7), 132bv9, 10bv7), 133bv9, 11bv7), 134bv9, 12bv7), 135bv9, 13bv7), 136bv9, 4bv7), 137bv9, 5bv7), 138bv9, 8bv7), 139bv9, 9bv7), 140bv9, 17bv7), 141bv9, 16bv7), 142bv9, 15bv7), 143bv9, 14bv7), 144bv9, 6bv7), 145bv9, 7bv7), 146bv9, 19bv7), 147bv9, 18bv7), 148bv9, 26bv7), 149bv9, 27bv7), 150bv9, 28bv7), 151bv9, 29bv7), 152bv9, 20bv7), 153bv9, 21bv7), 154bv9, 24bv7), 155bv9, 25bv7), 156bv9, 30bv7), 157bv9, 31bv7), 158bv9, 32bv7), 159bv9, 33bv7), 160bv9, 22bv7), 161bv9, 23bv7), 162bv9, 34bv7), 163bv9, 35bv7), 164bv9, 42bv7), 165bv9, 43bv7), 166bv9, 44bv7), 167bv9, 45bv7), 168bv9, 36bv7), 169bv9, 37bv7), 170bv9, 40bv7), 171bv9, 41bv7), 172bv9, 46bv7), 173bv9, 47bv7), 174bv9, 48bv7), 175bv9, 49bv7), 176bv9, 38bv7), 177bv9, 39bv7), 178bv9, 50bv7), 179bv9, 51bv7), 180bv9, 56bv7), 181bv9, 57bv7), 182bv9, 58bv7), 183bv9, 59bv7), 184bv9, 52bv7), 185bv9, 53bv7), 186bv9, 54bv7), 187bv9, 55bv7), 188bv9, 60bv7), 189bv9, 61bv7), 190bv9, 62bv7), 191bv9, 63bv7);
  assume (0 <= I#[AC_PRED_DIR]) && (I#[AC_PRED_DIR] <= R#[AC_PRED_DIR]) && (R#[AC_PRED_DIR] <= C#[AC_PRED_DIR]);
  assume (0 <= I#[QFS_AC]) && (I#[QFS_AC] <= R#[QFS_AC]) && (R#[QFS_AC] <= C#[QFS_AC]);
  assume (0 <= I#[PQF_AC]) && (I#[PQF_AC] <= R#[PQF_AC]) && (R#[PQF_AC] <= C#[PQF_AC]);
  assume ((St# == rest) || (St# == read)) || (St# == write);
  assume AT#BvSle8(1bv8, count) && AT#BvSle8(count, 64bv8);
  assume (St# == rest) ==> (count == 1bv8);
  assume (Mode#[this#] == Skip) && ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) > 0) ==> AT#BvSlt3(M#[AC_PRED_DIR][I#[AC_PRED_DIR]], 0bv3);
  assume (Mode#[this#] == Skip) ==> (St# == rest);
  assume (Mode#[this#] == Skip) ==> ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assume (Mode#[this#] == Main) && ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) > 0) ==> AT#BvSge3(M#[AC_PRED_DIR][I#[AC_PRED_DIR]], 0bv3);
  assume (Mode#[this#] == Main) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 0) ==> (St# == rest);
  assume (Mode#[this#] == Main) && (St# == rest) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 0) ==> ((R#[QFS_AC] - I#[QFS_AC]) == 0) && ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assume (Mode#[this#] == Main) && (St# == read) ==> ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) && ((R#[QFS_AC] - I#[QFS_AC]) == (AT#Bv2Int8(count) - 1)) && ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assume (Mode#[this#] == Main) && (St# == write) ==> ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) && ((R#[QFS_AC] - I#[QFS_AC]) == 63) && ((C#[PQF_AC] - I#[PQF_AC]) == (AT#Bv2Int8(count) - 1));
  assume (Mode#[this#] == Main) && (St# == rest) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) ==> ((R#[QFS_AC] - I#[QFS_AC]) == 63) && ((C#[PQF_AC] - I#[PQF_AC]) == 63);
  assume (Mode#[this#] == Skip) ==> ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) <= 1) && ((C#[QFS_AC] - I#[QFS_AC]) == 0);
  assume (Mode#[this#] == Main) ==> ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) <= 1) && ((C#[QFS_AC] - I#[QFS_AC]) <= 63);
  assume true;
  assume !((count == 64bv8) && ((St# == read) || (St# == write)));
  assume AT#BvSlt8(count, 64bv8) && (St# == write);
  addr := AT#BvAdd9(addr, 1bv9);
  count := AT#BvAdd8(count, 1bv8);
  St# := write;
  M#[PQF_AC][C#[PQF_AC]] := Map#Select(buf, Algo_IS_simple#ra(Map#Select(Scanmode, addr)));
  C#[PQF_AC] := C#[PQF_AC] + 1;
  assert {:msg "Algo_IS_simple.cal(123.3): Action 'write_only' at <unknown_file>(-1.-1) might not preserve the invariant (#70)"} ((St# == rest) || (St# == read)) || (St# == write);
  assert {:msg "Algo_IS_simple.cal(36.13): Action 'write_only' at <unknown_file>(-1.-1) might not preserve the invariant (#71)"} AT#BvSle8(1bv8, count) && AT#BvSle8(count, 64bv8);
  assert {:msg "Algo_IS_simple.cal(37.13): Action 'write_only' at <unknown_file>(-1.-1) might not preserve the invariant (#72)"} (St# == rest) ==> (count == 1bv8);
  assert {:msg "Algo_IS_simple.cal(39.13): Action 'write_only' at <unknown_file>(-1.-1) might not preserve the invariant (#73)"} (Mode#[this#] == Skip) && ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) > 0) ==> AT#BvSlt3(M#[AC_PRED_DIR][I#[AC_PRED_DIR]], 0bv3);
  assert {:msg "Algo_IS_simple.cal(40.13): Action 'write_only' at <unknown_file>(-1.-1) might not preserve the invariant (#74)"} (Mode#[this#] == Skip) ==> (St# == rest);
  assert {:msg "Algo_IS_simple.cal(41.13): Action 'write_only' at <unknown_file>(-1.-1) might not preserve the invariant (#75)"} (Mode#[this#] == Skip) ==> ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assert {:msg "Algo_IS_simple.cal(43.13): Action 'write_only' at <unknown_file>(-1.-1) might not preserve the invariant (#76)"} (Mode#[this#] == Main) && ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) > 0) ==> AT#BvSge3(M#[AC_PRED_DIR][I#[AC_PRED_DIR]], 0bv3);
  assert {:msg "Algo_IS_simple.cal(44.13): Action 'write_only' at <unknown_file>(-1.-1) might not preserve the invariant (#77)"} (Mode#[this#] == Main) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 0) ==> (St# == rest);
  assert {:msg "Algo_IS_simple.cal(45.13): Action 'write_only' at <unknown_file>(-1.-1) might not preserve the invariant (#78)"} (Mode#[this#] == Main) && (St# == rest) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 0) ==> ((R#[QFS_AC] - I#[QFS_AC]) == 0) && ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assert {:msg "Algo_IS_simple.cal(46.13): Action 'write_only' at <unknown_file>(-1.-1) might not preserve the invariant (#79)"} (Mode#[this#] == Main) && (St# == read) ==> ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) && ((R#[QFS_AC] - I#[QFS_AC]) == (AT#Bv2Int8(count) - 1)) && ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assert {:msg "Algo_IS_simple.cal(47.13): Action 'write_only' at <unknown_file>(-1.-1) might not preserve the invariant (#80)"} (Mode#[this#] == Main) && (St# == write) ==> ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) && ((R#[QFS_AC] - I#[QFS_AC]) == 63) && ((C#[PQF_AC] - I#[PQF_AC]) == (AT#Bv2Int8(count) - 1));
  assert {:msg "Algo_IS_simple.cal(48.13): Action 'write_only' at <unknown_file>(-1.-1) might not preserve the invariant (#81)"} (Mode#[this#] == Main) && (St# == rest) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) ==> ((R#[QFS_AC] - I#[QFS_AC]) == 63) && ((C#[PQF_AC] - I#[PQF_AC]) == 63);
  assert {:msg "Action 'write_only' at <unknown_file>(-1.-1) might not preserve the invariant (#82)"} (Mode#[this#] == Skip) ==> ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) <= 1) && ((C#[QFS_AC] - I#[QFS_AC]) == 0);
  assert {:msg "Action 'write_only' at <unknown_file>(-1.-1) might not preserve the invariant (#83)"} (Mode#[this#] == Main) ==> ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) <= 1) && ((C#[QFS_AC] - I#[QFS_AC]) <= 63);
}
procedure Algo_IS_simple##GuardWD#6()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var AC_PRED_DIR: Chan (bv3);
  var QFS_AC: Chan (bv13);
  var PQF_AC: Chan (bv13);
  var Skip: int;
  var Main: int;
  var St#: int;
  var write: int;
  var read: int;
  var rest: int;
  var Scanmode: Map (bv9) (bv7);
  var count: bv8;
  var addr: bv9;
  var add_buf: bv3;
  var buf: Map (bv7) (bv13);
  var half_: bool;
  var AC_PRED_DIR#0: bv3;
  var QFS_AC#0: bv13;
  assume QFS_AC != PQF_AC;
  assume Skip == 0;
  assume Main == 1;
  assume (Mode#[this#] == Skip) || (Mode#[this#] == Main);
  assume write == 2;
  assume read == 1;
  assume rest == 0;
  assume Scanmode == Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Empty(0bv9, 0bv7), 0bv9, 0bv7), 1bv9, 1bv7), 2bv9, 5bv7), 3bv9, 6bv7), 4bv9, 14bv7), 5bv9, 15bv7), 6bv9, 27bv7), 7bv9, 28bv7), 8bv9, 2bv7), 9bv9, 4bv7), 10bv9, 7bv7), 11bv9, 13bv7), 12bv9, 16bv7), 13bv9, 26bv7), 14bv9, 29bv7), 15bv9, 42bv7), 16bv9, 3bv7), 17bv9, 8bv7), 18bv9, 12bv7), 19bv9, 17bv7), 20bv9, 25bv7), 21bv9, 30bv7), 22bv9, 41bv7), 23bv9, 43bv7), 24bv9, 9bv7), 25bv9, 11bv7), 26bv9, 18bv7), 27bv9, 24bv7), 28bv9, 31bv7), 29bv9, 40bv7), 30bv9, 44bv7), 31bv9, 53bv7), 32bv9, 10bv7), 33bv9, 19bv7), 34bv9, 23bv7), 35bv9, 32bv7), 36bv9, 39bv7), 37bv9, 45bv7), 38bv9, 52bv7), 39bv9, 54bv7), 40bv9, 20bv7), 41bv9, 22bv7), 42bv9, 33bv7), 43bv9, 38bv7), 44bv9, 46bv7), 45bv9, 51bv7), 46bv9, 55bv7), 47bv9, 60bv7), 48bv9, 21bv7), 49bv9, 34bv7), 50bv9, 37bv7), 51bv9, 47bv7), 52bv9, 50bv7), 53bv9, 56bv7), 54bv9, 59bv7), 55bv9, 61bv7), 56bv9, 35bv7), 57bv9, 36bv7), 58bv9, 48bv7), 59bv9, 49bv7), 60bv9, 57bv7), 61bv9, 58bv7), 62bv9, 62bv7), 63bv9, 63bv7), 64bv9, 0bv7), 65bv9, 4bv7), 66bv9, 6bv7), 67bv9, 20bv7), 68bv9, 22bv7), 69bv9, 36bv7), 70bv9, 38bv7), 71bv9, 52bv7), 72bv9, 1bv7), 73bv9, 5bv7), 74bv9, 7bv7), 75bv9, 21bv7), 76bv9, 23bv7), 77bv9, 37bv7), 78bv9, 39bv7), 79bv9, 53bv7), 80bv9, 2bv7), 81bv9, 8bv7), 82bv9, 19bv7), 83bv9, 24bv7), 84bv9, 34bv7), 85bv9, 40bv7), 86bv9, 50bv7), 87bv9, 54bv7), 88bv9, 3bv7), 89bv9, 9bv7), 90bv9, 18bv7), 91bv9, 25bv7), 92bv9, 35bv7), 93bv9, 41bv7), 94bv9, 51bv7), 95bv9, 55bv7), 96bv9, 10bv7), 97bv9, 17bv7), 98bv9, 26bv7), 99bv9, 30bv7), 100bv9, 42bv7), 101bv9, 46bv7), 102bv9, 56bv7), 103bv9, 60bv7), 104bv9, 11bv7), 105bv9, 16bv7), 106bv9, 27bv7), 107bv9, 31bv7), 108bv9, 43bv7), 109bv9, 47bv7), 110bv9, 57bv7), 111bv9, 61bv7), 112bv9, 12bv7), 113bv9, 15bv7), 114bv9, 28bv7), 115bv9, 32bv7), 116bv9, 44bv7), 117bv9, 48bv7), 118bv9, 58bv7), 119bv9, 62bv7), 120bv9, 13bv7), 121bv9, 14bv7), 122bv9, 29bv7), 123bv9, 33bv7), 124bv9, 45bv7), 125bv9, 49bv7), 126bv9, 59bv7), 127bv9, 63bv7), 128bv9, 0bv7), 129bv9, 1bv7), 130bv9, 2bv7), 131bv9, 3bv7), 132bv9, 10bv7), 133bv9, 11bv7), 134bv9, 12bv7), 135bv9, 13bv7), 136bv9, 4bv7), 137bv9, 5bv7), 138bv9, 8bv7), 139bv9, 9bv7), 140bv9, 17bv7), 141bv9, 16bv7), 142bv9, 15bv7), 143bv9, 14bv7), 144bv9, 6bv7), 145bv9, 7bv7), 146bv9, 19bv7), 147bv9, 18bv7), 148bv9, 26bv7), 149bv9, 27bv7), 150bv9, 28bv7), 151bv9, 29bv7), 152bv9, 20bv7), 153bv9, 21bv7), 154bv9, 24bv7), 155bv9, 25bv7), 156bv9, 30bv7), 157bv9, 31bv7), 158bv9, 32bv7), 159bv9, 33bv7), 160bv9, 22bv7), 161bv9, 23bv7), 162bv9, 34bv7), 163bv9, 35bv7), 164bv9, 42bv7), 165bv9, 43bv7), 166bv9, 44bv7), 167bv9, 45bv7), 168bv9, 36bv7), 169bv9, 37bv7), 170bv9, 40bv7), 171bv9, 41bv7), 172bv9, 46bv7), 173bv9, 47bv7), 174bv9, 48bv7), 175bv9, 49bv7), 176bv9, 38bv7), 177bv9, 39bv7), 178bv9, 50bv7), 179bv9, 51bv7), 180bv9, 56bv7), 181bv9, 57bv7), 182bv9, 58bv7), 183bv9, 59bv7), 184bv9, 52bv7), 185bv9, 53bv7), 186bv9, 54bv7), 187bv9, 55bv7), 188bv9, 60bv7), 189bv9, 61bv7), 190bv9, 62bv7), 191bv9, 63bv7);
  assume (0 <= I#[AC_PRED_DIR]) && (I#[AC_PRED_DIR] <= R#[AC_PRED_DIR]) && (R#[AC_PRED_DIR] <= C#[AC_PRED_DIR]);
  assume (0 <= I#[QFS_AC]) && (I#[QFS_AC] <= R#[QFS_AC]) && (R#[QFS_AC] <= C#[QFS_AC]);
  assume (0 <= I#[PQF_AC]) && (I#[PQF_AC] <= R#[PQF_AC]) && (R#[PQF_AC] <= C#[PQF_AC]);
  assume ((St# == rest) || (St# == read)) || (St# == write);
  assume AT#BvSle8(1bv8, count) && AT#BvSle8(count, 64bv8);
  assume (St# == rest) ==> (count == 1bv8);
  assume (Mode#[this#] == Skip) && ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) > 0) ==> AT#BvSlt3(M#[AC_PRED_DIR][I#[AC_PRED_DIR]], 0bv3);
  assume (Mode#[this#] == Skip) ==> (St# == rest);
  assume (Mode#[this#] == Skip) ==> ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assume (Mode#[this#] == Main) && ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) > 0) ==> AT#BvSge3(M#[AC_PRED_DIR][I#[AC_PRED_DIR]], 0bv3);
  assume (Mode#[this#] == Main) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 0) ==> (St# == rest);
  assume (Mode#[this#] == Main) && (St# == rest) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 0) ==> ((R#[QFS_AC] - I#[QFS_AC]) == 0) && ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assume (Mode#[this#] == Main) && (St# == read) ==> ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) && ((R#[QFS_AC] - I#[QFS_AC]) == (AT#Bv2Int8(count) - 1)) && ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assume (Mode#[this#] == Main) && (St# == write) ==> ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) && ((R#[QFS_AC] - I#[QFS_AC]) == 63) && ((C#[PQF_AC] - I#[PQF_AC]) == (AT#Bv2Int8(count) - 1));
  assume (Mode#[this#] == Main) && (St# == rest) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) ==> ((R#[QFS_AC] - I#[QFS_AC]) == 63) && ((C#[PQF_AC] - I#[PQF_AC]) == 63);
  assume (Mode#[this#] == Skip) ==> ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) <= 1) && ((C#[QFS_AC] - I#[QFS_AC]) == 0);
  assume (Mode#[this#] == Main) ==> ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) <= 1) && ((C#[QFS_AC] - I#[QFS_AC]) <= 63);
  assert {:msg "The actions 'start' and 'done' of actor 'Algo_IS_simple' might not have mutually exclusive guards (#84)"} !(true && (!((1 <= (C#[AC_PRED_DIR] - R#[AC_PRED_DIR])) && AT#BvSlt3(M#[AC_PRED_DIR][R#[AC_PRED_DIR]], 0bv3) && (St# == rest))) && (1 <= (C#[AC_PRED_DIR] - R#[AC_PRED_DIR])) && AT#BvSge3(M#[AC_PRED_DIR][R#[AC_PRED_DIR]], 0bv3) && (St# == rest) && true && true && (count == 64bv8) && ((St# == read) || (St# == write)));
  assert {:msg "The actions 'start' and 'read_only' of actor 'Algo_IS_simple' might not have mutually exclusive guards (#85)"} !(true && (!((1 <= (C#[AC_PRED_DIR] - R#[AC_PRED_DIR])) && AT#BvSlt3(M#[AC_PRED_DIR][R#[AC_PRED_DIR]], 0bv3) && (St# == rest))) && (1 <= (C#[AC_PRED_DIR] - R#[AC_PRED_DIR])) && AT#BvSge3(M#[AC_PRED_DIR][R#[AC_PRED_DIR]], 0bv3) && (St# == rest) && true && (!(true && (count == 64bv8) && ((St# == read) || (St# == write)))) && (1 <= (C#[QFS_AC] - R#[QFS_AC])) && AT#BvSlt8(count, 64bv8) && (St# == read));
  assert {:msg "The actions 'start' and 'write_only' of actor 'Algo_IS_simple' might not have mutually exclusive guards (#86)"} !(true && (!((1 <= (C#[AC_PRED_DIR] - R#[AC_PRED_DIR])) && AT#BvSlt3(M#[AC_PRED_DIR][R#[AC_PRED_DIR]], 0bv3) && (St# == rest))) && (1 <= (C#[AC_PRED_DIR] - R#[AC_PRED_DIR])) && AT#BvSge3(M#[AC_PRED_DIR][R#[AC_PRED_DIR]], 0bv3) && (St# == rest) && true && (!(true && (count == 64bv8) && ((St# == read) || (St# == write)))) && true && AT#BvSlt8(count, 64bv8) && (St# == write));
  assert {:msg "The actions 'start' and 'skip' of actor 'Algo_IS_simple' might not have mutually exclusive guards (#87)"} !(true && (!((1 <= (C#[AC_PRED_DIR] - R#[AC_PRED_DIR])) && AT#BvSlt3(M#[AC_PRED_DIR][R#[AC_PRED_DIR]], 0bv3) && (St# == rest))) && (1 <= (C#[AC_PRED_DIR] - R#[AC_PRED_DIR])) && AT#BvSge3(M#[AC_PRED_DIR][R#[AC_PRED_DIR]], 0bv3) && (St# == rest) && true && (1 <= (C#[AC_PRED_DIR] - R#[AC_PRED_DIR])) && AT#BvSlt3(M#[AC_PRED_DIR][R#[AC_PRED_DIR]], 0bv3) && (St# == rest));
  assert {:msg "The actions 'done' and 'read_only' of actor 'Algo_IS_simple' might not have mutually exclusive guards (#88)"} !(true && true && (count == 64bv8) && ((St# == read) || (St# == write)) && true && (!(true && (count == 64bv8) && ((St# == read) || (St# == write)))) && (1 <= (C#[QFS_AC] - R#[QFS_AC])) && AT#BvSlt8(count, 64bv8) && (St# == read));
  assert {:msg "The actions 'done' and 'write_only' of actor 'Algo_IS_simple' might not have mutually exclusive guards (#89)"} !(true && true && (count == 64bv8) && ((St# == read) || (St# == write)) && true && (!(true && (count == 64bv8) && ((St# == read) || (St# == write)))) && true && AT#BvSlt8(count, 64bv8) && (St# == write));
  assert {:msg "The actions 'done' and 'skip' of actor 'Algo_IS_simple' might not have mutually exclusive guards (#90)"} !(true && true && (count == 64bv8) && ((St# == read) || (St# == write)) && true && (1 <= (C#[AC_PRED_DIR] - R#[AC_PRED_DIR])) && AT#BvSlt3(M#[AC_PRED_DIR][R#[AC_PRED_DIR]], 0bv3) && (St# == rest));
  assert {:msg "The actions 'read_only' and 'write_only' of actor 'Algo_IS_simple' might not have mutually exclusive guards (#91)"} !(true && (!(true && (count == 64bv8) && ((St# == read) || (St# == write)))) && (1 <= (C#[QFS_AC] - R#[QFS_AC])) && AT#BvSlt8(count, 64bv8) && (St# == read) && true && (!(true && (count == 64bv8) && ((St# == read) || (St# == write)))) && true && AT#BvSlt8(count, 64bv8) && (St# == write));
  assert {:msg "The actions 'read_only' and 'skip' of actor 'Algo_IS_simple' might not have mutually exclusive guards (#92)"} !(true && (!(true && (count == 64bv8) && ((St# == read) || (St# == write)))) && (1 <= (C#[QFS_AC] - R#[QFS_AC])) && AT#BvSlt8(count, 64bv8) && (St# == read) && true && (1 <= (C#[AC_PRED_DIR] - R#[AC_PRED_DIR])) && AT#BvSlt3(M#[AC_PRED_DIR][R#[AC_PRED_DIR]], 0bv3) && (St# == rest));
  assert {:msg "The actions 'write_only' and 'skip' of actor 'Algo_IS_simple' might not have mutually exclusive guards (#93)"} !(true && (!(true && (count == 64bv8) && ((St# == read) || (St# == write)))) && true && AT#BvSlt8(count, 64bv8) && (St# == write) && true && (1 <= (C#[AC_PRED_DIR] - R#[AC_PRED_DIR])) && AT#BvSlt3(M#[AC_PRED_DIR][R#[AC_PRED_DIR]], 0bv3) && (St# == rest));
}
procedure Algo_IS_simple#contract#Skip#input#7()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var AC_PRED_DIR: Chan (bv3);
  var QFS_AC: Chan (bv13);
  var PQF_AC: Chan (bv13);
  var Skip: int;
  var Main: int;
  var St#: int;
  var write: int;
  var read: int;
  var rest: int;
  var Scanmode: Map (bv9) (bv7);
  var count: bv8;
  var addr: bv9;
  var add_buf: bv3;
  var buf: Map (bv7) (bv13);
  var half_: bool;
  assume QFS_AC != PQF_AC;
  assume Skip == 0;
  assume Main == 1;
  assume (Mode#[this#] == Skip) || (Mode#[this#] == Main);
  assume write == 2;
  assume read == 1;
  assume rest == 0;
  assume Scanmode == Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Empty(0bv9, 0bv7), 0bv9, 0bv7), 1bv9, 1bv7), 2bv9, 5bv7), 3bv9, 6bv7), 4bv9, 14bv7), 5bv9, 15bv7), 6bv9, 27bv7), 7bv9, 28bv7), 8bv9, 2bv7), 9bv9, 4bv7), 10bv9, 7bv7), 11bv9, 13bv7), 12bv9, 16bv7), 13bv9, 26bv7), 14bv9, 29bv7), 15bv9, 42bv7), 16bv9, 3bv7), 17bv9, 8bv7), 18bv9, 12bv7), 19bv9, 17bv7), 20bv9, 25bv7), 21bv9, 30bv7), 22bv9, 41bv7), 23bv9, 43bv7), 24bv9, 9bv7), 25bv9, 11bv7), 26bv9, 18bv7), 27bv9, 24bv7), 28bv9, 31bv7), 29bv9, 40bv7), 30bv9, 44bv7), 31bv9, 53bv7), 32bv9, 10bv7), 33bv9, 19bv7), 34bv9, 23bv7), 35bv9, 32bv7), 36bv9, 39bv7), 37bv9, 45bv7), 38bv9, 52bv7), 39bv9, 54bv7), 40bv9, 20bv7), 41bv9, 22bv7), 42bv9, 33bv7), 43bv9, 38bv7), 44bv9, 46bv7), 45bv9, 51bv7), 46bv9, 55bv7), 47bv9, 60bv7), 48bv9, 21bv7), 49bv9, 34bv7), 50bv9, 37bv7), 51bv9, 47bv7), 52bv9, 50bv7), 53bv9, 56bv7), 54bv9, 59bv7), 55bv9, 61bv7), 56bv9, 35bv7), 57bv9, 36bv7), 58bv9, 48bv7), 59bv9, 49bv7), 60bv9, 57bv7), 61bv9, 58bv7), 62bv9, 62bv7), 63bv9, 63bv7), 64bv9, 0bv7), 65bv9, 4bv7), 66bv9, 6bv7), 67bv9, 20bv7), 68bv9, 22bv7), 69bv9, 36bv7), 70bv9, 38bv7), 71bv9, 52bv7), 72bv9, 1bv7), 73bv9, 5bv7), 74bv9, 7bv7), 75bv9, 21bv7), 76bv9, 23bv7), 77bv9, 37bv7), 78bv9, 39bv7), 79bv9, 53bv7), 80bv9, 2bv7), 81bv9, 8bv7), 82bv9, 19bv7), 83bv9, 24bv7), 84bv9, 34bv7), 85bv9, 40bv7), 86bv9, 50bv7), 87bv9, 54bv7), 88bv9, 3bv7), 89bv9, 9bv7), 90bv9, 18bv7), 91bv9, 25bv7), 92bv9, 35bv7), 93bv9, 41bv7), 94bv9, 51bv7), 95bv9, 55bv7), 96bv9, 10bv7), 97bv9, 17bv7), 98bv9, 26bv7), 99bv9, 30bv7), 100bv9, 42bv7), 101bv9, 46bv7), 102bv9, 56bv7), 103bv9, 60bv7), 104bv9, 11bv7), 105bv9, 16bv7), 106bv9, 27bv7), 107bv9, 31bv7), 108bv9, 43bv7), 109bv9, 47bv7), 110bv9, 57bv7), 111bv9, 61bv7), 112bv9, 12bv7), 113bv9, 15bv7), 114bv9, 28bv7), 115bv9, 32bv7), 116bv9, 44bv7), 117bv9, 48bv7), 118bv9, 58bv7), 119bv9, 62bv7), 120bv9, 13bv7), 121bv9, 14bv7), 122bv9, 29bv7), 123bv9, 33bv7), 124bv9, 45bv7), 125bv9, 49bv7), 126bv9, 59bv7), 127bv9, 63bv7), 128bv9, 0bv7), 129bv9, 1bv7), 130bv9, 2bv7), 131bv9, 3bv7), 132bv9, 10bv7), 133bv9, 11bv7), 134bv9, 12bv7), 135bv9, 13bv7), 136bv9, 4bv7), 137bv9, 5bv7), 138bv9, 8bv7), 139bv9, 9bv7), 140bv9, 17bv7), 141bv9, 16bv7), 142bv9, 15bv7), 143bv9, 14bv7), 144bv9, 6bv7), 145bv9, 7bv7), 146bv9, 19bv7), 147bv9, 18bv7), 148bv9, 26bv7), 149bv9, 27bv7), 150bv9, 28bv7), 151bv9, 29bv7), 152bv9, 20bv7), 153bv9, 21bv7), 154bv9, 24bv7), 155bv9, 25bv7), 156bv9, 30bv7), 157bv9, 31bv7), 158bv9, 32bv7), 159bv9, 33bv7), 160bv9, 22bv7), 161bv9, 23bv7), 162bv9, 34bv7), 163bv9, 35bv7), 164bv9, 42bv7), 165bv9, 43bv7), 166bv9, 44bv7), 167bv9, 45bv7), 168bv9, 36bv7), 169bv9, 37bv7), 170bv9, 40bv7), 171bv9, 41bv7), 172bv9, 46bv7), 173bv9, 47bv7), 174bv9, 48bv7), 175bv9, 49bv7), 176bv9, 38bv7), 177bv9, 39bv7), 178bv9, 50bv7), 179bv9, 51bv7), 180bv9, 56bv7), 181bv9, 57bv7), 182bv9, 58bv7), 183bv9, 59bv7), 184bv9, 52bv7), 185bv9, 53bv7), 186bv9, 54bv7), 187bv9, 55bv7), 188bv9, 60bv7), 189bv9, 61bv7), 190bv9, 62bv7), 191bv9, 63bv7);
  assume (0 <= I#[AC_PRED_DIR]) && (I#[AC_PRED_DIR] <= R#[AC_PRED_DIR]) && (R#[AC_PRED_DIR] <= C#[AC_PRED_DIR]);
  assume (0 <= I#[QFS_AC]) && (I#[QFS_AC] <= R#[QFS_AC]) && (R#[QFS_AC] <= C#[QFS_AC]);
  assume (0 <= I#[PQF_AC]) && (I#[PQF_AC] <= R#[PQF_AC]) && (R#[PQF_AC] <= C#[PQF_AC]);
  assume Mode#[this#] == Skip;
  assume R#[PQF_AC] == I#[PQF_AC];
  assume ((St# == rest) || (St# == read)) || (St# == write);
  assume AT#BvSle8(1bv8, count) && AT#BvSle8(count, 64bv8);
  assume (St# == rest) ==> (count == 1bv8);
  assume (Mode#[this#] == Skip) && ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) > 0) ==> AT#BvSlt3(M#[AC_PRED_DIR][I#[AC_PRED_DIR]], 0bv3);
  assume (Mode#[this#] == Skip) ==> (St# == rest);
  assume (Mode#[this#] == Skip) ==> ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assume (Mode#[this#] == Main) && ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) > 0) ==> AT#BvSge3(M#[AC_PRED_DIR][I#[AC_PRED_DIR]], 0bv3);
  assume (Mode#[this#] == Main) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 0) ==> (St# == rest);
  assume (Mode#[this#] == Main) && (St# == rest) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 0) ==> ((R#[QFS_AC] - I#[QFS_AC]) == 0) && ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assume (Mode#[this#] == Main) && (St# == read) ==> ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) && ((R#[QFS_AC] - I#[QFS_AC]) == (AT#Bv2Int8(count) - 1)) && ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assume (Mode#[this#] == Main) && (St# == write) ==> ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) && ((R#[QFS_AC] - I#[QFS_AC]) == 63) && ((C#[PQF_AC] - I#[PQF_AC]) == (AT#Bv2Int8(count) - 1));
  assume (Mode#[this#] == Main) && (St# == rest) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) ==> ((R#[QFS_AC] - I#[QFS_AC]) == 63) && ((C#[PQF_AC] - I#[PQF_AC]) == 63);
  assume (Mode#[this#] == Skip) ==> ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) <= 1) && ((C#[QFS_AC] - I#[QFS_AC]) == 0);
  assume (Mode#[this#] == Main) ==> ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) <= 1) && ((C#[QFS_AC] - I#[QFS_AC]) <= 63);
  assume (C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) < 1;
  C#[AC_PRED_DIR] := C#[AC_PRED_DIR] + 1;
  assume AT#BvSlt3(M#[AC_PRED_DIR][I#[AC_PRED_DIR]], 0bv3);
  assert {:msg "Algo_IS_simple.cal(123.3): Invariant might be falsified by actor input (#94)"} ((St# == rest) || (St# == read)) || (St# == write);
  assert {:msg "Algo_IS_simple.cal(36.13): Invariant might be falsified by actor input (#95)"} AT#BvSle8(1bv8, count) && AT#BvSle8(count, 64bv8);
  assert {:msg "Algo_IS_simple.cal(37.13): Invariant might be falsified by actor input (#96)"} (St# == rest) ==> (count == 1bv8);
  assert {:msg "Algo_IS_simple.cal(39.13): Invariant might be falsified by actor input (#97)"} (Mode#[this#] == Skip) && ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) > 0) ==> AT#BvSlt3(M#[AC_PRED_DIR][I#[AC_PRED_DIR]], 0bv3);
  assert {:msg "Algo_IS_simple.cal(40.13): Invariant might be falsified by actor input (#98)"} (Mode#[this#] == Skip) ==> (St# == rest);
  assert {:msg "Algo_IS_simple.cal(41.13): Invariant might be falsified by actor input (#99)"} (Mode#[this#] == Skip) ==> ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assert {:msg "Algo_IS_simple.cal(43.13): Invariant might be falsified by actor input (#100)"} (Mode#[this#] == Main) && ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) > 0) ==> AT#BvSge3(M#[AC_PRED_DIR][I#[AC_PRED_DIR]], 0bv3);
  assert {:msg "Algo_IS_simple.cal(44.13): Invariant might be falsified by actor input (#101)"} (Mode#[this#] == Main) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 0) ==> (St# == rest);
  assert {:msg "Algo_IS_simple.cal(45.13): Invariant might be falsified by actor input (#102)"} (Mode#[this#] == Main) && (St# == rest) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 0) ==> ((R#[QFS_AC] - I#[QFS_AC]) == 0) && ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assert {:msg "Algo_IS_simple.cal(46.13): Invariant might be falsified by actor input (#103)"} (Mode#[this#] == Main) && (St# == read) ==> ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) && ((R#[QFS_AC] - I#[QFS_AC]) == (AT#Bv2Int8(count) - 1)) && ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assert {:msg "Algo_IS_simple.cal(47.13): Invariant might be falsified by actor input (#104)"} (Mode#[this#] == Main) && (St# == write) ==> ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) && ((R#[QFS_AC] - I#[QFS_AC]) == 63) && ((C#[PQF_AC] - I#[PQF_AC]) == (AT#Bv2Int8(count) - 1));
  assert {:msg "Algo_IS_simple.cal(48.13): Invariant might be falsified by actor input (#105)"} (Mode#[this#] == Main) && (St# == rest) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) ==> ((R#[QFS_AC] - I#[QFS_AC]) == 63) && ((C#[PQF_AC] - I#[PQF_AC]) == 63);
  assert {:msg "Invariant might be falsified by actor input (#106)"} (Mode#[this#] == Skip) ==> ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) <= 1) && ((C#[QFS_AC] - I#[QFS_AC]) == 0);
  assert {:msg "Invariant might be falsified by actor input (#107)"} (Mode#[this#] == Main) ==> ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) <= 1) && ((C#[QFS_AC] - I#[QFS_AC]) <= 63);
}
procedure Algo_IS_simple#contract#Skip#exit#8()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var AC_PRED_DIR: Chan (bv3);
  var QFS_AC: Chan (bv13);
  var PQF_AC: Chan (bv13);
  var Skip: int;
  var Main: int;
  var St#: int;
  var write: int;
  var read: int;
  var rest: int;
  var Scanmode: Map (bv9) (bv7);
  var count: bv8;
  var addr: bv9;
  var add_buf: bv3;
  var buf: Map (bv7) (bv13);
  var half_: bool;
  assume QFS_AC != PQF_AC;
  assume Skip == 0;
  assume Main == 1;
  assume (Mode#[this#] == Skip) || (Mode#[this#] == Main);
  assume write == 2;
  assume read == 1;
  assume rest == 0;
  assume Scanmode == Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Empty(0bv9, 0bv7), 0bv9, 0bv7), 1bv9, 1bv7), 2bv9, 5bv7), 3bv9, 6bv7), 4bv9, 14bv7), 5bv9, 15bv7), 6bv9, 27bv7), 7bv9, 28bv7), 8bv9, 2bv7), 9bv9, 4bv7), 10bv9, 7bv7), 11bv9, 13bv7), 12bv9, 16bv7), 13bv9, 26bv7), 14bv9, 29bv7), 15bv9, 42bv7), 16bv9, 3bv7), 17bv9, 8bv7), 18bv9, 12bv7), 19bv9, 17bv7), 20bv9, 25bv7), 21bv9, 30bv7), 22bv9, 41bv7), 23bv9, 43bv7), 24bv9, 9bv7), 25bv9, 11bv7), 26bv9, 18bv7), 27bv9, 24bv7), 28bv9, 31bv7), 29bv9, 40bv7), 30bv9, 44bv7), 31bv9, 53bv7), 32bv9, 10bv7), 33bv9, 19bv7), 34bv9, 23bv7), 35bv9, 32bv7), 36bv9, 39bv7), 37bv9, 45bv7), 38bv9, 52bv7), 39bv9, 54bv7), 40bv9, 20bv7), 41bv9, 22bv7), 42bv9, 33bv7), 43bv9, 38bv7), 44bv9, 46bv7), 45bv9, 51bv7), 46bv9, 55bv7), 47bv9, 60bv7), 48bv9, 21bv7), 49bv9, 34bv7), 50bv9, 37bv7), 51bv9, 47bv7), 52bv9, 50bv7), 53bv9, 56bv7), 54bv9, 59bv7), 55bv9, 61bv7), 56bv9, 35bv7), 57bv9, 36bv7), 58bv9, 48bv7), 59bv9, 49bv7), 60bv9, 57bv7), 61bv9, 58bv7), 62bv9, 62bv7), 63bv9, 63bv7), 64bv9, 0bv7), 65bv9, 4bv7), 66bv9, 6bv7), 67bv9, 20bv7), 68bv9, 22bv7), 69bv9, 36bv7), 70bv9, 38bv7), 71bv9, 52bv7), 72bv9, 1bv7), 73bv9, 5bv7), 74bv9, 7bv7), 75bv9, 21bv7), 76bv9, 23bv7), 77bv9, 37bv7), 78bv9, 39bv7), 79bv9, 53bv7), 80bv9, 2bv7), 81bv9, 8bv7), 82bv9, 19bv7), 83bv9, 24bv7), 84bv9, 34bv7), 85bv9, 40bv7), 86bv9, 50bv7), 87bv9, 54bv7), 88bv9, 3bv7), 89bv9, 9bv7), 90bv9, 18bv7), 91bv9, 25bv7), 92bv9, 35bv7), 93bv9, 41bv7), 94bv9, 51bv7), 95bv9, 55bv7), 96bv9, 10bv7), 97bv9, 17bv7), 98bv9, 26bv7), 99bv9, 30bv7), 100bv9, 42bv7), 101bv9, 46bv7), 102bv9, 56bv7), 103bv9, 60bv7), 104bv9, 11bv7), 105bv9, 16bv7), 106bv9, 27bv7), 107bv9, 31bv7), 108bv9, 43bv7), 109bv9, 47bv7), 110bv9, 57bv7), 111bv9, 61bv7), 112bv9, 12bv7), 113bv9, 15bv7), 114bv9, 28bv7), 115bv9, 32bv7), 116bv9, 44bv7), 117bv9, 48bv7), 118bv9, 58bv7), 119bv9, 62bv7), 120bv9, 13bv7), 121bv9, 14bv7), 122bv9, 29bv7), 123bv9, 33bv7), 124bv9, 45bv7), 125bv9, 49bv7), 126bv9, 59bv7), 127bv9, 63bv7), 128bv9, 0bv7), 129bv9, 1bv7), 130bv9, 2bv7), 131bv9, 3bv7), 132bv9, 10bv7), 133bv9, 11bv7), 134bv9, 12bv7), 135bv9, 13bv7), 136bv9, 4bv7), 137bv9, 5bv7), 138bv9, 8bv7), 139bv9, 9bv7), 140bv9, 17bv7), 141bv9, 16bv7), 142bv9, 15bv7), 143bv9, 14bv7), 144bv9, 6bv7), 145bv9, 7bv7), 146bv9, 19bv7), 147bv9, 18bv7), 148bv9, 26bv7), 149bv9, 27bv7), 150bv9, 28bv7), 151bv9, 29bv7), 152bv9, 20bv7), 153bv9, 21bv7), 154bv9, 24bv7), 155bv9, 25bv7), 156bv9, 30bv7), 157bv9, 31bv7), 158bv9, 32bv7), 159bv9, 33bv7), 160bv9, 22bv7), 161bv9, 23bv7), 162bv9, 34bv7), 163bv9, 35bv7), 164bv9, 42bv7), 165bv9, 43bv7), 166bv9, 44bv7), 167bv9, 45bv7), 168bv9, 36bv7), 169bv9, 37bv7), 170bv9, 40bv7), 171bv9, 41bv7), 172bv9, 46bv7), 173bv9, 47bv7), 174bv9, 48bv7), 175bv9, 49bv7), 176bv9, 38bv7), 177bv9, 39bv7), 178bv9, 50bv7), 179bv9, 51bv7), 180bv9, 56bv7), 181bv9, 57bv7), 182bv9, 58bv7), 183bv9, 59bv7), 184bv9, 52bv7), 185bv9, 53bv7), 186bv9, 54bv7), 187bv9, 55bv7), 188bv9, 60bv7), 189bv9, 61bv7), 190bv9, 62bv7), 191bv9, 63bv7);
  assume (0 <= I#[AC_PRED_DIR]) && (I#[AC_PRED_DIR] <= R#[AC_PRED_DIR]) && (R#[AC_PRED_DIR] <= C#[AC_PRED_DIR]);
  assume (0 <= I#[QFS_AC]) && (I#[QFS_AC] <= R#[QFS_AC]) && (R#[QFS_AC] <= C#[QFS_AC]);
  assume (0 <= I#[PQF_AC]) && (I#[PQF_AC] <= R#[PQF_AC]) && (R#[PQF_AC] <= C#[PQF_AC]);
  assume Mode#[this#] == Skip;
  assume R#[PQF_AC] == I#[PQF_AC];
  assume ((St# == rest) || (St# == read)) || (St# == write);
  assume AT#BvSle8(1bv8, count) && AT#BvSle8(count, 64bv8);
  assume (St# == rest) ==> (count == 1bv8);
  assume (Mode#[this#] == Skip) && ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) > 0) ==> AT#BvSlt3(M#[AC_PRED_DIR][I#[AC_PRED_DIR]], 0bv3);
  assume (Mode#[this#] == Skip) ==> (St# == rest);
  assume (Mode#[this#] == Skip) ==> ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assume (Mode#[this#] == Main) && ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) > 0) ==> AT#BvSge3(M#[AC_PRED_DIR][I#[AC_PRED_DIR]], 0bv3);
  assume (Mode#[this#] == Main) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 0) ==> (St# == rest);
  assume (Mode#[this#] == Main) && (St# == rest) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 0) ==> ((R#[QFS_AC] - I#[QFS_AC]) == 0) && ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assume (Mode#[this#] == Main) && (St# == read) ==> ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) && ((R#[QFS_AC] - I#[QFS_AC]) == (AT#Bv2Int8(count) - 1)) && ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assume (Mode#[this#] == Main) && (St# == write) ==> ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) && ((R#[QFS_AC] - I#[QFS_AC]) == 63) && ((C#[PQF_AC] - I#[PQF_AC]) == (AT#Bv2Int8(count) - 1));
  assume (Mode#[this#] == Main) && (St# == rest) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) ==> ((R#[QFS_AC] - I#[QFS_AC]) == 63) && ((C#[PQF_AC] - I#[PQF_AC]) == 63);
  assume (Mode#[this#] == Skip) ==> ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) <= 1) && ((C#[QFS_AC] - I#[QFS_AC]) == 0);
  assume (Mode#[this#] == Main) ==> ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) <= 1) && ((C#[QFS_AC] - I#[QFS_AC]) <= 63);
  assume (C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1;
  assume (C#[QFS_AC] - I#[QFS_AC]) == 0;
  assume !(true && (!((1 <= (C#[AC_PRED_DIR] - R#[AC_PRED_DIR])) && AT#BvSlt3(M#[AC_PRED_DIR][R#[AC_PRED_DIR]], 0bv3) && (St# == rest))) && (1 <= (C#[AC_PRED_DIR] - R#[AC_PRED_DIR])) && AT#BvSge3(M#[AC_PRED_DIR][R#[AC_PRED_DIR]], 0bv3) && (St# == rest));
  assume !(true && true && (count == 64bv8) && ((St# == read) || (St# == write)));
  assume !(true && (!(true && (count == 64bv8) && ((St# == read) || (St# == write)))) && (1 <= (C#[QFS_AC] - R#[QFS_AC])) && AT#BvSlt8(count, 64bv8) && (St# == read));
  assume !(true && (!(true && (count == 64bv8) && ((St# == read) || (St# == write)))) && true && AT#BvSlt8(count, 64bv8) && (St# == write));
  assume !(true && (1 <= (C#[AC_PRED_DIR] - R#[AC_PRED_DIR])) && AT#BvSlt3(M#[AC_PRED_DIR][R#[AC_PRED_DIR]], 0bv3) && (St# == rest));
  assert {:msg "Algo_IS_simple.cal(26.3): The correct number of tokens might not be produced on output 'PQF_AC' with contract 'Skip' (#108)"} (C#[PQF_AC] - I#[PQF_AC]) == 0;
  R#[PQF_AC] := R#[PQF_AC] + 0;
  I# := R#;
  assert {:msg "Algo_IS_simple.cal(123.3): The actor might not preserve the invariant with contract 'Skip' at Algo_IS_simple.cal(26.3) (#109)"} ((St# == rest) || (St# == read)) || (St# == write);
  assert {:msg "Algo_IS_simple.cal(36.13): The actor might not preserve the invariant with contract 'Skip' at Algo_IS_simple.cal(26.3) (#110)"} AT#BvSle8(1bv8, count) && AT#BvSle8(count, 64bv8);
  assert {:msg "Algo_IS_simple.cal(37.13): The actor might not preserve the invariant with contract 'Skip' at Algo_IS_simple.cal(26.3) (#111)"} (St# == rest) ==> (count == 1bv8);
  assert {:msg "Algo_IS_simple.cal(39.13): The actor might not preserve the invariant with contract 'Skip' at Algo_IS_simple.cal(26.3) (#112)"} (Mode#[this#] == Skip) && ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) > 0) ==> AT#BvSlt3(M#[AC_PRED_DIR][I#[AC_PRED_DIR]], 0bv3);
  assert {:msg "Algo_IS_simple.cal(40.13): The actor might not preserve the invariant with contract 'Skip' at Algo_IS_simple.cal(26.3) (#113)"} (Mode#[this#] == Skip) ==> (St# == rest);
  assert {:msg "Algo_IS_simple.cal(41.13): The actor might not preserve the invariant with contract 'Skip' at Algo_IS_simple.cal(26.3) (#114)"} (Mode#[this#] == Skip) ==> ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assert {:msg "Algo_IS_simple.cal(43.13): The actor might not preserve the invariant with contract 'Skip' at Algo_IS_simple.cal(26.3) (#115)"} (Mode#[this#] == Main) && ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) > 0) ==> AT#BvSge3(M#[AC_PRED_DIR][I#[AC_PRED_DIR]], 0bv3);
  assert {:msg "Algo_IS_simple.cal(44.13): The actor might not preserve the invariant with contract 'Skip' at Algo_IS_simple.cal(26.3) (#116)"} (Mode#[this#] == Main) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 0) ==> (St# == rest);
  assert {:msg "Algo_IS_simple.cal(45.13): The actor might not preserve the invariant with contract 'Skip' at Algo_IS_simple.cal(26.3) (#117)"} (Mode#[this#] == Main) && (St# == rest) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 0) ==> ((R#[QFS_AC] - I#[QFS_AC]) == 0) && ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assert {:msg "Algo_IS_simple.cal(46.13): The actor might not preserve the invariant with contract 'Skip' at Algo_IS_simple.cal(26.3) (#118)"} (Mode#[this#] == Main) && (St# == read) ==> ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) && ((R#[QFS_AC] - I#[QFS_AC]) == (AT#Bv2Int8(count) - 1)) && ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assert {:msg "Algo_IS_simple.cal(47.13): The actor might not preserve the invariant with contract 'Skip' at Algo_IS_simple.cal(26.3) (#119)"} (Mode#[this#] == Main) && (St# == write) ==> ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) && ((R#[QFS_AC] - I#[QFS_AC]) == 63) && ((C#[PQF_AC] - I#[PQF_AC]) == (AT#Bv2Int8(count) - 1));
  assert {:msg "Algo_IS_simple.cal(48.13): The actor might not preserve the invariant with contract 'Skip' at Algo_IS_simple.cal(26.3) (#120)"} (Mode#[this#] == Main) && (St# == rest) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) ==> ((R#[QFS_AC] - I#[QFS_AC]) == 63) && ((C#[PQF_AC] - I#[PQF_AC]) == 63);
  assert {:msg "The actor might not preserve the invariant with contract 'Skip' at Algo_IS_simple.cal(26.3) (#121)"} (Mode#[this#] == Skip) ==> ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) <= 1) && ((C#[QFS_AC] - I#[QFS_AC]) == 0);
  assert {:msg "The actor might not preserve the invariant with contract 'Skip' at Algo_IS_simple.cal(26.3) (#122)"} (Mode#[this#] == Main) ==> ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) <= 1) && ((C#[QFS_AC] - I#[QFS_AC]) <= 63);
}
procedure Algo_IS_simple#contract#Main#input#9()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var AC_PRED_DIR: Chan (bv3);
  var QFS_AC: Chan (bv13);
  var PQF_AC: Chan (bv13);
  var Skip: int;
  var Main: int;
  var St#: int;
  var write: int;
  var read: int;
  var rest: int;
  var Scanmode: Map (bv9) (bv7);
  var count: bv8;
  var addr: bv9;
  var add_buf: bv3;
  var buf: Map (bv7) (bv13);
  var half_: bool;
  assume QFS_AC != PQF_AC;
  assume Skip == 0;
  assume Main == 1;
  assume (Mode#[this#] == Skip) || (Mode#[this#] == Main);
  assume write == 2;
  assume read == 1;
  assume rest == 0;
  assume Scanmode == Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Empty(0bv9, 0bv7), 0bv9, 0bv7), 1bv9, 1bv7), 2bv9, 5bv7), 3bv9, 6bv7), 4bv9, 14bv7), 5bv9, 15bv7), 6bv9, 27bv7), 7bv9, 28bv7), 8bv9, 2bv7), 9bv9, 4bv7), 10bv9, 7bv7), 11bv9, 13bv7), 12bv9, 16bv7), 13bv9, 26bv7), 14bv9, 29bv7), 15bv9, 42bv7), 16bv9, 3bv7), 17bv9, 8bv7), 18bv9, 12bv7), 19bv9, 17bv7), 20bv9, 25bv7), 21bv9, 30bv7), 22bv9, 41bv7), 23bv9, 43bv7), 24bv9, 9bv7), 25bv9, 11bv7), 26bv9, 18bv7), 27bv9, 24bv7), 28bv9, 31bv7), 29bv9, 40bv7), 30bv9, 44bv7), 31bv9, 53bv7), 32bv9, 10bv7), 33bv9, 19bv7), 34bv9, 23bv7), 35bv9, 32bv7), 36bv9, 39bv7), 37bv9, 45bv7), 38bv9, 52bv7), 39bv9, 54bv7), 40bv9, 20bv7), 41bv9, 22bv7), 42bv9, 33bv7), 43bv9, 38bv7), 44bv9, 46bv7), 45bv9, 51bv7), 46bv9, 55bv7), 47bv9, 60bv7), 48bv9, 21bv7), 49bv9, 34bv7), 50bv9, 37bv7), 51bv9, 47bv7), 52bv9, 50bv7), 53bv9, 56bv7), 54bv9, 59bv7), 55bv9, 61bv7), 56bv9, 35bv7), 57bv9, 36bv7), 58bv9, 48bv7), 59bv9, 49bv7), 60bv9, 57bv7), 61bv9, 58bv7), 62bv9, 62bv7), 63bv9, 63bv7), 64bv9, 0bv7), 65bv9, 4bv7), 66bv9, 6bv7), 67bv9, 20bv7), 68bv9, 22bv7), 69bv9, 36bv7), 70bv9, 38bv7), 71bv9, 52bv7), 72bv9, 1bv7), 73bv9, 5bv7), 74bv9, 7bv7), 75bv9, 21bv7), 76bv9, 23bv7), 77bv9, 37bv7), 78bv9, 39bv7), 79bv9, 53bv7), 80bv9, 2bv7), 81bv9, 8bv7), 82bv9, 19bv7), 83bv9, 24bv7), 84bv9, 34bv7), 85bv9, 40bv7), 86bv9, 50bv7), 87bv9, 54bv7), 88bv9, 3bv7), 89bv9, 9bv7), 90bv9, 18bv7), 91bv9, 25bv7), 92bv9, 35bv7), 93bv9, 41bv7), 94bv9, 51bv7), 95bv9, 55bv7), 96bv9, 10bv7), 97bv9, 17bv7), 98bv9, 26bv7), 99bv9, 30bv7), 100bv9, 42bv7), 101bv9, 46bv7), 102bv9, 56bv7), 103bv9, 60bv7), 104bv9, 11bv7), 105bv9, 16bv7), 106bv9, 27bv7), 107bv9, 31bv7), 108bv9, 43bv7), 109bv9, 47bv7), 110bv9, 57bv7), 111bv9, 61bv7), 112bv9, 12bv7), 113bv9, 15bv7), 114bv9, 28bv7), 115bv9, 32bv7), 116bv9, 44bv7), 117bv9, 48bv7), 118bv9, 58bv7), 119bv9, 62bv7), 120bv9, 13bv7), 121bv9, 14bv7), 122bv9, 29bv7), 123bv9, 33bv7), 124bv9, 45bv7), 125bv9, 49bv7), 126bv9, 59bv7), 127bv9, 63bv7), 128bv9, 0bv7), 129bv9, 1bv7), 130bv9, 2bv7), 131bv9, 3bv7), 132bv9, 10bv7), 133bv9, 11bv7), 134bv9, 12bv7), 135bv9, 13bv7), 136bv9, 4bv7), 137bv9, 5bv7), 138bv9, 8bv7), 139bv9, 9bv7), 140bv9, 17bv7), 141bv9, 16bv7), 142bv9, 15bv7), 143bv9, 14bv7), 144bv9, 6bv7), 145bv9, 7bv7), 146bv9, 19bv7), 147bv9, 18bv7), 148bv9, 26bv7), 149bv9, 27bv7), 150bv9, 28bv7), 151bv9, 29bv7), 152bv9, 20bv7), 153bv9, 21bv7), 154bv9, 24bv7), 155bv9, 25bv7), 156bv9, 30bv7), 157bv9, 31bv7), 158bv9, 32bv7), 159bv9, 33bv7), 160bv9, 22bv7), 161bv9, 23bv7), 162bv9, 34bv7), 163bv9, 35bv7), 164bv9, 42bv7), 165bv9, 43bv7), 166bv9, 44bv7), 167bv9, 45bv7), 168bv9, 36bv7), 169bv9, 37bv7), 170bv9, 40bv7), 171bv9, 41bv7), 172bv9, 46bv7), 173bv9, 47bv7), 174bv9, 48bv7), 175bv9, 49bv7), 176bv9, 38bv7), 177bv9, 39bv7), 178bv9, 50bv7), 179bv9, 51bv7), 180bv9, 56bv7), 181bv9, 57bv7), 182bv9, 58bv7), 183bv9, 59bv7), 184bv9, 52bv7), 185bv9, 53bv7), 186bv9, 54bv7), 187bv9, 55bv7), 188bv9, 60bv7), 189bv9, 61bv7), 190bv9, 62bv7), 191bv9, 63bv7);
  assume (0 <= I#[AC_PRED_DIR]) && (I#[AC_PRED_DIR] <= R#[AC_PRED_DIR]) && (R#[AC_PRED_DIR] <= C#[AC_PRED_DIR]);
  assume (0 <= I#[QFS_AC]) && (I#[QFS_AC] <= R#[QFS_AC]) && (R#[QFS_AC] <= C#[QFS_AC]);
  assume (0 <= I#[PQF_AC]) && (I#[PQF_AC] <= R#[PQF_AC]) && (R#[PQF_AC] <= C#[PQF_AC]);
  assume Mode#[this#] == Main;
  assume R#[PQF_AC] == I#[PQF_AC];
  assume ((St# == rest) || (St# == read)) || (St# == write);
  assume AT#BvSle8(1bv8, count) && AT#BvSle8(count, 64bv8);
  assume (St# == rest) ==> (count == 1bv8);
  assume (Mode#[this#] == Skip) && ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) > 0) ==> AT#BvSlt3(M#[AC_PRED_DIR][I#[AC_PRED_DIR]], 0bv3);
  assume (Mode#[this#] == Skip) ==> (St# == rest);
  assume (Mode#[this#] == Skip) ==> ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assume (Mode#[this#] == Main) && ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) > 0) ==> AT#BvSge3(M#[AC_PRED_DIR][I#[AC_PRED_DIR]], 0bv3);
  assume (Mode#[this#] == Main) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 0) ==> (St# == rest);
  assume (Mode#[this#] == Main) && (St# == rest) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 0) ==> ((R#[QFS_AC] - I#[QFS_AC]) == 0) && ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assume (Mode#[this#] == Main) && (St# == read) ==> ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) && ((R#[QFS_AC] - I#[QFS_AC]) == (AT#Bv2Int8(count) - 1)) && ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assume (Mode#[this#] == Main) && (St# == write) ==> ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) && ((R#[QFS_AC] - I#[QFS_AC]) == 63) && ((C#[PQF_AC] - I#[PQF_AC]) == (AT#Bv2Int8(count) - 1));
  assume (Mode#[this#] == Main) && (St# == rest) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) ==> ((R#[QFS_AC] - I#[QFS_AC]) == 63) && ((C#[PQF_AC] - I#[PQF_AC]) == 63);
  assume (Mode#[this#] == Skip) ==> ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) <= 1) && ((C#[QFS_AC] - I#[QFS_AC]) == 0);
  assume (Mode#[this#] == Main) ==> ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) <= 1) && ((C#[QFS_AC] - I#[QFS_AC]) <= 63);
  assume (C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) < 1;
  C#[AC_PRED_DIR] := C#[AC_PRED_DIR] + 1;
  assume AT#BvSge3(M#[AC_PRED_DIR][I#[AC_PRED_DIR]], 0bv3);
  assert {:msg "Algo_IS_simple.cal(123.3): Invariant might be falsified by actor input (#123)"} ((St# == rest) || (St# == read)) || (St# == write);
  assert {:msg "Algo_IS_simple.cal(36.13): Invariant might be falsified by actor input (#124)"} AT#BvSle8(1bv8, count) && AT#BvSle8(count, 64bv8);
  assert {:msg "Algo_IS_simple.cal(37.13): Invariant might be falsified by actor input (#125)"} (St# == rest) ==> (count == 1bv8);
  assert {:msg "Algo_IS_simple.cal(39.13): Invariant might be falsified by actor input (#126)"} (Mode#[this#] == Skip) && ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) > 0) ==> AT#BvSlt3(M#[AC_PRED_DIR][I#[AC_PRED_DIR]], 0bv3);
  assert {:msg "Algo_IS_simple.cal(40.13): Invariant might be falsified by actor input (#127)"} (Mode#[this#] == Skip) ==> (St# == rest);
  assert {:msg "Algo_IS_simple.cal(41.13): Invariant might be falsified by actor input (#128)"} (Mode#[this#] == Skip) ==> ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assert {:msg "Algo_IS_simple.cal(43.13): Invariant might be falsified by actor input (#129)"} (Mode#[this#] == Main) && ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) > 0) ==> AT#BvSge3(M#[AC_PRED_DIR][I#[AC_PRED_DIR]], 0bv3);
  assert {:msg "Algo_IS_simple.cal(44.13): Invariant might be falsified by actor input (#130)"} (Mode#[this#] == Main) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 0) ==> (St# == rest);
  assert {:msg "Algo_IS_simple.cal(45.13): Invariant might be falsified by actor input (#131)"} (Mode#[this#] == Main) && (St# == rest) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 0) ==> ((R#[QFS_AC] - I#[QFS_AC]) == 0) && ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assert {:msg "Algo_IS_simple.cal(46.13): Invariant might be falsified by actor input (#132)"} (Mode#[this#] == Main) && (St# == read) ==> ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) && ((R#[QFS_AC] - I#[QFS_AC]) == (AT#Bv2Int8(count) - 1)) && ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assert {:msg "Algo_IS_simple.cal(47.13): Invariant might be falsified by actor input (#133)"} (Mode#[this#] == Main) && (St# == write) ==> ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) && ((R#[QFS_AC] - I#[QFS_AC]) == 63) && ((C#[PQF_AC] - I#[PQF_AC]) == (AT#Bv2Int8(count) - 1));
  assert {:msg "Algo_IS_simple.cal(48.13): Invariant might be falsified by actor input (#134)"} (Mode#[this#] == Main) && (St# == rest) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) ==> ((R#[QFS_AC] - I#[QFS_AC]) == 63) && ((C#[PQF_AC] - I#[PQF_AC]) == 63);
  assert {:msg "Invariant might be falsified by actor input (#135)"} (Mode#[this#] == Skip) ==> ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) <= 1) && ((C#[QFS_AC] - I#[QFS_AC]) == 0);
  assert {:msg "Invariant might be falsified by actor input (#136)"} (Mode#[this#] == Main) ==> ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) <= 1) && ((C#[QFS_AC] - I#[QFS_AC]) <= 63);
}
procedure Algo_IS_simple#contract#Main#input#10()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var AC_PRED_DIR: Chan (bv3);
  var QFS_AC: Chan (bv13);
  var PQF_AC: Chan (bv13);
  var Skip: int;
  var Main: int;
  var St#: int;
  var write: int;
  var read: int;
  var rest: int;
  var Scanmode: Map (bv9) (bv7);
  var count: bv8;
  var addr: bv9;
  var add_buf: bv3;
  var buf: Map (bv7) (bv13);
  var half_: bool;
  assume QFS_AC != PQF_AC;
  assume Skip == 0;
  assume Main == 1;
  assume (Mode#[this#] == Skip) || (Mode#[this#] == Main);
  assume write == 2;
  assume read == 1;
  assume rest == 0;
  assume Scanmode == Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Empty(0bv9, 0bv7), 0bv9, 0bv7), 1bv9, 1bv7), 2bv9, 5bv7), 3bv9, 6bv7), 4bv9, 14bv7), 5bv9, 15bv7), 6bv9, 27bv7), 7bv9, 28bv7), 8bv9, 2bv7), 9bv9, 4bv7), 10bv9, 7bv7), 11bv9, 13bv7), 12bv9, 16bv7), 13bv9, 26bv7), 14bv9, 29bv7), 15bv9, 42bv7), 16bv9, 3bv7), 17bv9, 8bv7), 18bv9, 12bv7), 19bv9, 17bv7), 20bv9, 25bv7), 21bv9, 30bv7), 22bv9, 41bv7), 23bv9, 43bv7), 24bv9, 9bv7), 25bv9, 11bv7), 26bv9, 18bv7), 27bv9, 24bv7), 28bv9, 31bv7), 29bv9, 40bv7), 30bv9, 44bv7), 31bv9, 53bv7), 32bv9, 10bv7), 33bv9, 19bv7), 34bv9, 23bv7), 35bv9, 32bv7), 36bv9, 39bv7), 37bv9, 45bv7), 38bv9, 52bv7), 39bv9, 54bv7), 40bv9, 20bv7), 41bv9, 22bv7), 42bv9, 33bv7), 43bv9, 38bv7), 44bv9, 46bv7), 45bv9, 51bv7), 46bv9, 55bv7), 47bv9, 60bv7), 48bv9, 21bv7), 49bv9, 34bv7), 50bv9, 37bv7), 51bv9, 47bv7), 52bv9, 50bv7), 53bv9, 56bv7), 54bv9, 59bv7), 55bv9, 61bv7), 56bv9, 35bv7), 57bv9, 36bv7), 58bv9, 48bv7), 59bv9, 49bv7), 60bv9, 57bv7), 61bv9, 58bv7), 62bv9, 62bv7), 63bv9, 63bv7), 64bv9, 0bv7), 65bv9, 4bv7), 66bv9, 6bv7), 67bv9, 20bv7), 68bv9, 22bv7), 69bv9, 36bv7), 70bv9, 38bv7), 71bv9, 52bv7), 72bv9, 1bv7), 73bv9, 5bv7), 74bv9, 7bv7), 75bv9, 21bv7), 76bv9, 23bv7), 77bv9, 37bv7), 78bv9, 39bv7), 79bv9, 53bv7), 80bv9, 2bv7), 81bv9, 8bv7), 82bv9, 19bv7), 83bv9, 24bv7), 84bv9, 34bv7), 85bv9, 40bv7), 86bv9, 50bv7), 87bv9, 54bv7), 88bv9, 3bv7), 89bv9, 9bv7), 90bv9, 18bv7), 91bv9, 25bv7), 92bv9, 35bv7), 93bv9, 41bv7), 94bv9, 51bv7), 95bv9, 55bv7), 96bv9, 10bv7), 97bv9, 17bv7), 98bv9, 26bv7), 99bv9, 30bv7), 100bv9, 42bv7), 101bv9, 46bv7), 102bv9, 56bv7), 103bv9, 60bv7), 104bv9, 11bv7), 105bv9, 16bv7), 106bv9, 27bv7), 107bv9, 31bv7), 108bv9, 43bv7), 109bv9, 47bv7), 110bv9, 57bv7), 111bv9, 61bv7), 112bv9, 12bv7), 113bv9, 15bv7), 114bv9, 28bv7), 115bv9, 32bv7), 116bv9, 44bv7), 117bv9, 48bv7), 118bv9, 58bv7), 119bv9, 62bv7), 120bv9, 13bv7), 121bv9, 14bv7), 122bv9, 29bv7), 123bv9, 33bv7), 124bv9, 45bv7), 125bv9, 49bv7), 126bv9, 59bv7), 127bv9, 63bv7), 128bv9, 0bv7), 129bv9, 1bv7), 130bv9, 2bv7), 131bv9, 3bv7), 132bv9, 10bv7), 133bv9, 11bv7), 134bv9, 12bv7), 135bv9, 13bv7), 136bv9, 4bv7), 137bv9, 5bv7), 138bv9, 8bv7), 139bv9, 9bv7), 140bv9, 17bv7), 141bv9, 16bv7), 142bv9, 15bv7), 143bv9, 14bv7), 144bv9, 6bv7), 145bv9, 7bv7), 146bv9, 19bv7), 147bv9, 18bv7), 148bv9, 26bv7), 149bv9, 27bv7), 150bv9, 28bv7), 151bv9, 29bv7), 152bv9, 20bv7), 153bv9, 21bv7), 154bv9, 24bv7), 155bv9, 25bv7), 156bv9, 30bv7), 157bv9, 31bv7), 158bv9, 32bv7), 159bv9, 33bv7), 160bv9, 22bv7), 161bv9, 23bv7), 162bv9, 34bv7), 163bv9, 35bv7), 164bv9, 42bv7), 165bv9, 43bv7), 166bv9, 44bv7), 167bv9, 45bv7), 168bv9, 36bv7), 169bv9, 37bv7), 170bv9, 40bv7), 171bv9, 41bv7), 172bv9, 46bv7), 173bv9, 47bv7), 174bv9, 48bv7), 175bv9, 49bv7), 176bv9, 38bv7), 177bv9, 39bv7), 178bv9, 50bv7), 179bv9, 51bv7), 180bv9, 56bv7), 181bv9, 57bv7), 182bv9, 58bv7), 183bv9, 59bv7), 184bv9, 52bv7), 185bv9, 53bv7), 186bv9, 54bv7), 187bv9, 55bv7), 188bv9, 60bv7), 189bv9, 61bv7), 190bv9, 62bv7), 191bv9, 63bv7);
  assume (0 <= I#[AC_PRED_DIR]) && (I#[AC_PRED_DIR] <= R#[AC_PRED_DIR]) && (R#[AC_PRED_DIR] <= C#[AC_PRED_DIR]);
  assume (0 <= I#[QFS_AC]) && (I#[QFS_AC] <= R#[QFS_AC]) && (R#[QFS_AC] <= C#[QFS_AC]);
  assume (0 <= I#[PQF_AC]) && (I#[PQF_AC] <= R#[PQF_AC]) && (R#[PQF_AC] <= C#[PQF_AC]);
  assume Mode#[this#] == Main;
  assume R#[PQF_AC] == I#[PQF_AC];
  assume ((St# == rest) || (St# == read)) || (St# == write);
  assume AT#BvSle8(1bv8, count) && AT#BvSle8(count, 64bv8);
  assume (St# == rest) ==> (count == 1bv8);
  assume (Mode#[this#] == Skip) && ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) > 0) ==> AT#BvSlt3(M#[AC_PRED_DIR][I#[AC_PRED_DIR]], 0bv3);
  assume (Mode#[this#] == Skip) ==> (St# == rest);
  assume (Mode#[this#] == Skip) ==> ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assume (Mode#[this#] == Main) && ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) > 0) ==> AT#BvSge3(M#[AC_PRED_DIR][I#[AC_PRED_DIR]], 0bv3);
  assume (Mode#[this#] == Main) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 0) ==> (St# == rest);
  assume (Mode#[this#] == Main) && (St# == rest) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 0) ==> ((R#[QFS_AC] - I#[QFS_AC]) == 0) && ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assume (Mode#[this#] == Main) && (St# == read) ==> ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) && ((R#[QFS_AC] - I#[QFS_AC]) == (AT#Bv2Int8(count) - 1)) && ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assume (Mode#[this#] == Main) && (St# == write) ==> ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) && ((R#[QFS_AC] - I#[QFS_AC]) == 63) && ((C#[PQF_AC] - I#[PQF_AC]) == (AT#Bv2Int8(count) - 1));
  assume (Mode#[this#] == Main) && (St# == rest) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) ==> ((R#[QFS_AC] - I#[QFS_AC]) == 63) && ((C#[PQF_AC] - I#[PQF_AC]) == 63);
  assume (Mode#[this#] == Skip) ==> ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) <= 1) && ((C#[QFS_AC] - I#[QFS_AC]) == 0);
  assume (Mode#[this#] == Main) ==> ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) <= 1) && ((C#[QFS_AC] - I#[QFS_AC]) <= 63);
  assume (C#[QFS_AC] - I#[QFS_AC]) < 63;
  C#[QFS_AC] := C#[QFS_AC] + 1;
  assume AT#BvSge3(M#[AC_PRED_DIR][I#[AC_PRED_DIR]], 0bv3);
  assert {:msg "Algo_IS_simple.cal(123.3): Invariant might be falsified by actor input (#137)"} ((St# == rest) || (St# == read)) || (St# == write);
  assert {:msg "Algo_IS_simple.cal(36.13): Invariant might be falsified by actor input (#138)"} AT#BvSle8(1bv8, count) && AT#BvSle8(count, 64bv8);
  assert {:msg "Algo_IS_simple.cal(37.13): Invariant might be falsified by actor input (#139)"} (St# == rest) ==> (count == 1bv8);
  assert {:msg "Algo_IS_simple.cal(39.13): Invariant might be falsified by actor input (#140)"} (Mode#[this#] == Skip) && ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) > 0) ==> AT#BvSlt3(M#[AC_PRED_DIR][I#[AC_PRED_DIR]], 0bv3);
  assert {:msg "Algo_IS_simple.cal(40.13): Invariant might be falsified by actor input (#141)"} (Mode#[this#] == Skip) ==> (St# == rest);
  assert {:msg "Algo_IS_simple.cal(41.13): Invariant might be falsified by actor input (#142)"} (Mode#[this#] == Skip) ==> ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assert {:msg "Algo_IS_simple.cal(43.13): Invariant might be falsified by actor input (#143)"} (Mode#[this#] == Main) && ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) > 0) ==> AT#BvSge3(M#[AC_PRED_DIR][I#[AC_PRED_DIR]], 0bv3);
  assert {:msg "Algo_IS_simple.cal(44.13): Invariant might be falsified by actor input (#144)"} (Mode#[this#] == Main) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 0) ==> (St# == rest);
  assert {:msg "Algo_IS_simple.cal(45.13): Invariant might be falsified by actor input (#145)"} (Mode#[this#] == Main) && (St# == rest) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 0) ==> ((R#[QFS_AC] - I#[QFS_AC]) == 0) && ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assert {:msg "Algo_IS_simple.cal(46.13): Invariant might be falsified by actor input (#146)"} (Mode#[this#] == Main) && (St# == read) ==> ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) && ((R#[QFS_AC] - I#[QFS_AC]) == (AT#Bv2Int8(count) - 1)) && ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assert {:msg "Algo_IS_simple.cal(47.13): Invariant might be falsified by actor input (#147)"} (Mode#[this#] == Main) && (St# == write) ==> ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) && ((R#[QFS_AC] - I#[QFS_AC]) == 63) && ((C#[PQF_AC] - I#[PQF_AC]) == (AT#Bv2Int8(count) - 1));
  assert {:msg "Algo_IS_simple.cal(48.13): Invariant might be falsified by actor input (#148)"} (Mode#[this#] == Main) && (St# == rest) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) ==> ((R#[QFS_AC] - I#[QFS_AC]) == 63) && ((C#[PQF_AC] - I#[PQF_AC]) == 63);
  assert {:msg "Invariant might be falsified by actor input (#149)"} (Mode#[this#] == Skip) ==> ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) <= 1) && ((C#[QFS_AC] - I#[QFS_AC]) == 0);
  assert {:msg "Invariant might be falsified by actor input (#150)"} (Mode#[this#] == Main) ==> ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) <= 1) && ((C#[QFS_AC] - I#[QFS_AC]) <= 63);
}
procedure Algo_IS_simple#contract#Main#exit#11()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var AC_PRED_DIR: Chan (bv3);
  var QFS_AC: Chan (bv13);
  var PQF_AC: Chan (bv13);
  var Skip: int;
  var Main: int;
  var St#: int;
  var write: int;
  var read: int;
  var rest: int;
  var Scanmode: Map (bv9) (bv7);
  var count: bv8;
  var addr: bv9;
  var add_buf: bv3;
  var buf: Map (bv7) (bv13);
  var half_: bool;
  assume QFS_AC != PQF_AC;
  assume Skip == 0;
  assume Main == 1;
  assume (Mode#[this#] == Skip) || (Mode#[this#] == Main);
  assume write == 2;
  assume read == 1;
  assume rest == 0;
  assume Scanmode == Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Empty(0bv9, 0bv7), 0bv9, 0bv7), 1bv9, 1bv7), 2bv9, 5bv7), 3bv9, 6bv7), 4bv9, 14bv7), 5bv9, 15bv7), 6bv9, 27bv7), 7bv9, 28bv7), 8bv9, 2bv7), 9bv9, 4bv7), 10bv9, 7bv7), 11bv9, 13bv7), 12bv9, 16bv7), 13bv9, 26bv7), 14bv9, 29bv7), 15bv9, 42bv7), 16bv9, 3bv7), 17bv9, 8bv7), 18bv9, 12bv7), 19bv9, 17bv7), 20bv9, 25bv7), 21bv9, 30bv7), 22bv9, 41bv7), 23bv9, 43bv7), 24bv9, 9bv7), 25bv9, 11bv7), 26bv9, 18bv7), 27bv9, 24bv7), 28bv9, 31bv7), 29bv9, 40bv7), 30bv9, 44bv7), 31bv9, 53bv7), 32bv9, 10bv7), 33bv9, 19bv7), 34bv9, 23bv7), 35bv9, 32bv7), 36bv9, 39bv7), 37bv9, 45bv7), 38bv9, 52bv7), 39bv9, 54bv7), 40bv9, 20bv7), 41bv9, 22bv7), 42bv9, 33bv7), 43bv9, 38bv7), 44bv9, 46bv7), 45bv9, 51bv7), 46bv9, 55bv7), 47bv9, 60bv7), 48bv9, 21bv7), 49bv9, 34bv7), 50bv9, 37bv7), 51bv9, 47bv7), 52bv9, 50bv7), 53bv9, 56bv7), 54bv9, 59bv7), 55bv9, 61bv7), 56bv9, 35bv7), 57bv9, 36bv7), 58bv9, 48bv7), 59bv9, 49bv7), 60bv9, 57bv7), 61bv9, 58bv7), 62bv9, 62bv7), 63bv9, 63bv7), 64bv9, 0bv7), 65bv9, 4bv7), 66bv9, 6bv7), 67bv9, 20bv7), 68bv9, 22bv7), 69bv9, 36bv7), 70bv9, 38bv7), 71bv9, 52bv7), 72bv9, 1bv7), 73bv9, 5bv7), 74bv9, 7bv7), 75bv9, 21bv7), 76bv9, 23bv7), 77bv9, 37bv7), 78bv9, 39bv7), 79bv9, 53bv7), 80bv9, 2bv7), 81bv9, 8bv7), 82bv9, 19bv7), 83bv9, 24bv7), 84bv9, 34bv7), 85bv9, 40bv7), 86bv9, 50bv7), 87bv9, 54bv7), 88bv9, 3bv7), 89bv9, 9bv7), 90bv9, 18bv7), 91bv9, 25bv7), 92bv9, 35bv7), 93bv9, 41bv7), 94bv9, 51bv7), 95bv9, 55bv7), 96bv9, 10bv7), 97bv9, 17bv7), 98bv9, 26bv7), 99bv9, 30bv7), 100bv9, 42bv7), 101bv9, 46bv7), 102bv9, 56bv7), 103bv9, 60bv7), 104bv9, 11bv7), 105bv9, 16bv7), 106bv9, 27bv7), 107bv9, 31bv7), 108bv9, 43bv7), 109bv9, 47bv7), 110bv9, 57bv7), 111bv9, 61bv7), 112bv9, 12bv7), 113bv9, 15bv7), 114bv9, 28bv7), 115bv9, 32bv7), 116bv9, 44bv7), 117bv9, 48bv7), 118bv9, 58bv7), 119bv9, 62bv7), 120bv9, 13bv7), 121bv9, 14bv7), 122bv9, 29bv7), 123bv9, 33bv7), 124bv9, 45bv7), 125bv9, 49bv7), 126bv9, 59bv7), 127bv9, 63bv7), 128bv9, 0bv7), 129bv9, 1bv7), 130bv9, 2bv7), 131bv9, 3bv7), 132bv9, 10bv7), 133bv9, 11bv7), 134bv9, 12bv7), 135bv9, 13bv7), 136bv9, 4bv7), 137bv9, 5bv7), 138bv9, 8bv7), 139bv9, 9bv7), 140bv9, 17bv7), 141bv9, 16bv7), 142bv9, 15bv7), 143bv9, 14bv7), 144bv9, 6bv7), 145bv9, 7bv7), 146bv9, 19bv7), 147bv9, 18bv7), 148bv9, 26bv7), 149bv9, 27bv7), 150bv9, 28bv7), 151bv9, 29bv7), 152bv9, 20bv7), 153bv9, 21bv7), 154bv9, 24bv7), 155bv9, 25bv7), 156bv9, 30bv7), 157bv9, 31bv7), 158bv9, 32bv7), 159bv9, 33bv7), 160bv9, 22bv7), 161bv9, 23bv7), 162bv9, 34bv7), 163bv9, 35bv7), 164bv9, 42bv7), 165bv9, 43bv7), 166bv9, 44bv7), 167bv9, 45bv7), 168bv9, 36bv7), 169bv9, 37bv7), 170bv9, 40bv7), 171bv9, 41bv7), 172bv9, 46bv7), 173bv9, 47bv7), 174bv9, 48bv7), 175bv9, 49bv7), 176bv9, 38bv7), 177bv9, 39bv7), 178bv9, 50bv7), 179bv9, 51bv7), 180bv9, 56bv7), 181bv9, 57bv7), 182bv9, 58bv7), 183bv9, 59bv7), 184bv9, 52bv7), 185bv9, 53bv7), 186bv9, 54bv7), 187bv9, 55bv7), 188bv9, 60bv7), 189bv9, 61bv7), 190bv9, 62bv7), 191bv9, 63bv7);
  assume (0 <= I#[AC_PRED_DIR]) && (I#[AC_PRED_DIR] <= R#[AC_PRED_DIR]) && (R#[AC_PRED_DIR] <= C#[AC_PRED_DIR]);
  assume (0 <= I#[QFS_AC]) && (I#[QFS_AC] <= R#[QFS_AC]) && (R#[QFS_AC] <= C#[QFS_AC]);
  assume (0 <= I#[PQF_AC]) && (I#[PQF_AC] <= R#[PQF_AC]) && (R#[PQF_AC] <= C#[PQF_AC]);
  assume Mode#[this#] == Main;
  assume R#[PQF_AC] == I#[PQF_AC];
  assume ((St# == rest) || (St# == read)) || (St# == write);
  assume AT#BvSle8(1bv8, count) && AT#BvSle8(count, 64bv8);
  assume (St# == rest) ==> (count == 1bv8);
  assume (Mode#[this#] == Skip) && ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) > 0) ==> AT#BvSlt3(M#[AC_PRED_DIR][I#[AC_PRED_DIR]], 0bv3);
  assume (Mode#[this#] == Skip) ==> (St# == rest);
  assume (Mode#[this#] == Skip) ==> ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assume (Mode#[this#] == Main) && ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) > 0) ==> AT#BvSge3(M#[AC_PRED_DIR][I#[AC_PRED_DIR]], 0bv3);
  assume (Mode#[this#] == Main) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 0) ==> (St# == rest);
  assume (Mode#[this#] == Main) && (St# == rest) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 0) ==> ((R#[QFS_AC] - I#[QFS_AC]) == 0) && ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assume (Mode#[this#] == Main) && (St# == read) ==> ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) && ((R#[QFS_AC] - I#[QFS_AC]) == (AT#Bv2Int8(count) - 1)) && ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assume (Mode#[this#] == Main) && (St# == write) ==> ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) && ((R#[QFS_AC] - I#[QFS_AC]) == 63) && ((C#[PQF_AC] - I#[PQF_AC]) == (AT#Bv2Int8(count) - 1));
  assume (Mode#[this#] == Main) && (St# == rest) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) ==> ((R#[QFS_AC] - I#[QFS_AC]) == 63) && ((C#[PQF_AC] - I#[PQF_AC]) == 63);
  assume (Mode#[this#] == Skip) ==> ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) <= 1) && ((C#[QFS_AC] - I#[QFS_AC]) == 0);
  assume (Mode#[this#] == Main) ==> ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) <= 1) && ((C#[QFS_AC] - I#[QFS_AC]) <= 63);
  assume (C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1;
  assume (C#[QFS_AC] - I#[QFS_AC]) == 63;
  assume !(true && (!((1 <= (C#[AC_PRED_DIR] - R#[AC_PRED_DIR])) && AT#BvSlt3(M#[AC_PRED_DIR][R#[AC_PRED_DIR]], 0bv3) && (St# == rest))) && (1 <= (C#[AC_PRED_DIR] - R#[AC_PRED_DIR])) && AT#BvSge3(M#[AC_PRED_DIR][R#[AC_PRED_DIR]], 0bv3) && (St# == rest));
  assume !(true && true && (count == 64bv8) && ((St# == read) || (St# == write)));
  assume !(true && (!(true && (count == 64bv8) && ((St# == read) || (St# == write)))) && (1 <= (C#[QFS_AC] - R#[QFS_AC])) && AT#BvSlt8(count, 64bv8) && (St# == read));
  assume !(true && (!(true && (count == 64bv8) && ((St# == read) || (St# == write)))) && true && AT#BvSlt8(count, 64bv8) && (St# == write));
  assume !(true && (1 <= (C#[AC_PRED_DIR] - R#[AC_PRED_DIR])) && AT#BvSlt3(M#[AC_PRED_DIR][R#[AC_PRED_DIR]], 0bv3) && (St# == rest));
  assert {:msg "Algo_IS_simple.cal(31.3): The correct number of tokens might not be produced on output 'PQF_AC' with contract 'Main' (#151)"} (C#[PQF_AC] - I#[PQF_AC]) == 63;
  R#[PQF_AC] := R#[PQF_AC] + 63;
  I# := R#;
  assert {:msg "Algo_IS_simple.cal(123.3): The actor might not preserve the invariant with contract 'Main' at Algo_IS_simple.cal(31.3) (#152)"} ((St# == rest) || (St# == read)) || (St# == write);
  assert {:msg "Algo_IS_simple.cal(36.13): The actor might not preserve the invariant with contract 'Main' at Algo_IS_simple.cal(31.3) (#153)"} AT#BvSle8(1bv8, count) && AT#BvSle8(count, 64bv8);
  assert {:msg "Algo_IS_simple.cal(37.13): The actor might not preserve the invariant with contract 'Main' at Algo_IS_simple.cal(31.3) (#154)"} (St# == rest) ==> (count == 1bv8);
  assert {:msg "Algo_IS_simple.cal(39.13): The actor might not preserve the invariant with contract 'Main' at Algo_IS_simple.cal(31.3) (#155)"} (Mode#[this#] == Skip) && ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) > 0) ==> AT#BvSlt3(M#[AC_PRED_DIR][I#[AC_PRED_DIR]], 0bv3);
  assert {:msg "Algo_IS_simple.cal(40.13): The actor might not preserve the invariant with contract 'Main' at Algo_IS_simple.cal(31.3) (#156)"} (Mode#[this#] == Skip) ==> (St# == rest);
  assert {:msg "Algo_IS_simple.cal(41.13): The actor might not preserve the invariant with contract 'Main' at Algo_IS_simple.cal(31.3) (#157)"} (Mode#[this#] == Skip) ==> ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assert {:msg "Algo_IS_simple.cal(43.13): The actor might not preserve the invariant with contract 'Main' at Algo_IS_simple.cal(31.3) (#158)"} (Mode#[this#] == Main) && ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) > 0) ==> AT#BvSge3(M#[AC_PRED_DIR][I#[AC_PRED_DIR]], 0bv3);
  assert {:msg "Algo_IS_simple.cal(44.13): The actor might not preserve the invariant with contract 'Main' at Algo_IS_simple.cal(31.3) (#159)"} (Mode#[this#] == Main) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 0) ==> (St# == rest);
  assert {:msg "Algo_IS_simple.cal(45.13): The actor might not preserve the invariant with contract 'Main' at Algo_IS_simple.cal(31.3) (#160)"} (Mode#[this#] == Main) && (St# == rest) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 0) ==> ((R#[QFS_AC] - I#[QFS_AC]) == 0) && ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assert {:msg "Algo_IS_simple.cal(46.13): The actor might not preserve the invariant with contract 'Main' at Algo_IS_simple.cal(31.3) (#161)"} (Mode#[this#] == Main) && (St# == read) ==> ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) && ((R#[QFS_AC] - I#[QFS_AC]) == (AT#Bv2Int8(count) - 1)) && ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assert {:msg "Algo_IS_simple.cal(47.13): The actor might not preserve the invariant with contract 'Main' at Algo_IS_simple.cal(31.3) (#162)"} (Mode#[this#] == Main) && (St# == write) ==> ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) && ((R#[QFS_AC] - I#[QFS_AC]) == 63) && ((C#[PQF_AC] - I#[PQF_AC]) == (AT#Bv2Int8(count) - 1));
  assert {:msg "Algo_IS_simple.cal(48.13): The actor might not preserve the invariant with contract 'Main' at Algo_IS_simple.cal(31.3) (#163)"} (Mode#[this#] == Main) && (St# == rest) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) ==> ((R#[QFS_AC] - I#[QFS_AC]) == 63) && ((C#[PQF_AC] - I#[PQF_AC]) == 63);
  assert {:msg "The actor might not preserve the invariant with contract 'Main' at Algo_IS_simple.cal(31.3) (#164)"} (Mode#[this#] == Skip) ==> ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) <= 1) && ((C#[QFS_AC] - I#[QFS_AC]) == 0);
  assert {:msg "The actor might not preserve the invariant with contract 'Main' at Algo_IS_simple.cal(31.3) (#165)"} (Mode#[this#] == Main) ==> ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) <= 1) && ((C#[QFS_AC] - I#[QFS_AC]) <= 63);
}
procedure Algo_IS_simple##GuardWD#12()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var AC_PRED_DIR: Chan (bv3);
  var QFS_AC: Chan (bv13);
  var PQF_AC: Chan (bv13);
  var Skip: int;
  var Main: int;
  var St#: int;
  var write: int;
  var read: int;
  var rest: int;
  var Scanmode: Map (bv9) (bv7);
  var count: bv8;
  var addr: bv9;
  var add_buf: bv3;
  var buf: Map (bv7) (bv13);
  var half_: bool;
  assume QFS_AC != PQF_AC;
  assume Skip == 0;
  assume Main == 1;
  assume (Mode#[this#] == Skip) || (Mode#[this#] == Main);
  assume write == 2;
  assume read == 1;
  assume rest == 0;
  assume Scanmode == Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Store(Map#Empty(0bv9, 0bv7), 0bv9, 0bv7), 1bv9, 1bv7), 2bv9, 5bv7), 3bv9, 6bv7), 4bv9, 14bv7), 5bv9, 15bv7), 6bv9, 27bv7), 7bv9, 28bv7), 8bv9, 2bv7), 9bv9, 4bv7), 10bv9, 7bv7), 11bv9, 13bv7), 12bv9, 16bv7), 13bv9, 26bv7), 14bv9, 29bv7), 15bv9, 42bv7), 16bv9, 3bv7), 17bv9, 8bv7), 18bv9, 12bv7), 19bv9, 17bv7), 20bv9, 25bv7), 21bv9, 30bv7), 22bv9, 41bv7), 23bv9, 43bv7), 24bv9, 9bv7), 25bv9, 11bv7), 26bv9, 18bv7), 27bv9, 24bv7), 28bv9, 31bv7), 29bv9, 40bv7), 30bv9, 44bv7), 31bv9, 53bv7), 32bv9, 10bv7), 33bv9, 19bv7), 34bv9, 23bv7), 35bv9, 32bv7), 36bv9, 39bv7), 37bv9, 45bv7), 38bv9, 52bv7), 39bv9, 54bv7), 40bv9, 20bv7), 41bv9, 22bv7), 42bv9, 33bv7), 43bv9, 38bv7), 44bv9, 46bv7), 45bv9, 51bv7), 46bv9, 55bv7), 47bv9, 60bv7), 48bv9, 21bv7), 49bv9, 34bv7), 50bv9, 37bv7), 51bv9, 47bv7), 52bv9, 50bv7), 53bv9, 56bv7), 54bv9, 59bv7), 55bv9, 61bv7), 56bv9, 35bv7), 57bv9, 36bv7), 58bv9, 48bv7), 59bv9, 49bv7), 60bv9, 57bv7), 61bv9, 58bv7), 62bv9, 62bv7), 63bv9, 63bv7), 64bv9, 0bv7), 65bv9, 4bv7), 66bv9, 6bv7), 67bv9, 20bv7), 68bv9, 22bv7), 69bv9, 36bv7), 70bv9, 38bv7), 71bv9, 52bv7), 72bv9, 1bv7), 73bv9, 5bv7), 74bv9, 7bv7), 75bv9, 21bv7), 76bv9, 23bv7), 77bv9, 37bv7), 78bv9, 39bv7), 79bv9, 53bv7), 80bv9, 2bv7), 81bv9, 8bv7), 82bv9, 19bv7), 83bv9, 24bv7), 84bv9, 34bv7), 85bv9, 40bv7), 86bv9, 50bv7), 87bv9, 54bv7), 88bv9, 3bv7), 89bv9, 9bv7), 90bv9, 18bv7), 91bv9, 25bv7), 92bv9, 35bv7), 93bv9, 41bv7), 94bv9, 51bv7), 95bv9, 55bv7), 96bv9, 10bv7), 97bv9, 17bv7), 98bv9, 26bv7), 99bv9, 30bv7), 100bv9, 42bv7), 101bv9, 46bv7), 102bv9, 56bv7), 103bv9, 60bv7), 104bv9, 11bv7), 105bv9, 16bv7), 106bv9, 27bv7), 107bv9, 31bv7), 108bv9, 43bv7), 109bv9, 47bv7), 110bv9, 57bv7), 111bv9, 61bv7), 112bv9, 12bv7), 113bv9, 15bv7), 114bv9, 28bv7), 115bv9, 32bv7), 116bv9, 44bv7), 117bv9, 48bv7), 118bv9, 58bv7), 119bv9, 62bv7), 120bv9, 13bv7), 121bv9, 14bv7), 122bv9, 29bv7), 123bv9, 33bv7), 124bv9, 45bv7), 125bv9, 49bv7), 126bv9, 59bv7), 127bv9, 63bv7), 128bv9, 0bv7), 129bv9, 1bv7), 130bv9, 2bv7), 131bv9, 3bv7), 132bv9, 10bv7), 133bv9, 11bv7), 134bv9, 12bv7), 135bv9, 13bv7), 136bv9, 4bv7), 137bv9, 5bv7), 138bv9, 8bv7), 139bv9, 9bv7), 140bv9, 17bv7), 141bv9, 16bv7), 142bv9, 15bv7), 143bv9, 14bv7), 144bv9, 6bv7), 145bv9, 7bv7), 146bv9, 19bv7), 147bv9, 18bv7), 148bv9, 26bv7), 149bv9, 27bv7), 150bv9, 28bv7), 151bv9, 29bv7), 152bv9, 20bv7), 153bv9, 21bv7), 154bv9, 24bv7), 155bv9, 25bv7), 156bv9, 30bv7), 157bv9, 31bv7), 158bv9, 32bv7), 159bv9, 33bv7), 160bv9, 22bv7), 161bv9, 23bv7), 162bv9, 34bv7), 163bv9, 35bv7), 164bv9, 42bv7), 165bv9, 43bv7), 166bv9, 44bv7), 167bv9, 45bv7), 168bv9, 36bv7), 169bv9, 37bv7), 170bv9, 40bv7), 171bv9, 41bv7), 172bv9, 46bv7), 173bv9, 47bv7), 174bv9, 48bv7), 175bv9, 49bv7), 176bv9, 38bv7), 177bv9, 39bv7), 178bv9, 50bv7), 179bv9, 51bv7), 180bv9, 56bv7), 181bv9, 57bv7), 182bv9, 58bv7), 183bv9, 59bv7), 184bv9, 52bv7), 185bv9, 53bv7), 186bv9, 54bv7), 187bv9, 55bv7), 188bv9, 60bv7), 189bv9, 61bv7), 190bv9, 62bv7), 191bv9, 63bv7);
  assume (0 <= I#[AC_PRED_DIR]) && (I#[AC_PRED_DIR] <= R#[AC_PRED_DIR]) && (R#[AC_PRED_DIR] <= C#[AC_PRED_DIR]);
  assume (0 <= I#[QFS_AC]) && (I#[QFS_AC] <= R#[QFS_AC]) && (R#[QFS_AC] <= C#[QFS_AC]);
  assume (0 <= I#[PQF_AC]) && (I#[PQF_AC] <= R#[PQF_AC]) && (R#[PQF_AC] <= C#[PQF_AC]);
  assume ((St# == rest) || (St# == read)) || (St# == write);
  assume AT#BvSle8(1bv8, count) && AT#BvSle8(count, 64bv8);
  assume (St# == rest) ==> (count == 1bv8);
  assume (Mode#[this#] == Skip) && ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) > 0) ==> AT#BvSlt3(M#[AC_PRED_DIR][I#[AC_PRED_DIR]], 0bv3);
  assume (Mode#[this#] == Skip) ==> (St# == rest);
  assume (Mode#[this#] == Skip) ==> ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assume (Mode#[this#] == Main) && ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) > 0) ==> AT#BvSge3(M#[AC_PRED_DIR][I#[AC_PRED_DIR]], 0bv3);
  assume (Mode#[this#] == Main) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 0) ==> (St# == rest);
  assume (Mode#[this#] == Main) && (St# == rest) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 0) ==> ((R#[QFS_AC] - I#[QFS_AC]) == 0) && ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assume (Mode#[this#] == Main) && (St# == read) ==> ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) && ((R#[QFS_AC] - I#[QFS_AC]) == (AT#Bv2Int8(count) - 1)) && ((C#[PQF_AC] - I#[PQF_AC]) == 0);
  assume (Mode#[this#] == Main) && (St# == write) ==> ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) && ((R#[QFS_AC] - I#[QFS_AC]) == 63) && ((C#[PQF_AC] - I#[PQF_AC]) == (AT#Bv2Int8(count) - 1));
  assume (Mode#[this#] == Main) && (St# == rest) && ((R#[AC_PRED_DIR] - I#[AC_PRED_DIR]) == 1) ==> ((R#[QFS_AC] - I#[QFS_AC]) == 63) && ((C#[PQF_AC] - I#[PQF_AC]) == 63);
  assume (Mode#[this#] == Skip) ==> ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) <= 1) && ((C#[QFS_AC] - I#[QFS_AC]) == 0);
  assume (Mode#[this#] == Main) ==> ((C#[AC_PRED_DIR] - I#[AC_PRED_DIR]) <= 1) && ((C#[QFS_AC] - I#[QFS_AC]) <= 63);
  assert {:msg "The actions 'Skip' and 'Main' of actor 'Algo_IS_simple' might not have mutually exclusive guards (#166)"} !(true && (1 <= (C#[AC_PRED_DIR] - R#[AC_PRED_DIR])) && AT#BvSlt3(M#[AC_PRED_DIR][I#[AC_PRED_DIR]], 0bv3) && true && (1 <= (C#[AC_PRED_DIR] - R#[AC_PRED_DIR])) && (63 <= (C#[QFS_AC] - R#[QFS_AC])) && AT#BvSge3(M#[AC_PRED_DIR][I#[AC_PRED_DIR]], 0bv3));
}

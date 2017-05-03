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
var I#sub: CType;

var H: HType;

const unique this#: Actor;

function AT#Min(x:int, y: int): int { if x <= y then x else y }

// ---------------------------------------------------------------
// -- Bit vector operations --------------------------------------
// ---------------------------------------------------------------
// Size: 12
function {:bvbuiltin "bvand"} AT#BvAnd12(a: bv12, b: bv12): bv12;
function {:bvbuiltin "bvor"} AT#BvOr12(a: bv12, b: bv12): bv12;
function {:bvbuiltin "bvnot"} AT#BvNot12(a: bv12): bv12;
function {:bvbuiltin "bvadd"} AT#BvAdd12(a: bv12, b: bv12): bv12;
function {:bvbuiltin "bvsub"} AT#BvSub12(a: bv12, b: bv12): bv12;
function {:bvbuiltin "bvmul"} AT#BvMul12(a: bv12, b: bv12): bv12;
function {:bvbuiltin "bvshl"} AT#BvShl12(bv12,bv12): bv12;
function {:bvbuiltin "bvlshr"} AT#BvLshr12(bv12,bv12): bv12;
function {:bvbuiltin "bvashr"} AT#BvAshr12(bv12,bv12): bv12;
function {:bvbuiltin "bvule"} AT#BvUle12(a: bv12, b: bv12): bool;
function {:bvbuiltin "bvult"} AT#BvUlt12(a: bv12, b: bv12): bool;
function {:bvbuiltin "bvuge"} AT#BvUge12(a: bv12, b: bv12): bool;
function {:bvbuiltin "bvugt"} AT#BvUgt12(a: bv12, b: bv12): bool;
function AT#BvXor12(a: bv12, b: bv12): bv12;

axiom (forall a,b: bv12 :: AT#BvXor12(a,b) == AT#BvAnd12(AT#BvOr12(a,b), AT#BvNot12(AT#BvAnd12(a,b))) );

// ---------------------------------------------------------------
// -- Bit vector operations --------------------------------------
// ---------------------------------------------------------------
// Size: 10
function {:bvbuiltin "bvand"} AT#BvAnd10(a: bv10, b: bv10): bv10;
function {:bvbuiltin "bvor"} AT#BvOr10(a: bv10, b: bv10): bv10;
function {:bvbuiltin "bvnot"} AT#BvNot10(a: bv10): bv10;
function {:bvbuiltin "bvadd"} AT#BvAdd10(a: bv10, b: bv10): bv10;
function {:bvbuiltin "bvsub"} AT#BvSub10(a: bv10, b: bv10): bv10;
function {:bvbuiltin "bvmul"} AT#BvMul10(a: bv10, b: bv10): bv10;
function {:bvbuiltin "bvshl"} AT#BvShl10(bv10,bv10): bv10;
function {:bvbuiltin "bvlshr"} AT#BvLshr10(bv10,bv10): bv10;
function {:bvbuiltin "bvashr"} AT#BvAshr10(bv10,bv10): bv10;
function {:bvbuiltin "bvule"} AT#BvUle10(a: bv10, b: bv10): bool;
function {:bvbuiltin "bvult"} AT#BvUlt10(a: bv10, b: bv10): bool;
function {:bvbuiltin "bvuge"} AT#BvUge10(a: bv10, b: bv10): bool;
function {:bvbuiltin "bvugt"} AT#BvUgt10(a: bv10, b: bv10): bool;
function AT#BvXor10(a: bv10, b: bv10): bv10;

axiom (forall a,b: bv10 :: AT#BvXor10(a,b) == AT#BvAnd10(AT#BvOr10(a,b), AT#BvNot10(AT#BvAnd10(a,b))) );

// ---------------------------------------------------------------
// -- Bit vector operations --------------------------------------
// ---------------------------------------------------------------
// Size: 9
function {:bvbuiltin "bvand"} AT#BvAnd9(a: bv9, b: bv9): bv9;
function {:bvbuiltin "bvor"} AT#BvOr9(a: bv9, b: bv9): bv9;
function {:bvbuiltin "bvnot"} AT#BvNot9(a: bv9): bv9;
function {:bvbuiltin "bvadd"} AT#BvAdd9(a: bv9, b: bv9): bv9;
function {:bvbuiltin "bvsub"} AT#BvSub9(a: bv9, b: bv9): bv9;
function {:bvbuiltin "bvmul"} AT#BvMul9(a: bv9, b: bv9): bv9;
function {:bvbuiltin "bvshl"} AT#BvShl9(bv9,bv9): bv9;
function {:bvbuiltin "bvlshr"} AT#BvLshr9(bv9,bv9): bv9;
function {:bvbuiltin "bvashr"} AT#BvAshr9(bv9,bv9): bv9;
function {:bvbuiltin "bvule"} AT#BvUle9(a: bv9, b: bv9): bool;
function {:bvbuiltin "bvult"} AT#BvUlt9(a: bv9, b: bv9): bool;
function {:bvbuiltin "bvuge"} AT#BvUge9(a: bv9, b: bv9): bool;
function {:bvbuiltin "bvugt"} AT#BvUgt9(a: bv9, b: bv9): bool;
function AT#BvXor9(a: bv9, b: bv9): bv9;

axiom (forall a,b: bv9 :: AT#BvXor9(a,b) == AT#BvAnd9(AT#BvOr9(a,b), AT#BvNot9(AT#BvAnd9(a,b))) );

// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

procedure Add#init#0()
  modifies C, R, M, I, H, I#sub;
{
  var MOT: Chan (bv9);
  var TEX: Chan (bv9);
  var BTYPE: Chan (bv12);
  var VID: Chan (bv9);
  var Ch#NEWVOP: Chan (bv12);
  var Ch#INTRA: Chan (bv12);
  var Ch#ACCODED: Chan (bv12);
  var Ch#count: Chan (int);
  var Ch#St: Chan (int);
  var NEWVOP: bv12;
  var INTRA: bv12;
  var ACCODED: bv12;
  var count: int;
  var St: int;
  assume (MOT != TEX) && (MOT != VID) && (TEX != VID);
  assume (I[MOT] == 0) && (R[MOT] == 0) && (C[MOT] == 0);
  assume (I[TEX] == 0) && (R[TEX] == 0) && (C[TEX] == 0);
  assume (I[BTYPE] == 0) && (R[BTYPE] == 0) && (C[BTYPE] == 0);
  assume (I[VID] == 0) && (R[VID] == 0) && (C[VID] == 0);
  assume (R[Ch#NEWVOP] == 0) && (C[Ch#NEWVOP] == 0);
  assume (R[Ch#INTRA] == 0) && (C[Ch#INTRA] == 0);
  assume (R[Ch#ACCODED] == 0) && (C[Ch#ACCODED] == 0);
  assume (R[Ch#count] == 0) && (C[Ch#count] == 0);
  assume (R[Ch#St] == 0) && (C[Ch#St] == 0);
  count := 0;
  St := 0;
  assert {:msg "Add.cal(18.12): Initialization might not establish the invariant (#0)"} ((R[BTYPE] - I[BTYPE]) > 0) && (AT#BvAnd12(M[BTYPE][I[BTYPE]], INTRA) != 0bv12) && ((R[TEX] - I[TEX]) < 64) ==> (St == 1);
}
procedure Add#cmd.newVop#1()
  modifies C, R, M, I, H, I#sub;
{
  var MOT: Chan (bv9);
  var TEX: Chan (bv9);
  var BTYPE: Chan (bv12);
  var VID: Chan (bv9);
  var Ch#NEWVOP: Chan (bv12);
  var Ch#INTRA: Chan (bv12);
  var Ch#ACCODED: Chan (bv12);
  var Ch#count: Chan (int);
  var Ch#St: Chan (int);
  var NEWVOP: bv12;
  var INTRA: bv12;
  var ACCODED: bv12;
  var count: int;
  var St: int;
  var BTYPE#0: bv12;
  var TEX#0: bv9;
  var MOT#0: bv9;
  assume (MOT != TEX) && (MOT != VID) && (TEX != VID);
  assume (0 <= I[MOT]) && (I[MOT] <= R[MOT]) && (R[MOT] <= C[MOT]);
  assume (0 <= I[TEX]) && (I[TEX] <= R[TEX]) && (R[TEX] <= C[TEX]);
  assume (0 <= I[BTYPE]) && (I[BTYPE] <= R[BTYPE]) && (R[BTYPE] <= C[BTYPE]);
  assume (0 <= I[VID]) && (I[VID] <= R[VID]) && (R[VID] <= C[VID]);
  assume (0 <= R[Ch#NEWVOP]) && (C[Ch#NEWVOP] == (R[Ch#NEWVOP] + 1));
  assume (0 <= R[Ch#INTRA]) && (C[Ch#INTRA] == (R[Ch#INTRA] + 1));
  assume (0 <= R[Ch#ACCODED]) && (C[Ch#ACCODED] == (R[Ch#ACCODED] + 1));
  assume (0 <= R[Ch#count]) && (C[Ch#count] == (R[Ch#count] + 1));
  assume (0 <= R[Ch#St]) && (C[Ch#St] == (R[Ch#St] + 1));
  assume NEWVOP == 2048bv12;
  assume INTRA == 1024bv12;
  assume NEWVOP == 2048bv12;
  assume ACCODED == 2bv12;
  assume ((R[BTYPE] - I[BTYPE]) > 0) && (AT#BvAnd12(M[BTYPE][I[BTYPE]], INTRA) != 0bv12) && ((R[TEX] - I[TEX]) < 64) ==> (St == 1);
  BTYPE#0 := M[BTYPE][R[BTYPE]];
  R[BTYPE] := R[BTYPE] + 1;
  assume (St == 0) && (AT#BvAnd12(BTYPE#0, NEWVOP) != 0bv12);
  St := 4;
  assert {:msg "Add.cal(18.12): Action at Add.cal(41.2) might not preserve invariant (#1)"} ((R[BTYPE] - I[BTYPE]) > 0) && (AT#BvAnd12(M[BTYPE][I[BTYPE]], INTRA) != 0bv12) && ((R[TEX] - I[TEX]) < 64) ==> (St == 1);
}
procedure Add#cmd.textureOnly#2()
  modifies C, R, M, I, H, I#sub;
{
  var MOT: Chan (bv9);
  var TEX: Chan (bv9);
  var BTYPE: Chan (bv12);
  var VID: Chan (bv9);
  var Ch#NEWVOP: Chan (bv12);
  var Ch#INTRA: Chan (bv12);
  var Ch#ACCODED: Chan (bv12);
  var Ch#count: Chan (int);
  var Ch#St: Chan (int);
  var NEWVOP: bv12;
  var INTRA: bv12;
  var ACCODED: bv12;
  var count: int;
  var St: int;
  var BTYPE#0: bv12;
  var TEX#0: bv9;
  var MOT#0: bv9;
  assume (MOT != TEX) && (MOT != VID) && (TEX != VID);
  assume (0 <= I[MOT]) && (I[MOT] <= R[MOT]) && (R[MOT] <= C[MOT]);
  assume (0 <= I[TEX]) && (I[TEX] <= R[TEX]) && (R[TEX] <= C[TEX]);
  assume (0 <= I[BTYPE]) && (I[BTYPE] <= R[BTYPE]) && (R[BTYPE] <= C[BTYPE]);
  assume (0 <= I[VID]) && (I[VID] <= R[VID]) && (R[VID] <= C[VID]);
  assume (0 <= R[Ch#NEWVOP]) && (C[Ch#NEWVOP] == (R[Ch#NEWVOP] + 1));
  assume (0 <= R[Ch#INTRA]) && (C[Ch#INTRA] == (R[Ch#INTRA] + 1));
  assume (0 <= R[Ch#ACCODED]) && (C[Ch#ACCODED] == (R[Ch#ACCODED] + 1));
  assume (0 <= R[Ch#count]) && (C[Ch#count] == (R[Ch#count] + 1));
  assume (0 <= R[Ch#St]) && (C[Ch#St] == (R[Ch#St] + 1));
  assume NEWVOP == 2048bv12;
  assume INTRA == 1024bv12;
  assume NEWVOP == 2048bv12;
  assume ACCODED == 2bv12;
  assume ((R[BTYPE] - I[BTYPE]) > 0) && (AT#BvAnd12(M[BTYPE][I[BTYPE]], INTRA) != 0bv12) && ((R[TEX] - I[TEX]) < 64) ==> (St == 1);
  BTYPE#0 := M[BTYPE][R[BTYPE]];
  R[BTYPE] := R[BTYPE] + 1;
  assume !((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(BTYPE#0, NEWVOP) != 0bv12));
  assume (St == 0) && (AT#BvAnd12(BTYPE#0, INTRA) != 0bv12);
  St := 1;
  assert {:msg "Add.cal(18.12): Action at Add.cal(50.2) might not preserve invariant (#2)"} ((R[BTYPE] - I[BTYPE]) > 0) && (AT#BvAnd12(M[BTYPE][I[BTYPE]], INTRA) != 0bv12) && ((R[TEX] - I[TEX]) < 64) ==> (St == 1);
}
procedure Add#cmd.motionOnly#3()
  modifies C, R, M, I, H, I#sub;
{
  var MOT: Chan (bv9);
  var TEX: Chan (bv9);
  var BTYPE: Chan (bv12);
  var VID: Chan (bv9);
  var Ch#NEWVOP: Chan (bv12);
  var Ch#INTRA: Chan (bv12);
  var Ch#ACCODED: Chan (bv12);
  var Ch#count: Chan (int);
  var Ch#St: Chan (int);
  var NEWVOP: bv12;
  var INTRA: bv12;
  var ACCODED: bv12;
  var count: int;
  var St: int;
  var BTYPE#0: bv12;
  var TEX#0: bv9;
  var MOT#0: bv9;
  assume (MOT != TEX) && (MOT != VID) && (TEX != VID);
  assume (0 <= I[MOT]) && (I[MOT] <= R[MOT]) && (R[MOT] <= C[MOT]);
  assume (0 <= I[TEX]) && (I[TEX] <= R[TEX]) && (R[TEX] <= C[TEX]);
  assume (0 <= I[BTYPE]) && (I[BTYPE] <= R[BTYPE]) && (R[BTYPE] <= C[BTYPE]);
  assume (0 <= I[VID]) && (I[VID] <= R[VID]) && (R[VID] <= C[VID]);
  assume (0 <= R[Ch#NEWVOP]) && (C[Ch#NEWVOP] == (R[Ch#NEWVOP] + 1));
  assume (0 <= R[Ch#INTRA]) && (C[Ch#INTRA] == (R[Ch#INTRA] + 1));
  assume (0 <= R[Ch#ACCODED]) && (C[Ch#ACCODED] == (R[Ch#ACCODED] + 1));
  assume (0 <= R[Ch#count]) && (C[Ch#count] == (R[Ch#count] + 1));
  assume (0 <= R[Ch#St]) && (C[Ch#St] == (R[Ch#St] + 1));
  assume NEWVOP == 2048bv12;
  assume INTRA == 1024bv12;
  assume NEWVOP == 2048bv12;
  assume ACCODED == 2bv12;
  assume ((R[BTYPE] - I[BTYPE]) > 0) && (AT#BvAnd12(M[BTYPE][I[BTYPE]], INTRA) != 0bv12) && ((R[TEX] - I[TEX]) < 64) ==> (St == 1);
  BTYPE#0 := M[BTYPE][R[BTYPE]];
  R[BTYPE] := R[BTYPE] + 1;
  assume !((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(BTYPE#0, INTRA) != 0bv12));
  assume !((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(BTYPE#0, NEWVOP) != 0bv12));
  assume (St == 0) && (AT#BvAnd12(BTYPE#0, ACCODED) == 0bv12);
  St := 2;
  assert {:msg "Add.cal(18.12): Action at Add.cal(59.2) might not preserve invariant (#3)"} ((R[BTYPE] - I[BTYPE]) > 0) && (AT#BvAnd12(M[BTYPE][I[BTYPE]], INTRA) != 0bv12) && ((R[TEX] - I[TEX]) < 64) ==> (St == 1);
}
procedure Add#cmd.other#4()
  modifies C, R, M, I, H, I#sub;
{
  var MOT: Chan (bv9);
  var TEX: Chan (bv9);
  var BTYPE: Chan (bv12);
  var VID: Chan (bv9);
  var Ch#NEWVOP: Chan (bv12);
  var Ch#INTRA: Chan (bv12);
  var Ch#ACCODED: Chan (bv12);
  var Ch#count: Chan (int);
  var Ch#St: Chan (int);
  var NEWVOP: bv12;
  var INTRA: bv12;
  var ACCODED: bv12;
  var count: int;
  var St: int;
  var BTYPE#0: bv12;
  var TEX#0: bv9;
  var MOT#0: bv9;
  assume (MOT != TEX) && (MOT != VID) && (TEX != VID);
  assume (0 <= I[MOT]) && (I[MOT] <= R[MOT]) && (R[MOT] <= C[MOT]);
  assume (0 <= I[TEX]) && (I[TEX] <= R[TEX]) && (R[TEX] <= C[TEX]);
  assume (0 <= I[BTYPE]) && (I[BTYPE] <= R[BTYPE]) && (R[BTYPE] <= C[BTYPE]);
  assume (0 <= I[VID]) && (I[VID] <= R[VID]) && (R[VID] <= C[VID]);
  assume (0 <= R[Ch#NEWVOP]) && (C[Ch#NEWVOP] == (R[Ch#NEWVOP] + 1));
  assume (0 <= R[Ch#INTRA]) && (C[Ch#INTRA] == (R[Ch#INTRA] + 1));
  assume (0 <= R[Ch#ACCODED]) && (C[Ch#ACCODED] == (R[Ch#ACCODED] + 1));
  assume (0 <= R[Ch#count]) && (C[Ch#count] == (R[Ch#count] + 1));
  assume (0 <= R[Ch#St]) && (C[Ch#St] == (R[Ch#St] + 1));
  assume NEWVOP == 2048bv12;
  assume INTRA == 1024bv12;
  assume NEWVOP == 2048bv12;
  assume ACCODED == 2bv12;
  assume ((R[BTYPE] - I[BTYPE]) > 0) && (AT#BvAnd12(M[BTYPE][I[BTYPE]], INTRA) != 0bv12) && ((R[TEX] - I[TEX]) < 64) ==> (St == 1);
  BTYPE#0 := M[BTYPE][R[BTYPE]];
  R[BTYPE] := R[BTYPE] + 1;
  assume !((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(BTYPE#0, ACCODED) == 0bv12));
  assume !((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(BTYPE#0, INTRA) != 0bv12));
  assume !((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(BTYPE#0, NEWVOP) != 0bv12));
  assume ((St == 0) || (St == 4)) || (St == 5);
  St := (if St == 0 then 3 else (if St == 4 then 5 else 0));
  assert {:msg "Add.cal(18.12): Action at Add.cal(69.2) might not preserve invariant (#4)"} ((R[BTYPE] - I[BTYPE]) > 0) && (AT#BvAnd12(M[BTYPE][I[BTYPE]], INTRA) != 0bv12) && ((R[TEX] - I[TEX]) < 64) ==> (St == 1);
}
procedure Add#done#5()
  modifies C, R, M, I, H, I#sub;
{
  var MOT: Chan (bv9);
  var TEX: Chan (bv9);
  var BTYPE: Chan (bv12);
  var VID: Chan (bv9);
  var Ch#NEWVOP: Chan (bv12);
  var Ch#INTRA: Chan (bv12);
  var Ch#ACCODED: Chan (bv12);
  var Ch#count: Chan (int);
  var Ch#St: Chan (int);
  var NEWVOP: bv12;
  var INTRA: bv12;
  var ACCODED: bv12;
  var count: int;
  var St: int;
  var BTYPE#0: bv12;
  var TEX#0: bv9;
  var MOT#0: bv9;
  assume (MOT != TEX) && (MOT != VID) && (TEX != VID);
  assume (0 <= I[MOT]) && (I[MOT] <= R[MOT]) && (R[MOT] <= C[MOT]);
  assume (0 <= I[TEX]) && (I[TEX] <= R[TEX]) && (R[TEX] <= C[TEX]);
  assume (0 <= I[BTYPE]) && (I[BTYPE] <= R[BTYPE]) && (R[BTYPE] <= C[BTYPE]);
  assume (0 <= I[VID]) && (I[VID] <= R[VID]) && (R[VID] <= C[VID]);
  assume (0 <= R[Ch#NEWVOP]) && (C[Ch#NEWVOP] == (R[Ch#NEWVOP] + 1));
  assume (0 <= R[Ch#INTRA]) && (C[Ch#INTRA] == (R[Ch#INTRA] + 1));
  assume (0 <= R[Ch#ACCODED]) && (C[Ch#ACCODED] == (R[Ch#ACCODED] + 1));
  assume (0 <= R[Ch#count]) && (C[Ch#count] == (R[Ch#count] + 1));
  assume (0 <= R[Ch#St]) && (C[Ch#St] == (R[Ch#St] + 1));
  assume NEWVOP == 2048bv12;
  assume INTRA == 1024bv12;
  assume NEWVOP == 2048bv12;
  assume ACCODED == 2bv12;
  assume ((R[BTYPE] - I[BTYPE]) > 0) && (AT#BvAnd12(M[BTYPE][I[BTYPE]], INTRA) != 0bv12) && ((R[TEX] - I[TEX]) < 64) ==> (St == 1);
  assume (((St == 1) || (St == 2)) || (St == 3)) && (count == 64);
  count := 0;
  assert {:msg "Add.cal(18.12): Action at Add.cal(80.2) might not preserve invariant (#5)"} ((R[BTYPE] - I[BTYPE]) > 0) && (AT#BvAnd12(M[BTYPE][I[BTYPE]], INTRA) != 0bv12) && ((R[TEX] - I[TEX]) < 64) ==> (St == 1);
}
procedure Add#texture#6()
  modifies C, R, M, I, H, I#sub;
{
  var MOT: Chan (bv9);
  var TEX: Chan (bv9);
  var BTYPE: Chan (bv12);
  var VID: Chan (bv9);
  var Ch#NEWVOP: Chan (bv12);
  var Ch#INTRA: Chan (bv12);
  var Ch#ACCODED: Chan (bv12);
  var Ch#count: Chan (int);
  var Ch#St: Chan (int);
  var NEWVOP: bv12;
  var INTRA: bv12;
  var ACCODED: bv12;
  var count: int;
  var St: int;
  var BTYPE#0: bv12;
  var TEX#0: bv9;
  var MOT#0: bv9;
  assume (MOT != TEX) && (MOT != VID) && (TEX != VID);
  assume (0 <= I[MOT]) && (I[MOT] <= R[MOT]) && (R[MOT] <= C[MOT]);
  assume (0 <= I[TEX]) && (I[TEX] <= R[TEX]) && (R[TEX] <= C[TEX]);
  assume (0 <= I[BTYPE]) && (I[BTYPE] <= R[BTYPE]) && (R[BTYPE] <= C[BTYPE]);
  assume (0 <= I[VID]) && (I[VID] <= R[VID]) && (R[VID] <= C[VID]);
  assume (0 <= R[Ch#NEWVOP]) && (C[Ch#NEWVOP] == (R[Ch#NEWVOP] + 1));
  assume (0 <= R[Ch#INTRA]) && (C[Ch#INTRA] == (R[Ch#INTRA] + 1));
  assume (0 <= R[Ch#ACCODED]) && (C[Ch#ACCODED] == (R[Ch#ACCODED] + 1));
  assume (0 <= R[Ch#count]) && (C[Ch#count] == (R[Ch#count] + 1));
  assume (0 <= R[Ch#St]) && (C[Ch#St] == (R[Ch#St] + 1));
  assume NEWVOP == 2048bv12;
  assume INTRA == 1024bv12;
  assume NEWVOP == 2048bv12;
  assume ACCODED == 2bv12;
  assume ((R[BTYPE] - I[BTYPE]) > 0) && (AT#BvAnd12(M[BTYPE][I[BTYPE]], INTRA) != 0bv12) && ((R[TEX] - I[TEX]) < 64) ==> (St == 1);
  TEX#0 := M[TEX][R[TEX]];
  R[TEX] := R[TEX] + 1;
  assume !(true && (((St == 1) || (St == 2)) || (St == 3)) && (count == 64));
  assume St == 1;
  count := count + 1;
  M[VID][C[VID]] := TEX#0;
  C[VID] := C[VID] + 1;
  assert {:msg "Add.cal(18.12): Action at Add.cal(88.2) might not preserve invariant (#6)"} ((R[BTYPE] - I[BTYPE]) > 0) && (AT#BvAnd12(M[BTYPE][I[BTYPE]], INTRA) != 0bv12) && ((R[TEX] - I[TEX]) < 64) ==> (St == 1);
}
procedure Add#motion#7()
  modifies C, R, M, I, H, I#sub;
{
  var MOT: Chan (bv9);
  var TEX: Chan (bv9);
  var BTYPE: Chan (bv12);
  var VID: Chan (bv9);
  var Ch#NEWVOP: Chan (bv12);
  var Ch#INTRA: Chan (bv12);
  var Ch#ACCODED: Chan (bv12);
  var Ch#count: Chan (int);
  var Ch#St: Chan (int);
  var NEWVOP: bv12;
  var INTRA: bv12;
  var ACCODED: bv12;
  var count: int;
  var St: int;
  var BTYPE#0: bv12;
  var TEX#0: bv9;
  var MOT#0: bv9;
  assume (MOT != TEX) && (MOT != VID) && (TEX != VID);
  assume (0 <= I[MOT]) && (I[MOT] <= R[MOT]) && (R[MOT] <= C[MOT]);
  assume (0 <= I[TEX]) && (I[TEX] <= R[TEX]) && (R[TEX] <= C[TEX]);
  assume (0 <= I[BTYPE]) && (I[BTYPE] <= R[BTYPE]) && (R[BTYPE] <= C[BTYPE]);
  assume (0 <= I[VID]) && (I[VID] <= R[VID]) && (R[VID] <= C[VID]);
  assume (0 <= R[Ch#NEWVOP]) && (C[Ch#NEWVOP] == (R[Ch#NEWVOP] + 1));
  assume (0 <= R[Ch#INTRA]) && (C[Ch#INTRA] == (R[Ch#INTRA] + 1));
  assume (0 <= R[Ch#ACCODED]) && (C[Ch#ACCODED] == (R[Ch#ACCODED] + 1));
  assume (0 <= R[Ch#count]) && (C[Ch#count] == (R[Ch#count] + 1));
  assume (0 <= R[Ch#St]) && (C[Ch#St] == (R[Ch#St] + 1));
  assume NEWVOP == 2048bv12;
  assume INTRA == 1024bv12;
  assume NEWVOP == 2048bv12;
  assume ACCODED == 2bv12;
  assume ((R[BTYPE] - I[BTYPE]) > 0) && (AT#BvAnd12(M[BTYPE][I[BTYPE]], INTRA) != 0bv12) && ((R[TEX] - I[TEX]) < 64) ==> (St == 1);
  MOT#0 := M[MOT][R[MOT]];
  R[MOT] := R[MOT] + 1;
  assume !(true && (((St == 1) || (St == 2)) || (St == 3)) && (count == 64));
  assume St == 2;
  count := count + 1;
  M[VID][C[VID]] := MOT#0;
  C[VID] := C[VID] + 1;
  assert {:msg "Add.cal(18.12): Action at Add.cal(95.2) might not preserve invariant (#7)"} ((R[BTYPE] - I[BTYPE]) > 0) && (AT#BvAnd12(M[BTYPE][I[BTYPE]], INTRA) != 0bv12) && ((R[TEX] - I[TEX]) < 64) ==> (St == 1);
}
procedure Add#combine#8()
  modifies C, R, M, I, H, I#sub;
{
  var MOT: Chan (bv9);
  var TEX: Chan (bv9);
  var BTYPE: Chan (bv12);
  var VID: Chan (bv9);
  var Ch#NEWVOP: Chan (bv12);
  var Ch#INTRA: Chan (bv12);
  var Ch#ACCODED: Chan (bv12);
  var Ch#count: Chan (int);
  var Ch#St: Chan (int);
  var NEWVOP: bv12;
  var INTRA: bv12;
  var ACCODED: bv12;
  var count: int;
  var St: int;
  var BTYPE#0: bv12;
  var TEX#0: bv9;
  var MOT#0: bv9;
  assume (MOT != TEX) && (MOT != VID) && (TEX != VID);
  assume (0 <= I[MOT]) && (I[MOT] <= R[MOT]) && (R[MOT] <= C[MOT]);
  assume (0 <= I[TEX]) && (I[TEX] <= R[TEX]) && (R[TEX] <= C[TEX]);
  assume (0 <= I[BTYPE]) && (I[BTYPE] <= R[BTYPE]) && (R[BTYPE] <= C[BTYPE]);
  assume (0 <= I[VID]) && (I[VID] <= R[VID]) && (R[VID] <= C[VID]);
  assume (0 <= R[Ch#NEWVOP]) && (C[Ch#NEWVOP] == (R[Ch#NEWVOP] + 1));
  assume (0 <= R[Ch#INTRA]) && (C[Ch#INTRA] == (R[Ch#INTRA] + 1));
  assume (0 <= R[Ch#ACCODED]) && (C[Ch#ACCODED] == (R[Ch#ACCODED] + 1));
  assume (0 <= R[Ch#count]) && (C[Ch#count] == (R[Ch#count] + 1));
  assume (0 <= R[Ch#St]) && (C[Ch#St] == (R[Ch#St] + 1));
  assume NEWVOP == 2048bv12;
  assume INTRA == 1024bv12;
  assume NEWVOP == 2048bv12;
  assume ACCODED == 2bv12;
  assume ((R[BTYPE] - I[BTYPE]) > 0) && (AT#BvAnd12(M[BTYPE][I[BTYPE]], INTRA) != 0bv12) && ((R[TEX] - I[TEX]) < 64) ==> (St == 1);
  MOT#0 := M[MOT][R[MOT]];
  R[MOT] := R[MOT] + 1;
  TEX#0 := M[TEX][R[TEX]];
  R[TEX] := R[TEX] + 1;
  assume !(true && (((St == 1) || (St == 2)) || (St == 3)) && (count == 64));
  assume St == 3;
  count := count + 1;
  M[VID][C[VID]] := (if AT#BvUlt10(AT#BvAdd10(0bv1 ++ TEX#0, 0bv1 ++ MOT#0), 0bv10) then 0bv9 else (if AT#BvUgt10(AT#BvAdd10(0bv1 ++ TEX#0, 0bv1 ++ MOT#0), 255bv10) then 255bv9 else AT#BvAdd9(TEX#0, MOT#0)));
  C[VID] := C[VID] + 1;
  assert {:msg "Add.cal(18.12): Action at Add.cal(102.2) might not preserve invariant (#8)"} ((R[BTYPE] - I[BTYPE]) > 0) && (AT#BvAnd12(M[BTYPE][I[BTYPE]], INTRA) != 0bv12) && ((R[TEX] - I[TEX]) < 64) ==> (St == 1);
}
procedure Add##GuardWD#9()
  modifies C, R, M, I, H, I#sub;
{
  var MOT: Chan (bv9);
  var TEX: Chan (bv9);
  var BTYPE: Chan (bv12);
  var VID: Chan (bv9);
  var Ch#NEWVOP: Chan (bv12);
  var Ch#INTRA: Chan (bv12);
  var Ch#ACCODED: Chan (bv12);
  var Ch#count: Chan (int);
  var Ch#St: Chan (int);
  var NEWVOP: bv12;
  var INTRA: bv12;
  var ACCODED: bv12;
  var count: int;
  var St: int;
  var BTYPE#0: bv12;
  var TEX#0: bv9;
  var MOT#0: bv9;
  assume (MOT != TEX) && (MOT != VID) && (TEX != VID);
  assume NEWVOP == 2048bv12;
  assume INTRA == 1024bv12;
  assume NEWVOP == 2048bv12;
  assume ACCODED == 2bv12;
  assume ((R[BTYPE] - I[BTYPE]) > 0) && (AT#BvAnd12(M[BTYPE][I[BTYPE]], INTRA) != 0bv12) && ((R[TEX] - I[TEX]) < 64) ==> (St == 1);
  assert {:msg "Add.cal(1.1): The actions 'texture' and 'done' of actor 'Add' might not have mutually exclusive guards (#9)"} !(true && (!(true && (((St == 1) || (St == 2)) || (St == 3)) && (count == 64))) && (1 <= (C[TEX] - R[TEX])) && (St == 1) && true && true && (((St == 1) || (St == 2)) || (St == 3)) && (count == 64));
  assert {:msg "Add.cal(1.1): The actions 'texture' and 'cmd.motionOnly' of actor 'Add' might not have mutually exclusive guards (#10)"} !(true && (!(true && (((St == 1) || (St == 2)) || (St == 3)) && (count == 64))) && (1 <= (C[TEX] - R[TEX])) && (St == 1) && true && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], INTRA) != 0bv12))) && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], NEWVOP) != 0bv12))) && (1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], ACCODED) == 0bv12));
  assert {:msg "Add.cal(1.1): The actions 'texture' and 'cmd.textureOnly' of actor 'Add' might not have mutually exclusive guards (#11)"} !(true && (!(true && (((St == 1) || (St == 2)) || (St == 3)) && (count == 64))) && (1 <= (C[TEX] - R[TEX])) && (St == 1) && true && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], NEWVOP) != 0bv12))) && (1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], INTRA) != 0bv12));
  assert {:msg "Add.cal(1.1): The actions 'texture' and 'motion' of actor 'Add' might not have mutually exclusive guards (#12)"} !(true && (!(true && (((St == 1) || (St == 2)) || (St == 3)) && (count == 64))) && (1 <= (C[TEX] - R[TEX])) && (St == 1) && true && (!(true && (((St == 1) || (St == 2)) || (St == 3)) && (count == 64))) && (1 <= (C[MOT] - R[MOT])) && (St == 2));
  assert {:msg "Add.cal(1.1): The actions 'texture' and 'cmd.other' of actor 'Add' might not have mutually exclusive guards (#13)"} !(true && (!(true && (((St == 1) || (St == 2)) || (St == 3)) && (count == 64))) && (1 <= (C[TEX] - R[TEX])) && (St == 1) && true && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], ACCODED) == 0bv12))) && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], INTRA) != 0bv12))) && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], NEWVOP) != 0bv12))) && (1 <= (C[BTYPE] - R[BTYPE])) && (((St == 0) || (St == 4)) || (St == 5)));
  assert {:msg "Add.cal(1.1): The actions 'texture' and 'combine' of actor 'Add' might not have mutually exclusive guards (#14)"} !(true && (!(true && (((St == 1) || (St == 2)) || (St == 3)) && (count == 64))) && (1 <= (C[TEX] - R[TEX])) && (St == 1) && true && (!(true && (((St == 1) || (St == 2)) || (St == 3)) && (count == 64))) && (1 <= (C[MOT] - R[MOT])) && (1 <= (C[TEX] - R[TEX])) && (St == 3));
  assert {:msg "Add.cal(1.1): The actions 'texture' and 'cmd.newVop' of actor 'Add' might not have mutually exclusive guards (#15)"} !(true && (!(true && (((St == 1) || (St == 2)) || (St == 3)) && (count == 64))) && (1 <= (C[TEX] - R[TEX])) && (St == 1) && true && (1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], NEWVOP) != 0bv12));
  assert {:msg "Add.cal(1.1): The actions 'done' and 'cmd.motionOnly' of actor 'Add' might not have mutually exclusive guards (#16)"} !(true && true && (((St == 1) || (St == 2)) || (St == 3)) && (count == 64) && true && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], INTRA) != 0bv12))) && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], NEWVOP) != 0bv12))) && (1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], ACCODED) == 0bv12));
  assert {:msg "Add.cal(1.1): The actions 'done' and 'cmd.textureOnly' of actor 'Add' might not have mutually exclusive guards (#17)"} !(true && true && (((St == 1) || (St == 2)) || (St == 3)) && (count == 64) && true && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], NEWVOP) != 0bv12))) && (1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], INTRA) != 0bv12));
  assert {:msg "Add.cal(1.1): The actions 'done' and 'motion' of actor 'Add' might not have mutually exclusive guards (#18)"} !(true && true && (((St == 1) || (St == 2)) || (St == 3)) && (count == 64) && true && (!(true && (((St == 1) || (St == 2)) || (St == 3)) && (count == 64))) && (1 <= (C[MOT] - R[MOT])) && (St == 2));
  assert {:msg "Add.cal(1.1): The actions 'done' and 'cmd.other' of actor 'Add' might not have mutually exclusive guards (#19)"} !(true && true && (((St == 1) || (St == 2)) || (St == 3)) && (count == 64) && true && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], ACCODED) == 0bv12))) && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], INTRA) != 0bv12))) && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], NEWVOP) != 0bv12))) && (1 <= (C[BTYPE] - R[BTYPE])) && (((St == 0) || (St == 4)) || (St == 5)));
  assert {:msg "Add.cal(1.1): The actions 'done' and 'combine' of actor 'Add' might not have mutually exclusive guards (#20)"} !(true && true && (((St == 1) || (St == 2)) || (St == 3)) && (count == 64) && true && (!(true && (((St == 1) || (St == 2)) || (St == 3)) && (count == 64))) && (1 <= (C[MOT] - R[MOT])) && (1 <= (C[TEX] - R[TEX])) && (St == 3));
  assert {:msg "Add.cal(1.1): The actions 'done' and 'cmd.newVop' of actor 'Add' might not have mutually exclusive guards (#21)"} !(true && true && (((St == 1) || (St == 2)) || (St == 3)) && (count == 64) && true && (1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], NEWVOP) != 0bv12));
  assert {:msg "Add.cal(1.1): The actions 'cmd.motionOnly' and 'cmd.textureOnly' of actor 'Add' might not have mutually exclusive guards (#22)"} !(true && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], INTRA) != 0bv12))) && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], NEWVOP) != 0bv12))) && (1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], ACCODED) == 0bv12) && true && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], NEWVOP) != 0bv12))) && (1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], INTRA) != 0bv12));
  assert {:msg "Add.cal(1.1): The actions 'cmd.motionOnly' and 'motion' of actor 'Add' might not have mutually exclusive guards (#23)"} !(true && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], INTRA) != 0bv12))) && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], NEWVOP) != 0bv12))) && (1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], ACCODED) == 0bv12) && true && (!(true && (((St == 1) || (St == 2)) || (St == 3)) && (count == 64))) && (1 <= (C[MOT] - R[MOT])) && (St == 2));
  assert {:msg "Add.cal(1.1): The actions 'cmd.motionOnly' and 'cmd.other' of actor 'Add' might not have mutually exclusive guards (#24)"} !(true && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], INTRA) != 0bv12))) && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], NEWVOP) != 0bv12))) && (1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], ACCODED) == 0bv12) && true && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], ACCODED) == 0bv12))) && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], INTRA) != 0bv12))) && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], NEWVOP) != 0bv12))) && (1 <= (C[BTYPE] - R[BTYPE])) && (((St == 0) || (St == 4)) || (St == 5)));
  assert {:msg "Add.cal(1.1): The actions 'cmd.motionOnly' and 'combine' of actor 'Add' might not have mutually exclusive guards (#25)"} !(true && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], INTRA) != 0bv12))) && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], NEWVOP) != 0bv12))) && (1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], ACCODED) == 0bv12) && true && (!(true && (((St == 1) || (St == 2)) || (St == 3)) && (count == 64))) && (1 <= (C[MOT] - R[MOT])) && (1 <= (C[TEX] - R[TEX])) && (St == 3));
  assert {:msg "Add.cal(1.1): The actions 'cmd.motionOnly' and 'cmd.newVop' of actor 'Add' might not have mutually exclusive guards (#26)"} !(true && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], INTRA) != 0bv12))) && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], NEWVOP) != 0bv12))) && (1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], ACCODED) == 0bv12) && true && (1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], NEWVOP) != 0bv12));
  assert {:msg "Add.cal(1.1): The actions 'cmd.textureOnly' and 'motion' of actor 'Add' might not have mutually exclusive guards (#27)"} !(true && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], NEWVOP) != 0bv12))) && (1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], INTRA) != 0bv12) && true && (!(true && (((St == 1) || (St == 2)) || (St == 3)) && (count == 64))) && (1 <= (C[MOT] - R[MOT])) && (St == 2));
  assert {:msg "Add.cal(1.1): The actions 'cmd.textureOnly' and 'cmd.other' of actor 'Add' might not have mutually exclusive guards (#28)"} !(true && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], NEWVOP) != 0bv12))) && (1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], INTRA) != 0bv12) && true && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], ACCODED) == 0bv12))) && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], INTRA) != 0bv12))) && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], NEWVOP) != 0bv12))) && (1 <= (C[BTYPE] - R[BTYPE])) && (((St == 0) || (St == 4)) || (St == 5)));
  assert {:msg "Add.cal(1.1): The actions 'cmd.textureOnly' and 'combine' of actor 'Add' might not have mutually exclusive guards (#29)"} !(true && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], NEWVOP) != 0bv12))) && (1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], INTRA) != 0bv12) && true && (!(true && (((St == 1) || (St == 2)) || (St == 3)) && (count == 64))) && (1 <= (C[MOT] - R[MOT])) && (1 <= (C[TEX] - R[TEX])) && (St == 3));
  assert {:msg "Add.cal(1.1): The actions 'cmd.textureOnly' and 'cmd.newVop' of actor 'Add' might not have mutually exclusive guards (#30)"} !(true && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], NEWVOP) != 0bv12))) && (1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], INTRA) != 0bv12) && true && (1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], NEWVOP) != 0bv12));
  assert {:msg "Add.cal(1.1): The actions 'motion' and 'cmd.other' of actor 'Add' might not have mutually exclusive guards (#31)"} !(true && (!(true && (((St == 1) || (St == 2)) || (St == 3)) && (count == 64))) && (1 <= (C[MOT] - R[MOT])) && (St == 2) && true && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], ACCODED) == 0bv12))) && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], INTRA) != 0bv12))) && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], NEWVOP) != 0bv12))) && (1 <= (C[BTYPE] - R[BTYPE])) && (((St == 0) || (St == 4)) || (St == 5)));
  assert {:msg "Add.cal(1.1): The actions 'motion' and 'combine' of actor 'Add' might not have mutually exclusive guards (#32)"} !(true && (!(true && (((St == 1) || (St == 2)) || (St == 3)) && (count == 64))) && (1 <= (C[MOT] - R[MOT])) && (St == 2) && true && (!(true && (((St == 1) || (St == 2)) || (St == 3)) && (count == 64))) && (1 <= (C[MOT] - R[MOT])) && (1 <= (C[TEX] - R[TEX])) && (St == 3));
  assert {:msg "Add.cal(1.1): The actions 'motion' and 'cmd.newVop' of actor 'Add' might not have mutually exclusive guards (#33)"} !(true && (!(true && (((St == 1) || (St == 2)) || (St == 3)) && (count == 64))) && (1 <= (C[MOT] - R[MOT])) && (St == 2) && true && (1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], NEWVOP) != 0bv12));
  assert {:msg "Add.cal(1.1): The actions 'cmd.other' and 'combine' of actor 'Add' might not have mutually exclusive guards (#34)"} !(true && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], ACCODED) == 0bv12))) && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], INTRA) != 0bv12))) && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], NEWVOP) != 0bv12))) && (1 <= (C[BTYPE] - R[BTYPE])) && (((St == 0) || (St == 4)) || (St == 5)) && true && (!(true && (((St == 1) || (St == 2)) || (St == 3)) && (count == 64))) && (1 <= (C[MOT] - R[MOT])) && (1 <= (C[TEX] - R[TEX])) && (St == 3));
  assert {:msg "Add.cal(1.1): The actions 'cmd.other' and 'cmd.newVop' of actor 'Add' might not have mutually exclusive guards (#35)"} !(true && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], ACCODED) == 0bv12))) && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], INTRA) != 0bv12))) && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], NEWVOP) != 0bv12))) && (1 <= (C[BTYPE] - R[BTYPE])) && (((St == 0) || (St == 4)) || (St == 5)) && true && (1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], NEWVOP) != 0bv12));
  assert {:msg "Add.cal(1.1): The actions 'combine' and 'cmd.newVop' of actor 'Add' might not have mutually exclusive guards (#36)"} !(true && (!(true && (((St == 1) || (St == 2)) || (St == 3)) && (count == 64))) && (1 <= (C[MOT] - R[MOT])) && (1 <= (C[TEX] - R[TEX])) && (St == 3) && true && (1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], NEWVOP) != 0bv12));
}
procedure Add#contract#anon$0#10()
  modifies C, R, M, I, H, I#sub;
{
  var MOT: Chan (bv9);
  var TEX: Chan (bv9);
  var BTYPE: Chan (bv12);
  var VID: Chan (bv9);
  var Ch#NEWVOP: Chan (bv12);
  var Ch#INTRA: Chan (bv12);
  var Ch#ACCODED: Chan (bv12);
  var Ch#count: Chan (int);
  var Ch#St: Chan (int);
  var NEWVOP: bv12;
  var INTRA: bv12;
  var ACCODED: bv12;
  var count: int;
  var St: int;
  assume (MOT != TEX) && (MOT != VID) && (TEX != VID);
  assume (0 <= I[MOT]) && (I[MOT] <= R[MOT]) && (R[MOT] <= C[MOT]);
  assume (0 <= I[TEX]) && (I[TEX] <= R[TEX]) && (R[TEX] <= C[TEX]);
  assume (0 <= I[BTYPE]) && (I[BTYPE] <= R[BTYPE]) && (R[BTYPE] <= C[BTYPE]);
  assume (0 <= I[VID]) && (I[VID] <= R[VID]) && (R[VID] <= C[VID]);
  assume (0 <= R[Ch#NEWVOP]) && (C[Ch#NEWVOP] == (R[Ch#NEWVOP] + 1));
  assume (0 <= R[Ch#INTRA]) && (C[Ch#INTRA] == (R[Ch#INTRA] + 1));
  assume (0 <= R[Ch#ACCODED]) && (C[Ch#ACCODED] == (R[Ch#ACCODED] + 1));
  assume (0 <= R[Ch#count]) && (C[Ch#count] == (R[Ch#count] + 1));
  assume (0 <= R[Ch#St]) && (C[Ch#St] == (R[Ch#St] + 1));
  assume R[VID] == I[VID];
  assume NEWVOP == 2048bv12;
  assume INTRA == 1024bv12;
  assume NEWVOP == 2048bv12;
  assume ACCODED == 2bv12;
  assume ((R[BTYPE] - I[BTYPE]) > 0) && (AT#BvAnd12(M[BTYPE][I[BTYPE]], INTRA) != 0bv12) && ((R[TEX] - I[TEX]) < 64) ==> (St == 1);
  assume (C[MOT] - I[MOT]) == 0;
  assume (C[TEX] - I[TEX]) == 64;
  assume (C[BTYPE] - I[BTYPE]) == 1;
  assume AT#BvAnd12(M[BTYPE][I[BTYPE]], INTRA) != 0bv12;
  assume !(true && (!(true && (((St == 1) || (St == 2)) || (St == 3)) && (count == 64))) && (1 <= (C[TEX] - R[TEX])) && (St == 1));
  assume !(true && true && (((St == 1) || (St == 2)) || (St == 3)) && (count == 64));
  assume !(true && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], INTRA) != 0bv12))) && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], NEWVOP) != 0bv12))) && (1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], ACCODED) == 0bv12));
  assume !(true && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], NEWVOP) != 0bv12))) && (1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], INTRA) != 0bv12));
  assume !(true && (!(true && (((St == 1) || (St == 2)) || (St == 3)) && (count == 64))) && (1 <= (C[MOT] - R[MOT])) && (St == 2));
  assume !(true && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], ACCODED) == 0bv12))) && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], INTRA) != 0bv12))) && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], NEWVOP) != 0bv12))) && (1 <= (C[BTYPE] - R[BTYPE])) && (((St == 0) || (St == 4)) || (St == 5)));
  assume !(true && (!(true && (((St == 1) || (St == 2)) || (St == 3)) && (count == 64))) && (1 <= (C[MOT] - R[MOT])) && (1 <= (C[TEX] - R[TEX])) && (St == 3));
  assume !(true && (1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], NEWVOP) != 0bv12));
  assert {:msg "Add.cal(20.2): The correct number of tokens might not be produced on output 'VID' (#37)"} (C[VID] - I[VID]) == 64;
  R[VID] := R[VID] + 64;
  I := R;
  assert {:msg "Add.cal(18.12): The actor might not preserve the channel invariant (#38)"} ((R[BTYPE] - I[BTYPE]) > 0) && (AT#BvAnd12(M[BTYPE][I[BTYPE]], INTRA) != 0bv12) && ((R[TEX] - I[TEX]) < 64) ==> (St == 1);
}
procedure Add#contract#anon$1#11()
  modifies C, R, M, I, H, I#sub;
{
  var MOT: Chan (bv9);
  var TEX: Chan (bv9);
  var BTYPE: Chan (bv12);
  var VID: Chan (bv9);
  var Ch#NEWVOP: Chan (bv12);
  var Ch#INTRA: Chan (bv12);
  var Ch#ACCODED: Chan (bv12);
  var Ch#count: Chan (int);
  var Ch#St: Chan (int);
  var NEWVOP: bv12;
  var INTRA: bv12;
  var ACCODED: bv12;
  var count: int;
  var St: int;
  assume (MOT != TEX) && (MOT != VID) && (TEX != VID);
  assume (0 <= I[MOT]) && (I[MOT] <= R[MOT]) && (R[MOT] <= C[MOT]);
  assume (0 <= I[TEX]) && (I[TEX] <= R[TEX]) && (R[TEX] <= C[TEX]);
  assume (0 <= I[BTYPE]) && (I[BTYPE] <= R[BTYPE]) && (R[BTYPE] <= C[BTYPE]);
  assume (0 <= I[VID]) && (I[VID] <= R[VID]) && (R[VID] <= C[VID]);
  assume (0 <= R[Ch#NEWVOP]) && (C[Ch#NEWVOP] == (R[Ch#NEWVOP] + 1));
  assume (0 <= R[Ch#INTRA]) && (C[Ch#INTRA] == (R[Ch#INTRA] + 1));
  assume (0 <= R[Ch#ACCODED]) && (C[Ch#ACCODED] == (R[Ch#ACCODED] + 1));
  assume (0 <= R[Ch#count]) && (C[Ch#count] == (R[Ch#count] + 1));
  assume (0 <= R[Ch#St]) && (C[Ch#St] == (R[Ch#St] + 1));
  assume R[VID] == I[VID];
  assume NEWVOP == 2048bv12;
  assume INTRA == 1024bv12;
  assume NEWVOP == 2048bv12;
  assume ACCODED == 2bv12;
  assume ((R[BTYPE] - I[BTYPE]) > 0) && (AT#BvAnd12(M[BTYPE][I[BTYPE]], INTRA) != 0bv12) && ((R[TEX] - I[TEX]) < 64) ==> (St == 1);
  assume (C[MOT] - I[MOT]) == 64;
  assume (C[TEX] - I[TEX]) == 0;
  assume (C[BTYPE] - I[BTYPE]) == 1;
  assume AT#BvAnd12(M[BTYPE][I[BTYPE]], ACCODED) != 0bv12;
  assume !(true && (!(true && (((St == 1) || (St == 2)) || (St == 3)) && (count == 64))) && (1 <= (C[TEX] - R[TEX])) && (St == 1));
  assume !(true && true && (((St == 1) || (St == 2)) || (St == 3)) && (count == 64));
  assume !(true && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], INTRA) != 0bv12))) && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], NEWVOP) != 0bv12))) && (1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], ACCODED) == 0bv12));
  assume !(true && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], NEWVOP) != 0bv12))) && (1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], INTRA) != 0bv12));
  assume !(true && (!(true && (((St == 1) || (St == 2)) || (St == 3)) && (count == 64))) && (1 <= (C[MOT] - R[MOT])) && (St == 2));
  assume !(true && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], ACCODED) == 0bv12))) && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], INTRA) != 0bv12))) && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], NEWVOP) != 0bv12))) && (1 <= (C[BTYPE] - R[BTYPE])) && (((St == 0) || (St == 4)) || (St == 5)));
  assume !(true && (!(true && (((St == 1) || (St == 2)) || (St == 3)) && (count == 64))) && (1 <= (C[MOT] - R[MOT])) && (1 <= (C[TEX] - R[TEX])) && (St == 3));
  assume !(true && (1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], NEWVOP) != 0bv12));
  assert {:msg "Add.cal(24.2): The correct number of tokens might not be produced on output 'VID' (#39)"} (C[VID] - I[VID]) == 64;
  R[VID] := R[VID] + 64;
  I := R;
  assert {:msg "Add.cal(18.12): The actor might not preserve the channel invariant (#40)"} ((R[BTYPE] - I[BTYPE]) > 0) && (AT#BvAnd12(M[BTYPE][I[BTYPE]], INTRA) != 0bv12) && ((R[TEX] - I[TEX]) < 64) ==> (St == 1);
}
procedure Add#contract#anon$2#12()
  modifies C, R, M, I, H, I#sub;
{
  var MOT: Chan (bv9);
  var TEX: Chan (bv9);
  var BTYPE: Chan (bv12);
  var VID: Chan (bv9);
  var Ch#NEWVOP: Chan (bv12);
  var Ch#INTRA: Chan (bv12);
  var Ch#ACCODED: Chan (bv12);
  var Ch#count: Chan (int);
  var Ch#St: Chan (int);
  var NEWVOP: bv12;
  var INTRA: bv12;
  var ACCODED: bv12;
  var count: int;
  var St: int;
  assume (MOT != TEX) && (MOT != VID) && (TEX != VID);
  assume (0 <= I[MOT]) && (I[MOT] <= R[MOT]) && (R[MOT] <= C[MOT]);
  assume (0 <= I[TEX]) && (I[TEX] <= R[TEX]) && (R[TEX] <= C[TEX]);
  assume (0 <= I[BTYPE]) && (I[BTYPE] <= R[BTYPE]) && (R[BTYPE] <= C[BTYPE]);
  assume (0 <= I[VID]) && (I[VID] <= R[VID]) && (R[VID] <= C[VID]);
  assume (0 <= R[Ch#NEWVOP]) && (C[Ch#NEWVOP] == (R[Ch#NEWVOP] + 1));
  assume (0 <= R[Ch#INTRA]) && (C[Ch#INTRA] == (R[Ch#INTRA] + 1));
  assume (0 <= R[Ch#ACCODED]) && (C[Ch#ACCODED] == (R[Ch#ACCODED] + 1));
  assume (0 <= R[Ch#count]) && (C[Ch#count] == (R[Ch#count] + 1));
  assume (0 <= R[Ch#St]) && (C[Ch#St] == (R[Ch#St] + 1));
  assume R[VID] == I[VID];
  assume NEWVOP == 2048bv12;
  assume INTRA == 1024bv12;
  assume NEWVOP == 2048bv12;
  assume ACCODED == 2bv12;
  assume ((R[BTYPE] - I[BTYPE]) > 0) && (AT#BvAnd12(M[BTYPE][I[BTYPE]], INTRA) != 0bv12) && ((R[TEX] - I[TEX]) < 64) ==> (St == 1);
  assume (C[MOT] - I[MOT]) == 64;
  assume (C[TEX] - I[TEX]) == 64;
  assume (C[BTYPE] - I[BTYPE]) == 1;
  assume !(AT#BvAnd12(M[BTYPE][I[BTYPE]], NEWVOP) != 0bv12);
  assume !(AT#BvAnd12(M[BTYPE][I[BTYPE]], ACCODED) != 0bv12);
  assume !(AT#BvAnd12(M[BTYPE][I[BTYPE]], INTRA) != 0bv12);
  assume !(true && (!(true && (((St == 1) || (St == 2)) || (St == 3)) && (count == 64))) && (1 <= (C[TEX] - R[TEX])) && (St == 1));
  assume !(true && true && (((St == 1) || (St == 2)) || (St == 3)) && (count == 64));
  assume !(true && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], INTRA) != 0bv12))) && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], NEWVOP) != 0bv12))) && (1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], ACCODED) == 0bv12));
  assume !(true && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], NEWVOP) != 0bv12))) && (1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], INTRA) != 0bv12));
  assume !(true && (!(true && (((St == 1) || (St == 2)) || (St == 3)) && (count == 64))) && (1 <= (C[MOT] - R[MOT])) && (St == 2));
  assume !(true && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], ACCODED) == 0bv12))) && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], INTRA) != 0bv12))) && (!((1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], NEWVOP) != 0bv12))) && (1 <= (C[BTYPE] - R[BTYPE])) && (((St == 0) || (St == 4)) || (St == 5)));
  assume !(true && (!(true && (((St == 1) || (St == 2)) || (St == 3)) && (count == 64))) && (1 <= (C[MOT] - R[MOT])) && (1 <= (C[TEX] - R[TEX])) && (St == 3));
  assume !(true && (1 <= (C[BTYPE] - R[BTYPE])) && (St == 0) && (AT#BvAnd12(M[BTYPE][R[BTYPE]], NEWVOP) != 0bv12));
  assert {:msg "Add.cal(28.2): The correct number of tokens might not be produced on output 'VID' (#41)"} (C[VID] - I[VID]) == 64;
  R[VID] := R[VID] + 64;
  I := R;
  assert {:msg "Add.cal(18.12): The actor might not preserve the channel invariant (#42)"} ((R[BTYPE] - I[BTYPE]) > 0) && (AT#BvAnd12(M[BTYPE][I[BTYPE]], INTRA) != 0bv12) && ((R[TEX] - I[TEX]) < 64) ==> (St == 1);
}

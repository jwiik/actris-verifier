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
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------


function {:bvbuiltin "bvand"} AT#BvAnd(a: bv32, b: bv32): bv32;
function {:bvbuiltin "bvadd"} AT#BvAdd(a: bv32, b: bv32): bv32;
function {:bvbuiltin "bvsub"} AT#BvSub(a: bv32, b: bv32): bv32;
function {:bvbuiltin "bvule"} AT#BvUle(a: bv32, b: bv32): bool;
function {:bvbuiltin "bvult"} AT#BvUlt(a: bv32, b: bv32): bool;
function AT#RShift(bv32,bv32): bv32;
function AT#LShift(bv32,bv32): bv32;
procedure Shift#init#0()
  modifies C, R, M, I, H;
{
  var In: Chan (bv32);
  var Out: Chan (bv32);
  assume In != Out;
  assume R[In] == 0;
  assume C[Out] == 0;
  assert {:msg "2.20: Initialization might not establish the invariant (#0)"} 0 < R[In] ==> (M[Out][C[Out] - 1] == AT#LShift(M[In][R[In] - 1], 2bv32));
}
procedure Shift#anon$0#1()
  modifies C, R, M, I, H;
{
  var In: Chan (bv32);
  var Out: Chan (bv32);
  var In#0: bv32;
  assume In != Out;
  
  assume 0 <= R[In];
  assume 0 <= C[Out];
  assume 0 < R[In] ==> (M[Out][C[Out] - 1] == AT#LShift(M[In][R[In] - 1], 2bv32));
  In#0 := M[In][R[In]];
  R[In] := R[In] + 1;
  M[Out][C[Out]] := AT#LShift(In#0, 2bv32);
  C[Out] := C[Out]+1;
  assert {:msg "2.20: Action at 3.3 might not preserve invariant (#1)"} 0 < R[In] ==> (M[Out][C[Out] - 1] == AT#LShift(M[In][R[In] - 1], 2bv32));
}

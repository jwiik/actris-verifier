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
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

procedure Sum#init#0()
  modifies C, R, M, I, H;
{
  var x: Chan (int);
  var y: Chan (int);
  var Ch#sum: Chan (int);
  var sum: int;
  assume x != y;
  assume R[x] == 0;
  assume C[y] == 0;
  assume (R[Ch#sum] == 0) && (C[Ch#sum] == 0);
  sum := 0;
}
procedure Sum#anon$1#1()
  modifies C, R, M, I, H;
{
  var x: Chan (int);
  var y: Chan (int);
  var Ch#sum: Chan (int);
  var sum: int;
  var x#0: int;
  assume x != y;
  assume 0 <= R[x];
  assume 0 <= C[y];
  assume (0 <= R[Ch#sum]) && (C[Ch#sum] == (R[Ch#sum] + 1));
  assume R[x] == C[y];
  x#0 := M[x][R[x]];
  R[x] := R[x] + 1;
  assume 0 <= x#0;
  sum := sum + x#0;
  assert {:msg "Sum_ContractAction.actor(17.13): Action postcondition might not hold (#0)"} x#0 <= sum;
  M[y][C[y]] := sum;
  C[y] := C[y] + 1;
}

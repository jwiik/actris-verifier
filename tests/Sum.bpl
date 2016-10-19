// ---------------------------------------------------------------
// -- Types and global variables ---------------------------------
// ---------------------------------------------------------------
type Chan a;
type Actor;
type CType = <a>[Chan a]int;
type MType = <a>[Chan a][int]a;
type State;

var M: MType;
var C: CType;
var R: CType;
var I: CType;
var St: [Actor]State;

const unique this#: Actor;
type List a = [int]a;
var AT#intlst: List int;

function AT#Min(x:int, y: int): int { if x <= y then x else y }

// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

procedure Sum#init#0()
  modifies C, R, M, I, St;
{
  var x: Chan (int);
  var y: Chan (int);
  var sum: int;
  assume x != y;
  assume R[x] == 0;
  assume C[y] == 0;
  sum := 0;
  assert {:msg "3.13: Initialization might not establish the invariant (#0)"} 0 <= sum;
}
procedure Sum#anon$1#1()
  modifies C, R, M, I, St;
{
  var x: Chan (int);
  var y: Chan (int);
  var sum: int;
  var x#0: int;
  assume x != y;
  assume 0 <= R[x];
  assume 0 <= C[y];
  assume 0 <= sum;
  x#0 := M[x][R[x]];
  R[x] := R[x] + 1;
  assume 0 <= x#0;
  sum := sum + x#0;
  assert {:msg "9.13: Action postcondition might not hold (#1)"} x#0 <= sum;
  M[y][C[y]] := sum;
  C[y] := C[y] + 1;
  assert {:msg "3.13: Action at 7.3 might not preserve invariant (#2)"} 0 <= sum;
}

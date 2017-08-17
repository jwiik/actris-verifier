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
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

procedure Procedure#init#0()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var x: Chan (int);
  var y: Chan (int);
  var m: int;
  assume x != y;
  assume (I#[x] == 0) && (R#[x] == 0) && (C#[x] == 0);
  assume (I#[y] == 0) && (R#[y] == 0) && (C#[y] == 0);
  assert {:msg "Initialization might not establish the invariant (#0)"} R#[x] == C#[y];
}
procedure Procedure#anon__1#1()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var x: Chan (int);
  var y: Chan (int);
  var m: int;
  var x#0: int;
  var proc#m: int;
  assume x != y;
  assume (0 <= I#[x]) && (I#[x] <= R#[x]) && (R#[x] <= C#[x]);
  assume (0 <= I#[y]) && (I#[y] <= R#[y]) && (R#[y] <= C#[y]);
  assume R#[x] == C#[y];
  assume 1 <= (C#[x] - R#[x]);
  x#0 := M#[x][R#[x]];
  R#[x] := R#[x] + 1;
  assume true;
  m := x#0;
  proc#m := 2 * m;
  m := proc#m + 2;
  M#[y][C#[y]] := m;
  C#[y] := C#[y] + 1;
  assert {:msg "Action 'anon__1' at <unknown_file>(-1.-1) might not preserve the invariant (#1)"} R#[x] == C#[y];
}

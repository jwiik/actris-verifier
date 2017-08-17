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
const List#Empty: Map int int;
function List#Empty<U>(U): Map int U;
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
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

procedure ForEach#init#0()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var x: Chan (int);
  var y: Chan (int);
  var list: Map (int) (int);
  assume x != y;
  assume (I#[x] == 0) && (R#[x] == 0) && (C#[x] == 0);
  assume (I#[y] == 0) && (R#[y] == 0) && (C#[y] == 0);
  assert {:msg "Initialization might not establish the invariant (#0)"} R#[x] == C#[y];
}
procedure ForEach#anon__3#1()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var x: Chan (int);
  var y: Chan (int);
  var list: Map (int) (int);
  var x#0: int;
  var sum: int;
  var s: int;
  assume x != y;
  assume (0 <= I#[x]) && (I#[x] <= R#[x]) && (R#[x] <= C#[x]);
  assume (0 <= I#[y]) && (I#[y] <= R#[y]) && (R#[y] <= C#[y]);
  assume R#[x] == C#[y];
  assume 1 <= (C#[x] - R#[x]);
  x#0 := M#[x][R#[x]];
  R#[x] := R#[x] + 1;
  assume true;
  sum := 0;
  s := 0;
  sum := sum + (s * x#0);
  s := 1;
  sum := sum + (s * x#0);
  s := 2;
  sum := sum + (s * x#0);
  s := 3;
  sum := sum + (s * x#0);
  s := 4;
  sum := sum + (s * x#0);
  s := 5;
  sum := sum + (s * x#0);
  M#[y][C#[y]] := x#0;
  C#[y] := C#[y] + 1;
  assert {:msg "Action 'anon__3' at <unknown_file>(-1.-1) might not preserve the invariant (#1)"} R#[x] == C#[y];
}

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
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

procedure List1#init#0()
  modifies C, R, M, I, H;
{
  var x: Chan (int);
  var y: Chan (int);
  var test: Map (int) (int);
  assume x != y;
  assume R[x] == 0;
  assume C[y] == 0;
  test := Map#Store(test, 0, 0);
  test := Map#Store(test, 1, 1);
  assert {:msg "5.12: Initialization might not establish the invariant (#0)"} (Map#Select(test, 0) == 0) && (Map#Select(test, 1) == 1);
}
procedure List1#anon$1#1()
  modifies C, R, M, I, H;
{
  var x: Chan (int);
  var y: Chan (int);
  var test: Map (int) (int);
  var x#0: int;
  assume x != y;
  assume 0 <= R[x];
  assume 0 <= C[y];
  assume (Map#Select(test, 0) == 0) && (Map#Select(test, 1) == 1);
  x#0 := M[x][R[x]];
  R[x] := R[x] + 1;
  test := Map#Store(test, 0, 0);
  test := Map#Store(test, 1, 1);
  M[y][C[y]] := x#0;
  C[y] := C[y] + 1;
  assert {:msg "5.12: Action at 13.2 might not preserve invariant (#1)"} (Map#Select(test, 0) == 0) && (Map#Select(test, 1) == 1);
}

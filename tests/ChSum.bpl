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

function AT#ChSum(MType, Chan int, int): int;
axiom (
  forall mm: MType, ch: Chan int, limit: int :: {AT#ChSum(mm,ch,limit)} {AT#ChSum(mm,ch,limit-1)} 
    (limit > 0 ==> AT#ChSum(mm,ch,limit) == mm[ch][limit-1]+AT#ChSum(mm,ch,limit-1)) &&
    (limit == 0 ==> AT#ChSum(mm,ch,limit) == 0)
);
axiom (
  forall mm: MType, ch: Chan int :: {AT#ChSum(mm,ch,0)} 
    AT#ChSum(mm,ch,0) == 0
);

// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

procedure ChSum#init#0()
  modifies C, R, M, I, H;
{
  var x: Chan (int);
  var y: Chan (int);
  var sum: int;
  assume x != y;
  assume R[x] == 0;
  assume C[y] == 0;
  sum := 0;
  assert {:msg "3.13: Initialization might not establish the invariant (#0)"} R[x] == C[y];
  assert {:msg "4.13: Initialization might not establish the invariant (#1)"} (C[y] > 0) ==> (M[y][C[y] - 1] == AT#ChSum(M, x, R[x]));
}
procedure ChSum#anon$1#1()
  modifies C, R, M, I, H;
{
  var x: Chan (int);
  var y: Chan (int);
  var sum: int;
  var x#0: int;
  assume x != y;
  assume 0 <= R[x];
  assume 0 <= C[y];
  assume R[x] == C[y];
  assume (C[y] > 0) ==> (M[y][C[y] - 1] == AT#ChSum(M, x, R[x]));
  x#0 := M[x][R[x]];
  R[x] := R[x] + 1;
  sum := sum + x#0;
  M[y][C[y]] := sum;
  C[y] := C[y] + 1;
  assert {:msg "3.13: Action at 11.3 might not preserve invariant (#2)"} R[x] == C[y];
  assert {:msg "4.13: Action at 11.3 might not preserve invariant (#3)"} (C[y] > 0) ==> (M[y][C[y] - 1] == AT#ChSum(M, x, R[x]));
}

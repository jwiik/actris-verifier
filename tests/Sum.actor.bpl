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

procedure Sum#anon__11#init#0()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var x: Chan (int);
  var y: Chan (int);
  var sum#ch: Chan (int);
  var sum: int;
  assume (x != y) && (x != sum#ch) && (y != sum#ch);
  assume (0 <= I#[x]) && (I#[x] <= R#[x]) && (R#[x] <= C#[x]);
  assume (0 <= I#[y]) && (I#[y] <= R#[y]) && (R#[y] <= C#[y]);
  assume (0 <= I#[sum#ch]) && (I#[sum#ch] <= R#[sum#ch]) && (R#[sum#ch] <= C#[sum#ch]);
  assume (I#[x] == 0) && (R#[x] == 0) && (C#[x] == 0);
  assume (I#[y] == 0) && (R#[y] == 0) && (C#[y] == 0);
  assume (I#[sum#ch] == 0) && (R#[sum#ch] == 0) && (C#[sum#ch] == 0);
  sum := 0;
  M#[sum#ch][C#[sum#ch]] := sum;
  C#[sum#ch] := C#[sum#ch] + 1;
  assert {:msg "Sum.actor(4.13): Initialization might not establish the invariant (#0)"} 0 <= sum;
  assert {:msg "Sum.actor(5.13): Initialization might not establish the invariant (#1)"} (R#[x] > 0) ==> (sum == M#[y][C#[y] - 1]);
  assert {:msg "Sum.actor(6.13): Initialization might not establish the invariant (#2)"} (R#[x] == 0) ==> (sum == 0);
  assert {:msg "Sum.actor(7.20): Initialization might not establish the invariant (#3)"} R#[x] == C#[y];
  assert {:msg "Sum.actor(8.20): Initialization might not establish the invariant (#4)"} (C#[y] > 0) ==> (M#[y][0] == M#[x][0]);
  assert {:msg "Sum.actor(9.21): Initialization might not establish the invariant (#5)"} (forall i: int :: 
    (0 <= i) && (i < C#[y]) ==> (M#[y][i] >= M#[x][i])
  );
  assert {:msg "Sum.actor(10.21): Initialization might not establish the invariant (#6)"} (forall i: int :: 
    ((0 + 1) <= i) && (i < (C#[y] - 0)) ==> (M#[y][i] == (M#[y][i - 1] + M#[x][i]))
  );
  assert {:msg "Initialization might not establish the invariant (#7)"} R#[x] == C#[y];
}
procedure Sum#anon__12#1()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var x: Chan (int);
  var y: Chan (int);
  var sum#ch: Chan (int);
  var sum: int;
  var x#0: int;
  assume (x != y) && (x != sum#ch) && (y != sum#ch);
  assume (0 <= I#[x]) && (I#[x] <= R#[x]) && (R#[x] <= C#[x]);
  assume (0 <= I#[y]) && (I#[y] <= R#[y]) && (R#[y] <= C#[y]);
  assume (0 <= I#[sum#ch]) && (I#[sum#ch] <= R#[sum#ch]) && (R#[sum#ch] <= C#[sum#ch]);
  assume (R#[sum#ch] + 1) == C#[sum#ch];
  assume 0 <= sum;
  assume (R#[x] > 0) ==> (sum == M#[y][C#[y] - 1]);
  assume (R#[x] == 0) ==> (sum == 0);
  assume R#[x] == C#[y];
  assume (C#[y] > 0) ==> (M#[y][0] == M#[x][0]);
  assume (forall i: int :: 
    (0 <= i) && (i < C#[y]) ==> (M#[y][i] >= M#[x][i])
  );
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C#[y] - 0)) ==> (M#[y][i] == (M#[y][i - 1] + M#[x][i]))
  );
  assume R#[x] == C#[y];
  assume M#[sum#ch][R#[sum#ch]] == sum;
  R#[sum#ch] := R#[sum#ch] + 1;
  assume 1 <= (C#[x] - R#[x]);
  x#0 := M#[x][R#[x]];
  R#[x] := R#[x] + 1;
  assume 0 <= x#0;
  assume true;
  sum := sum + x#0;
  assert {:msg "Action postcondition might not hold (#8)"} x#0 <= sum;
  assert {:msg "Action postcondition might not hold (#9)"} sum == (M#[sum#ch][R#[sum#ch] - 1] + x#0);
  M#[y][C#[y]] := sum;
  C#[y] := C#[y] + 1;
  M#[sum#ch][C#[sum#ch]] := sum;
  C#[sum#ch] := C#[sum#ch] + 1;
  assert {:msg "Sum.actor(4.13): Action 'anon__12' at Sum.actor(15.3) might not preserve the invariant (#10)"} 0 <= sum;
  assert {:msg "Sum.actor(5.13): Action 'anon__12' at Sum.actor(15.3) might not preserve the invariant (#11)"} (R#[x] > 0) ==> (sum == M#[y][C#[y] - 1]);
  assert {:msg "Sum.actor(6.13): Action 'anon__12' at Sum.actor(15.3) might not preserve the invariant (#12)"} (R#[x] == 0) ==> (sum == 0);
  assert {:msg "Sum.actor(7.20): Action 'anon__12' at Sum.actor(15.3) might not preserve the invariant (#13)"} R#[x] == C#[y];
  assert {:msg "Sum.actor(8.20): Action 'anon__12' at Sum.actor(15.3) might not preserve the invariant (#14)"} (C#[y] > 0) ==> (M#[y][0] == M#[x][0]);
  assert {:msg "Sum.actor(9.21): Action 'anon__12' at Sum.actor(15.3) might not preserve the invariant (#15)"} (forall i: int :: 
    (0 <= i) && (i < C#[y]) ==> (M#[y][i] >= M#[x][i])
  );
  assert {:msg "Sum.actor(10.21): Action 'anon__12' at Sum.actor(15.3) might not preserve the invariant (#16)"} (forall i: int :: 
    ((0 + 1) <= i) && (i < (C#[y] - 0)) ==> (M#[y][i] == (M#[y][i - 1] + M#[x][i]))
  );
  assert {:msg "Action 'anon__12' at Sum.actor(15.3) might not preserve the invariant (#17)"} R#[x] == C#[y];
}

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
var L: CType;
var St: [Actor]State;
const Base#L: int;
axiom 1 <= Base#L;

const unique this#: Actor;
type List a = [int]a;
var AT#intlst: List int;

function AT#Min(x:int, y: int): int { if x <= y then x else y }


// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

procedure TimeDep#A#0()
  modifies C, R, M, St;
{
  var IV#in#0: int;
  assume true;
  assume true;
}
procedure TimeDep#B#1()
  modifies C, R, M, St;
{
  var IV#in#0: int;
  var IV#in#1: int;
  assume true;
  assume true;
}
procedure Net#init#2()
  modifies C, R, M, St;
{
  assume C[Net#a] == 0;
  assume R[Net#a] == 0;
  assume C[Net#b] == 0;
  assume R[Net#b] == 0;
}
const unique Net#tp: Actor;
const unique Net#a: Chan (int);
const unique Net#b: Chan (int);
procedure Net#anon$0#entry#3()
  modifies C, R, M, St;
{
  var ActionPH#y: int;
  assume L[Net#a] == (2 * Base#L);
  assume R[Net#a] == 0;
  assume C[Net#a] == 0;
  assume R[Net#b] == 0;
  assume C[Net#b] == 0;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) <= L[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume R[Net#b] == 0;
  assert {:msg "  11.3: Channel invariant might not hold on action entry (#6)"} (2 * (R[Net#b] + C[Net#b])) == R[Net#a];
}
procedure Net#anon$0#TimeDep#B#4()
  modifies C, R, M, St;
{
  var ActionPH#y: int;
  var St#next: State;
  var in#i: int;
  var in#j: int;
  assume L[Net#a] == (2 * Base#L);
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) <= L[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume R[Net#b] == 0;
  assume (2 * (R[Net#b] + C[Net#b])) == R[Net#a];
  assume true;
  assume 2 <= C[Net#a];
  in#i := M[Net#a][R[Net#a]];
  R[Net#a] := R[Net#a] + 1;
  C[Net#a] := C[Net#a] - 1;
  in#j := M[Net#a][R[Net#a]];
  R[Net#a] := R[Net#a] + 1;
  C[Net#a] := C[Net#a] - 1;
  M[Net#b][R[Net#b] + C[Net#b]] := in#i;
  C[Net#b] := C[Net#b] + 1;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) <= L[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume R[Net#b] == 0;
  assert {:msg "  11.3: Action at 3.3 ('B') for actor instance 'tp' might not preserve the channel invariant (#13)"} (2 * (R[Net#b] + C[Net#b])) == R[Net#a];
}
procedure Net#anon$0#TimeDep#A#5()
  modifies C, R, M, St;
{
  var ActionPH#y: int;
  var St#next: State;
  var in#i: int;
  assume L[Net#a] == (2 * Base#L);
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) <= L[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume R[Net#b] == 0;
  assume (2 * (R[Net#b] + C[Net#b])) == R[Net#a];
  assume true;
  assume (!(2 <= C[Net#a])) && (1 <= C[Net#a]);
  in#i := M[Net#a][R[Net#a]];
  R[Net#a] := R[Net#a] + 1;
  C[Net#a] := C[Net#a] - 1;
  M[Net#b][R[Net#b] + C[Net#b]] := in#i;
  C[Net#b] := C[Net#b] + 1;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) <= L[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume R[Net#b] == 0;
  assert {:msg "  11.3: Action at 2.3 ('A') for actor instance 'tp' might not preserve the channel invariant (#20)"} (2 * (R[Net#b] + C[Net#b])) == R[Net#a];
}
procedure Net#anon$0#exit#6()
  modifies C, R, M, St;
{
  var ActionPH#y: int;
  assume L[Net#a] == (2 * Base#L);
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) <= L[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume R[Net#b] == 0;
  assume (2 * (R[Net#b] + C[Net#b])) == R[Net#a];
  assume !((R[Net#a] + C[Net#a]) < L[Net#a]);
  assume !((!(2 <= C[Net#a])) && (1 <= C[Net#a]));
  assume !(2 <= C[Net#a]);
  ActionPH#y := M[Net#b][0];
  R[Net#b] := R[Net#b] + C[Net#b];
  C[Net#b] := C[Net#b] - (1 * Base#L);
  assert {:msg "  9.3: The network might leave unread tokens on channel a"} C[Net#a] == 0;
  assert {:msg "  9.3: The network might not produce the specified number of tokens on output out"} C[Net#b] == 0;
}

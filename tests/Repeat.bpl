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
var I: CType;
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

procedure Repeater#anon$0#0()
  modifies C, R, M, I, St;
{
  var in: Chan (int);
  var out: Chan (int);
  assume true;
  assume true;
}
procedure Net#init#1()
  modifies C, R, M, I, St;
{
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume I[Net#b] == R[Net#b];
  assume C[Net#a] == 0;
  assume R[Net#a] == 0;
  assume C[Net#b] == 0;
  assume R[Net#b] == 0;
  assert {:msg "  9.15: Network initialization might not establish the channel invariant (#0)"} (2 * I[Net#a]) == I[Net#b];
  assert {:msg "  10.15: Network initialization might not establish the channel invariant (#1)"} C[Net#b] == (2 * R[Net#a]);
}
const unique Net#rep: Actor;
const unique Net#a: Chan (int);
const unique Net#b: Chan (int);
procedure Net#anon$1#input#in#2()
  modifies C, R, M, I, St;
{
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume I[Net#b] == R[Net#b];
  assume (2 * I[Net#a]) == I[Net#b];
  assume C[Net#b] == (2 * R[Net#a]);
  C[Net#a] := C[Net#a] + 1;
  assert {:msg "  9.15: Channel invariant might be falsified by network input (#2)"} (2 * I[Net#a]) == I[Net#b];
  assert {:msg "  10.15: Channel invariant might be falsified by network input (#3)"} C[Net#b] == (2 * R[Net#a]);
}
procedure Net#anon$1#Repeater#anon$0#3()
  modifies C, R, M, I, St;
{
  var St#next: State;
  var in#i: int;
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume I[Net#b] == R[Net#b];
  assume (2 * I[Net#a]) == I[Net#b];
  assume C[Net#b] == (2 * R[Net#a]);
  assume true;
  assume 1 <= (C[Net#a] - R[Net#a]);
  in#i := M[Net#a][R[Net#a]];
  R[Net#a] := R[Net#a] + 1;
  M[Net#b][C[Net#b]] := in#i;
  C[Net#b] := C[Net#b] + 1;
  M[Net#b][C[Net#b]] := in#i;
  C[Net#b] := C[Net#b] + 1;
  assert {:msg "  9.15: Action at 2.3 ('anon$0') for actor instance 'rep' might not preserve the channel invariant (#4)"} (2 * I[Net#a]) == I[Net#b];
  assert {:msg "  10.15: Action at 2.3 ('anon$0') for actor instance 'rep' might not preserve the channel invariant (#5)"} C[Net#b] == (2 * R[Net#a]);
}
procedure Net#anon$1#exit#4()
  modifies C, R, M, I, St;
{
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume I[Net#b] == R[Net#b];
  assume L[Net#a] == (1 * Base#L);
  assume (C[Net#a] - I[Net#a]) <= L[Net#a];
  assume (2 * I[Net#a]) == I[Net#b];
  assume C[Net#b] == (2 * R[Net#a]);
  assume !((C[Net#a] - I[Net#a]) < L[Net#a]);
  assume !(1 <= (C[Net#a] - R[Net#a]));
  R[Net#b] := R[Net#b] + (2 * Base#L);
  I := R;
  assert {:msg "  9.15: The network might not preserve the channel invariant (#6)"} (2 * I[Net#a]) == I[Net#b];
  assert {:msg "  10.15: The network might not preserve the channel invariant (#7)"} C[Net#b] == (2 * R[Net#a]);
  assert {:msg "  7.3: The network might leave unread tokens on channel a"} (C[Net#a] - R[Net#a]) == 0;
  assert {:msg "  7.3: The network might not produce the specified number of tokens on output out"} (C[Net#b] - R[Net#b]) == 0;
}

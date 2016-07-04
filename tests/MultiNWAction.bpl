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

procedure Split#anon$0#0()
  modifies C, R, M, St;
{
  var IV#in#0: int;
  assume true;
  assume 0 <= IV#in#0;
  assume true;
}
procedure Split#anon$1#1()
  modifies C, R, M, St;
{
  var IV#in#0: int;
  assume true;
  assume IV#in#0 < 0;
  assume true;
}
procedure Net#init#2()
  modifies C, R, M, St;
{
  assume C[Net#a] == 0;
  assume R[Net#a] == 0;
  assume C[Net#b] == 0;
  assume R[Net#b] == 0;
  assume C[Net#c] == 0;
  assume R[Net#c] == 0;
}
const unique Net#spl: Actor;
const unique Net#a: Chan (int);
const unique Net#b: Chan (int);
const unique Net#c: Chan (int);
procedure Net#anon$2#entry#3()
  modifies C, R, M, St;
{
  var Net#out1#0: int;
  assume L[Net#a] == (1 * Base#L);
  assume R[Net#a] == 0;
  assume C[Net#a] == 0;
  assume R[Net#b] == 0;
  assume C[Net#b] == 0;
  assume R[Net#c] == 0;
  assume C[Net#c] == 0;
  assume 0 <= M[Net#a][0];
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) <= L[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume R[Net#b] == 0;
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume R[Net#c] == 0;
}
procedure Net#anon$2#Split#anon$0#4()
  modifies C, R, M, St;
{
  var Net#out1#0: int;
  var St#next: State;
  var in#i: int;
  assume L[Net#a] == (1 * Base#L);
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) <= L[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume R[Net#b] == 0;
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume R[Net#c] == 0;
  assume 0 <= M[Net#a][R[Net#a] - 0];
  assume true;
  assume (1 <= C[Net#a]) && (0 <= M[Net#a][R[Net#a] - 0]);
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
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume R[Net#c] == 0;
}
procedure Net#anon$2#Split#anon$1#5()
  modifies C, R, M, St;
{
  var Net#out1#0: int;
  var St#next: State;
  var in#i: int;
  assume L[Net#a] == (1 * Base#L);
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) <= L[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume R[Net#b] == 0;
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume R[Net#c] == 0;
  assume M[Net#a][R[Net#a] - 0] < 0;
  assume true;
  assume (1 <= C[Net#a]) && (M[Net#a][R[Net#a] - 0] < 0);
  in#i := M[Net#a][R[Net#a]];
  R[Net#a] := R[Net#a] + 1;
  C[Net#a] := C[Net#a] - 1;
  M[Net#c][R[Net#c] + C[Net#c]] := in#i;
  C[Net#c] := C[Net#c] + 1;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) <= L[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume R[Net#b] == 0;
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume R[Net#c] == 0;
}
procedure Net#anon$2#exit#6()
  modifies C, R, M, St;
{
  var Net#out1#0: int;
  assume L[Net#a] == (1 * Base#L);
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) <= L[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume R[Net#b] == 0;
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume R[Net#c] == 0;
  assume !((R[Net#a] + C[Net#a]) < L[Net#a]);
  assume !((1 <= C[Net#a]) && (0 <= M[Net#a][R[Net#a] - 0]));
  assume !((1 <= C[Net#a]) && (M[Net#a][R[Net#a] - 0] < 0));
  Net#out1#0 := M[Net#b][0];
  assert {:msg "  12.27: Network output might not conform to the specified action output"} Net#out1#0 == M[Net#a][0];
  R[Net#b] := R[Net#b] + C[Net#b];
  C[Net#b] := C[Net#b] - (1 * Base#L);
  R[Net#c] := R[Net#c] + C[Net#c];
  C[Net#c] := C[Net#c] - (0 * Base#L);
  assert {:msg "  12.3: The network might leave unread tokens on channel a"} C[Net#a] == 0;
  assert {:msg "  12.3: The network might not produce the specified number of tokens on output out1"} C[Net#b] == 0;
  assert {:msg "  12.3: The network might not produce the specified number of tokens on output out2"} C[Net#c] == 0;
}
const unique Net#spl: Actor;
const unique Net#a: Chan (int);
const unique Net#b: Chan (int);
const unique Net#c: Chan (int);
procedure Net#anon$3#entry#7()
  modifies C, R, M, St;
{
  var Net#out2#0: int;
  assume L[Net#a] == (1 * Base#L);
  assume R[Net#a] == 0;
  assume C[Net#a] == 0;
  assume R[Net#b] == 0;
  assume C[Net#b] == 0;
  assume R[Net#c] == 0;
  assume C[Net#c] == 0;
  assume M[Net#a][0] < 0;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) <= L[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume R[Net#b] == 0;
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume R[Net#c] == 0;
}
procedure Net#anon$3#Split#anon$0#8()
  modifies C, R, M, St;
{
  var Net#out2#0: int;
  var St#next: State;
  var in#i: int;
  assume L[Net#a] == (1 * Base#L);
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) <= L[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume R[Net#b] == 0;
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume R[Net#c] == 0;
  assume 0 <= M[Net#a][R[Net#a] - 0];
  assume true;
  assume (1 <= C[Net#a]) && (0 <= M[Net#a][R[Net#a] - 0]);
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
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume R[Net#c] == 0;
}
procedure Net#anon$3#Split#anon$1#9()
  modifies C, R, M, St;
{
  var Net#out2#0: int;
  var St#next: State;
  var in#i: int;
  assume L[Net#a] == (1 * Base#L);
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) <= L[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume R[Net#b] == 0;
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume R[Net#c] == 0;
  assume M[Net#a][R[Net#a] - 0] < 0;
  assume true;
  assume (1 <= C[Net#a]) && (M[Net#a][R[Net#a] - 0] < 0);
  in#i := M[Net#a][R[Net#a]];
  R[Net#a] := R[Net#a] + 1;
  C[Net#a] := C[Net#a] - 1;
  M[Net#c][R[Net#c] + C[Net#c]] := in#i;
  C[Net#c] := C[Net#c] + 1;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) <= L[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume R[Net#b] == 0;
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume R[Net#c] == 0;
}
procedure Net#anon$3#exit#10()
  modifies C, R, M, St;
{
  var Net#out2#0: int;
  assume L[Net#a] == (1 * Base#L);
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) <= L[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume R[Net#b] == 0;
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume R[Net#c] == 0;
  assume !((R[Net#a] + C[Net#a]) < L[Net#a]);
  assume !((1 <= C[Net#a]) && (0 <= M[Net#a][R[Net#a] - 0]));
  assume !((1 <= C[Net#a]) && (M[Net#a][R[Net#a] - 0] < 0));
  Net#out2#0 := M[Net#c][0];
  assert {:msg "  15.27: Network output might not conform to the specified action output"} Net#out2#0 == M[Net#a][0];
  R[Net#b] := R[Net#b] + C[Net#b];
  C[Net#b] := C[Net#b] - (0 * Base#L);
  R[Net#c] := R[Net#c] + C[Net#c];
  C[Net#c] := C[Net#c] - (1 * Base#L);
  assert {:msg "  15.3: The network might leave unread tokens on channel a"} C[Net#a] == 0;
  assert {:msg "  15.3: The network might not produce the specified number of tokens on output out1"} C[Net#b] == 0;
  assert {:msg "  15.3: The network might not produce the specified number of tokens on output out2"} C[Net#c] == 0;
}

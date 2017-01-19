// ---------------------------------------------------------------
// -- Types and global variables ---------------------------------
// ---------------------------------------------------------------
type Chan;
type Field a;
type Actor;
type CType = [Chan]int;
type MType = <a>[Chan][int][Field a]a;
type State;

var M: MType;
var C: CType;
var R: CType;
var I: CType;

const unique this#: Actor;

const unique data#int: Field int;
const unique data#bool: Field bool;

type List a = [int]a;
var AT#intlst: List int;

function AT#Min(x:int, y: int): int { if x <= y then x else y }

// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

procedure Add#init#0()
  modifies C, R, M, I;
{
  var in1: Chan;
  var in2: Chan;
  var out: Chan;
  assume (in1 != in2) && (in1 != out) && (in2 != out);
  assume R[in1] == 0;
  assume R[in2] == 0;
  assume C[out] == 0;
}
procedure Add#anon$0#1()
  modifies C, R, M, I;
{
  var in1: Chan;
  var in2: Chan;
  var out: Chan;
  var in1#0: int;
  var in2#0: int;
  assume (in1 != in2) && (in1 != out) && (in2 != out);
  assume 0 <= R[in1];
  assume 0 <= R[in2];
  assume 0 <= C[out];
  in1#0 := M[in1][R[in1]][data#int];
  R[in1] := R[in1] + 1;
  in2#0 := M[in2][R[in2]][data#int];
  R[in2] := R[in2] + 1;
  M[out][C[out]][data#int] := in1#0 + in2#0;
  C[out] := C[out] + 1;
}
procedure Net#init#2()
  modifies C, R, M, I;
{
  var Net#add: Actor;
  var Net#a: Chan;
  var Net#a#data: Field (int);
  var Net#b: Chan;
  var Net#b#data: Field (int);
  var Net#c: Chan;
  var Net#c#data: Field (int);
  assume (Net#a != Net#b) && (Net#a != Net#c) && (Net#a#data != Net#b#data) && (Net#a#data != Net#c#data) && (Net#b != Net#c) && (Net#b#data != Net#c#data);
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume 0 <= I[Net#c];
  assume I[Net#c] <= R[Net#c];
  assume R[Net#c] <= C[Net#c];
  assume I[Net#c] == R[Net#c];
  assume C[Net#a] == 0;
  assume R[Net#a] == 0;
  assume C[Net#b] == 0;
  assume R[Net#b] == 0;
  assume C[Net#c] == 0;
  assume R[Net#c] == 0;
  I := R;
  assert {:msg "Initialization of network 'Net' might not establish the network invariant: Unread tokens might be left on channel a (#0)"} (C[Net#a] - R[Net#a]) == 0;
  assert {:msg "Initialization of network 'Net' might not establish the network invariant: Unread tokens might be left on channel b (#1)"} (C[Net#b] - R[Net#b]) == 0;
  assert {:msg "Initialization of network 'Net' might not establish the network invariant: Unread tokens might be left on channel c (#2)"} (C[Net#c] - R[Net#c]) == 0;
}
procedure Net##Add#anon$0#3()
  modifies C, R, M, I;
{
  var Net#add: Actor;
  var Net#a: Chan;
  var Net#a#data: Field (int);
  var Net#b: Chan;
  var Net#b#data: Field (int);
  var Net#c: Chan;
  var Net#c#data: Field (int);
  var in1#i: int;
  var in2#j: int;
  assume (Net#a != Net#b) && (Net#a != Net#c) && (Net#a#data != Net#b#data) && (Net#a#data != Net#c#data) && (Net#b != Net#c) && (Net#b#data != Net#c#data);
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume 0 <= I[Net#c];
  assume I[Net#c] <= R[Net#c];
  assume R[Net#c] <= C[Net#c];
  assume I[Net#c] == R[Net#c];
  assume (1 <= (C[Net#a] - R[Net#a])) && (1 <= (C[Net#b] - R[Net#b]));
  in1#i := M[Net#a][R[Net#a]][data#int];
  R[Net#a] := R[Net#a] + 1;
  in2#j := M[Net#b][R[Net#b]][data#int];
  R[Net#b] := R[Net#b] + 1;
  M[Net#c][C[Net#c]][data#int] := in1#i + in2#j;
  C[Net#c] := C[Net#c] + 1;
}
procedure Net#anon$1#input#in1#4()
  modifies C, R, M, I;
{
  var Net#add: Actor;
  var Net#a: Chan;
  var Net#a#data: Field (int);
  var Net#b: Chan;
  var Net#b#data: Field (int);
  var Net#c: Chan;
  var Net#c#data: Field (int);
  assume (Net#a != Net#b) && (Net#a != Net#c) && (Net#a#data != Net#b#data) && (Net#a#data != Net#c#data) && (Net#b != Net#c) && (Net#b#data != Net#c#data);
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume 0 <= I[Net#c];
  assume I[Net#c] <= R[Net#c];
  assume R[Net#c] <= C[Net#c];
  assume I[Net#c] == R[Net#c];
  assume (C[Net#a] - I[Net#a]) < 1;
  C[Net#a] := C[Net#a] + 1;
}
procedure Net#anon$1#input#in2#5()
  modifies C, R, M, I;
{
  var Net#add: Actor;
  var Net#a: Chan;
  var Net#a#data: Field (int);
  var Net#b: Chan;
  var Net#b#data: Field (int);
  var Net#c: Chan;
  var Net#c#data: Field (int);
  assume (Net#a != Net#b) && (Net#a != Net#c) && (Net#a#data != Net#b#data) && (Net#a#data != Net#c#data) && (Net#b != Net#c) && (Net#b#data != Net#c#data);
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume 0 <= I[Net#c];
  assume I[Net#c] <= R[Net#c];
  assume R[Net#c] <= C[Net#c];
  assume I[Net#c] == R[Net#c];
  assume (C[Net#b] - I[Net#b]) < 1;
  C[Net#b] := C[Net#b] + 1;
}
procedure Net#anon$1#exit#6()
  modifies C, R, M, I;
{
  var Net#add: Actor;
  var Net#a: Chan;
  var Net#a#data: Field (int);
  var Net#b: Chan;
  var Net#b#data: Field (int);
  var Net#c: Chan;
  var Net#c#data: Field (int);
  assume (Net#a != Net#b) && (Net#a != Net#c) && (Net#a#data != Net#b#data) && (Net#a#data != Net#c#data) && (Net#b != Net#c) && (Net#b#data != Net#c#data);
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume 0 <= I[Net#c];
  assume I[Net#c] <= R[Net#c];
  assume R[Net#c] <= C[Net#c];
  assume I[Net#c] == R[Net#c];
  assume (C[Net#a] - I[Net#a]) == 1;
  assume (C[Net#b] - I[Net#b]) == 1;
  assume !((1 <= (C[Net#a] - R[Net#a])) && (1 <= (C[Net#b] - R[Net#b])));
  R[Net#c] := R[Net#c] + 1;
  I := R;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel a (#3)"} (C[Net#a] - R[Net#a]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel b (#4)"} (C[Net#b] - R[Net#b]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel c (#5)"} (C[Net#c] - R[Net#c]) == 0;
}

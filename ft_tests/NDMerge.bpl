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

// -- Sequence numbering for FT ----------------------------------
const unique sqn#: Field int;

// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

procedure NonDetMerge#init#0()
  modifies C, R, M, I, H;
{
  var x1: Chan (int);
  var x2: Chan (int);
  var y: Chan (int);
  assume (x1 != x2) && (x1 != y) && (x2 != y);
  assume R[x1] == 0;
  assume R[x2] == 0;
  assume C[y] == 0;
  assert {:msg "3.20: Initialization might not establish the invariant (#0)"} C[y] == (R[x1] + R[x2]);
}
procedure NonDetMerge#a1#1()
  modifies C, R, M, I, H;
{
  var x1: Chan (int);
  var x2: Chan (int);
  var y: Chan (int);
  var x1#0: int;
  var x2#0: int;
  assume (x1 != x2) && (x1 != y) && (x2 != y);
  assume 0 <= R[x1];
  assume 0 <= R[x2];
  assume 0 <= C[y];
  assume C[y] == (R[x1] + R[x2]);
  x1#0 := M[x1][R[x1]];
  R[x1] := R[x1] + 1;
  M[y][C[y]] := x1#0;
  C[y] := C[y] + 1;
  assert {:msg "3.20: Action at 5.3 might not preserve invariant (#1)"} C[y] == (R[x1] + R[x2]);
}
procedure NonDetMerge#a2#2()
  modifies C, R, M, I, H;
{
  var x1: Chan (int);
  var x2: Chan (int);
  var y: Chan (int);
  var x1#0: int;
  var x2#0: int;
  assume (x1 != x2) && (x1 != y) && (x2 != y);
  assume 0 <= R[x1];
  assume 0 <= R[x2];
  assume 0 <= C[y];
  assume C[y] == (R[x1] + R[x2]);
  x2#0 := M[x2][R[x2]];
  R[x2] := R[x2] + 1;
  M[y][C[y]] := x2#0;
  C[y] := C[y] + 1;
  assert {:msg "3.20: Action at 6.3 might not preserve invariant (#2)"} C[y] == (R[x1] + R[x2]);
}
procedure NonDetMerge##GuardWD#3()
  modifies C, R, M, I, H;
{
  var x1: Chan (int);
  var x2: Chan (int);
  var y: Chan (int);
  var x1#0: int;
  var x2#0: int;
  assume (x1 != x2) && (x1 != y) && (x2 != y);
  assert {:msg "1.1: The actions 'a1' and 'a2' of actor 'NonDetMerge' might not have mutually exclusive guards (#3)"} !(true && (1 <= (C[x1] - R[x1])) && true && true && (1 <= (C[x2] - R[x2])) && true);
}
procedure Top#init#4()
  modifies C, R, M, I, H;
{
  var Top#ndm: Actor;
  var Top#a: Chan (int);
  var Top#b: Chan (int);
  var Top#c: Chan (int);
  assume (Top#a != Top#b) && (Top#a != Top#c) && (Top#b != Top#c);
  assume 0 <= I[Top#a];
  assume I[Top#a] <= R[Top#a];
  assume R[Top#a] <= C[Top#a];
  assume 0 <= I[Top#b];
  assume I[Top#b] <= R[Top#b];
  assume R[Top#b] <= C[Top#b];
  assume 0 <= I[Top#c];
  assume I[Top#c] <= R[Top#c];
  assume R[Top#c] <= C[Top#c];
  assume I[Top#c] == R[Top#c];
  assume C[Top#a] == 0;
  assume R[Top#a] == 0;
  assume C[Top#b] == 0;
  assume R[Top#b] == 0;
  assume C[Top#c] == 0;
  assume R[Top#c] == 0;
  assert {:msg "20.15: Initialization of network 'Top' might not establish the channel invariant (#4)"} ((C[Top#c] - I[Top#c]) > 0) && ((R[Top#b] - I[Top#b]) == 0) ==> (M[Top#c][I[Top#c]] == M[Top#a][I[Top#a]]);
  assert {:msg "21.15: Initialization of network 'Top' might not establish the channel invariant (#5)"} ((C[Top#c] - I[Top#c]) > 0) && ((R[Top#a] - I[Top#a]) == 0) ==> (M[Top#c][I[Top#c]] == M[Top#b][I[Top#b]]);
  assert {:msg "22.15: Initialization of network 'Top' might not establish the channel invariant (#6)"} ((R[Top#a] - I[Top#a]) + (R[Top#b] - I[Top#b])) == (C[Top#c] - I[Top#c]);
  I := R;
  assert {:msg "Initialization of network 'Top' might not establish the network invariant: Unread tokens might be left on channel a (#7)"} (C[Top#a] - R[Top#a]) == 0;
  assert {:msg "Initialization of network 'Top' might not establish the network invariant: Unread tokens might be left on channel b (#8)"} (C[Top#b] - R[Top#b]) == 0;
  assert {:msg "Initialization of network 'Top' might not establish the network invariant: Unread tokens might be left on channel c (#9)"} (C[Top#c] - R[Top#c]) == 0;
}
procedure Top##NonDetMerge#a1#5()
  modifies C, R, M, I, H;
{
  var Top#ndm: Actor;
  var Top#a: Chan (int);
  var Top#b: Chan (int);
  var Top#c: Chan (int);
  var x1#i: int;
  assume (Top#a != Top#b) && (Top#a != Top#c) && (Top#b != Top#c);
  assume 0 <= I[Top#a];
  assume I[Top#a] <= R[Top#a];
  assume R[Top#a] <= C[Top#a];
  assume 0 <= I[Top#b];
  assume I[Top#b] <= R[Top#b];
  assume R[Top#b] <= C[Top#b];
  assume 0 <= I[Top#c];
  assume I[Top#c] <= R[Top#c];
  assume R[Top#c] <= C[Top#c];
  assume I[Top#c] == R[Top#c];
  assume ((C[Top#c] - I[Top#c]) > 0) && ((R[Top#b] - I[Top#b]) == 0) ==> (M[Top#c][I[Top#c]] == M[Top#a][I[Top#a]]);
  assume ((C[Top#c] - I[Top#c]) > 0) && ((R[Top#a] - I[Top#a]) == 0) ==> (M[Top#c][I[Top#c]] == M[Top#b][I[Top#b]]);
  assume ((R[Top#a] - I[Top#a]) + (R[Top#b] - I[Top#b])) == (C[Top#c] - I[Top#c]);
  assume C[Top#c] == (R[Top#a] + R[Top#b]);
  assume 1 <= (C[Top#a] - R[Top#a]);
  x1#i := M[Top#a][R[Top#a]];
  R[Top#a] := R[Top#a] + 1;
  M[Top#c][C[Top#c]] := x1#i;
  C[Top#c] := C[Top#c] + 1;
  assume C[Top#c] == (R[Top#a] + R[Top#b]);
  assert {:msg "20.15: Action at 5.3 ('a1') for actor instance 'ndm' might not preserve the channel invariant (#10)"} ((C[Top#c] - I[Top#c]) > 0) && ((R[Top#b] - I[Top#b]) == 0) ==> (M[Top#c][I[Top#c]] == M[Top#a][I[Top#a]]);
  assert {:msg "21.15: Action at 5.3 ('a1') for actor instance 'ndm' might not preserve the channel invariant (#11)"} ((C[Top#c] - I[Top#c]) > 0) && ((R[Top#a] - I[Top#a]) == 0) ==> (M[Top#c][I[Top#c]] == M[Top#b][I[Top#b]]);
  assert {:msg "22.15: Action at 5.3 ('a1') for actor instance 'ndm' might not preserve the channel invariant (#12)"} ((R[Top#a] - I[Top#a]) + (R[Top#b] - I[Top#b])) == (C[Top#c] - I[Top#c]);
}
procedure Top##NonDetMerge#a2#6()
  modifies C, R, M, I, H;
{
  var Top#ndm: Actor;
  var Top#a: Chan (int);
  var Top#b: Chan (int);
  var Top#c: Chan (int);
  var x2#i: int;
  assume (Top#a != Top#b) && (Top#a != Top#c) && (Top#b != Top#c);
  assume 0 <= I[Top#a];
  assume I[Top#a] <= R[Top#a];
  assume R[Top#a] <= C[Top#a];
  assume 0 <= I[Top#b];
  assume I[Top#b] <= R[Top#b];
  assume R[Top#b] <= C[Top#b];
  assume 0 <= I[Top#c];
  assume I[Top#c] <= R[Top#c];
  assume R[Top#c] <= C[Top#c];
  assume I[Top#c] == R[Top#c];
  assume ((C[Top#c] - I[Top#c]) > 0) && ((R[Top#b] - I[Top#b]) == 0) ==> (M[Top#c][I[Top#c]] == M[Top#a][I[Top#a]]);
  assume ((C[Top#c] - I[Top#c]) > 0) && ((R[Top#a] - I[Top#a]) == 0) ==> (M[Top#c][I[Top#c]] == M[Top#b][I[Top#b]]);
  assume ((R[Top#a] - I[Top#a]) + (R[Top#b] - I[Top#b])) == (C[Top#c] - I[Top#c]);
  assume C[Top#c] == (R[Top#a] + R[Top#b]);
  assume 1 <= (C[Top#b] - R[Top#b]);
  x2#i := M[Top#b][R[Top#b]];
  R[Top#b] := R[Top#b] + 1;
  M[Top#c][C[Top#c]] := x2#i;
  C[Top#c] := C[Top#c] + 1;
  assume C[Top#c] == (R[Top#a] + R[Top#b]);
  assert {:msg "20.15: Action at 6.3 ('a2') for actor instance 'ndm' might not preserve the channel invariant (#13)"} ((C[Top#c] - I[Top#c]) > 0) && ((R[Top#b] - I[Top#b]) == 0) ==> (M[Top#c][I[Top#c]] == M[Top#a][I[Top#a]]);
  assert {:msg "21.15: Action at 6.3 ('a2') for actor instance 'ndm' might not preserve the channel invariant (#14)"} ((C[Top#c] - I[Top#c]) > 0) && ((R[Top#a] - I[Top#a]) == 0) ==> (M[Top#c][I[Top#c]] == M[Top#b][I[Top#b]]);
  assert {:msg "22.15: Action at 6.3 ('a2') for actor instance 'ndm' might not preserve the channel invariant (#15)"} ((R[Top#a] - I[Top#a]) + (R[Top#b] - I[Top#b])) == (C[Top#c] - I[Top#c]);
}
procedure Top#anon$0#input#in1#7()
  modifies C, R, M, I, H;
{
  var Top#ndm: Actor;
  var Top#a: Chan (int);
  var Top#b: Chan (int);
  var Top#c: Chan (int);
  assume (Top#a != Top#b) && (Top#a != Top#c) && (Top#b != Top#c);
  assume 0 <= I[Top#a];
  assume I[Top#a] <= R[Top#a];
  assume R[Top#a] <= C[Top#a];
  assume 0 <= I[Top#b];
  assume I[Top#b] <= R[Top#b];
  assume R[Top#b] <= C[Top#b];
  assume 0 <= I[Top#c];
  assume I[Top#c] <= R[Top#c];
  assume R[Top#c] <= C[Top#c];
  assume I[Top#c] == R[Top#c];
  assume ((C[Top#c] - I[Top#c]) > 0) && ((R[Top#b] - I[Top#b]) == 0) ==> (M[Top#c][I[Top#c]] == M[Top#a][I[Top#a]]);
  assume ((C[Top#c] - I[Top#c]) > 0) && ((R[Top#a] - I[Top#a]) == 0) ==> (M[Top#c][I[Top#c]] == M[Top#b][I[Top#b]]);
  assume ((R[Top#a] - I[Top#a]) + (R[Top#b] - I[Top#b])) == (C[Top#c] - I[Top#c]);
  assume C[Top#c] == (R[Top#a] + R[Top#b]);
  C[Top#a] := C[Top#a] + 1;
  assert {:msg "20.15: Channel invariant might be falsified by network input (#16)"} ((C[Top#c] - I[Top#c]) > 0) && ((R[Top#b] - I[Top#b]) == 0) ==> (M[Top#c][I[Top#c]] == M[Top#a][I[Top#a]]);
  assert {:msg "21.15: Channel invariant might be falsified by network input (#17)"} ((C[Top#c] - I[Top#c]) > 0) && ((R[Top#a] - I[Top#a]) == 0) ==> (M[Top#c][I[Top#c]] == M[Top#b][I[Top#b]]);
  assert {:msg "22.15: Channel invariant might be falsified by network input (#18)"} ((R[Top#a] - I[Top#a]) + (R[Top#b] - I[Top#b])) == (C[Top#c] - I[Top#c]);
}
procedure Top#anon$0#exit#8()
  modifies C, R, M, I, H;
{
  var Top#ndm: Actor;
  var Top#a: Chan (int);
  var Top#b: Chan (int);
  var Top#c: Chan (int);
  assume (Top#a != Top#b) && (Top#a != Top#c) && (Top#b != Top#c);
  assume 0 <= I[Top#a];
  assume I[Top#a] <= R[Top#a];
  assume R[Top#a] <= C[Top#a];
  assume 0 <= I[Top#b];
  assume I[Top#b] <= R[Top#b];
  assume R[Top#b] <= C[Top#b];
  assume 0 <= I[Top#c];
  assume I[Top#c] <= R[Top#c];
  assume R[Top#c] <= C[Top#c];
  assume I[Top#c] == R[Top#c];
  assume ((C[Top#c] - I[Top#c]) > 0) && ((R[Top#b] - I[Top#b]) == 0) ==> (M[Top#c][I[Top#c]] == M[Top#a][I[Top#a]]);
  assume ((C[Top#c] - I[Top#c]) > 0) && ((R[Top#a] - I[Top#a]) == 0) ==> (M[Top#c][I[Top#c]] == M[Top#b][I[Top#b]]);
  assume ((R[Top#a] - I[Top#a]) + (R[Top#b] - I[Top#b])) == (C[Top#c] - I[Top#c]);
  assume C[Top#c] == (R[Top#a] + R[Top#b]);
  assume (C[Top#a] - I[Top#a]) == 1;
  assume true;
  assume !(1 <= (C[Top#a] - R[Top#a]));
  assume !(1 <= (C[Top#b] - R[Top#b]));
  assert {:msg "13.13: Network action postcondition might not hold (#19)"} M[Top#c][I[Top#c]] == M[Top#a][I[Top#a]];
  R[Top#c] := R[Top#c] + 1;
  I := R;
  assert {:msg "20.15: The network might not preserve the channel invariant (#20)"} ((C[Top#c] - I[Top#c]) > 0) && ((R[Top#b] - I[Top#b]) == 0) ==> (M[Top#c][I[Top#c]] == M[Top#a][I[Top#a]]);
  assert {:msg "21.15: The network might not preserve the channel invariant (#21)"} ((C[Top#c] - I[Top#c]) > 0) && ((R[Top#a] - I[Top#a]) == 0) ==> (M[Top#c][I[Top#c]] == M[Top#b][I[Top#b]]);
  assert {:msg "22.15: The network might not preserve the channel invariant (#22)"} ((R[Top#a] - I[Top#a]) + (R[Top#b] - I[Top#b])) == (C[Top#c] - I[Top#c]);
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel a (#23)"} (C[Top#a] - R[Top#a]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel b (#24)"} (C[Top#b] - R[Top#b]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel c (#25)"} (C[Top#c] - R[Top#c]) == 0;
}
procedure Top#anon$1#input#in2#9()
  modifies C, R, M, I, H;
{
  var Top#ndm: Actor;
  var Top#a: Chan (int);
  var Top#b: Chan (int);
  var Top#c: Chan (int);
  assume (Top#a != Top#b) && (Top#a != Top#c) && (Top#b != Top#c);
  assume 0 <= I[Top#a];
  assume I[Top#a] <= R[Top#a];
  assume R[Top#a] <= C[Top#a];
  assume 0 <= I[Top#b];
  assume I[Top#b] <= R[Top#b];
  assume R[Top#b] <= C[Top#b];
  assume 0 <= I[Top#c];
  assume I[Top#c] <= R[Top#c];
  assume R[Top#c] <= C[Top#c];
  assume I[Top#c] == R[Top#c];
  assume ((C[Top#c] - I[Top#c]) > 0) && ((R[Top#b] - I[Top#b]) == 0) ==> (M[Top#c][I[Top#c]] == M[Top#a][I[Top#a]]);
  assume ((C[Top#c] - I[Top#c]) > 0) && ((R[Top#a] - I[Top#a]) == 0) ==> (M[Top#c][I[Top#c]] == M[Top#b][I[Top#b]]);
  assume ((R[Top#a] - I[Top#a]) + (R[Top#b] - I[Top#b])) == (C[Top#c] - I[Top#c]);
  assume C[Top#c] == (R[Top#a] + R[Top#b]);
  C[Top#b] := C[Top#b] + 1;
  assert {:msg "20.15: Channel invariant might be falsified by network input (#26)"} ((C[Top#c] - I[Top#c]) > 0) && ((R[Top#b] - I[Top#b]) == 0) ==> (M[Top#c][I[Top#c]] == M[Top#a][I[Top#a]]);
  assert {:msg "21.15: Channel invariant might be falsified by network input (#27)"} ((C[Top#c] - I[Top#c]) > 0) && ((R[Top#a] - I[Top#a]) == 0) ==> (M[Top#c][I[Top#c]] == M[Top#b][I[Top#b]]);
  assert {:msg "22.15: Channel invariant might be falsified by network input (#28)"} ((R[Top#a] - I[Top#a]) + (R[Top#b] - I[Top#b])) == (C[Top#c] - I[Top#c]);
}
procedure Top#anon$1#exit#10()
  modifies C, R, M, I, H;
{
  var Top#ndm: Actor;
  var Top#a: Chan (int);
  var Top#b: Chan (int);
  var Top#c: Chan (int);
  assume (Top#a != Top#b) && (Top#a != Top#c) && (Top#b != Top#c);
  assume 0 <= I[Top#a];
  assume I[Top#a] <= R[Top#a];
  assume R[Top#a] <= C[Top#a];
  assume 0 <= I[Top#b];
  assume I[Top#b] <= R[Top#b];
  assume R[Top#b] <= C[Top#b];
  assume 0 <= I[Top#c];
  assume I[Top#c] <= R[Top#c];
  assume R[Top#c] <= C[Top#c];
  assume I[Top#c] == R[Top#c];
  assume ((C[Top#c] - I[Top#c]) > 0) && ((R[Top#b] - I[Top#b]) == 0) ==> (M[Top#c][I[Top#c]] == M[Top#a][I[Top#a]]);
  assume ((C[Top#c] - I[Top#c]) > 0) && ((R[Top#a] - I[Top#a]) == 0) ==> (M[Top#c][I[Top#c]] == M[Top#b][I[Top#b]]);
  assume ((R[Top#a] - I[Top#a]) + (R[Top#b] - I[Top#b])) == (C[Top#c] - I[Top#c]);
  assume C[Top#c] == (R[Top#a] + R[Top#b]);
  assume true;
  assume (C[Top#b] - I[Top#b]) == 1;
  assume !(1 <= (C[Top#a] - R[Top#a]));
  assume !(1 <= (C[Top#b] - R[Top#b]));
  assert {:msg "17.13: Network action postcondition might not hold (#29)"} M[Top#c][I[Top#c]] == M[Top#b][I[Top#b]];
  R[Top#c] := R[Top#c] + 1;
  I := R;
  assert {:msg "20.15: The network might not preserve the channel invariant (#30)"} ((C[Top#c] - I[Top#c]) > 0) && ((R[Top#b] - I[Top#b]) == 0) ==> (M[Top#c][I[Top#c]] == M[Top#a][I[Top#a]]);
  assert {:msg "21.15: The network might not preserve the channel invariant (#31)"} ((C[Top#c] - I[Top#c]) > 0) && ((R[Top#a] - I[Top#a]) == 0) ==> (M[Top#c][I[Top#c]] == M[Top#b][I[Top#b]]);
  assert {:msg "22.15: The network might not preserve the channel invariant (#32)"} ((R[Top#a] - I[Top#a]) + (R[Top#b] - I[Top#b])) == (C[Top#c] - I[Top#c]);
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel a (#33)"} (C[Top#a] - R[Top#a]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel b (#34)"} (C[Top#b] - R[Top#b]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel c (#35)"} (C[Top#c] - R[Top#c]) == 0;
}

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
var I: CType;
var St: [Actor]State;

const unique this#: Actor;
type List a = [int]a;
var AT#intlst: List int;

function AT#Min(x:int, y: int): int { if x <= y then x else y }

// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

procedure NonDetMerge#init#0()
  modifies C, R, M, I, St;
{
  var x1: Chan (int);
  var x2: Chan (int);
  var y: Chan (int);
  assume (x1 != x2) && (x1 != y) && (x2 != y);
  assume R[x1] == 0;
  assume R[x2] == 0;
  assume C[y] == 0;
}
procedure NonDetMerge#a1#1()
  modifies C, R, M, I, St;
{
  var x1: Chan (int);
  var x2: Chan (int);
  var y: Chan (int);
  var x1#0: int;
  assume (x1 != x2) && (x1 != y) && (x2 != y);
  assume 0 <= R[x1];
  assume 0 <= R[x2];
  assume 0 <= C[y];
  x1#0 := M[x1][R[x1]];
  R[x1] := R[x1] + 1;
  assume true;
  M[y][C[y]] := x1#0;
  C[y] := C[y] + 1;
}
procedure NonDetMerge#a2#2()
  modifies C, R, M, I, St;
{
  var x1: Chan (int);
  var x2: Chan (int);
  var y: Chan (int);
  var x2#0: int;
  assume (x1 != x2) && (x1 != y) && (x2 != y);
  assume 0 <= R[x1];
  assume 0 <= R[x2];
  assume 0 <= C[y];
  x2#0 := M[x2][R[x2]];
  R[x2] := R[x2] + 1;
  assume true;
  M[y][C[y]] := x2#0;
  C[y] := C[y] + 1;
}
procedure NonDetMerge##GuardWD#3()
  modifies C, R, M, I, St;
{
  var x1: Chan (int);
  var x2: Chan (int);
  var y: Chan (int);
  var x1#0: int;
  var x2#0: int;
  assume (x1 != x2) && (x1 != y) && (x2 != y);
  assert {:msg "1.1: The actions of actor 'NonDetMerge' might not have mutually exclusive guards (#0)"} !((1 <= (C[x1] - R[x1])) && (1 <= (C[x2] - R[x2])));
}
procedure Top#init#4()
  modifies C, R, M, I, St;
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
  assert {:msg "15.15: Initialization of network 'Top' might not establish the channel invariant (#1)"} (C[Top#c] - I[Top#c]) == ((R[Top#a] - I[Top#a]) + (R[Top#b] - I[Top#b]));
  assert {:msg "16.15: Initialization of network 'Top' might not establish the channel invariant (#2)"} ((C[Top#c] - I[Top#c]) > 0) && ((R[Top#b] - I[Top#b]) == 0) ==> (M[Top#c][I[Top#c]] == M[Top#a][I[Top#a]]);
  assert {:msg "17.15: Initialization of network 'Top' might not establish the channel invariant (#3)"} ((C[Top#c] - I[Top#c]) > 0) && ((R[Top#a] - I[Top#a]) == 0) ==> (M[Top#c][I[Top#c]] == M[Top#b][I[Top#b]]);
  I := R;
  assert {:msg "23.5: The initialization might produce unspecified tokens on channel a (#4)"} (C[Top#a] - R[Top#a]) == 0;
  assert {:msg "24.5: The initialization might produce unspecified tokens on channel b (#5)"} (C[Top#b] - R[Top#b]) == 0;
  assert {:msg "25.5: The initialization might produce unspecified tokens on channel c (#6)"} (C[Top#c] - R[Top#c]) == 0;
}
procedure Top##NonDetMerge#a1#5()
  modifies C, R, M, I, St;
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
  assume (C[Top#c] - I[Top#c]) == ((R[Top#a] - I[Top#a]) + (R[Top#b] - I[Top#b]));
  assume ((C[Top#c] - I[Top#c]) > 0) && ((R[Top#b] - I[Top#b]) == 0) ==> (M[Top#c][I[Top#c]] == M[Top#a][I[Top#a]]);
  assume ((C[Top#c] - I[Top#c]) > 0) && ((R[Top#a] - I[Top#a]) == 0) ==> (M[Top#c][I[Top#c]] == M[Top#b][I[Top#b]]);
  assume 1 <= (C[Top#a] - R[Top#a]);
  x1#i := M[Top#a][R[Top#a]];
  R[Top#a] := R[Top#a] + 1;
  M[Top#c][C[Top#c]] := x1#i;
  C[Top#c] := C[Top#c] + 1;
  assert {:msg "15.15: Action at 2.3 ('a1') for actor instance 'ndm' might not preserve the channel invariant (#7)"} (C[Top#c] - I[Top#c]) == ((R[Top#a] - I[Top#a]) + (R[Top#b] - I[Top#b]));
  assert {:msg "16.15: Action at 2.3 ('a1') for actor instance 'ndm' might not preserve the channel invariant (#8)"} ((C[Top#c] - I[Top#c]) > 0) && ((R[Top#b] - I[Top#b]) == 0) ==> (M[Top#c][I[Top#c]] == M[Top#a][I[Top#a]]);
  assert {:msg "17.15: Action at 2.3 ('a1') for actor instance 'ndm' might not preserve the channel invariant (#9)"} ((C[Top#c] - I[Top#c]) > 0) && ((R[Top#a] - I[Top#a]) == 0) ==> (M[Top#c][I[Top#c]] == M[Top#b][I[Top#b]]);
}
procedure Top##NonDetMerge#a2#6()
  modifies C, R, M, I, St;
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
  assume (C[Top#c] - I[Top#c]) == ((R[Top#a] - I[Top#a]) + (R[Top#b] - I[Top#b]));
  assume ((C[Top#c] - I[Top#c]) > 0) && ((R[Top#b] - I[Top#b]) == 0) ==> (M[Top#c][I[Top#c]] == M[Top#a][I[Top#a]]);
  assume ((C[Top#c] - I[Top#c]) > 0) && ((R[Top#a] - I[Top#a]) == 0) ==> (M[Top#c][I[Top#c]] == M[Top#b][I[Top#b]]);
  assume 1 <= (C[Top#b] - R[Top#b]);
  x2#i := M[Top#b][R[Top#b]];
  R[Top#b] := R[Top#b] + 1;
  M[Top#c][C[Top#c]] := x2#i;
  C[Top#c] := C[Top#c] + 1;
  assert {:msg "15.15: Action at 3.3 ('a2') for actor instance 'ndm' might not preserve the channel invariant (#10)"} (C[Top#c] - I[Top#c]) == ((R[Top#a] - I[Top#a]) + (R[Top#b] - I[Top#b]));
  assert {:msg "16.15: Action at 3.3 ('a2') for actor instance 'ndm' might not preserve the channel invariant (#11)"} ((C[Top#c] - I[Top#c]) > 0) && ((R[Top#b] - I[Top#b]) == 0) ==> (M[Top#c][I[Top#c]] == M[Top#a][I[Top#a]]);
  assert {:msg "17.15: Action at 3.3 ('a2') for actor instance 'ndm' might not preserve the channel invariant (#12)"} ((C[Top#c] - I[Top#c]) > 0) && ((R[Top#a] - I[Top#a]) == 0) ==> (M[Top#c][I[Top#c]] == M[Top#b][I[Top#b]]);
}
procedure Top#entry()
  modifies C, R, M, I, St;
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
  assume C[Top#a] == R[Top#a];
  assume C[Top#b] == R[Top#b];
  assume C[Top#c] == R[Top#c];
  assume (C[Top#c] - I[Top#c]) == ((R[Top#a] - I[Top#a]) + (R[Top#b] - I[Top#b]));
  assume ((C[Top#c] - I[Top#c]) > 0) && ((R[Top#b] - I[Top#b]) == 0) ==> (M[Top#c][I[Top#c]] == M[Top#a][I[Top#a]]);
  assume ((C[Top#c] - I[Top#c]) > 0) && ((R[Top#a] - I[Top#a]) == 0) ==> (M[Top#c][I[Top#c]] == M[Top#b][I[Top#b]]);
  assert {:msg "6.1: Sub-actors in the network might fire without network input. This is not permitted. (#13)"} !(1 <= (C[Top#a] - R[Top#a]));
  assert {:msg "6.1: Sub-actors in the network might fire without network input. This is not permitted. (#14)"} !(1 <= (C[Top#b] - R[Top#b]));
}
procedure Top#anon$0#input#in1#7()
  modifies C, R, M, I, St;
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
  assume C[Top#a] < 1;
  assume (C[Top#c] - I[Top#c]) == ((R[Top#a] - I[Top#a]) + (R[Top#b] - I[Top#b]));
  assume ((C[Top#c] - I[Top#c]) > 0) && ((R[Top#b] - I[Top#b]) == 0) ==> (M[Top#c][I[Top#c]] == M[Top#a][I[Top#a]]);
  assume ((C[Top#c] - I[Top#c]) > 0) && ((R[Top#a] - I[Top#a]) == 0) ==> (M[Top#c][I[Top#c]] == M[Top#b][I[Top#b]]);
  C[Top#a] := C[Top#a] + 1;
  assert {:msg "15.15: Channel invariant might be falsified by network input (#15)"} (C[Top#c] - I[Top#c]) == ((R[Top#a] - I[Top#a]) + (R[Top#b] - I[Top#b]));
  assert {:msg "16.15: Channel invariant might be falsified by network input (#16)"} ((C[Top#c] - I[Top#c]) > 0) && ((R[Top#b] - I[Top#b]) == 0) ==> (M[Top#c][I[Top#c]] == M[Top#a][I[Top#a]]);
  assert {:msg "17.15: Channel invariant might be falsified by network input (#17)"} ((C[Top#c] - I[Top#c]) > 0) && ((R[Top#a] - I[Top#a]) == 0) ==> (M[Top#c][I[Top#c]] == M[Top#b][I[Top#b]]);
}
procedure Top#anon$0#exit#8()
  modifies C, R, M, I, St;
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
  assume (C[Top#c] - I[Top#c]) == ((R[Top#a] - I[Top#a]) + (R[Top#b] - I[Top#b]));
  assume ((C[Top#c] - I[Top#c]) > 0) && ((R[Top#b] - I[Top#b]) == 0) ==> (M[Top#c][I[Top#c]] == M[Top#a][I[Top#a]]);
  assume ((C[Top#c] - I[Top#c]) > 0) && ((R[Top#a] - I[Top#a]) == 0) ==> (M[Top#c][I[Top#c]] == M[Top#b][I[Top#b]]);
  assume (C[Top#a] - I[Top#a]) == 1;
  assume (C[Top#b] - I[Top#b]) == 0;
  assume !(1 <= (C[Top#a] - R[Top#a]));
  assume !(1 <= (C[Top#b] - R[Top#b]));
  assert {:msg "9.13: Network action postcondition might not hold (#18)"} M[Top#c][I[Top#c]] == M[Top#a][I[Top#a]];
  R[Top#c] := R[Top#c] + 1;
  I := R;
  assert {:msg "15.15: The network might not preserve the channel invariant (#19)"} (C[Top#c] - I[Top#c]) == ((R[Top#a] - I[Top#a]) + (R[Top#b] - I[Top#b]));
  assert {:msg "16.15: The network might not preserve the channel invariant (#20)"} ((C[Top#c] - I[Top#c]) > 0) && ((R[Top#b] - I[Top#b]) == 0) ==> (M[Top#c][I[Top#c]] == M[Top#a][I[Top#a]]);
  assert {:msg "17.15: The network might not preserve the channel invariant (#21)"} ((C[Top#c] - I[Top#c]) > 0) && ((R[Top#a] - I[Top#a]) == 0) ==> (M[Top#c][I[Top#c]] == M[Top#b][I[Top#b]]);
  assert {:msg "8.3: The network might leave unread tokens on channel a (#22)"} C[Top#a] == R[Top#a];
  assert {:msg "8.3: The network might leave unread tokens on channel b (#23)"} C[Top#b] == R[Top#b];
  assert {:msg "8.3: The network might not produce the specified number of tokens on output out (#24)"} C[Top#c] == R[Top#c];
}
procedure Top#anon$1#input#in2#9()
  modifies C, R, M, I, St;
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
  assume C[Top#b] < 1;
  assume (C[Top#c] - I[Top#c]) == ((R[Top#a] - I[Top#a]) + (R[Top#b] - I[Top#b]));
  assume ((C[Top#c] - I[Top#c]) > 0) && ((R[Top#b] - I[Top#b]) == 0) ==> (M[Top#c][I[Top#c]] == M[Top#a][I[Top#a]]);
  assume ((C[Top#c] - I[Top#c]) > 0) && ((R[Top#a] - I[Top#a]) == 0) ==> (M[Top#c][I[Top#c]] == M[Top#b][I[Top#b]]);
  C[Top#b] := C[Top#b] + 1;
  assert {:msg "15.15: Channel invariant might be falsified by network input (#25)"} (C[Top#c] - I[Top#c]) == ((R[Top#a] - I[Top#a]) + (R[Top#b] - I[Top#b]));
  assert {:msg "16.15: Channel invariant might be falsified by network input (#26)"} ((C[Top#c] - I[Top#c]) > 0) && ((R[Top#b] - I[Top#b]) == 0) ==> (M[Top#c][I[Top#c]] == M[Top#a][I[Top#a]]);
  assert {:msg "17.15: Channel invariant might be falsified by network input (#27)"} ((C[Top#c] - I[Top#c]) > 0) && ((R[Top#a] - I[Top#a]) == 0) ==> (M[Top#c][I[Top#c]] == M[Top#b][I[Top#b]]);
}
procedure Top#anon$1#exit#10()
  modifies C, R, M, I, St;
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
  assume (C[Top#c] - I[Top#c]) == ((R[Top#a] - I[Top#a]) + (R[Top#b] - I[Top#b]));
  assume ((C[Top#c] - I[Top#c]) > 0) && ((R[Top#b] - I[Top#b]) == 0) ==> (M[Top#c][I[Top#c]] == M[Top#a][I[Top#a]]);
  assume ((C[Top#c] - I[Top#c]) > 0) && ((R[Top#a] - I[Top#a]) == 0) ==> (M[Top#c][I[Top#c]] == M[Top#b][I[Top#b]]);
  assume (C[Top#a] - I[Top#a]) == 0;
  assume (C[Top#b] - I[Top#b]) == 1;
  assume !(1 <= (C[Top#a] - R[Top#a]));
  assume !(1 <= (C[Top#b] - R[Top#b]));
  assert {:msg "12.13: Network action postcondition might not hold (#28)"} M[Top#c][I[Top#c]] == M[Top#b][I[Top#b]];
  R[Top#c] := R[Top#c] + 1;
  I := R;
  assert {:msg "15.15: The network might not preserve the channel invariant (#29)"} (C[Top#c] - I[Top#c]) == ((R[Top#a] - I[Top#a]) + (R[Top#b] - I[Top#b]));
  assert {:msg "16.15: The network might not preserve the channel invariant (#30)"} ((C[Top#c] - I[Top#c]) > 0) && ((R[Top#b] - I[Top#b]) == 0) ==> (M[Top#c][I[Top#c]] == M[Top#a][I[Top#a]]);
  assert {:msg "17.15: The network might not preserve the channel invariant (#31)"} ((C[Top#c] - I[Top#c]) > 0) && ((R[Top#a] - I[Top#a]) == 0) ==> (M[Top#c][I[Top#c]] == M[Top#b][I[Top#b]]);
  assert {:msg "11.3: The network might leave unread tokens on channel a (#32)"} C[Top#a] == R[Top#a];
  assert {:msg "11.3: The network might leave unread tokens on channel b (#33)"} C[Top#b] == R[Top#b];
  assert {:msg "11.3: The network might not produce the specified number of tokens on output out (#34)"} C[Top#c] == R[Top#c];
}

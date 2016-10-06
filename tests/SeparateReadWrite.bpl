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

procedure RW#init#0()
  modifies C, R, M, I, St;
{
  var in: Chan (int);
  var out: Chan (int);
  var step: int;
  var data: int;
  assume R[in] == 0;
  assume C[in] == 0;
  assume R[out] == 0;
  assume C[out] == 0;
  step := 1;
  assert {:msg "3.15: Action at 10.2 might not preserve invariant (#0)"} (step == 0) || (step == 1);
  assert {:msg "4.15: Action at 10.2 might not preserve invariant (#1)"} (step == 1) <==> (R[in] == C[out]);
  assert {:msg "5.15: Action at 10.2 might not preserve invariant (#2)"} (step == 0) <==> (R[in] == (C[out] + 1));
}
procedure RW#read#1()
  modifies C, R, M, I, St;
{
  var in: Chan (int);
  var out: Chan (int);
  var step: int;
  var data: int;
  assume 0 <= R[in];
  assume R[in] <= C[in];
  assume 0 <= R[out];
  assume R[out] <= C[out];
  assume (step == 0) || (step == 1);
  assume (step == 1) <==> (R[in] == C[out]);
  assume (step == 0) <==> (R[in] == (C[out] + 1));
  assume step == 1;
  R[in] := R[in] + 1;
  step := 0;
  data := data + M[in][0];
  assert {:msg "3.15: Action at 12.2 might not preserve invariant (#3)"} (step == 0) || (step == 1);
  assert {:msg "4.15: Action at 12.2 might not preserve invariant (#4)"} (step == 1) <==> (R[in] == C[out]);
  assert {:msg "5.15: Action at 12.2 might not preserve invariant (#5)"} (step == 0) <==> (R[in] == (C[out] + 1));
}
procedure RW#write#2()
  modifies C, R, M, I, St;
{
  var in: Chan (int);
  var out: Chan (int);
  var step: int;
  var data: int;
  assume 0 <= R[in];
  assume R[in] <= C[in];
  assume 0 <= R[out];
  assume R[out] <= C[out];
  assume (step == 0) || (step == 1);
  assume (step == 1) <==> (R[in] == C[out]);
  assume (step == 0) <==> (R[in] == (C[out] + 1));
  assume step == 0;
  step := 1;
  C[out] := C[out] + 1;
  assert {:msg "3.15: Action at 17.2 might not preserve invariant (#6)"} (step == 0) || (step == 1);
  assert {:msg "4.15: Action at 17.2 might not preserve invariant (#7)"} (step == 1) <==> (R[in] == C[out]);
  assert {:msg "5.15: Action at 17.2 might not preserve invariant (#8)"} (step == 0) <==> (R[in] == (C[out] + 1));
}
procedure RW##GuardWD#3()
  modifies C, R, M, I, St;
{
  var data: int;
  var in: Chan (int);
  var out: Chan (int);
  var step: int;
  assert {:msg "1.1: The actions of actor 'RW' might not have mutually exclusive guards (#9)"} !((1 <= (C[in] - R[in])) && (step == 1) && (step == 0));
}
const unique Net#rw: Actor;
const unique Net#a: Chan (int);
const unique Net#b: Chan (int);
procedure Net#init#4()
  modifies C, R, M, I, St;
{
  var AV#rw#step: int;
  var AV#rw#data: int;
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
  assume (AV#rw#step == 0) || (AV#rw#step == 1);
  assume (AV#rw#step == 1) <==> (R[Net#a] == C[Net#b]);
  assume (AV#rw#step == 0) <==> (R[Net#a] == (C[Net#b] + 1));
  assert {:msg "32.15: Network initialization might not establish the channel invariant (#10)"} (AV#rw#step == 1) || (AV#rw#step == 0);
  assert {:msg "33.15: Network initialization might not establish the channel invariant (#11)"} (AV#rw#step == 1) <==> ((R[Net#a] - I[Net#a]) == (C[Net#b] - I[Net#b]));
  assert {:msg "34.15: Network initialization might not establish the channel invariant (#12)"} (AV#rw#step == 0) <==> ((R[Net#a] - I[Net#a]) == ((C[Net#b] - I[Net#b]) + 1));
  assert {:msg "Network initialization might not establish the channel invariant (#13)"} true;
  I := R;
  assert {:msg "41.5: The initialization might unspecified tokens on channel a (#14)"} (C[Net#a] - R[Net#a]) == 0;
  assert {:msg "42.5: The initialization might unspecified tokens on channel b (#15)"} (C[Net#b] - R[Net#b]) == 0;
}
procedure Net##RW#write#5()
  modifies C, R, M, I, St;
{
  var AV#rw#step: int;
  var AV#rw#data: int;
  var St#next: State;
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume I[Net#b] == R[Net#b];
  assume (AV#rw#step == 1) || (AV#rw#step == 0);
  assume (AV#rw#step == 1) <==> ((R[Net#a] - I[Net#a]) == (C[Net#b] - I[Net#b]));
  assume (AV#rw#step == 0) <==> ((R[Net#a] - I[Net#a]) == ((C[Net#b] - I[Net#b]) + 1));
  assume true;
  assume AV#rw#step == 0;
  assume true;
  assume AV#rw#step == 0;
  assume (AV#rw#step == 0) || (AV#rw#step == 1);
  assume (AV#rw#step == 1) <==> (R[Net#a] == C[Net#b]);
  assume (AV#rw#step == 0) <==> (R[Net#a] == (C[Net#b] + 1));
  havoc AV#rw#step;
  havoc AV#rw#data;
  M[Net#b][C[Net#b]] := AV#rw#data;
  C[Net#b] := C[Net#b] + 1;
  assume (AV#rw#step == 0) || (AV#rw#step == 1);
  assume (AV#rw#step == 1) <==> (R[Net#a] == C[Net#b]);
  assume (AV#rw#step == 0) <==> (R[Net#a] == (C[Net#b] + 1));
  assert {:msg "32.15: Action at 17.2 ('write') for actor instance 'rw' might not preserve the channel invariant (#16)"} (AV#rw#step == 1) || (AV#rw#step == 0);
  assert {:msg "33.15: Action at 17.2 ('write') for actor instance 'rw' might not preserve the channel invariant (#17)"} (AV#rw#step == 1) <==> ((R[Net#a] - I[Net#a]) == (C[Net#b] - I[Net#b]));
  assert {:msg "34.15: Action at 17.2 ('write') for actor instance 'rw' might not preserve the channel invariant (#18)"} (AV#rw#step == 0) <==> ((R[Net#a] - I[Net#a]) == ((C[Net#b] - I[Net#b]) + 1));
  assert {:msg "Action at 17.2 ('write') for actor instance 'rw' might not preserve the channel invariant (#19)"} true;
}
procedure Net##RW#read#6()
  modifies C, R, M, I, St;
{
  var AV#rw#step: int;
  var AV#rw#data: int;
  var St#next: State;
  var in#data_in: int;
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume I[Net#b] == R[Net#b];
  assume (AV#rw#step == 1) || (AV#rw#step == 0);
  assume (AV#rw#step == 1) <==> ((R[Net#a] - I[Net#a]) == (C[Net#b] - I[Net#b]));
  assume (AV#rw#step == 0) <==> ((R[Net#a] - I[Net#a]) == ((C[Net#b] - I[Net#b]) + 1));
  assume true;
  assume AV#rw#step == 1;
  assume true;
  assume (!(AV#rw#step == 0)) && (1 <= (C[Net#a] - R[Net#a])) && (AV#rw#step == 1);
  assume (AV#rw#step == 0) || (AV#rw#step == 1);
  assume (AV#rw#step == 1) <==> (R[Net#a] == C[Net#b]);
  assume (AV#rw#step == 0) <==> (R[Net#a] == (C[Net#b] + 1));
  in#data_in := M[Net#a][R[Net#a]];
  R[Net#a] := R[Net#a] + 1;
  havoc AV#rw#step;
  havoc AV#rw#data;
  assume (AV#rw#step == 0) || (AV#rw#step == 1);
  assume (AV#rw#step == 1) <==> (R[Net#a] == C[Net#b]);
  assume (AV#rw#step == 0) <==> (R[Net#a] == (C[Net#b] + 1));
  assert {:msg "32.15: Action at 12.2 ('read') for actor instance 'rw' might not preserve the channel invariant (#20)"} (AV#rw#step == 1) || (AV#rw#step == 0);
  assert {:msg "33.15: Action at 12.2 ('read') for actor instance 'rw' might not preserve the channel invariant (#21)"} (AV#rw#step == 1) <==> ((R[Net#a] - I[Net#a]) == (C[Net#b] - I[Net#b]));
  assert {:msg "34.15: Action at 12.2 ('read') for actor instance 'rw' might not preserve the channel invariant (#22)"} (AV#rw#step == 0) <==> ((R[Net#a] - I[Net#a]) == ((C[Net#b] - I[Net#b]) + 1));
  assert {:msg "Action at 12.2 ('read') for actor instance 'rw' might not preserve the channel invariant (#23)"} true;
}
procedure Net#anon$0#input#in#7()
  modifies C, R, M, I, St;
{
  var AV#rw#step: int;
  var AV#rw#data: int;
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume I[Net#b] == R[Net#b];
  assume C[Net#a] < 1;
  assume (AV#rw#step == 1) || (AV#rw#step == 0);
  assume (AV#rw#step == 1) <==> ((R[Net#a] - I[Net#a]) == (C[Net#b] - I[Net#b]));
  assume (AV#rw#step == 0) <==> ((R[Net#a] - I[Net#a]) == ((C[Net#b] - I[Net#b]) + 1));
  assume true;
  C[Net#a] := C[Net#a] + 1;
  assert {:msg "32.15: Channel invariant might be falsified by network input (#24)"} (AV#rw#step == 1) || (AV#rw#step == 0);
  assert {:msg "33.15: Channel invariant might be falsified by network input (#25)"} (AV#rw#step == 1) <==> ((R[Net#a] - I[Net#a]) == (C[Net#b] - I[Net#b]));
  assert {:msg "34.15: Channel invariant might be falsified by network input (#26)"} (AV#rw#step == 0) <==> ((R[Net#a] - I[Net#a]) == ((C[Net#b] - I[Net#b]) + 1));
  assert {:msg "Channel invariant might be falsified by network input (#27)"} true;
}
procedure Net#anon$0#exit#8()
  modifies C, R, M, I, St;
{
  var AV#rw#step: int;
  var AV#rw#data: int;
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume I[Net#b] == R[Net#b];
  assume (AV#rw#step == 1) || (AV#rw#step == 0);
  assume (AV#rw#step == 1) <==> ((R[Net#a] - I[Net#a]) == (C[Net#b] - I[Net#b]));
  assume (AV#rw#step == 0) <==> ((R[Net#a] - I[Net#a]) == ((C[Net#b] - I[Net#b]) + 1));
  assume true;
  assume (C[Net#a] - I[Net#a]) == 1;
  assume !((!(AV#rw#step == 0)) && (1 <= (C[Net#a] - R[Net#a])) && (AV#rw#step == 1));
  assume !(AV#rw#step == 0);
  R[Net#b] := R[Net#b] + 1;
  I := R;
  assert {:msg "32.15: The network might not preserve the channel invariant (#28)"} (AV#rw#step == 1) || (AV#rw#step == 0);
  assert {:msg "33.15: The network might not preserve the channel invariant (#29)"} (AV#rw#step == 1) <==> ((R[Net#a] - I[Net#a]) == (C[Net#b] - I[Net#b]));
  assert {:msg "34.15: The network might not preserve the channel invariant (#30)"} (AV#rw#step == 0) <==> ((R[Net#a] - I[Net#a]) == ((C[Net#b] - I[Net#b]) + 1));
  assert {:msg "The network might not preserve the channel invariant (#31)"} true;
  assert {:msg "30.3: The network might leave unread tokens on channel a (#32)"} C[Net#a] == R[Net#a];
  assert {:msg "30.3: The network might not produce the specified number of tokens on output out (#33)"} C[Net#b] == R[Net#b];
}

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

const unique this#: Actor;
type List a = [int]a;
var AT#intlst: List int;

function AT#Min(x:int, y: int): int { if x <= y then x else y }

// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

procedure Route#init#0()
  modifies C, R, M, I;
{
  var in1: Chan (int);
  var in2: Chan (int);
  var out1: Chan (int);
  var out2: Chan (int);
  assume (in1 != in2) && (in1 != out1) && (in1 != out2) && (in2 != out1) && (in2 != out2) && (out1 != out2);
  assume R[in1] == 0;
  assume R[in2] == 0;
  assume C[out1] == 0;
  assume C[out2] == 0;
}
procedure Route#a#1()
  modifies C, R, M, I;
{
  var in1: Chan (int);
  var in2: Chan (int);
  var out1: Chan (int);
  var out2: Chan (int);
  var in1#0: int;
  assume (in1 != in2) && (in1 != out1) && (in1 != out2) && (in2 != out1) && (in2 != out2) && (out1 != out2);
  assume 0 <= R[in1];
  assume 0 <= R[in2];
  assume 0 <= C[out1];
  assume 0 <= C[out2];
  in1#0 := M[in1][R[in1]];
  R[in1] := R[in1] + 1;
  assume true;
  M[out2][C[out2]] := in1#0;
  C[out2] := C[out2] + 1;
}
procedure Route#b#2()
  modifies C, R, M, I;
{
  var in1: Chan (int);
  var in2: Chan (int);
  var out1: Chan (int);
  var out2: Chan (int);
  var in2#0: int;
  assume (in1 != in2) && (in1 != out1) && (in1 != out2) && (in2 != out1) && (in2 != out2) && (out1 != out2);
  assume 0 <= R[in1];
  assume 0 <= R[in2];
  assume 0 <= C[out1];
  assume 0 <= C[out2];
  in2#0 := M[in2][R[in2]];
  R[in2] := R[in2] + 1;
  assume !(1 <= (C[in1] - R[in1]));
  assume true;
  M[out1][C[out1]] := in2#0;
  C[out1] := C[out1] + 1;
}
procedure Route##GuardWD#3()
  modifies C, R, M, I;
{
  var in1: Chan (int);
  var in2: Chan (int);
  var out1: Chan (int);
  var out2: Chan (int);
  var in1#0: int;
  var in2#0: int;
  assume (in1 != in2) && (in1 != out1) && (in1 != out2) && (in2 != out1) && (in2 != out2) && (out1 != out2);
  assert {:msg "1.1: The actions of actor 'Route' might not have mutually exclusive guards (#0)"} !((1 <= (C[in1] - R[in1])) && (!(1 <= (C[in1] - R[in1]))) && (1 <= (C[in2] - R[in2])));
}
procedure Repeat#init#4()
  modifies C, R, M, I;
{
  var in: Chan (int);
  var out: Chan (int);
  assume in != out;
  assume R[in] == 0;
  assume C[out] == 0;
  assert {:msg "Initialization might not establish the invariant (#1)"} R[in] == C[out];
  assert {:msg "Initialization might not establish the invariant (#2)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == M[in][idx$])
  );
}
procedure Repeat#anon$0#5()
  modifies C, R, M, I;
{
  var in: Chan (int);
  var out: Chan (int);
  var in#0: int;
  assume in != out;
  assume 0 <= R[in];
  assume 0 <= C[out];
  assume R[in] == C[out];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == M[in][idx$])
  );
  in#0 := M[in][R[in]];
  R[in] := R[in] + 1;
  assume true;
  M[out][C[out]] := in#0;
  C[out] := C[out] + 1;
  assert {:msg "Action at 8.3 might not preserve invariant (#3)"} R[in] == C[out];
  assert {:msg "Action at 8.3 might not preserve invariant (#4)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == M[in][idx$])
  );
}
procedure Net#init#6()
  modifies C, R, M, I;
{
  var Net#rou: Actor;
  var Net#rep: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (int);
  var Net#d: Chan (int);
  assume Net#rou != Net#rep;
  assume (Net#a != Net#b) && (Net#a != Net#c) && (Net#a != Net#d) && (Net#b != Net#c) && (Net#b != Net#d) && (Net#c != Net#d);
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume 0 <= I[Net#c];
  assume I[Net#c] <= R[Net#c];
  assume R[Net#c] <= C[Net#c];
  assume 0 <= I[Net#d];
  assume I[Net#d] <= R[Net#d];
  assume R[Net#d] <= C[Net#d];
  assume I[Net#d] == R[Net#d];
  assume C[Net#a] == 0;
  assume R[Net#a] == 0;
  assume C[Net#b] == 0;
  assume R[Net#b] == 0;
  assume C[Net#c] == 0;
  assume R[Net#c] == 0;
  assume C[Net#d] == 0;
  assume R[Net#d] == 0;
  assume R[Net#b] == C[Net#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == M[Net#b][idx$])
  );
  assert {:msg "16.15: Initialization of network 'Net' might not establish the channel invariant (#5)"} (C[Net#b] - I[Net#b]) == (R[Net#a] - I[Net#a]);
  assert {:msg "17.15: Initialization of network 'Net' might not establish the channel invariant (#6)"} (C[Net#d] - I[Net#d]) == (R[Net#c] - I[Net#c]);
  assert {:msg "Initialization of network 'Net' might not establish the channel invariant (#7)"} I[Net#c] == I[Net#b];
  assert {:msg "Initialization of network 'Net' might not establish the channel invariant (#8)"} true;
  I := R;
  assert {:msg "25.5: The initialization might produce unspecified tokens on channel a (#9)"} (C[Net#a] - R[Net#a]) == 0;
  assert {:msg "26.5: The initialization might produce unspecified tokens on channel b (#10)"} (C[Net#b] - R[Net#b]) == 0;
  assert {:msg "27.5: The initialization might produce unspecified tokens on channel c (#11)"} (C[Net#c] - R[Net#c]) == 0;
  assert {:msg "28.5: The initialization might produce unspecified tokens on channel d (#12)"} (C[Net#d] - R[Net#d]) == 0;
}
procedure Net##Route#a#7()
  modifies C, R, M, I;
{
  var Net#rou: Actor;
  var Net#rep: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (int);
  var Net#d: Chan (int);
  var in1#i: int;
  assume Net#rou != Net#rep;
  assume (Net#a != Net#b) && (Net#a != Net#c) && (Net#a != Net#d) && (Net#b != Net#c) && (Net#b != Net#d) && (Net#c != Net#d);
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume 0 <= I[Net#c];
  assume I[Net#c] <= R[Net#c];
  assume R[Net#c] <= C[Net#c];
  assume 0 <= I[Net#d];
  assume I[Net#d] <= R[Net#d];
  assume R[Net#d] <= C[Net#d];
  assume I[Net#d] == R[Net#d];
  assume (C[Net#b] - I[Net#b]) == (R[Net#a] - I[Net#a]);
  assume (C[Net#d] - I[Net#d]) == (R[Net#c] - I[Net#c]);
  assume I[Net#c] == I[Net#b];
  assume true;
  assume R[Net#b] == C[Net#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == M[Net#b][idx$])
  );
  assume 1 <= (C[Net#a] - R[Net#a]);
  in1#i := M[Net#a][R[Net#a]];
  R[Net#a] := R[Net#a] + 1;
  M[Net#b][C[Net#b]] := in1#i;
  C[Net#b] := C[Net#b] + 1;
  assert {:msg "16.15: Action at 2.3 ('a') for actor instance 'rou' might not preserve the channel invariant (#13)"} (C[Net#b] - I[Net#b]) == (R[Net#a] - I[Net#a]);
  assert {:msg "17.15: Action at 2.3 ('a') for actor instance 'rou' might not preserve the channel invariant (#14)"} (C[Net#d] - I[Net#d]) == (R[Net#c] - I[Net#c]);
  assert {:msg "Action at 2.3 ('a') for actor instance 'rou' might not preserve the channel invariant (#15)"} I[Net#c] == I[Net#b];
  assert {:msg "Action at 2.3 ('a') for actor instance 'rou' might not preserve the channel invariant (#16)"} true;
}
procedure Net##Route#b#8()
  modifies C, R, M, I;
{
  var Net#rou: Actor;
  var Net#rep: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (int);
  var Net#d: Chan (int);
  var in2#i: int;
  assume Net#rou != Net#rep;
  assume (Net#a != Net#b) && (Net#a != Net#c) && (Net#a != Net#d) && (Net#b != Net#c) && (Net#b != Net#d) && (Net#c != Net#d);
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume 0 <= I[Net#c];
  assume I[Net#c] <= R[Net#c];
  assume R[Net#c] <= C[Net#c];
  assume 0 <= I[Net#d];
  assume I[Net#d] <= R[Net#d];
  assume R[Net#d] <= C[Net#d];
  assume I[Net#d] == R[Net#d];
  assume (C[Net#b] - I[Net#b]) == (R[Net#a] - I[Net#a]);
  assume (C[Net#d] - I[Net#d]) == (R[Net#c] - I[Net#c]);
  assume I[Net#c] == I[Net#b];
  assume true;
  assume R[Net#b] == C[Net#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == M[Net#b][idx$])
  );
  assume (!(1 <= (C[Net#a] - R[Net#a]))) && (1 <= (C[Net#c] - R[Net#c]));
  in2#i := M[Net#c][R[Net#c]];
  R[Net#c] := R[Net#c] + 1;
  M[Net#d][C[Net#d]] := in2#i;
  C[Net#d] := C[Net#d] + 1;
  assert {:msg "16.15: Action at 3.3 ('b') for actor instance 'rou' might not preserve the channel invariant (#17)"} (C[Net#b] - I[Net#b]) == (R[Net#a] - I[Net#a]);
  assert {:msg "17.15: Action at 3.3 ('b') for actor instance 'rou' might not preserve the channel invariant (#18)"} (C[Net#d] - I[Net#d]) == (R[Net#c] - I[Net#c]);
  assert {:msg "Action at 3.3 ('b') for actor instance 'rou' might not preserve the channel invariant (#19)"} I[Net#c] == I[Net#b];
  assert {:msg "Action at 3.3 ('b') for actor instance 'rou' might not preserve the channel invariant (#20)"} true;
}
procedure Net##Repeat#anon$0#9()
  modifies C, R, M, I;
{
  var Net#rou: Actor;
  var Net#rep: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (int);
  var Net#d: Chan (int);
  var in#i: int;
  assume Net#rou != Net#rep;
  assume (Net#a != Net#b) && (Net#a != Net#c) && (Net#a != Net#d) && (Net#b != Net#c) && (Net#b != Net#d) && (Net#c != Net#d);
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume 0 <= I[Net#c];
  assume I[Net#c] <= R[Net#c];
  assume R[Net#c] <= C[Net#c];
  assume 0 <= I[Net#d];
  assume I[Net#d] <= R[Net#d];
  assume R[Net#d] <= C[Net#d];
  assume I[Net#d] == R[Net#d];
  assume (C[Net#b] - I[Net#b]) == (R[Net#a] - I[Net#a]);
  assume (C[Net#d] - I[Net#d]) == (R[Net#c] - I[Net#c]);
  assume I[Net#c] == I[Net#b];
  assume true;
  assume R[Net#b] == C[Net#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == M[Net#b][idx$])
  );
  assume 1 <= (C[Net#b] - R[Net#b]);
  assume R[Net#b] == C[Net#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == M[Net#b][idx$])
  );
  in#i := M[Net#b][R[Net#b]];
  R[Net#b] := R[Net#b] + 1;
  M[Net#c][C[Net#c]] := in#i;
  C[Net#c] := C[Net#c] + 1;
  assume R[Net#b] == C[Net#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == M[Net#b][idx$])
  );
  assert {:msg "16.15: Action at 8.3 ('anon$0') for actor instance 'rep' might not preserve the channel invariant (#21)"} (C[Net#b] - I[Net#b]) == (R[Net#a] - I[Net#a]);
  assert {:msg "17.15: Action at 8.3 ('anon$0') for actor instance 'rep' might not preserve the channel invariant (#22)"} (C[Net#d] - I[Net#d]) == (R[Net#c] - I[Net#c]);
  assert {:msg "Action at 8.3 ('anon$0') for actor instance 'rep' might not preserve the channel invariant (#23)"} I[Net#c] == I[Net#b];
  assert {:msg "Action at 8.3 ('anon$0') for actor instance 'rep' might not preserve the channel invariant (#24)"} true;
}
procedure Net#entry()
  modifies C, R, M, I;
{
  var Net#rou: Actor;
  var Net#rep: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (int);
  var Net#d: Chan (int);
  assume Net#rou != Net#rep;
  assume (Net#a != Net#b) && (Net#a != Net#c) && (Net#a != Net#d) && (Net#b != Net#c) && (Net#b != Net#d) && (Net#c != Net#d);
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume 0 <= I[Net#c];
  assume I[Net#c] <= R[Net#c];
  assume R[Net#c] <= C[Net#c];
  assume 0 <= I[Net#d];
  assume I[Net#d] <= R[Net#d];
  assume R[Net#d] <= C[Net#d];
  assume I[Net#d] == R[Net#d];
  assume C[Net#a] == R[Net#a];
  assume C[Net#b] == R[Net#b];
  assume C[Net#c] == R[Net#c];
  assume C[Net#d] == R[Net#d];
  assume (C[Net#b] - I[Net#b]) == (R[Net#a] - I[Net#a]);
  assume (C[Net#d] - I[Net#d]) == (R[Net#c] - I[Net#c]);
  assume I[Net#c] == I[Net#b];
  assume true;
  assume R[Net#b] == C[Net#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == M[Net#b][idx$])
  );
  assert {:msg "12.1: Sub-actors in the network might fire without network input. This is not permitted. (#25)"} !((!(1 <= (C[Net#a] - R[Net#a]))) && (1 <= (C[Net#c] - R[Net#c])));
  assert {:msg "12.1: Sub-actors in the network might fire without network input. This is not permitted. (#26)"} !(1 <= (C[Net#a] - R[Net#a]));
  assert {:msg "12.1: Sub-actors in the network might fire without network input. This is not permitted. (#27)"} !(1 <= (C[Net#b] - R[Net#b]));
}
procedure Net#anon$1#input#in#10()
  modifies C, R, M, I;
{
  var Net#rou: Actor;
  var Net#rep: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (int);
  var Net#d: Chan (int);
  assume Net#rou != Net#rep;
  assume (Net#a != Net#b) && (Net#a != Net#c) && (Net#a != Net#d) && (Net#b != Net#c) && (Net#b != Net#d) && (Net#c != Net#d);
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume 0 <= I[Net#c];
  assume I[Net#c] <= R[Net#c];
  assume R[Net#c] <= C[Net#c];
  assume 0 <= I[Net#d];
  assume I[Net#d] <= R[Net#d];
  assume R[Net#d] <= C[Net#d];
  assume I[Net#d] == R[Net#d];
  assume C[Net#a] < 1;
  assume (C[Net#b] - I[Net#b]) == (R[Net#a] - I[Net#a]);
  assume (C[Net#d] - I[Net#d]) == (R[Net#c] - I[Net#c]);
  assume I[Net#c] == I[Net#b];
  assume true;
  assume R[Net#b] == C[Net#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == M[Net#b][idx$])
  );
  C[Net#a] := C[Net#a] + 1;
  assert {:msg "16.15: Channel invariant might be falsified by network input (#28)"} (C[Net#b] - I[Net#b]) == (R[Net#a] - I[Net#a]);
  assert {:msg "17.15: Channel invariant might be falsified by network input (#29)"} (C[Net#d] - I[Net#d]) == (R[Net#c] - I[Net#c]);
  assert {:msg "Channel invariant might be falsified by network input (#30)"} I[Net#c] == I[Net#b];
  assert {:msg "Channel invariant might be falsified by network input (#31)"} true;
}
procedure Net#anon$1#exit#11()
  modifies C, R, M, I;
{
  var Net#rou: Actor;
  var Net#rep: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (int);
  var Net#d: Chan (int);
  assume Net#rou != Net#rep;
  assume (Net#a != Net#b) && (Net#a != Net#c) && (Net#a != Net#d) && (Net#b != Net#c) && (Net#b != Net#d) && (Net#c != Net#d);
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume 0 <= I[Net#c];
  assume I[Net#c] <= R[Net#c];
  assume R[Net#c] <= C[Net#c];
  assume 0 <= I[Net#d];
  assume I[Net#d] <= R[Net#d];
  assume R[Net#d] <= C[Net#d];
  assume I[Net#d] == R[Net#d];
  assume (C[Net#b] - I[Net#b]) == (R[Net#a] - I[Net#a]);
  assume (C[Net#d] - I[Net#d]) == (R[Net#c] - I[Net#c]);
  assume I[Net#c] == I[Net#b];
  assume true;
  assume R[Net#b] == C[Net#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == M[Net#b][idx$])
  );
  assume (C[Net#a] - I[Net#a]) == 1;
  assume !((!(1 <= (C[Net#a] - R[Net#a]))) && (1 <= (C[Net#c] - R[Net#c])));
  assume !(1 <= (C[Net#a] - R[Net#a]));
  assume !(1 <= (C[Net#b] - R[Net#b]));
  R[Net#d] := R[Net#d] + 1;
  I := R;
  assert {:msg "16.15: The network might not preserve the channel invariant (#32)"} (C[Net#b] - I[Net#b]) == (R[Net#a] - I[Net#a]);
  assert {:msg "17.15: The network might not preserve the channel invariant (#33)"} (C[Net#d] - I[Net#d]) == (R[Net#c] - I[Net#c]);
  assert {:msg "The network might not preserve the channel invariant (#34)"} I[Net#c] == I[Net#b];
  assert {:msg "The network might not preserve the channel invariant (#35)"} true;
  assert {:msg "14.3: The network might leave unread tokens on channel a (#36)"} C[Net#a] == R[Net#a];
  assert {:msg "14.3: The network might leave unread tokens on channel b (#37)"} C[Net#b] == R[Net#b];
  assert {:msg "14.3: The network might leave unread tokens on channel c (#38)"} C[Net#c] == R[Net#c];
  assert {:msg "14.3: The network might not produce the specified number of tokens on output out (#39)"} C[Net#d] == R[Net#d];
}

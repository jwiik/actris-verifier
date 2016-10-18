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

procedure Add#init#0()
  modifies C, R, M, I, St;
{
  var in1: Chan (int);
  var in2: Chan (int);
  var out: Chan (int);
  assume (in1 != in2) && (in1 != out) && (in2 != out);
  assume R[in1] == 0;
  assume R[in2] == 0;
  assume C[out] == 0;
  assert {:msg "Initialization might not establish the invariant (#0)"} R[in1] == C[out];
  assert {:msg "Initialization might not establish the invariant (#1)"} R[in2] == C[out];
  assert {:msg "Initialization might not establish the invariant (#2)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == (M[in1][idx$] + M[in2][idx$]))
  );
}
procedure Add#anon$0#1()
  modifies C, R, M, I, St;
{
  var in1: Chan (int);
  var in2: Chan (int);
  var out: Chan (int);
  var in1#0: int;
  var in2#0: int;
  assume (in1 != in2) && (in1 != out) && (in2 != out);
  assume 0 <= R[in1];
  assume 0 <= R[in2];
  assume 0 <= C[out];
  assume R[in1] == C[out];
  assume R[in2] == C[out];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == (M[in1][idx$] + M[in2][idx$]))
  );
  in1#0 := M[in1][R[in1]];
  R[in1] := R[in1] + 1;
  in2#0 := M[in2][R[in2]];
  R[in2] := R[in2] + 1;
  assume true;
  M[out][C[out]] := in1#0 + in2#0;
  C[out] := C[out] + 1;
  assert {:msg "Action at 3.3 might not preserve invariant (#3)"} R[in1] == C[out];
  assert {:msg "Action at 3.3 might not preserve invariant (#4)"} R[in2] == C[out];
  assert {:msg "Action at 3.3 might not preserve invariant (#5)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == (M[in1][idx$] + M[in2][idx$]))
  );
}
procedure Net#init#2()
  modifies C, R, M, I, St;
{
  var Net#add: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (int);
  assume (Net#a != Net#b) && (Net#a != Net#c) && (Net#b != Net#c);
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
  assume R[Net#a] == C[Net#c];
  assume R[Net#b] == C[Net#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assert {:msg "Initialization of network 'Net' might not establish the channel invariant (#6)"} I[Net#c] == I[Net#a];
  assert {:msg "Initialization of network 'Net' might not establish the channel invariant (#7)"} I[Net#c] == I[Net#b];
  I := R;
  assert {:msg "17.5: The initialization might produce unspecified tokens on channel a (#8)"} (C[Net#a] - R[Net#a]) == 0;
  assert {:msg "18.5: The initialization might produce unspecified tokens on channel b (#9)"} (C[Net#b] - R[Net#b]) == 0;
  assert {:msg "19.5: The initialization might produce unspecified tokens on channel c (#10)"} (C[Net#c] - R[Net#c]) == 0;
}
procedure Net##Add#anon$0#3()
  modifies C, R, M, I, St;
{
  var Net#add: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (int);
  var in1#i: int;
  var in2#j: int;
  assume (Net#a != Net#b) && (Net#a != Net#c) && (Net#b != Net#c);
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
  assume I[Net#c] == I[Net#a];
  assume I[Net#c] == I[Net#b];
  assume R[Net#a] == C[Net#c];
  assume R[Net#b] == C[Net#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assume (1 <= (C[Net#a] - R[Net#a])) && (1 <= (C[Net#b] - R[Net#b]));
  assume R[Net#a] == C[Net#c];
  assume R[Net#b] == C[Net#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  in1#i := M[Net#a][R[Net#a]];
  R[Net#a] := R[Net#a] + 1;
  in2#j := M[Net#b][R[Net#b]];
  R[Net#b] := R[Net#b] + 1;
  M[Net#c][C[Net#c]] := in1#i + in2#j;
  C[Net#c] := C[Net#c] + 1;
  assume R[Net#a] == C[Net#c];
  assume R[Net#b] == C[Net#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assert {:msg "Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#11)"} I[Net#c] == I[Net#a];
  assert {:msg "Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#12)"} I[Net#c] == I[Net#b];
}
procedure Net#entry()
  modifies C, R, M, I, St;
{
  var Net#add: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (int);
  assume (Net#a != Net#b) && (Net#a != Net#c) && (Net#b != Net#c);
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
  assume C[Net#a] == R[Net#a];
  assume C[Net#b] == R[Net#b];
  assume C[Net#c] == R[Net#c];
  assume I[Net#c] == I[Net#a];
  assume I[Net#c] == I[Net#b];
  assume R[Net#a] == C[Net#c];
  assume R[Net#b] == C[Net#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assert {:msg "6.1: Sub-actors in the network might fire without network input. This is not permitted. (#13)"} !((1 <= (C[Net#a] - R[Net#a])) && (1 <= (C[Net#b] - R[Net#b])));
}
procedure Net#anon$1#input#in1#4()
  modifies C, R, M, I, St;
{
  var Net#add: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (int);
  assume (Net#a != Net#b) && (Net#a != Net#c) && (Net#b != Net#c);
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
  assume C[Net#a] < 1;
  assume I[Net#c] == I[Net#a];
  assume I[Net#c] == I[Net#b];
  assume R[Net#a] == C[Net#c];
  assume R[Net#b] == C[Net#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  C[Net#a] := C[Net#a] + 1;
  assert {:msg "Channel invariant might be falsified by network input (#14)"} I[Net#c] == I[Net#a];
  assert {:msg "Channel invariant might be falsified by network input (#15)"} I[Net#c] == I[Net#b];
}
procedure Net#anon$1#input#in2#5()
  modifies C, R, M, I, St;
{
  var Net#add: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (int);
  assume (Net#a != Net#b) && (Net#a != Net#c) && (Net#b != Net#c);
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
  assume C[Net#b] < 1;
  assume I[Net#c] == I[Net#a];
  assume I[Net#c] == I[Net#b];
  assume R[Net#a] == C[Net#c];
  assume R[Net#b] == C[Net#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  C[Net#b] := C[Net#b] + 1;
  assert {:msg "Channel invariant might be falsified by network input (#16)"} I[Net#c] == I[Net#a];
  assert {:msg "Channel invariant might be falsified by network input (#17)"} I[Net#c] == I[Net#b];
}
procedure Net#anon$1#exit#6()
  modifies C, R, M, I, St;
{
  var Net#add: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (int);
  assume (Net#a != Net#b) && (Net#a != Net#c) && (Net#b != Net#c);
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
  assume I[Net#c] == I[Net#a];
  assume I[Net#c] == I[Net#b];
  assume R[Net#a] == C[Net#c];
  assume R[Net#b] == C[Net#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assume (C[Net#a] - I[Net#a]) == 1;
  assume (C[Net#b] - I[Net#b]) == 1;
  assume !((1 <= (C[Net#a] - R[Net#a])) && (1 <= (C[Net#b] - R[Net#b])));
  assert {:msg "9.13: Network action postcondition might not hold (#18)"} M[Net#c][I[Net#c]] == (M[Net#a][I[Net#a]] + M[Net#b][I[Net#b]]);
  R[Net#c] := R[Net#c] + 1;
  I := R;
  assert {:msg "The network might not preserve the channel invariant (#19)"} I[Net#c] == I[Net#a];
  assert {:msg "The network might not preserve the channel invariant (#20)"} I[Net#c] == I[Net#b];
  assert {:msg "8.3: The network might leave unread tokens on channel a (#21)"} C[Net#a] == R[Net#a];
  assert {:msg "8.3: The network might leave unread tokens on channel b (#22)"} C[Net#b] == R[Net#b];
  assert {:msg "8.3: The network might not produce the specified number of tokens on output out (#23)"} C[Net#c] == R[Net#c];
}

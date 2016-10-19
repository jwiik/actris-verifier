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

procedure Repeat#init#0()
  modifies C, R, M, I, St;
{
  var in: Chan (int);
  var out: Chan (int);
  assume in != out;
  assume R[in] == 0;
  assume C[out] == 0;
  assert {:msg "Initialization might not establish the invariant (#0)"} R[in] == C[out];
  assert {:msg "Initialization might not establish the invariant (#1)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == M[in][idx$])
  );
}
procedure Repeat#anon$0#1()
  modifies C, R, M, I, St;
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
  assert {:msg "Action at 2.3 might not preserve invariant (#2)"} R[in] == C[out];
  assert {:msg "Action at 2.3 might not preserve invariant (#3)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == M[in][idx$])
  );
}
procedure Delay#init#2()
  modifies C, R, M, I, St;
{
  var in: Chan (int);
  var out: Chan (int);
  var k: int;
  assume in != out;
  assume R[in] == 0;
  assume C[out] == 0;
  assume true;
  M[out][C[out]] := k;
  C[out] := C[out] + 1;
  assert {:msg "Initialization might not establish the invariant (#4)"} R[in] == (C[out] - 1);
  assert {:msg "Initialization might not establish the invariant (#5)"} (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == M[in][idx$ - 1])
  );
}
procedure Delay#anon$2#3()
  modifies C, R, M, I, St;
{
  var in: Chan (int);
  var out: Chan (int);
  var k: int;
  var in#0: int;
  assume in != out;
  assume 0 <= R[in];
  assume 0 <= C[out];
  assume R[in] == (C[out] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == M[in][idx$ - 1])
  );
  in#0 := M[in][R[in]];
  R[in] := R[in] + 1;
  assume true;
  M[out][C[out]] := in#0;
  C[out] := C[out] + 1;
  assert {:msg "Action at 7.3 might not preserve invariant (#6)"} R[in] == (C[out] - 1);
  assert {:msg "Action at 7.3 might not preserve invariant (#7)"} (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == M[in][idx$ - 1])
  );
}
procedure Net#init#4()
  modifies C, R, M, I, St;
{
  var Net#del: Actor;
  var Net#rep: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (int);
  assume Net#del != Net#rep;
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
  assume 0 == 0;
  M[Net#b][C[Net#b]] := 0;
  C[Net#b] := C[Net#b] + 1;
  assume R[Net#a] == (C[Net#b] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == M[Net#a][idx$ - 1])
  );
  assume R[Net#b] == C[Net#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == M[Net#b][idx$])
  );
  assert {:msg "Initialization of network 'Net' might not establish the channel invariant (#8)"} I[Net#b] == I[Net#a];
  assert {:msg "Initialization of network 'Net' might not establish the channel invariant (#9)"} I[Net#c] == I[Net#b];
  assert {:msg "Initialization of network 'Net' might not establish the channel invariant (#10)"} true;
  I := R;
  C[Net#b] := C[Net#b] - 1;
  assert {:msg "22.5: The initialization might produce unspecified tokens on channel a (#11)"} (C[Net#a] - R[Net#a]) == 0;
  assert {:msg "23.5: The initialization might produce unspecified tokens on channel b (#12)"} (C[Net#b] - R[Net#b]) == 0;
  assert {:msg "24.5: The initialization might produce unspecified tokens on channel c (#13)"} (C[Net#c] - R[Net#c]) == 0;
}
procedure Net##Delay#anon$2#5()
  modifies C, R, M, I, St;
{
  var Net#del: Actor;
  var Net#rep: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (int);
  var in#i: int;
  assume Net#del != Net#rep;
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
  assume I[Net#b] == I[Net#a];
  assume I[Net#c] == I[Net#b];
  assume true;
  assume R[Net#a] == (C[Net#b] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == M[Net#a][idx$ - 1])
  );
  assume R[Net#b] == C[Net#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == M[Net#b][idx$])
  );
  assume 1 <= (C[Net#a] - R[Net#a]);
  assume R[Net#a] == (C[Net#b] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == M[Net#a][idx$ - 1])
  );
  in#i := M[Net#a][R[Net#a]];
  R[Net#a] := R[Net#a] + 1;
  M[Net#b][C[Net#b]] := in#i;
  C[Net#b] := C[Net#b] + 1;
  assume R[Net#a] == (C[Net#b] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == M[Net#a][idx$ - 1])
  );
  assert {:msg "Action at 7.3 ('anon$2') for actor instance 'del' might not preserve the channel invariant (#14)"} I[Net#b] == I[Net#a];
  assert {:msg "Action at 7.3 ('anon$2') for actor instance 'del' might not preserve the channel invariant (#15)"} I[Net#c] == I[Net#b];
  assert {:msg "Action at 7.3 ('anon$2') for actor instance 'del' might not preserve the channel invariant (#16)"} true;
}
procedure Net##Repeat#anon$0#6()
  modifies C, R, M, I, St;
{
  var Net#del: Actor;
  var Net#rep: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (int);
  var in#i: int;
  assume Net#del != Net#rep;
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
  assume I[Net#b] == I[Net#a];
  assume I[Net#c] == I[Net#b];
  assume true;
  assume R[Net#a] == (C[Net#b] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == M[Net#a][idx$ - 1])
  );
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
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'rep' might not preserve the channel invariant (#17)"} I[Net#b] == I[Net#a];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'rep' might not preserve the channel invariant (#18)"} I[Net#c] == I[Net#b];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'rep' might not preserve the channel invariant (#19)"} true;
}
procedure Net#entry()
  modifies C, R, M, I, St;
{
  var Net#del: Actor;
  var Net#rep: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (int);
  assume Net#del != Net#rep;
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
  C[Net#b] := C[Net#b] + 1;
  assume I[Net#b] == I[Net#a];
  assume I[Net#c] == I[Net#b];
  assume true;
  assume R[Net#a] == (C[Net#b] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == M[Net#a][idx$ - 1])
  );
  assume R[Net#b] == C[Net#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == M[Net#b][idx$])
  );
  assert {:msg "10.1: Sub-actors in the network might fire without network input. This is not permitted. (#20)"} !(1 <= (C[Net#a] - R[Net#a]));
  assert {:msg "10.1: Sub-actors in the network might fire without network input. This is not permitted. (#21)"} !(1 <= (C[Net#b] - R[Net#b]));
}
procedure Net#anon$3#input#in#7()
  modifies C, R, M, I, St;
{
  var Net#del: Actor;
  var Net#rep: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (int);
  assume Net#del != Net#rep;
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
  assume I[Net#b] == I[Net#a];
  assume I[Net#c] == I[Net#b];
  assume true;
  assume R[Net#a] == (C[Net#b] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == M[Net#a][idx$ - 1])
  );
  assume R[Net#b] == C[Net#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == M[Net#b][idx$])
  );
  C[Net#a] := C[Net#a] + 1;
  assert {:msg "Channel invariant might be falsified by network input (#22)"} I[Net#b] == I[Net#a];
  assert {:msg "Channel invariant might be falsified by network input (#23)"} I[Net#c] == I[Net#b];
  assert {:msg "Channel invariant might be falsified by network input (#24)"} true;
}
procedure Net#anon$3#exit#8()
  modifies C, R, M, I, St;
{
  var Net#del: Actor;
  var Net#rep: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (int);
  assume Net#del != Net#rep;
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
  assume I[Net#b] == I[Net#a];
  assume I[Net#c] == I[Net#b];
  assume true;
  assume R[Net#a] == (C[Net#b] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == M[Net#a][idx$ - 1])
  );
  assume R[Net#b] == C[Net#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == M[Net#b][idx$])
  );
  assume (C[Net#a] - I[Net#a]) == 1;
  assume !(1 <= (C[Net#a] - R[Net#a]));
  assume !(1 <= (C[Net#b] - R[Net#b]));
  R[Net#c] := R[Net#c] + 1;
  I := R;
  assert {:msg "The network might not preserve the channel invariant (#25)"} I[Net#b] == I[Net#a];
  assert {:msg "The network might not preserve the channel invariant (#26)"} I[Net#c] == I[Net#b];
  assert {:msg "The network might not preserve the channel invariant (#27)"} true;
  C[Net#b] := C[Net#b] - 1;
  assert {:msg "12.3: The network might leave unread tokens on channel a (#28)"} C[Net#a] == R[Net#a];
  assert {:msg "12.3: The network might leave unread tokens on channel b (#29)"} C[Net#b] == R[Net#b];
  assert {:msg "12.3: The network might not produce the specified number of tokens on output out (#30)"} C[Net#c] == R[Net#c];
}

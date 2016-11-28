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

function AT#Abs(x: int): int { if 0 <= x then x else -x }
function AT#Div(int, int): int;
function AT#Mod(int, int): int;
axiom (forall a,b: int :: AT#Div(a,b)*b + AT#Mod(a,b) == a);
axiom (forall a,b: int :: 0 <= AT#Mod(a,b) && AT#Mod(a,b) < AT#Abs(b));

// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

procedure Repeater#init#0()
  modifies C, R, M, I;
{
  var in: Chan (int);
  var out: Chan (int);
  assume in != out;
  assume R[in] == 0;
  assume C[out] == 0;
  assert {:msg "Initialization might not establish the invariant (#0)"} (2 * R[in]) == C[out];
  assert {:msg "Initialization might not establish the invariant (#1)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) && (AT#Mod(idx$, 2) == 0) ==> (M[out][idx$] == M[in][AT#Div(idx$, 2)])
  );
  assert {:msg "Initialization might not establish the invariant (#2)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) && (AT#Mod(idx$, 2) == 1) ==> (M[out][idx$] == M[in][AT#Div(idx$, 2)])
  );
}
procedure Repeater#anon$0#1()
  modifies C, R, M, I;
{
  var in: Chan (int);
  var out: Chan (int);
  var in#0: int;
  assume in != out;
  assume 0 <= R[in];
  assume 0 <= C[out];
  assume (2 * R[in]) == C[out];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) && (AT#Mod(idx$, 2) == 0) ==> (M[out][idx$] == M[in][AT#Div(idx$, 2)])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) && (AT#Mod(idx$, 2) == 1) ==> (M[out][idx$] == M[in][AT#Div(idx$, 2)])
  );
  in#0 := M[in][R[in]];
  R[in] := R[in] + 1;
  assume true;
  M[out][C[out]] := in#0;
  C[out] := C[out] + 1;
  M[out][C[out]] := in#0;
  C[out] := C[out] + 1;
  assert {:msg "Action at 2.3 might not preserve invariant (#3)"} (2 * R[in]) == C[out];
  assert {:msg "Action at 2.3 might not preserve invariant (#4)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) && (AT#Mod(idx$, 2) == 0) ==> (M[out][idx$] == M[in][AT#Div(idx$, 2)])
  );
  assert {:msg "Action at 2.3 might not preserve invariant (#5)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) && (AT#Mod(idx$, 2) == 1) ==> (M[out][idx$] == M[in][AT#Div(idx$, 2)])
  );
}
procedure Net#init#2()
  modifies C, R, M, I;
{
  var Net#rep: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  assume Net#a != Net#b;
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
  assume (2 * R[Net#a]) == C[Net#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) && (AT#Mod(idx$, 2) == 0) ==> (M[Net#b][idx$] == M[Net#a][AT#Div(idx$, 2)])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) && (AT#Mod(idx$, 2) == 1) ==> (M[Net#b][idx$] == M[Net#a][AT#Div(idx$, 2)])
  );
  assert {:msg "9.15: Initialization of network 'Net' might not establish the channel invariant (#6)"} (2 * I[Net#a]) == I[Net#b];
  assert {:msg "10.15: Initialization of network 'Net' might not establish the channel invariant (#7)"} (2 * (R[Net#a] - I[Net#a])) == (C[Net#b] - I[Net#b]);
  assert {:msg "Initialization of network 'Net' might not establish the channel invariant (#8)"} I[Net#b] == (2 * I[Net#a]);
  assert {:msg "Initialization of network 'Net' might not establish the channel invariant (#9)"} true;
  I := R;
  assert {:msg "17.5: The initialization might produce unspecified tokens on channel a (#10)"} (C[Net#a] - R[Net#a]) == 0;
  assert {:msg "18.5: The initialization might produce unspecified tokens on channel b (#11)"} (C[Net#b] - R[Net#b]) == 0;
}
procedure Net##Repeater#anon$0#3()
  modifies C, R, M, I;
{
  var Net#rep: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var in#i: int;
  assume Net#a != Net#b;
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume I[Net#b] == R[Net#b];
  assume (2 * I[Net#a]) == I[Net#b];
  assume (2 * (R[Net#a] - I[Net#a])) == (C[Net#b] - I[Net#b]);
  assume I[Net#b] == (2 * I[Net#a]);
  assume true;
  assume (2 * R[Net#a]) == C[Net#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) && (AT#Mod(idx$, 2) == 0) ==> (M[Net#b][idx$] == M[Net#a][AT#Div(idx$, 2)])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) && (AT#Mod(idx$, 2) == 1) ==> (M[Net#b][idx$] == M[Net#a][AT#Div(idx$, 2)])
  );
  assume 1 <= (C[Net#a] - R[Net#a]);
  assume (2 * R[Net#a]) == C[Net#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) && (AT#Mod(idx$, 2) == 0) ==> (M[Net#b][idx$] == M[Net#a][AT#Div(idx$, 2)])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) && (AT#Mod(idx$, 2) == 1) ==> (M[Net#b][idx$] == M[Net#a][AT#Div(idx$, 2)])
  );
  in#i := M[Net#a][R[Net#a]];
  R[Net#a] := R[Net#a] + 1;
  M[Net#b][C[Net#b]] := in#i;
  C[Net#b] := C[Net#b] + 1;
  M[Net#b][C[Net#b]] := in#i;
  C[Net#b] := C[Net#b] + 1;
  assume (2 * R[Net#a]) == C[Net#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) && (AT#Mod(idx$, 2) == 0) ==> (M[Net#b][idx$] == M[Net#a][AT#Div(idx$, 2)])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) && (AT#Mod(idx$, 2) == 1) ==> (M[Net#b][idx$] == M[Net#a][AT#Div(idx$, 2)])
  );
  assert {:msg "9.15: Action at 2.3 ('anon$0') for actor instance 'rep' might not preserve the channel invariant (#12)"} (2 * I[Net#a]) == I[Net#b];
  assert {:msg "10.15: Action at 2.3 ('anon$0') for actor instance 'rep' might not preserve the channel invariant (#13)"} (2 * (R[Net#a] - I[Net#a])) == (C[Net#b] - I[Net#b]);
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'rep' might not preserve the channel invariant (#14)"} I[Net#b] == (2 * I[Net#a]);
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'rep' might not preserve the channel invariant (#15)"} true;
}
procedure Net#entry()
  modifies C, R, M, I;
{
  var Net#rep: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  assume Net#a != Net#b;
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume I[Net#b] == R[Net#b];
  assume C[Net#a] == R[Net#a];
  assume C[Net#b] == R[Net#b];
  assume (2 * I[Net#a]) == I[Net#b];
  assume (2 * (R[Net#a] - I[Net#a])) == (C[Net#b] - I[Net#b]);
  assume I[Net#b] == (2 * I[Net#a]);
  assume true;
  assume (2 * R[Net#a]) == C[Net#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) && (AT#Mod(idx$, 2) == 0) ==> (M[Net#b][idx$] == M[Net#a][AT#Div(idx$, 2)])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) && (AT#Mod(idx$, 2) == 1) ==> (M[Net#b][idx$] == M[Net#a][AT#Div(idx$, 2)])
  );
  assert {:msg "5.1: Sub-actors in the network might fire without network input. This is not permitted. (#16)"} !(1 <= (C[Net#a] - R[Net#a]));
}
procedure Net#anon$1#input#in#4()
  modifies C, R, M, I;
{
  var Net#rep: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  assume Net#a != Net#b;
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume I[Net#b] == R[Net#b];
  assume C[Net#a] < 1;
  assume (2 * I[Net#a]) == I[Net#b];
  assume (2 * (R[Net#a] - I[Net#a])) == (C[Net#b] - I[Net#b]);
  assume I[Net#b] == (2 * I[Net#a]);
  assume true;
  assume (2 * R[Net#a]) == C[Net#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) && (AT#Mod(idx$, 2) == 0) ==> (M[Net#b][idx$] == M[Net#a][AT#Div(idx$, 2)])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) && (AT#Mod(idx$, 2) == 1) ==> (M[Net#b][idx$] == M[Net#a][AT#Div(idx$, 2)])
  );
  C[Net#a] := C[Net#a] + 1;
  assert {:msg "9.15: Channel invariant might be falsified by network input (#17)"} (2 * I[Net#a]) == I[Net#b];
  assert {:msg "10.15: Channel invariant might be falsified by network input (#18)"} (2 * (R[Net#a] - I[Net#a])) == (C[Net#b] - I[Net#b]);
  assert {:msg "Channel invariant might be falsified by network input (#19)"} I[Net#b] == (2 * I[Net#a]);
  assert {:msg "Channel invariant might be falsified by network input (#20)"} true;
}
procedure Net#anon$1#exit#5()
  modifies C, R, M, I;
{
  var Net#rep: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  assume Net#a != Net#b;
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume I[Net#b] == R[Net#b];
  assume (2 * I[Net#a]) == I[Net#b];
  assume (2 * (R[Net#a] - I[Net#a])) == (C[Net#b] - I[Net#b]);
  assume I[Net#b] == (2 * I[Net#a]);
  assume true;
  assume (2 * R[Net#a]) == C[Net#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) && (AT#Mod(idx$, 2) == 0) ==> (M[Net#b][idx$] == M[Net#a][AT#Div(idx$, 2)])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) && (AT#Mod(idx$, 2) == 1) ==> (M[Net#b][idx$] == M[Net#a][AT#Div(idx$, 2)])
  );
  assume (C[Net#a] - I[Net#a]) == 1;
  assume !(1 <= (C[Net#a] - R[Net#a]));
  R[Net#b] := R[Net#b] + 2;
  I := R;
  assert {:msg "9.15: The network might not preserve the channel invariant (#21)"} (2 * I[Net#a]) == I[Net#b];
  assert {:msg "10.15: The network might not preserve the channel invariant (#22)"} (2 * (R[Net#a] - I[Net#a])) == (C[Net#b] - I[Net#b]);
  assert {:msg "The network might not preserve the channel invariant (#23)"} I[Net#b] == (2 * I[Net#a]);
  assert {:msg "The network might not preserve the channel invariant (#24)"} true;
  assert {:msg "7.3: The network might leave unread tokens on channel a (#25)"} C[Net#a] == R[Net#a];
  assert {:msg "7.3: The network might not produce the specified number of tokens on output out (#26)"} C[Net#b] == R[Net#b];
}

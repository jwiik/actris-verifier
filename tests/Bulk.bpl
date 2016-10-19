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

function AT#Abs(x: int): int { if 0 <= x then x else -x }
function AT#Div(int, int): int;
function AT#Mod(int, int): int;
axiom (forall a,b: int :: AT#Div(a,b)*b + AT#Mod(a,b) == a);
axiom (forall a,b: int :: 0 <= AT#Mod(a,b) && AT#Mod(a,b) < AT#Abs(b));

// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

procedure AddSeq#init#0()
  modifies C, R, M, I, St;
{
  var in: Chan (int);
  var out: Chan (int);
  assume in != out;
  assume R[in] == 0;
  assume C[out] == 0;
  assert {:msg "Initialization might not establish the invariant (#0)"} R[in] == (2 * C[out]);
  assert {:msg "Initialization might not establish the invariant (#1)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == (M[in][2 * idx$] + M[in][(2 * idx$) + 1]))
  );
}
procedure AddSeq#anon$0#1()
  modifies C, R, M, I, St;
{
  var in: Chan (int);
  var out: Chan (int);
  var in#0: int;
  var in#1: int;
  assume in != out;
  assume 0 <= R[in];
  assume 0 <= C[out];
  assume R[in] == (2 * C[out]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == (M[in][2 * idx$] + M[in][(2 * idx$) + 1]))
  );
  in#0 := M[in][R[in]];
  R[in] := R[in] + 1;
  in#1 := M[in][R[in]];
  R[in] := R[in] + 1;
  assume true;
  M[out][C[out]] := in#0 + in#1;
  C[out] := C[out] + 1;
  assert {:msg "Action at 3.3 might not preserve invariant (#2)"} R[in] == (2 * C[out]);
  assert {:msg "Action at 3.3 might not preserve invariant (#3)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == (M[in][2 * idx$] + M[in][(2 * idx$) + 1]))
  );
}
procedure Mod4#init#2()
  modifies C, R, M, I, St;
{
  var in: Chan (int);
  var out: Chan (int);
  assume in != out;
  assume R[in] == 0;
  assume C[out] == 0;
  assert {:msg "Initialization might not establish the invariant (#4)"} R[in] == C[out];
  assert {:msg "Initialization might not establish the invariant (#5)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == AT#Mod(M[in][idx$], 4))
  );
}
procedure Mod4#anon$1#3()
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
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == AT#Mod(M[in][idx$], 4))
  );
  in#0 := M[in][R[in]];
  R[in] := R[in] + 1;
  assume true;
  M[out][C[out]] := AT#Mod(in#0, 4);
  C[out] := C[out] + 1;
  assert {:msg "Action at 8.3 might not preserve invariant (#6)"} R[in] == C[out];
  assert {:msg "Action at 8.3 might not preserve invariant (#7)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == AT#Mod(M[in][idx$], 4))
  );
}
procedure SumMod4#init#4()
  modifies C, R, M, I, St;
{
  var SumMod4#add: Actor;
  var SumMod4#mod: Actor;
  var SumMod4#a: Chan (int);
  var SumMod4#b: Chan (int);
  var SumMod4#c: Chan (int);
  assume SumMod4#add != SumMod4#mod;
  assume (SumMod4#a != SumMod4#b) && (SumMod4#a != SumMod4#c) && (SumMod4#b != SumMod4#c);
  assume 0 <= I[SumMod4#a];
  assume I[SumMod4#a] <= R[SumMod4#a];
  assume R[SumMod4#a] <= C[SumMod4#a];
  assume 0 <= I[SumMod4#b];
  assume I[SumMod4#b] <= R[SumMod4#b];
  assume R[SumMod4#b] <= C[SumMod4#b];
  assume 0 <= I[SumMod4#c];
  assume I[SumMod4#c] <= R[SumMod4#c];
  assume R[SumMod4#c] <= C[SumMod4#c];
  assume I[SumMod4#c] == R[SumMod4#c];
  assume C[SumMod4#a] == 0;
  assume R[SumMod4#a] == 0;
  assume C[SumMod4#b] == 0;
  assume R[SumMod4#b] == 0;
  assume C[SumMod4#c] == 0;
  assume R[SumMod4#c] == 0;
  assume R[SumMod4#a] == (2 * C[SumMod4#b]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumMod4#b]) ==> (M[SumMod4#b][idx$] == (M[SumMod4#a][2 * idx$] + M[SumMod4#a][(2 * idx$) + 1]))
  );
  assume R[SumMod4#b] == C[SumMod4#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumMod4#c]) ==> (M[SumMod4#c][idx$] == AT#Mod(M[SumMod4#b][idx$], 4))
  );
  assert {:msg "18.15: Initialization of network 'SumMod4' might not establish the channel invariant (#8)"} (2 * I[SumMod4#b]) == I[SumMod4#a];
  assert {:msg "19.15: Initialization of network 'SumMod4' might not establish the channel invariant (#9)"} I[SumMod4#c] == I[SumMod4#b];
  assert {:msg "20.16: Initialization of network 'SumMod4' might not establish the channel invariant (#10)"} (forall i: int :: 
    (I[SumMod4#a] <= i) && (i < C[SumMod4#a]) ==> (AT#Mod(M[SumMod4#a][i], 2) == 1)
  );
  assert {:msg "21.16: Initialization of network 'SumMod4' might not establish the channel invariant (#11)"} (forall i: int :: 
    (I[SumMod4#b] <= i) && (i < C[SumMod4#b]) ==> (AT#Mod(M[SumMod4#b][i], 2) == 0)
  );
  assert {:msg "Initialization of network 'SumMod4' might not establish the channel invariant (#12)"} (2 * I[SumMod4#b]) == I[SumMod4#a];
  assert {:msg "Initialization of network 'SumMod4' might not establish the channel invariant (#13)"} I[SumMod4#c] == I[SumMod4#b];
  I := R;
  assert {:msg "30.5: The initialization might produce unspecified tokens on channel a (#14)"} (C[SumMod4#a] - R[SumMod4#a]) == 0;
  assert {:msg "31.5: The initialization might produce unspecified tokens on channel b (#15)"} (C[SumMod4#b] - R[SumMod4#b]) == 0;
  assert {:msg "32.5: The initialization might produce unspecified tokens on channel c (#16)"} (C[SumMod4#c] - R[SumMod4#c]) == 0;
}
procedure SumMod4##AddSeq#anon$0#5()
  modifies C, R, M, I, St;
{
  var SumMod4#add: Actor;
  var SumMod4#mod: Actor;
  var SumMod4#a: Chan (int);
  var SumMod4#b: Chan (int);
  var SumMod4#c: Chan (int);
  var in#i: int;
  var in#j: int;
  assume SumMod4#add != SumMod4#mod;
  assume (SumMod4#a != SumMod4#b) && (SumMod4#a != SumMod4#c) && (SumMod4#b != SumMod4#c);
  assume 0 <= I[SumMod4#a];
  assume I[SumMod4#a] <= R[SumMod4#a];
  assume R[SumMod4#a] <= C[SumMod4#a];
  assume 0 <= I[SumMod4#b];
  assume I[SumMod4#b] <= R[SumMod4#b];
  assume R[SumMod4#b] <= C[SumMod4#b];
  assume 0 <= I[SumMod4#c];
  assume I[SumMod4#c] <= R[SumMod4#c];
  assume R[SumMod4#c] <= C[SumMod4#c];
  assume I[SumMod4#c] == R[SumMod4#c];
  assume (2 * I[SumMod4#b]) == I[SumMod4#a];
  assume I[SumMod4#c] == I[SumMod4#b];
  assume (forall i: int :: 
    (I[SumMod4#a] <= i) && (i < C[SumMod4#a]) ==> (AT#Mod(M[SumMod4#a][i], 2) == 1)
  );
  assume (forall i: int :: 
    (I[SumMod4#b] <= i) && (i < C[SumMod4#b]) ==> (AT#Mod(M[SumMod4#b][i], 2) == 0)
  );
  assume (2 * I[SumMod4#b]) == I[SumMod4#a];
  assume I[SumMod4#c] == I[SumMod4#b];
  assume R[SumMod4#a] == (2 * C[SumMod4#b]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumMod4#b]) ==> (M[SumMod4#b][idx$] == (M[SumMod4#a][2 * idx$] + M[SumMod4#a][(2 * idx$) + 1]))
  );
  assume R[SumMod4#b] == C[SumMod4#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumMod4#c]) ==> (M[SumMod4#c][idx$] == AT#Mod(M[SumMod4#b][idx$], 4))
  );
  assume 2 <= (C[SumMod4#a] - R[SumMod4#a]);
  assume R[SumMod4#a] == (2 * C[SumMod4#b]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumMod4#b]) ==> (M[SumMod4#b][idx$] == (M[SumMod4#a][2 * idx$] + M[SumMod4#a][(2 * idx$) + 1]))
  );
  in#i := M[SumMod4#a][R[SumMod4#a]];
  R[SumMod4#a] := R[SumMod4#a] + 1;
  in#j := M[SumMod4#a][R[SumMod4#a]];
  R[SumMod4#a] := R[SumMod4#a] + 1;
  M[SumMod4#b][C[SumMod4#b]] := in#i + in#j;
  C[SumMod4#b] := C[SumMod4#b] + 1;
  assume R[SumMod4#a] == (2 * C[SumMod4#b]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumMod4#b]) ==> (M[SumMod4#b][idx$] == (M[SumMod4#a][2 * idx$] + M[SumMod4#a][(2 * idx$) + 1]))
  );
  assert {:msg "18.15: Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#17)"} (2 * I[SumMod4#b]) == I[SumMod4#a];
  assert {:msg "19.15: Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#18)"} I[SumMod4#c] == I[SumMod4#b];
  assert {:msg "20.16: Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#19)"} (forall i: int :: 
    (I[SumMod4#a] <= i) && (i < C[SumMod4#a]) ==> (AT#Mod(M[SumMod4#a][i], 2) == 1)
  );
  assert {:msg "21.16: Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#20)"} (forall i: int :: 
    (I[SumMod4#b] <= i) && (i < C[SumMod4#b]) ==> (AT#Mod(M[SumMod4#b][i], 2) == 0)
  );
  assert {:msg "Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#21)"} (2 * I[SumMod4#b]) == I[SumMod4#a];
  assert {:msg "Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#22)"} I[SumMod4#c] == I[SumMod4#b];
}
procedure SumMod4##Mod4#anon$1#6()
  modifies C, R, M, I, St;
{
  var SumMod4#add: Actor;
  var SumMod4#mod: Actor;
  var SumMod4#a: Chan (int);
  var SumMod4#b: Chan (int);
  var SumMod4#c: Chan (int);
  var in#i: int;
  assume SumMod4#add != SumMod4#mod;
  assume (SumMod4#a != SumMod4#b) && (SumMod4#a != SumMod4#c) && (SumMod4#b != SumMod4#c);
  assume 0 <= I[SumMod4#a];
  assume I[SumMod4#a] <= R[SumMod4#a];
  assume R[SumMod4#a] <= C[SumMod4#a];
  assume 0 <= I[SumMod4#b];
  assume I[SumMod4#b] <= R[SumMod4#b];
  assume R[SumMod4#b] <= C[SumMod4#b];
  assume 0 <= I[SumMod4#c];
  assume I[SumMod4#c] <= R[SumMod4#c];
  assume R[SumMod4#c] <= C[SumMod4#c];
  assume I[SumMod4#c] == R[SumMod4#c];
  assume (2 * I[SumMod4#b]) == I[SumMod4#a];
  assume I[SumMod4#c] == I[SumMod4#b];
  assume (forall i: int :: 
    (I[SumMod4#a] <= i) && (i < C[SumMod4#a]) ==> (AT#Mod(M[SumMod4#a][i], 2) == 1)
  );
  assume (forall i: int :: 
    (I[SumMod4#b] <= i) && (i < C[SumMod4#b]) ==> (AT#Mod(M[SumMod4#b][i], 2) == 0)
  );
  assume (2 * I[SumMod4#b]) == I[SumMod4#a];
  assume I[SumMod4#c] == I[SumMod4#b];
  assume R[SumMod4#a] == (2 * C[SumMod4#b]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumMod4#b]) ==> (M[SumMod4#b][idx$] == (M[SumMod4#a][2 * idx$] + M[SumMod4#a][(2 * idx$) + 1]))
  );
  assume R[SumMod4#b] == C[SumMod4#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumMod4#c]) ==> (M[SumMod4#c][idx$] == AT#Mod(M[SumMod4#b][idx$], 4))
  );
  assume 1 <= (C[SumMod4#b] - R[SumMod4#b]);
  assume R[SumMod4#b] == C[SumMod4#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumMod4#c]) ==> (M[SumMod4#c][idx$] == AT#Mod(M[SumMod4#b][idx$], 4))
  );
  in#i := M[SumMod4#b][R[SumMod4#b]];
  R[SumMod4#b] := R[SumMod4#b] + 1;
  M[SumMod4#c][C[SumMod4#c]] := AT#Mod(in#i, 4);
  C[SumMod4#c] := C[SumMod4#c] + 1;
  assume R[SumMod4#b] == C[SumMod4#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumMod4#c]) ==> (M[SumMod4#c][idx$] == AT#Mod(M[SumMod4#b][idx$], 4))
  );
  assert {:msg "18.15: Action at 8.3 ('anon$1') for actor instance 'mod' might not preserve the channel invariant (#23)"} (2 * I[SumMod4#b]) == I[SumMod4#a];
  assert {:msg "19.15: Action at 8.3 ('anon$1') for actor instance 'mod' might not preserve the channel invariant (#24)"} I[SumMod4#c] == I[SumMod4#b];
  assert {:msg "20.16: Action at 8.3 ('anon$1') for actor instance 'mod' might not preserve the channel invariant (#25)"} (forall i: int :: 
    (I[SumMod4#a] <= i) && (i < C[SumMod4#a]) ==> (AT#Mod(M[SumMod4#a][i], 2) == 1)
  );
  assert {:msg "21.16: Action at 8.3 ('anon$1') for actor instance 'mod' might not preserve the channel invariant (#26)"} (forall i: int :: 
    (I[SumMod4#b] <= i) && (i < C[SumMod4#b]) ==> (AT#Mod(M[SumMod4#b][i], 2) == 0)
  );
  assert {:msg "Action at 8.3 ('anon$1') for actor instance 'mod' might not preserve the channel invariant (#27)"} (2 * I[SumMod4#b]) == I[SumMod4#a];
  assert {:msg "Action at 8.3 ('anon$1') for actor instance 'mod' might not preserve the channel invariant (#28)"} I[SumMod4#c] == I[SumMod4#b];
}
procedure SumMod4#entry()
  modifies C, R, M, I, St;
{
  var SumMod4#add: Actor;
  var SumMod4#mod: Actor;
  var SumMod4#a: Chan (int);
  var SumMod4#b: Chan (int);
  var SumMod4#c: Chan (int);
  assume SumMod4#add != SumMod4#mod;
  assume (SumMod4#a != SumMod4#b) && (SumMod4#a != SumMod4#c) && (SumMod4#b != SumMod4#c);
  assume 0 <= I[SumMod4#a];
  assume I[SumMod4#a] <= R[SumMod4#a];
  assume R[SumMod4#a] <= C[SumMod4#a];
  assume 0 <= I[SumMod4#b];
  assume I[SumMod4#b] <= R[SumMod4#b];
  assume R[SumMod4#b] <= C[SumMod4#b];
  assume 0 <= I[SumMod4#c];
  assume I[SumMod4#c] <= R[SumMod4#c];
  assume R[SumMod4#c] <= C[SumMod4#c];
  assume I[SumMod4#c] == R[SumMod4#c];
  assume C[SumMod4#a] == R[SumMod4#a];
  assume C[SumMod4#b] == R[SumMod4#b];
  assume C[SumMod4#c] == R[SumMod4#c];
  assume (2 * I[SumMod4#b]) == I[SumMod4#a];
  assume I[SumMod4#c] == I[SumMod4#b];
  assume (forall i: int :: 
    (I[SumMod4#a] <= i) && (i < C[SumMod4#a]) ==> (AT#Mod(M[SumMod4#a][i], 2) == 1)
  );
  assume (forall i: int :: 
    (I[SumMod4#b] <= i) && (i < C[SumMod4#b]) ==> (AT#Mod(M[SumMod4#b][i], 2) == 0)
  );
  assume (2 * I[SumMod4#b]) == I[SumMod4#a];
  assume I[SumMod4#c] == I[SumMod4#b];
  assume R[SumMod4#a] == (2 * C[SumMod4#b]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumMod4#b]) ==> (M[SumMod4#b][idx$] == (M[SumMod4#a][2 * idx$] + M[SumMod4#a][(2 * idx$) + 1]))
  );
  assume R[SumMod4#b] == C[SumMod4#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumMod4#c]) ==> (M[SumMod4#c][idx$] == AT#Mod(M[SumMod4#b][idx$], 4))
  );
  assert {:msg "11.1: Sub-actors in the network might fire without network input. This is not permitted. (#29)"} !(2 <= (C[SumMod4#a] - R[SumMod4#a]));
  assert {:msg "11.1: Sub-actors in the network might fire without network input. This is not permitted. (#30)"} !(1 <= (C[SumMod4#b] - R[SumMod4#b]));
}
procedure SumMod4#anon$2#input#in#7()
  modifies C, R, M, I, St;
{
  var SumMod4#add: Actor;
  var SumMod4#mod: Actor;
  var SumMod4#a: Chan (int);
  var SumMod4#b: Chan (int);
  var SumMod4#c: Chan (int);
  assume SumMod4#add != SumMod4#mod;
  assume (SumMod4#a != SumMod4#b) && (SumMod4#a != SumMod4#c) && (SumMod4#b != SumMod4#c);
  assume 0 <= I[SumMod4#a];
  assume I[SumMod4#a] <= R[SumMod4#a];
  assume R[SumMod4#a] <= C[SumMod4#a];
  assume 0 <= I[SumMod4#b];
  assume I[SumMod4#b] <= R[SumMod4#b];
  assume R[SumMod4#b] <= C[SumMod4#b];
  assume 0 <= I[SumMod4#c];
  assume I[SumMod4#c] <= R[SumMod4#c];
  assume R[SumMod4#c] <= C[SumMod4#c];
  assume I[SumMod4#c] == R[SumMod4#c];
  assume C[SumMod4#a] < 32;
  assume (2 * I[SumMod4#b]) == I[SumMod4#a];
  assume I[SumMod4#c] == I[SumMod4#b];
  assume (forall i: int :: 
    (I[SumMod4#a] <= i) && (i < C[SumMod4#a]) ==> (AT#Mod(M[SumMod4#a][i], 2) == 1)
  );
  assume (forall i: int :: 
    (I[SumMod4#b] <= i) && (i < C[SumMod4#b]) ==> (AT#Mod(M[SumMod4#b][i], 2) == 0)
  );
  assume (2 * I[SumMod4#b]) == I[SumMod4#a];
  assume I[SumMod4#c] == I[SumMod4#b];
  assume R[SumMod4#a] == (2 * C[SumMod4#b]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumMod4#b]) ==> (M[SumMod4#b][idx$] == (M[SumMod4#a][2 * idx$] + M[SumMod4#a][(2 * idx$) + 1]))
  );
  assume R[SumMod4#b] == C[SumMod4#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumMod4#c]) ==> (M[SumMod4#c][idx$] == AT#Mod(M[SumMod4#b][idx$], 4))
  );
  C[SumMod4#a] := C[SumMod4#a] + 1;
  assume (forall i: int :: 
    (I[SumMod4#a] <= i) && (i < C[SumMod4#a]) ==> (AT#Mod(M[SumMod4#a][i], 2) == 1)
  );
  assert {:msg "18.15: Channel invariant might be falsified by network input (#31)"} (2 * I[SumMod4#b]) == I[SumMod4#a];
  assert {:msg "19.15: Channel invariant might be falsified by network input (#32)"} I[SumMod4#c] == I[SumMod4#b];
  assert {:msg "20.16: Channel invariant might be falsified by network input (#33)"} (forall i: int :: 
    (I[SumMod4#a] <= i) && (i < C[SumMod4#a]) ==> (AT#Mod(M[SumMod4#a][i], 2) == 1)
  );
  assert {:msg "21.16: Channel invariant might be falsified by network input (#34)"} (forall i: int :: 
    (I[SumMod4#b] <= i) && (i < C[SumMod4#b]) ==> (AT#Mod(M[SumMod4#b][i], 2) == 0)
  );
  assert {:msg "Channel invariant might be falsified by network input (#35)"} (2 * I[SumMod4#b]) == I[SumMod4#a];
  assert {:msg "Channel invariant might be falsified by network input (#36)"} I[SumMod4#c] == I[SumMod4#b];
}
procedure SumMod4#anon$2#exit#8()
  modifies C, R, M, I, St;
{
  var SumMod4#add: Actor;
  var SumMod4#mod: Actor;
  var SumMod4#a: Chan (int);
  var SumMod4#b: Chan (int);
  var SumMod4#c: Chan (int);
  assume SumMod4#add != SumMod4#mod;
  assume (SumMod4#a != SumMod4#b) && (SumMod4#a != SumMod4#c) && (SumMod4#b != SumMod4#c);
  assume 0 <= I[SumMod4#a];
  assume I[SumMod4#a] <= R[SumMod4#a];
  assume R[SumMod4#a] <= C[SumMod4#a];
  assume 0 <= I[SumMod4#b];
  assume I[SumMod4#b] <= R[SumMod4#b];
  assume R[SumMod4#b] <= C[SumMod4#b];
  assume 0 <= I[SumMod4#c];
  assume I[SumMod4#c] <= R[SumMod4#c];
  assume R[SumMod4#c] <= C[SumMod4#c];
  assume I[SumMod4#c] == R[SumMod4#c];
  assume (2 * I[SumMod4#b]) == I[SumMod4#a];
  assume I[SumMod4#c] == I[SumMod4#b];
  assume (forall i: int :: 
    (I[SumMod4#a] <= i) && (i < C[SumMod4#a]) ==> (AT#Mod(M[SumMod4#a][i], 2) == 1)
  );
  assume (forall i: int :: 
    (I[SumMod4#b] <= i) && (i < C[SumMod4#b]) ==> (AT#Mod(M[SumMod4#b][i], 2) == 0)
  );
  assume (2 * I[SumMod4#b]) == I[SumMod4#a];
  assume I[SumMod4#c] == I[SumMod4#b];
  assume R[SumMod4#a] == (2 * C[SumMod4#b]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumMod4#b]) ==> (M[SumMod4#b][idx$] == (M[SumMod4#a][2 * idx$] + M[SumMod4#a][(2 * idx$) + 1]))
  );
  assume R[SumMod4#b] == C[SumMod4#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumMod4#c]) ==> (M[SumMod4#c][idx$] == AT#Mod(M[SumMod4#b][idx$], 4))
  );
  assume (C[SumMod4#a] - I[SumMod4#a]) == 32;
  assume (forall i: int :: 
    (I[SumMod4#a] <= i) && (i < C[SumMod4#a]) ==> (AT#Mod(M[SumMod4#a][i], 2) == 1)
  );
  assume !(2 <= (C[SumMod4#a] - R[SumMod4#a]));
  assume !(1 <= (C[SumMod4#b] - R[SumMod4#b]));
  R[SumMod4#c] := R[SumMod4#c] + 16;
  I := R;
  assert {:msg "18.15: The network might not preserve the channel invariant (#37)"} (2 * I[SumMod4#b]) == I[SumMod4#a];
  assert {:msg "19.15: The network might not preserve the channel invariant (#38)"} I[SumMod4#c] == I[SumMod4#b];
  assert {:msg "20.16: The network might not preserve the channel invariant (#39)"} (forall i: int :: 
    (I[SumMod4#a] <= i) && (i < C[SumMod4#a]) ==> (AT#Mod(M[SumMod4#a][i], 2) == 1)
  );
  assert {:msg "21.16: The network might not preserve the channel invariant (#40)"} (forall i: int :: 
    (I[SumMod4#b] <= i) && (i < C[SumMod4#b]) ==> (AT#Mod(M[SumMod4#b][i], 2) == 0)
  );
  assert {:msg "The network might not preserve the channel invariant (#41)"} (2 * I[SumMod4#b]) == I[SumMod4#a];
  assert {:msg "The network might not preserve the channel invariant (#42)"} I[SumMod4#c] == I[SumMod4#b];
  assert {:msg "13.3: The network might leave unread tokens on channel a (#43)"} C[SumMod4#a] == R[SumMod4#a];
  assert {:msg "13.3: The network might leave unread tokens on channel b (#44)"} C[SumMod4#b] == R[SumMod4#b];
  assert {:msg "13.3: The network might not produce the specified number of tokens on output out (#45)"} C[SumMod4#c] == R[SumMod4#c];
}

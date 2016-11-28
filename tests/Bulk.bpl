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

procedure AddSeq#init#0()
  modifies C, R, M, I;
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
  modifies C, R, M, I;
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
  M[out][C[out]] := in#0 + in#1;
  C[out] := C[out] + 1;
  assert {:msg "Action at 3.3 might not preserve invariant (#2)"} R[in] == (2 * C[out]);
  assert {:msg "Action at 3.3 might not preserve invariant (#3)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == (M[in][2 * idx$] + M[in][(2 * idx$) + 1]))
  );
}
procedure Div#init#2()
  modifies C, R, M, I;
{
  var in: Chan (int);
  var out: Chan (int);
  var c: int;
  assume in != out;
  assume R[in] == 0;
  assume C[out] == 0;
  assert {:msg "Initialization might not establish the invariant (#4)"} R[in] == C[out];
  assert {:msg "Initialization might not establish the invariant (#5)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == AT#Div(M[in][idx$], c))
  );
}
procedure Div#anon$1#3()
  modifies C, R, M, I;
{
  var in: Chan (int);
  var out: Chan (int);
  var c: int;
  var in#0: int;
  assume in != out;
  assume 0 <= R[in];
  assume 0 <= C[out];
  assume R[in] == C[out];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == AT#Div(M[in][idx$], c))
  );
  in#0 := M[in][R[in]];
  R[in] := R[in] + 1;
  M[out][C[out]] := AT#Div(in#0, c);
  C[out] := C[out] + 1;
  assert {:msg "Action at 8.3 might not preserve invariant (#6)"} R[in] == C[out];
  assert {:msg "Action at 8.3 might not preserve invariant (#7)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == AT#Div(M[in][idx$], c))
  );
}
procedure SumDiv2#init#4()
  modifies C, R, M, I;
{
  var SumDiv2#add: Actor;
  var SumDiv2#div: Actor;
  var SumDiv2#anon$3: Chan (int);
  var SumDiv2#anon$4: Chan (int);
  var SumDiv2#anon$5: Chan (int);
  assume SumDiv2#add != SumDiv2#div;
  assume (SumDiv2#anon$3 != SumDiv2#anon$4) && (SumDiv2#anon$3 != SumDiv2#anon$5) && (SumDiv2#anon$4 != SumDiv2#anon$5);
  assume 0 <= I[SumDiv2#anon$3];
  assume I[SumDiv2#anon$3] <= R[SumDiv2#anon$3];
  assume R[SumDiv2#anon$3] <= C[SumDiv2#anon$3];
  assume 0 <= I[SumDiv2#anon$4];
  assume I[SumDiv2#anon$4] <= R[SumDiv2#anon$4];
  assume R[SumDiv2#anon$4] <= C[SumDiv2#anon$4];
  assume 0 <= I[SumDiv2#anon$5];
  assume I[SumDiv2#anon$5] <= R[SumDiv2#anon$5];
  assume R[SumDiv2#anon$5] <= C[SumDiv2#anon$5];
  assume I[SumDiv2#anon$5] == R[SumDiv2#anon$5];
  assume C[SumDiv2#anon$3] == 0;
  assume R[SumDiv2#anon$3] == 0;
  assume C[SumDiv2#anon$4] == 0;
  assume R[SumDiv2#anon$4] == 0;
  assume C[SumDiv2#anon$5] == 0;
  assume R[SumDiv2#anon$5] == 0;
  assume R[SumDiv2#anon$3] == (2 * C[SumDiv2#anon$4]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumDiv2#anon$4]) ==> (M[SumDiv2#anon$4][idx$] == (M[SumDiv2#anon$3][2 * idx$] + M[SumDiv2#anon$3][(2 * idx$) + 1]))
  );
  assume 2 == 2;
  assume R[SumDiv2#anon$4] == C[SumDiv2#anon$5];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumDiv2#anon$5]) ==> (M[SumDiv2#anon$5][idx$] == AT#Div(M[SumDiv2#anon$4][idx$], 2))
  );
  assert {:msg "Initialization of network 'SumDiv2' might not establish the channel invariant (#8)"} (2 * I[SumDiv2#anon$4]) == I[SumDiv2#anon$3];
  assert {:msg "Initialization of network 'SumDiv2' might not establish the channel invariant (#9)"} I[SumDiv2#anon$5] == I[SumDiv2#anon$4];
  I := R;
  assert {:msg "24.5: The initialization might produce unspecified tokens on channel anon$3 (#10)"} (C[SumDiv2#anon$3] - R[SumDiv2#anon$3]) == 0;
  assert {:msg "25.5: The initialization might produce unspecified tokens on channel anon$4 (#11)"} (C[SumDiv2#anon$4] - R[SumDiv2#anon$4]) == 0;
  assert {:msg "26.5: The initialization might produce unspecified tokens on channel anon$5 (#12)"} (C[SumDiv2#anon$5] - R[SumDiv2#anon$5]) == 0;
}
procedure SumDiv2##AddSeq#anon$0#5()
  modifies C, R, M, I;
{
  var SumDiv2#add: Actor;
  var SumDiv2#div: Actor;
  var SumDiv2#anon$3: Chan (int);
  var SumDiv2#anon$4: Chan (int);
  var SumDiv2#anon$5: Chan (int);
  var in#i: int;
  var in#j: int;
  assume SumDiv2#add != SumDiv2#div;
  assume (SumDiv2#anon$3 != SumDiv2#anon$4) && (SumDiv2#anon$3 != SumDiv2#anon$5) && (SumDiv2#anon$4 != SumDiv2#anon$5);
  assume 0 <= I[SumDiv2#anon$3];
  assume I[SumDiv2#anon$3] <= R[SumDiv2#anon$3];
  assume R[SumDiv2#anon$3] <= C[SumDiv2#anon$3];
  assume 0 <= I[SumDiv2#anon$4];
  assume I[SumDiv2#anon$4] <= R[SumDiv2#anon$4];
  assume R[SumDiv2#anon$4] <= C[SumDiv2#anon$4];
  assume 0 <= I[SumDiv2#anon$5];
  assume I[SumDiv2#anon$5] <= R[SumDiv2#anon$5];
  assume R[SumDiv2#anon$5] <= C[SumDiv2#anon$5];
  assume I[SumDiv2#anon$5] == R[SumDiv2#anon$5];
  assume (2 * I[SumDiv2#anon$4]) == I[SumDiv2#anon$3];
  assume I[SumDiv2#anon$5] == I[SumDiv2#anon$4];
  assume R[SumDiv2#anon$3] == (2 * C[SumDiv2#anon$4]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumDiv2#anon$4]) ==> (M[SumDiv2#anon$4][idx$] == (M[SumDiv2#anon$3][2 * idx$] + M[SumDiv2#anon$3][(2 * idx$) + 1]))
  );
  assume R[SumDiv2#anon$4] == C[SumDiv2#anon$5];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumDiv2#anon$5]) ==> (M[SumDiv2#anon$5][idx$] == AT#Div(M[SumDiv2#anon$4][idx$], 2))
  );
  assume 2 <= (C[SumDiv2#anon$3] - R[SumDiv2#anon$3]);
  assume R[SumDiv2#anon$3] == (2 * C[SumDiv2#anon$4]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumDiv2#anon$4]) ==> (M[SumDiv2#anon$4][idx$] == (M[SumDiv2#anon$3][2 * idx$] + M[SumDiv2#anon$3][(2 * idx$) + 1]))
  );
  in#i := M[SumDiv2#anon$3][R[SumDiv2#anon$3]];
  R[SumDiv2#anon$3] := R[SumDiv2#anon$3] + 1;
  in#j := M[SumDiv2#anon$3][R[SumDiv2#anon$3]];
  R[SumDiv2#anon$3] := R[SumDiv2#anon$3] + 1;
  M[SumDiv2#anon$4][C[SumDiv2#anon$4]] := in#i + in#j;
  C[SumDiv2#anon$4] := C[SumDiv2#anon$4] + 1;
  assume R[SumDiv2#anon$3] == (2 * C[SumDiv2#anon$4]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumDiv2#anon$4]) ==> (M[SumDiv2#anon$4][idx$] == (M[SumDiv2#anon$3][2 * idx$] + M[SumDiv2#anon$3][(2 * idx$) + 1]))
  );
  assume R[SumDiv2#anon$3] == (2 * C[SumDiv2#anon$4]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumDiv2#anon$4]) ==> (M[SumDiv2#anon$4][idx$] == (M[SumDiv2#anon$3][2 * idx$] + M[SumDiv2#anon$3][(2 * idx$) + 1]))
  );
  assume R[SumDiv2#anon$4] == C[SumDiv2#anon$5];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumDiv2#anon$5]) ==> (M[SumDiv2#anon$5][idx$] == AT#Div(M[SumDiv2#anon$4][idx$], 2))
  );
  assert {:msg "Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#13)"} (2 * I[SumDiv2#anon$4]) == I[SumDiv2#anon$3];
  assert {:msg "Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#14)"} I[SumDiv2#anon$5] == I[SumDiv2#anon$4];
}
procedure SumDiv2##Div#anon$1#6()
  modifies C, R, M, I;
{
  var SumDiv2#add: Actor;
  var SumDiv2#div: Actor;
  var SumDiv2#anon$3: Chan (int);
  var SumDiv2#anon$4: Chan (int);
  var SumDiv2#anon$5: Chan (int);
  var in#i: int;
  assume SumDiv2#add != SumDiv2#div;
  assume (SumDiv2#anon$3 != SumDiv2#anon$4) && (SumDiv2#anon$3 != SumDiv2#anon$5) && (SumDiv2#anon$4 != SumDiv2#anon$5);
  assume 0 <= I[SumDiv2#anon$3];
  assume I[SumDiv2#anon$3] <= R[SumDiv2#anon$3];
  assume R[SumDiv2#anon$3] <= C[SumDiv2#anon$3];
  assume 0 <= I[SumDiv2#anon$4];
  assume I[SumDiv2#anon$4] <= R[SumDiv2#anon$4];
  assume R[SumDiv2#anon$4] <= C[SumDiv2#anon$4];
  assume 0 <= I[SumDiv2#anon$5];
  assume I[SumDiv2#anon$5] <= R[SumDiv2#anon$5];
  assume R[SumDiv2#anon$5] <= C[SumDiv2#anon$5];
  assume I[SumDiv2#anon$5] == R[SumDiv2#anon$5];
  assume (2 * I[SumDiv2#anon$4]) == I[SumDiv2#anon$3];
  assume I[SumDiv2#anon$5] == I[SumDiv2#anon$4];
  assume R[SumDiv2#anon$3] == (2 * C[SumDiv2#anon$4]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumDiv2#anon$4]) ==> (M[SumDiv2#anon$4][idx$] == (M[SumDiv2#anon$3][2 * idx$] + M[SumDiv2#anon$3][(2 * idx$) + 1]))
  );
  assume R[SumDiv2#anon$4] == C[SumDiv2#anon$5];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumDiv2#anon$5]) ==> (M[SumDiv2#anon$5][idx$] == AT#Div(M[SumDiv2#anon$4][idx$], 2))
  );
  assume 1 <= (C[SumDiv2#anon$4] - R[SumDiv2#anon$4]);
  assume R[SumDiv2#anon$4] == C[SumDiv2#anon$5];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumDiv2#anon$5]) ==> (M[SumDiv2#anon$5][idx$] == AT#Div(M[SumDiv2#anon$4][idx$], 2))
  );
  in#i := M[SumDiv2#anon$4][R[SumDiv2#anon$4]];
  R[SumDiv2#anon$4] := R[SumDiv2#anon$4] + 1;
  M[SumDiv2#anon$5][C[SumDiv2#anon$5]] := AT#Div(in#i, 2);
  C[SumDiv2#anon$5] := C[SumDiv2#anon$5] + 1;
  assume R[SumDiv2#anon$4] == C[SumDiv2#anon$5];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumDiv2#anon$5]) ==> (M[SumDiv2#anon$5][idx$] == AT#Div(M[SumDiv2#anon$4][idx$], 2))
  );
  assume R[SumDiv2#anon$3] == (2 * C[SumDiv2#anon$4]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumDiv2#anon$4]) ==> (M[SumDiv2#anon$4][idx$] == (M[SumDiv2#anon$3][2 * idx$] + M[SumDiv2#anon$3][(2 * idx$) + 1]))
  );
  assume R[SumDiv2#anon$4] == C[SumDiv2#anon$5];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumDiv2#anon$5]) ==> (M[SumDiv2#anon$5][idx$] == AT#Div(M[SumDiv2#anon$4][idx$], 2))
  );
  assert {:msg "Action at 8.3 ('anon$1') for actor instance 'div' might not preserve the channel invariant (#15)"} (2 * I[SumDiv2#anon$4]) == I[SumDiv2#anon$3];
  assert {:msg "Action at 8.3 ('anon$1') for actor instance 'div' might not preserve the channel invariant (#16)"} I[SumDiv2#anon$5] == I[SumDiv2#anon$4];
}
procedure SumDiv2#entry()
  modifies C, R, M, I;
{
  var SumDiv2#add: Actor;
  var SumDiv2#div: Actor;
  var SumDiv2#anon$3: Chan (int);
  var SumDiv2#anon$4: Chan (int);
  var SumDiv2#anon$5: Chan (int);
  assume SumDiv2#add != SumDiv2#div;
  assume (SumDiv2#anon$3 != SumDiv2#anon$4) && (SumDiv2#anon$3 != SumDiv2#anon$5) && (SumDiv2#anon$4 != SumDiv2#anon$5);
  assume 0 <= I[SumDiv2#anon$3];
  assume I[SumDiv2#anon$3] <= R[SumDiv2#anon$3];
  assume R[SumDiv2#anon$3] <= C[SumDiv2#anon$3];
  assume 0 <= I[SumDiv2#anon$4];
  assume I[SumDiv2#anon$4] <= R[SumDiv2#anon$4];
  assume R[SumDiv2#anon$4] <= C[SumDiv2#anon$4];
  assume 0 <= I[SumDiv2#anon$5];
  assume I[SumDiv2#anon$5] <= R[SumDiv2#anon$5];
  assume R[SumDiv2#anon$5] <= C[SumDiv2#anon$5];
  assume I[SumDiv2#anon$5] == R[SumDiv2#anon$5];
  assume C[SumDiv2#anon$3] == R[SumDiv2#anon$3];
  assume C[SumDiv2#anon$4] == R[SumDiv2#anon$4];
  assume C[SumDiv2#anon$5] == R[SumDiv2#anon$5];
  assume (2 * I[SumDiv2#anon$4]) == I[SumDiv2#anon$3];
  assume I[SumDiv2#anon$5] == I[SumDiv2#anon$4];
  assume R[SumDiv2#anon$3] == (2 * C[SumDiv2#anon$4]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumDiv2#anon$4]) ==> (M[SumDiv2#anon$4][idx$] == (M[SumDiv2#anon$3][2 * idx$] + M[SumDiv2#anon$3][(2 * idx$) + 1]))
  );
  assume R[SumDiv2#anon$4] == C[SumDiv2#anon$5];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumDiv2#anon$5]) ==> (M[SumDiv2#anon$5][idx$] == AT#Div(M[SumDiv2#anon$4][idx$], 2))
  );
  assert {:msg "11.1: Sub-actors in the network might fire without network input. This is not permitted. (#17)"} !(2 <= (C[SumDiv2#anon$3] - R[SumDiv2#anon$3]));
  assert {:msg "11.1: Sub-actors in the network might fire without network input. This is not permitted. (#18)"} !(1 <= (C[SumDiv2#anon$4] - R[SumDiv2#anon$4]));
}
procedure SumDiv2#anon$2#input#in#7()
  modifies C, R, M, I;
{
  var SumDiv2#add: Actor;
  var SumDiv2#div: Actor;
  var SumDiv2#anon$3: Chan (int);
  var SumDiv2#anon$4: Chan (int);
  var SumDiv2#anon$5: Chan (int);
  assume SumDiv2#add != SumDiv2#div;
  assume (SumDiv2#anon$3 != SumDiv2#anon$4) && (SumDiv2#anon$3 != SumDiv2#anon$5) && (SumDiv2#anon$4 != SumDiv2#anon$5);
  assume 0 <= I[SumDiv2#anon$3];
  assume I[SumDiv2#anon$3] <= R[SumDiv2#anon$3];
  assume R[SumDiv2#anon$3] <= C[SumDiv2#anon$3];
  assume 0 <= I[SumDiv2#anon$4];
  assume I[SumDiv2#anon$4] <= R[SumDiv2#anon$4];
  assume R[SumDiv2#anon$4] <= C[SumDiv2#anon$4];
  assume 0 <= I[SumDiv2#anon$5];
  assume I[SumDiv2#anon$5] <= R[SumDiv2#anon$5];
  assume R[SumDiv2#anon$5] <= C[SumDiv2#anon$5];
  assume I[SumDiv2#anon$5] == R[SumDiv2#anon$5];
  assume (2 * I[SumDiv2#anon$4]) == I[SumDiv2#anon$3];
  assume I[SumDiv2#anon$5] == I[SumDiv2#anon$4];
  assume R[SumDiv2#anon$3] == (2 * C[SumDiv2#anon$4]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumDiv2#anon$4]) ==> (M[SumDiv2#anon$4][idx$] == (M[SumDiv2#anon$3][2 * idx$] + M[SumDiv2#anon$3][(2 * idx$) + 1]))
  );
  assume R[SumDiv2#anon$4] == C[SumDiv2#anon$5];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumDiv2#anon$5]) ==> (M[SumDiv2#anon$5][idx$] == AT#Div(M[SumDiv2#anon$4][idx$], 2))
  );
  C[SumDiv2#anon$3] := C[SumDiv2#anon$3] + 1;
  assume (forall i: int :: 
    (I[SumDiv2#anon$3] <= i) && (i < C[SumDiv2#anon$3]) ==> (AT#Mod(M[SumDiv2#anon$3][i], 2) == 1)
  );
  assert {:msg "Channel invariant might be falsified by network input (#19)"} (2 * I[SumDiv2#anon$4]) == I[SumDiv2#anon$3];
  assert {:msg "Channel invariant might be falsified by network input (#20)"} I[SumDiv2#anon$5] == I[SumDiv2#anon$4];
}
procedure SumDiv2#anon$2#exit#8()
  modifies C, R, M, I;
{
  var SumDiv2#add: Actor;
  var SumDiv2#div: Actor;
  var SumDiv2#anon$3: Chan (int);
  var SumDiv2#anon$4: Chan (int);
  var SumDiv2#anon$5: Chan (int);
  assume SumDiv2#add != SumDiv2#div;
  assume (SumDiv2#anon$3 != SumDiv2#anon$4) && (SumDiv2#anon$3 != SumDiv2#anon$5) && (SumDiv2#anon$4 != SumDiv2#anon$5);
  assume 0 <= I[SumDiv2#anon$3];
  assume I[SumDiv2#anon$3] <= R[SumDiv2#anon$3];
  assume R[SumDiv2#anon$3] <= C[SumDiv2#anon$3];
  assume 0 <= I[SumDiv2#anon$4];
  assume I[SumDiv2#anon$4] <= R[SumDiv2#anon$4];
  assume R[SumDiv2#anon$4] <= C[SumDiv2#anon$4];
  assume 0 <= I[SumDiv2#anon$5];
  assume I[SumDiv2#anon$5] <= R[SumDiv2#anon$5];
  assume R[SumDiv2#anon$5] <= C[SumDiv2#anon$5];
  assume I[SumDiv2#anon$5] == R[SumDiv2#anon$5];
  assume (2 * I[SumDiv2#anon$4]) == I[SumDiv2#anon$3];
  assume I[SumDiv2#anon$5] == I[SumDiv2#anon$4];
  assume R[SumDiv2#anon$3] == (2 * C[SumDiv2#anon$4]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumDiv2#anon$4]) ==> (M[SumDiv2#anon$4][idx$] == (M[SumDiv2#anon$3][2 * idx$] + M[SumDiv2#anon$3][(2 * idx$) + 1]))
  );
  assume R[SumDiv2#anon$4] == C[SumDiv2#anon$5];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumDiv2#anon$5]) ==> (M[SumDiv2#anon$5][idx$] == AT#Div(M[SumDiv2#anon$4][idx$], 2))
  );
  assume (C[SumDiv2#anon$3] - I[SumDiv2#anon$3]) == 32;
  assume (forall i: int :: 
    (I[SumDiv2#anon$3] <= i) && (i < C[SumDiv2#anon$3]) ==> (AT#Mod(M[SumDiv2#anon$3][i], 2) == 1)
  );
  assume !(2 <= (C[SumDiv2#anon$3] - R[SumDiv2#anon$3]));
  assume !(1 <= (C[SumDiv2#anon$4] - R[SumDiv2#anon$4]));
  assert {:msg "15.15: Network action postcondition might not hold (#21)"} (forall i: int :: 
    (I[SumDiv2#anon$5] <= i) && (i < C[SumDiv2#anon$5]) ==> ((2 * M[SumDiv2#anon$5][i]) == (M[SumDiv2#anon$3][2 * i] + M[SumDiv2#anon$3][(2 * i) + 1]))
  );
  R[SumDiv2#anon$5] := R[SumDiv2#anon$5] + 16;
  I := R;
  assert {:msg "The network might not preserve the channel invariant (#22)"} (2 * I[SumDiv2#anon$4]) == I[SumDiv2#anon$3];
  assert {:msg "The network might not preserve the channel invariant (#23)"} I[SumDiv2#anon$5] == I[SumDiv2#anon$4];
  assert {:msg "13.3: The network might leave unread tokens on channel anon$3 (#24)"} C[SumDiv2#anon$3] == R[SumDiv2#anon$3];
  assert {:msg "13.3: The network might leave unread tokens on channel anon$4 (#25)"} C[SumDiv2#anon$4] == R[SumDiv2#anon$4];
  assert {:msg "13.3: The network might not produce the specified number of tokens on output out (#26)"} C[SumDiv2#anon$5] == R[SumDiv2#anon$5];
}

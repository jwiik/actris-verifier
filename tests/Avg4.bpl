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
  assert {:msg "Initialization might not establish the invariant (#0)"} R[in] == (4 * C[out]);
  assert {:msg "Initialization might not establish the invariant (#1)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == (((M[in][4 * idx$] + M[in][(4 * idx$) + 1]) + M[in][(4 * idx$) + 2]) + M[in][(4 * idx$) + 3]))
  );
}
procedure AddSeq#anon$0#1()
  modifies C, R, M, I;
{
  var in: Chan (int);
  var out: Chan (int);
  var in#0: int;
  var in#1: int;
  var in#2: int;
  var in#3: int;
  assume in != out;
  assume 0 <= R[in];
  assume 0 <= C[out];
  assume R[in] == (4 * C[out]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == (((M[in][4 * idx$] + M[in][(4 * idx$) + 1]) + M[in][(4 * idx$) + 2]) + M[in][(4 * idx$) + 3]))
  );
  in#0 := M[in][R[in]];
  R[in] := R[in] + 1;
  in#1 := M[in][R[in]];
  R[in] := R[in] + 1;
  in#2 := M[in][R[in]];
  R[in] := R[in] + 1;
  in#3 := M[in][R[in]];
  R[in] := R[in] + 1;
  M[out][C[out]] := ((in#0 + in#1) + in#2) + in#3;
  C[out] := C[out] + 1;
  assert {:msg "Action at 3.3 might not preserve invariant (#2)"} R[in] == (4 * C[out]);
  assert {:msg "Action at 3.3 might not preserve invariant (#3)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == (((M[in][4 * idx$] + M[in][(4 * idx$) + 1]) + M[in][(4 * idx$) + 2]) + M[in][(4 * idx$) + 3]))
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
procedure Avg4#init#4()
  modifies C, R, M, I;
{
  var Avg4#add: Actor;
  var Avg4#div: Actor;
  var Avg4#anon$3: Chan (int);
  var Avg4#anon$4: Chan (int);
  var Avg4#anon$5: Chan (int);
  assume Avg4#add != Avg4#div;
  assume (Avg4#anon$3 != Avg4#anon$4) && (Avg4#anon$3 != Avg4#anon$5) && (Avg4#anon$4 != Avg4#anon$5);
  assume 0 <= I[Avg4#anon$3];
  assume I[Avg4#anon$3] <= R[Avg4#anon$3];
  assume R[Avg4#anon$3] <= C[Avg4#anon$3];
  assume 0 <= I[Avg4#anon$4];
  assume I[Avg4#anon$4] <= R[Avg4#anon$4];
  assume R[Avg4#anon$4] <= C[Avg4#anon$4];
  assume 0 <= I[Avg4#anon$5];
  assume I[Avg4#anon$5] <= R[Avg4#anon$5];
  assume R[Avg4#anon$5] <= C[Avg4#anon$5];
  assume I[Avg4#anon$5] == R[Avg4#anon$5];
  assume C[Avg4#anon$3] == 0;
  assume R[Avg4#anon$3] == 0;
  assume C[Avg4#anon$4] == 0;
  assume R[Avg4#anon$4] == 0;
  assume C[Avg4#anon$5] == 0;
  assume R[Avg4#anon$5] == 0;
  assume R[Avg4#anon$3] == (4 * C[Avg4#anon$4]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Avg4#anon$4]) ==> (M[Avg4#anon$4][idx$] == (((M[Avg4#anon$3][4 * idx$] + M[Avg4#anon$3][(4 * idx$) + 1]) + M[Avg4#anon$3][(4 * idx$) + 2]) + M[Avg4#anon$3][(4 * idx$) + 3]))
  );
  assume 4 == 4;
  assume R[Avg4#anon$4] == C[Avg4#anon$5];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Avg4#anon$5]) ==> (M[Avg4#anon$5][idx$] == AT#Div(M[Avg4#anon$4][idx$], 4))
  );
  assert {:msg "Initialization of network 'Avg4' might not establish the channel invariant (#8)"} (4 * I[Avg4#anon$4]) == I[Avg4#anon$3];
  assert {:msg "Initialization of network 'Avg4' might not establish the channel invariant (#9)"} I[Avg4#anon$5] == I[Avg4#anon$4];
  I := R;
  assert {:msg "25.5: The initialization might produce unspecified tokens on channel anon$3 (#10)"} (C[Avg4#anon$3] - R[Avg4#anon$3]) == 0;
  assert {:msg "26.5: The initialization might produce unspecified tokens on channel anon$4 (#11)"} (C[Avg4#anon$4] - R[Avg4#anon$4]) == 0;
  assert {:msg "27.5: The initialization might produce unspecified tokens on channel anon$5 (#12)"} (C[Avg4#anon$5] - R[Avg4#anon$5]) == 0;
}
procedure Avg4##AddSeq#anon$0#5()
  modifies C, R, M, I;
{
  var Avg4#add: Actor;
  var Avg4#div: Actor;
  var Avg4#anon$3: Chan (int);
  var Avg4#anon$4: Chan (int);
  var Avg4#anon$5: Chan (int);
  var in#i: int;
  var in#j: int;
  var in#k: int;
  var in#l: int;
  assume Avg4#add != Avg4#div;
  assume (Avg4#anon$3 != Avg4#anon$4) && (Avg4#anon$3 != Avg4#anon$5) && (Avg4#anon$4 != Avg4#anon$5);
  assume 0 <= I[Avg4#anon$3];
  assume I[Avg4#anon$3] <= R[Avg4#anon$3];
  assume R[Avg4#anon$3] <= C[Avg4#anon$3];
  assume 0 <= I[Avg4#anon$4];
  assume I[Avg4#anon$4] <= R[Avg4#anon$4];
  assume R[Avg4#anon$4] <= C[Avg4#anon$4];
  assume 0 <= I[Avg4#anon$5];
  assume I[Avg4#anon$5] <= R[Avg4#anon$5];
  assume R[Avg4#anon$5] <= C[Avg4#anon$5];
  assume I[Avg4#anon$5] == R[Avg4#anon$5];
  assume (4 * I[Avg4#anon$4]) == I[Avg4#anon$3];
  assume I[Avg4#anon$5] == I[Avg4#anon$4];
  assume R[Avg4#anon$3] == (4 * C[Avg4#anon$4]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Avg4#anon$4]) ==> (M[Avg4#anon$4][idx$] == (((M[Avg4#anon$3][4 * idx$] + M[Avg4#anon$3][(4 * idx$) + 1]) + M[Avg4#anon$3][(4 * idx$) + 2]) + M[Avg4#anon$3][(4 * idx$) + 3]))
  );
  assume R[Avg4#anon$4] == C[Avg4#anon$5];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Avg4#anon$5]) ==> (M[Avg4#anon$5][idx$] == AT#Div(M[Avg4#anon$4][idx$], 4))
  );
  assume 4 <= (C[Avg4#anon$3] - R[Avg4#anon$3]);
  assume R[Avg4#anon$3] == (4 * C[Avg4#anon$4]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Avg4#anon$4]) ==> (M[Avg4#anon$4][idx$] == (((M[Avg4#anon$3][4 * idx$] + M[Avg4#anon$3][(4 * idx$) + 1]) + M[Avg4#anon$3][(4 * idx$) + 2]) + M[Avg4#anon$3][(4 * idx$) + 3]))
  );
  in#i := M[Avg4#anon$3][R[Avg4#anon$3]];
  R[Avg4#anon$3] := R[Avg4#anon$3] + 1;
  in#j := M[Avg4#anon$3][R[Avg4#anon$3]];
  R[Avg4#anon$3] := R[Avg4#anon$3] + 1;
  in#k := M[Avg4#anon$3][R[Avg4#anon$3]];
  R[Avg4#anon$3] := R[Avg4#anon$3] + 1;
  in#l := M[Avg4#anon$3][R[Avg4#anon$3]];
  R[Avg4#anon$3] := R[Avg4#anon$3] + 1;
  M[Avg4#anon$4][C[Avg4#anon$4]] := ((in#i + in#j) + in#k) + in#l;
  C[Avg4#anon$4] := C[Avg4#anon$4] + 1;
  assume R[Avg4#anon$3] == (4 * C[Avg4#anon$4]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Avg4#anon$4]) ==> (M[Avg4#anon$4][idx$] == (((M[Avg4#anon$3][4 * idx$] + M[Avg4#anon$3][(4 * idx$) + 1]) + M[Avg4#anon$3][(4 * idx$) + 2]) + M[Avg4#anon$3][(4 * idx$) + 3]))
  );
  assume R[Avg4#anon$3] == (4 * C[Avg4#anon$4]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Avg4#anon$4]) ==> (M[Avg4#anon$4][idx$] == (((M[Avg4#anon$3][4 * idx$] + M[Avg4#anon$3][(4 * idx$) + 1]) + M[Avg4#anon$3][(4 * idx$) + 2]) + M[Avg4#anon$3][(4 * idx$) + 3]))
  );
  assume R[Avg4#anon$4] == C[Avg4#anon$5];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Avg4#anon$5]) ==> (M[Avg4#anon$5][idx$] == AT#Div(M[Avg4#anon$4][idx$], 4))
  );
  assert {:msg "Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#13)"} (4 * I[Avg4#anon$4]) == I[Avg4#anon$3];
  assert {:msg "Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#14)"} I[Avg4#anon$5] == I[Avg4#anon$4];
}
procedure Avg4##Div#anon$1#6()
  modifies C, R, M, I;
{
  var Avg4#add: Actor;
  var Avg4#div: Actor;
  var Avg4#anon$3: Chan (int);
  var Avg4#anon$4: Chan (int);
  var Avg4#anon$5: Chan (int);
  var in#i: int;
  assume Avg4#add != Avg4#div;
  assume (Avg4#anon$3 != Avg4#anon$4) && (Avg4#anon$3 != Avg4#anon$5) && (Avg4#anon$4 != Avg4#anon$5);
  assume 0 <= I[Avg4#anon$3];
  assume I[Avg4#anon$3] <= R[Avg4#anon$3];
  assume R[Avg4#anon$3] <= C[Avg4#anon$3];
  assume 0 <= I[Avg4#anon$4];
  assume I[Avg4#anon$4] <= R[Avg4#anon$4];
  assume R[Avg4#anon$4] <= C[Avg4#anon$4];
  assume 0 <= I[Avg4#anon$5];
  assume I[Avg4#anon$5] <= R[Avg4#anon$5];
  assume R[Avg4#anon$5] <= C[Avg4#anon$5];
  assume I[Avg4#anon$5] == R[Avg4#anon$5];
  assume (4 * I[Avg4#anon$4]) == I[Avg4#anon$3];
  assume I[Avg4#anon$5] == I[Avg4#anon$4];
  assume R[Avg4#anon$3] == (4 * C[Avg4#anon$4]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Avg4#anon$4]) ==> (M[Avg4#anon$4][idx$] == (((M[Avg4#anon$3][4 * idx$] + M[Avg4#anon$3][(4 * idx$) + 1]) + M[Avg4#anon$3][(4 * idx$) + 2]) + M[Avg4#anon$3][(4 * idx$) + 3]))
  );
  assume R[Avg4#anon$4] == C[Avg4#anon$5];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Avg4#anon$5]) ==> (M[Avg4#anon$5][idx$] == AT#Div(M[Avg4#anon$4][idx$], 4))
  );
  assume 1 <= (C[Avg4#anon$4] - R[Avg4#anon$4]);
  assume R[Avg4#anon$4] == C[Avg4#anon$5];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Avg4#anon$5]) ==> (M[Avg4#anon$5][idx$] == AT#Div(M[Avg4#anon$4][idx$], 4))
  );
  in#i := M[Avg4#anon$4][R[Avg4#anon$4]];
  R[Avg4#anon$4] := R[Avg4#anon$4] + 1;
  M[Avg4#anon$5][C[Avg4#anon$5]] := AT#Div(in#i, 4);
  C[Avg4#anon$5] := C[Avg4#anon$5] + 1;
  assume R[Avg4#anon$4] == C[Avg4#anon$5];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Avg4#anon$5]) ==> (M[Avg4#anon$5][idx$] == AT#Div(M[Avg4#anon$4][idx$], 4))
  );
  assume R[Avg4#anon$3] == (4 * C[Avg4#anon$4]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Avg4#anon$4]) ==> (M[Avg4#anon$4][idx$] == (((M[Avg4#anon$3][4 * idx$] + M[Avg4#anon$3][(4 * idx$) + 1]) + M[Avg4#anon$3][(4 * idx$) + 2]) + M[Avg4#anon$3][(4 * idx$) + 3]))
  );
  assume R[Avg4#anon$4] == C[Avg4#anon$5];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Avg4#anon$5]) ==> (M[Avg4#anon$5][idx$] == AT#Div(M[Avg4#anon$4][idx$], 4))
  );
  assert {:msg "Action at 8.3 ('anon$1') for actor instance 'div' might not preserve the channel invariant (#15)"} (4 * I[Avg4#anon$4]) == I[Avg4#anon$3];
  assert {:msg "Action at 8.3 ('anon$1') for actor instance 'div' might not preserve the channel invariant (#16)"} I[Avg4#anon$5] == I[Avg4#anon$4];
}
procedure Avg4#entry()
  modifies C, R, M, I;
{
  var Avg4#add: Actor;
  var Avg4#div: Actor;
  var Avg4#anon$3: Chan (int);
  var Avg4#anon$4: Chan (int);
  var Avg4#anon$5: Chan (int);
  assume Avg4#add != Avg4#div;
  assume (Avg4#anon$3 != Avg4#anon$4) && (Avg4#anon$3 != Avg4#anon$5) && (Avg4#anon$4 != Avg4#anon$5);
  assume 0 <= I[Avg4#anon$3];
  assume I[Avg4#anon$3] <= R[Avg4#anon$3];
  assume R[Avg4#anon$3] <= C[Avg4#anon$3];
  assume 0 <= I[Avg4#anon$4];
  assume I[Avg4#anon$4] <= R[Avg4#anon$4];
  assume R[Avg4#anon$4] <= C[Avg4#anon$4];
  assume 0 <= I[Avg4#anon$5];
  assume I[Avg4#anon$5] <= R[Avg4#anon$5];
  assume R[Avg4#anon$5] <= C[Avg4#anon$5];
  assume I[Avg4#anon$5] == R[Avg4#anon$5];
  assume C[Avg4#anon$3] == R[Avg4#anon$3];
  assume C[Avg4#anon$4] == R[Avg4#anon$4];
  assume C[Avg4#anon$5] == R[Avg4#anon$5];
  assume (4 * I[Avg4#anon$4]) == I[Avg4#anon$3];
  assume I[Avg4#anon$5] == I[Avg4#anon$4];
  assume R[Avg4#anon$3] == (4 * C[Avg4#anon$4]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Avg4#anon$4]) ==> (M[Avg4#anon$4][idx$] == (((M[Avg4#anon$3][4 * idx$] + M[Avg4#anon$3][(4 * idx$) + 1]) + M[Avg4#anon$3][(4 * idx$) + 2]) + M[Avg4#anon$3][(4 * idx$) + 3]))
  );
  assume R[Avg4#anon$4] == C[Avg4#anon$5];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Avg4#anon$5]) ==> (M[Avg4#anon$5][idx$] == AT#Div(M[Avg4#anon$4][idx$], 4))
  );
  assert {:msg "11.1: Sub-actors in the network might fire without network input. This is not permitted. (#17)"} !(4 <= (C[Avg4#anon$3] - R[Avg4#anon$3]));
  assert {:msg "11.1: Sub-actors in the network might fire without network input. This is not permitted. (#18)"} !(1 <= (C[Avg4#anon$4] - R[Avg4#anon$4]));
}
procedure Avg4#anon$2#input#in#7()
  modifies C, R, M, I;
{
  var Avg4#add: Actor;
  var Avg4#div: Actor;
  var Avg4#anon$3: Chan (int);
  var Avg4#anon$4: Chan (int);
  var Avg4#anon$5: Chan (int);
  var x: int;
  assume Avg4#add != Avg4#div;
  assume (Avg4#anon$3 != Avg4#anon$4) && (Avg4#anon$3 != Avg4#anon$5) && (Avg4#anon$4 != Avg4#anon$5);
  assume 0 <= I[Avg4#anon$3];
  assume I[Avg4#anon$3] <= R[Avg4#anon$3];
  assume R[Avg4#anon$3] <= C[Avg4#anon$3];
  assume 0 <= I[Avg4#anon$4];
  assume I[Avg4#anon$4] <= R[Avg4#anon$4];
  assume R[Avg4#anon$4] <= C[Avg4#anon$4];
  assume 0 <= I[Avg4#anon$5];
  assume I[Avg4#anon$5] <= R[Avg4#anon$5];
  assume R[Avg4#anon$5] <= C[Avg4#anon$5];
  assume I[Avg4#anon$5] == R[Avg4#anon$5];
  assume (4 * I[Avg4#anon$4]) == I[Avg4#anon$3];
  assume I[Avg4#anon$5] == I[Avg4#anon$4];
  assume R[Avg4#anon$3] == (4 * C[Avg4#anon$4]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Avg4#anon$4]) ==> (M[Avg4#anon$4][idx$] == (((M[Avg4#anon$3][4 * idx$] + M[Avg4#anon$3][(4 * idx$) + 1]) + M[Avg4#anon$3][(4 * idx$) + 2]) + M[Avg4#anon$3][(4 * idx$) + 3]))
  );
  assume R[Avg4#anon$4] == C[Avg4#anon$5];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Avg4#anon$5]) ==> (M[Avg4#anon$5][idx$] == AT#Div(M[Avg4#anon$4][idx$], 4))
  );
  assume 0 <= x;
  C[Avg4#anon$3] := C[Avg4#anon$3] + x;
  assume (forall i: int :: 
    (I[Avg4#anon$3] <= i) && (i < C[Avg4#anon$3]) ==> (0 <= M[Avg4#anon$3][i])
  );
  assert {:msg "Channel invariant might be falsified by network input (#19)"} (4 * I[Avg4#anon$4]) == I[Avg4#anon$3];
  assert {:msg "Channel invariant might be falsified by network input (#20)"} I[Avg4#anon$5] == I[Avg4#anon$4];
}
procedure Avg4#anon$2#exit#8()
  modifies C, R, M, I;
{
  var Avg4#add: Actor;
  var Avg4#div: Actor;
  var Avg4#anon$3: Chan (int);
  var Avg4#anon$4: Chan (int);
  var Avg4#anon$5: Chan (int);
  assume Avg4#add != Avg4#div;
  assume (Avg4#anon$3 != Avg4#anon$4) && (Avg4#anon$3 != Avg4#anon$5) && (Avg4#anon$4 != Avg4#anon$5);
  assume 0 <= I[Avg4#anon$3];
  assume I[Avg4#anon$3] <= R[Avg4#anon$3];
  assume R[Avg4#anon$3] <= C[Avg4#anon$3];
  assume 0 <= I[Avg4#anon$4];
  assume I[Avg4#anon$4] <= R[Avg4#anon$4];
  assume R[Avg4#anon$4] <= C[Avg4#anon$4];
  assume 0 <= I[Avg4#anon$5];
  assume I[Avg4#anon$5] <= R[Avg4#anon$5];
  assume R[Avg4#anon$5] <= C[Avg4#anon$5];
  assume I[Avg4#anon$5] == R[Avg4#anon$5];
  assume (4 * I[Avg4#anon$4]) == I[Avg4#anon$3];
  assume I[Avg4#anon$5] == I[Avg4#anon$4];
  assume R[Avg4#anon$3] == (4 * C[Avg4#anon$4]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Avg4#anon$4]) ==> (M[Avg4#anon$4][idx$] == (((M[Avg4#anon$3][4 * idx$] + M[Avg4#anon$3][(4 * idx$) + 1]) + M[Avg4#anon$3][(4 * idx$) + 2]) + M[Avg4#anon$3][(4 * idx$) + 3]))
  );
  assume R[Avg4#anon$4] == C[Avg4#anon$5];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Avg4#anon$5]) ==> (M[Avg4#anon$5][idx$] == AT#Div(M[Avg4#anon$4][idx$], 4))
  );
  assume (C[Avg4#anon$3] - I[Avg4#anon$3]) == 4;
  assume (forall i: int :: 
    (I[Avg4#anon$3] <= i) && (i < C[Avg4#anon$3]) ==> (0 <= M[Avg4#anon$3][i])
  );
  assume !(4 <= (C[Avg4#anon$3] - R[Avg4#anon$3]));
  assume !(1 <= (C[Avg4#anon$4] - R[Avg4#anon$4]));
  assert {:msg "15.14: Network action postcondition might not hold (#21)"} M[Avg4#anon$5][I[Avg4#anon$5]] == AT#Div(((M[Avg4#anon$3][I[Avg4#anon$3]] + M[Avg4#anon$3][I[Avg4#anon$3] + 1]) + M[Avg4#anon$3][I[Avg4#anon$3] + 2]) + M[Avg4#anon$3][I[Avg4#anon$3] + 3], 4);
  assert {:msg "16.14: Network action postcondition might not hold (#22)"} 0 <= M[Avg4#anon$5][I[Avg4#anon$5]];
  R[Avg4#anon$5] := R[Avg4#anon$5] + 1;
  I := R;
  assert {:msg "The network might not preserve the channel invariant (#23)"} (4 * I[Avg4#anon$4]) == I[Avg4#anon$3];
  assert {:msg "The network might not preserve the channel invariant (#24)"} I[Avg4#anon$5] == I[Avg4#anon$4];
  assert {:msg "13.3: The network might leave unread tokens on channel anon$3 (#25)"} C[Avg4#anon$3] == R[Avg4#anon$3];
  assert {:msg "13.3: The network might leave unread tokens on channel anon$4 (#26)"} C[Avg4#anon$4] == R[Avg4#anon$4];
  assert {:msg "13.3: The network might not produce the specified number of tokens on output out (#27)"} C[Avg4#anon$5] == R[Avg4#anon$5];
}

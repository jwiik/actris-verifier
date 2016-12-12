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
var T: CType;

const unique this#: Actor;
type List a = [int]a;
var AT#intlst: List int;

function AT#Min(x:int, y: int): int { if x <= y then x else y }

// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

procedure Add#init#0()
  modifies C, R, M, I;
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
  modifies C, R, M, I;
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
  M[out][C[out]] := in1#0 + in2#0;
  C[out] := C[out] + 1;
  assert {:msg "Action at 3.3 might not preserve invariant (#3)"} R[in1] == C[out];
  assert {:msg "Action at 3.3 might not preserve invariant (#4)"} R[in2] == C[out];
  assert {:msg "Action at 3.3 might not preserve invariant (#5)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == (M[in1][idx$] + M[in2][idx$]))
  );
}
procedure Split#init#2()
  modifies C, R, M, I;
{
  var in: Chan (int);
  var out1: Chan (int);
  var out2: Chan (int);
  assume (in != out1) && (in != out2) && (out1 != out2);
  assume R[in] == 0;
  assume C[out1] == 0;
  assume C[out2] == 0;
  assert {:msg "Initialization might not establish the invariant (#6)"} R[in] == C[out1];
  assert {:msg "Initialization might not establish the invariant (#7)"} R[in] == C[out2];
  assert {:msg "Initialization might not establish the invariant (#8)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out1]) ==> (M[out1][idx$] == M[in][idx$])
  );
  assert {:msg "Initialization might not establish the invariant (#9)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out2]) ==> (M[out2][idx$] == M[in][idx$])
  );
}
procedure Split#anon$1#3()
  modifies C, R, M, I;
{
  var in: Chan (int);
  var out1: Chan (int);
  var out2: Chan (int);
  var in#0: int;
  assume (in != out1) && (in != out2) && (out1 != out2);
  assume 0 <= R[in];
  assume 0 <= C[out1];
  assume 0 <= C[out2];
  assume R[in] == C[out1];
  assume R[in] == C[out2];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out1]) ==> (M[out1][idx$] == M[in][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out2]) ==> (M[out2][idx$] == M[in][idx$])
  );
  in#0 := M[in][R[in]];
  R[in] := R[in] + 1;
  M[out1][C[out1]] := in#0;
  C[out1] := C[out1] + 1;
  M[out2][C[out2]] := in#0;
  C[out2] := C[out2] + 1;
  assert {:msg "Action at 8.3 might not preserve invariant (#10)"} R[in] == C[out1];
  assert {:msg "Action at 8.3 might not preserve invariant (#11)"} R[in] == C[out2];
  assert {:msg "Action at 8.3 might not preserve invariant (#12)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out1]) ==> (M[out1][idx$] == M[in][idx$])
  );
  assert {:msg "Action at 8.3 might not preserve invariant (#13)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out2]) ==> (M[out2][idx$] == M[in][idx$])
  );
}
procedure Delay#init#4()
  modifies C, R, M, I;
{
  var in: Chan (int);
  var out: Chan (int);
  var k: int;
  assume in != out;
  assume R[in] == 0;
  assume C[out] == 0;
  M[out][C[out]] := k;
  C[out] := C[out] + 1;
  assert {:msg "Initialization might not establish the invariant (#14)"} R[in] == (C[out] - 1);
  assert {:msg "Initialization might not establish the invariant (#15)"} (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == M[in][idx$ - 1])
  );
}
procedure Delay#anon$3#5()
  modifies C, R, M, I;
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
  M[out][C[out]] := in#0;
  C[out] := C[out] + 1;
  assert {:msg "Action at 14.3 might not preserve invariant (#16)"} R[in] == (C[out] - 1);
  assert {:msg "Action at 14.3 might not preserve invariant (#17)"} (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == M[in][idx$ - 1])
  );
}
procedure SumNet#init#6()
  modifies C, R, M, I;
{
  var SumNet#add: Actor;
  var SumNet#del: Actor;
  var SumNet#spl: Actor;
  var SumNet#sn_a: Chan (int);
  var SumNet#sn_b: Chan (int);
  var SumNet#sn_c: Chan (int);
  var SumNet#sn_d: Chan (int);
  var SumNet#sn_e: Chan (int);
  assume (SumNet#add != SumNet#del) && (SumNet#add != SumNet#spl) && (SumNet#del != SumNet#spl);
  assume (SumNet#sn_a != SumNet#sn_b) && (SumNet#sn_a != SumNet#sn_c) && (SumNet#sn_a != SumNet#sn_d) && (SumNet#sn_a != SumNet#sn_e) && (SumNet#sn_b != SumNet#sn_c) && (SumNet#sn_b != SumNet#sn_d) && (SumNet#sn_b != SumNet#sn_e) && (SumNet#sn_c != SumNet#sn_d) && (SumNet#sn_c != SumNet#sn_e) && (SumNet#sn_d != SumNet#sn_e);
  assume 0 <= I[SumNet#sn_a];
  assume I[SumNet#sn_a] <= R[SumNet#sn_a];
  assume R[SumNet#sn_a] <= C[SumNet#sn_a];
  assume 0 <= I[SumNet#sn_b];
  assume I[SumNet#sn_b] <= R[SumNet#sn_b];
  assume R[SumNet#sn_b] <= C[SumNet#sn_b];
  assume 0 <= I[SumNet#sn_c];
  assume I[SumNet#sn_c] <= R[SumNet#sn_c];
  assume R[SumNet#sn_c] <= C[SumNet#sn_c];
  assume 0 <= I[SumNet#sn_d];
  assume I[SumNet#sn_d] <= R[SumNet#sn_d];
  assume R[SumNet#sn_d] <= C[SumNet#sn_d];
  assume I[SumNet#sn_d] == R[SumNet#sn_d];
  assume 0 <= I[SumNet#sn_e];
  assume I[SumNet#sn_e] <= R[SumNet#sn_e];
  assume R[SumNet#sn_e] <= C[SumNet#sn_e];
  assume C[SumNet#sn_a] == 0;
  assume R[SumNet#sn_a] == 0;
  assume C[SumNet#sn_b] == 0;
  assume R[SumNet#sn_b] == 0;
  assume C[SumNet#sn_c] == 0;
  assume R[SumNet#sn_c] == 0;
  assume C[SumNet#sn_d] == 0;
  assume R[SumNet#sn_d] == 0;
  assume C[SumNet#sn_e] == 0;
  assume R[SumNet#sn_e] == 0;
  assume 0 == 0;
  M[SumNet#sn_b][C[SumNet#sn_b]] := 0;
  C[SumNet#sn_b] := C[SumNet#sn_b] + 1;
  assert {:msg "31.15: Initialization of network 'SumNet' might not establish the channel invariant (#18)"} M[SumNet#sn_b][0] == 0;
  assert {:msg "32.15: Initialization of network 'SumNet' might not establish the channel invariant (#19)"} 0 <= M[SumNet#sn_b][I[SumNet#sn_b]];
  assert {:msg "Initialization of network 'SumNet' might not establish the channel invariant (#20)"} I[SumNet#sn_c] == I[SumNet#sn_a];
  assert {:msg "Initialization of network 'SumNet' might not establish the channel invariant (#21)"} I[SumNet#sn_c] == I[SumNet#sn_b];
  assert {:msg "Initialization of network 'SumNet' might not establish the channel invariant (#22)"} I[SumNet#sn_b] == I[SumNet#sn_e];
  assert {:msg "Initialization of network 'SumNet' might not establish the channel invariant (#23)"} I[SumNet#sn_d] == I[SumNet#sn_c];
  assert {:msg "Initialization of network 'SumNet' might not establish the channel invariant (#24)"} I[SumNet#sn_e] == I[SumNet#sn_c];
  I := R;
  assert {:msg "26.13: Network initialization might not establish the network invariant (#25)"} (C[SumNet#sn_b] - R[SumNet#sn_b]) == 1;
  assert {:msg "27.20: Network initialization might not establish the network invariant (#26)"} R[SumNet#sn_a] == C[SumNet#sn_d];
  assert {:msg "28.20: Network initialization might not establish the network invariant (#27)"} (C[SumNet#sn_d] > 0) ==> (M[SumNet#sn_d][0] == M[SumNet#sn_a][0]);
  assert {:msg "29.21: Network initialization might not establish the network invariant (#28)"} (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[SumNet#sn_d] - 0)) ==> (M[SumNet#sn_d][i] == (M[SumNet#sn_d][i - 1] + M[SumNet#sn_a][i]))
  );
  assert {:msg "41.5: The initialization might produce unspecified tokens on channel sn_a (#29)"} (C[SumNet#sn_a] - R[SumNet#sn_a]) == 0;
  assert {:msg "43.5: The initialization might produce unspecified tokens on channel sn_c (#30)"} (C[SumNet#sn_c] - R[SumNet#sn_c]) == 0;
  assert {:msg "44.5: The initialization might produce unspecified tokens on channel sn_d (#31)"} (C[SumNet#sn_d] - R[SumNet#sn_d]) == 0;
  assert {:msg "45.5: The initialization might produce unspecified tokens on channel sn_e (#32)"} (C[SumNet#sn_e] - R[SumNet#sn_e]) == 0;
}
procedure SumNet##Add#anon$0#7()
  modifies C, R, M, I;
{
  var SumNet#add: Actor;
  var SumNet#del: Actor;
  var SumNet#spl: Actor;
  var SumNet#sn_a: Chan (int);
  var SumNet#sn_b: Chan (int);
  var SumNet#sn_c: Chan (int);
  var SumNet#sn_d: Chan (int);
  var SumNet#sn_e: Chan (int);
  var in1#i: int;
  var in2#j: int;
  assume (SumNet#add != SumNet#del) && (SumNet#add != SumNet#spl) && (SumNet#del != SumNet#spl);
  assume (SumNet#sn_a != SumNet#sn_b) && (SumNet#sn_a != SumNet#sn_c) && (SumNet#sn_a != SumNet#sn_d) && (SumNet#sn_a != SumNet#sn_e) && (SumNet#sn_b != SumNet#sn_c) && (SumNet#sn_b != SumNet#sn_d) && (SumNet#sn_b != SumNet#sn_e) && (SumNet#sn_c != SumNet#sn_d) && (SumNet#sn_c != SumNet#sn_e) && (SumNet#sn_d != SumNet#sn_e);
  assume 0 <= I[SumNet#sn_a];
  assume I[SumNet#sn_a] <= R[SumNet#sn_a];
  assume R[SumNet#sn_a] <= C[SumNet#sn_a];
  assume 0 <= I[SumNet#sn_b];
  assume I[SumNet#sn_b] <= R[SumNet#sn_b];
  assume R[SumNet#sn_b] <= C[SumNet#sn_b];
  assume 0 <= I[SumNet#sn_c];
  assume I[SumNet#sn_c] <= R[SumNet#sn_c];
  assume R[SumNet#sn_c] <= C[SumNet#sn_c];
  assume 0 <= I[SumNet#sn_d];
  assume I[SumNet#sn_d] <= R[SumNet#sn_d];
  assume R[SumNet#sn_d] <= C[SumNet#sn_d];
  assume I[SumNet#sn_d] == R[SumNet#sn_d];
  assume 0 <= I[SumNet#sn_e];
  assume I[SumNet#sn_e] <= R[SumNet#sn_e];
  assume R[SumNet#sn_e] <= C[SumNet#sn_e];
  assume M[SumNet#sn_b][0] == 0;
  assume 0 <= M[SumNet#sn_b][I[SumNet#sn_b]];
  assume I[SumNet#sn_c] == I[SumNet#sn_a];
  assume I[SumNet#sn_c] == I[SumNet#sn_b];
  assume I[SumNet#sn_b] == I[SumNet#sn_e];
  assume I[SumNet#sn_d] == I[SumNet#sn_c];
  assume I[SumNet#sn_e] == I[SumNet#sn_c];
  assume 0 <= M[SumNet#sn_a][I[SumNet#sn_a]];
  assume R[SumNet#sn_a] == C[SumNet#sn_c];
  assume R[SumNet#sn_b] == C[SumNet#sn_c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumNet#sn_c]) ==> (M[SumNet#sn_c][idx$] == (M[SumNet#sn_a][idx$] + M[SumNet#sn_b][idx$]))
  );
  assume R[SumNet#sn_e] == (C[SumNet#sn_b] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[SumNet#sn_b]) ==> (M[SumNet#sn_b][idx$] == M[SumNet#sn_e][idx$ - 1])
  );
  assume R[SumNet#sn_c] == C[SumNet#sn_d];
  assume R[SumNet#sn_c] == C[SumNet#sn_e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumNet#sn_d]) ==> (M[SumNet#sn_d][idx$] == M[SumNet#sn_c][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumNet#sn_e]) ==> (M[SumNet#sn_e][idx$] == M[SumNet#sn_c][idx$])
  );
  assume (1 <= (C[SumNet#sn_a] - R[SumNet#sn_a])) && (1 <= (C[SumNet#sn_b] - R[SumNet#sn_b]));
  in1#i := M[SumNet#sn_a][R[SumNet#sn_a]];
  R[SumNet#sn_a] := R[SumNet#sn_a] + 1;
  in2#j := M[SumNet#sn_b][R[SumNet#sn_b]];
  R[SumNet#sn_b] := R[SumNet#sn_b] + 1;
  M[SumNet#sn_c][C[SumNet#sn_c]] := in1#i + in2#j;
  C[SumNet#sn_c] := C[SumNet#sn_c] + 1;
  assume R[SumNet#sn_a] == C[SumNet#sn_c];
  assume R[SumNet#sn_b] == C[SumNet#sn_c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumNet#sn_c]) ==> (M[SumNet#sn_c][idx$] == (M[SumNet#sn_a][idx$] + M[SumNet#sn_b][idx$]))
  );
  assume R[SumNet#sn_e] == (C[SumNet#sn_b] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[SumNet#sn_b]) ==> (M[SumNet#sn_b][idx$] == M[SumNet#sn_e][idx$ - 1])
  );
  assume R[SumNet#sn_c] == C[SumNet#sn_d];
  assume R[SumNet#sn_c] == C[SumNet#sn_e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumNet#sn_d]) ==> (M[SumNet#sn_d][idx$] == M[SumNet#sn_c][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumNet#sn_e]) ==> (M[SumNet#sn_e][idx$] == M[SumNet#sn_c][idx$])
  );
  assert {:msg "31.15: Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#33)"} M[SumNet#sn_b][0] == 0;
  assert {:msg "32.15: Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#34)"} 0 <= M[SumNet#sn_b][I[SumNet#sn_b]];
  assert {:msg "Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#35)"} I[SumNet#sn_c] == I[SumNet#sn_a];
  assert {:msg "Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#36)"} I[SumNet#sn_c] == I[SumNet#sn_b];
  assert {:msg "Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#37)"} I[SumNet#sn_b] == I[SumNet#sn_e];
  assert {:msg "Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#38)"} I[SumNet#sn_d] == I[SumNet#sn_c];
  assert {:msg "Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#39)"} I[SumNet#sn_e] == I[SumNet#sn_c];
}
procedure SumNet##Delay#anon$3#8()
  modifies C, R, M, I;
{
  var SumNet#add: Actor;
  var SumNet#del: Actor;
  var SumNet#spl: Actor;
  var SumNet#sn_a: Chan (int);
  var SumNet#sn_b: Chan (int);
  var SumNet#sn_c: Chan (int);
  var SumNet#sn_d: Chan (int);
  var SumNet#sn_e: Chan (int);
  var in#i: int;
  assume (SumNet#add != SumNet#del) && (SumNet#add != SumNet#spl) && (SumNet#del != SumNet#spl);
  assume (SumNet#sn_a != SumNet#sn_b) && (SumNet#sn_a != SumNet#sn_c) && (SumNet#sn_a != SumNet#sn_d) && (SumNet#sn_a != SumNet#sn_e) && (SumNet#sn_b != SumNet#sn_c) && (SumNet#sn_b != SumNet#sn_d) && (SumNet#sn_b != SumNet#sn_e) && (SumNet#sn_c != SumNet#sn_d) && (SumNet#sn_c != SumNet#sn_e) && (SumNet#sn_d != SumNet#sn_e);
  assume 0 <= I[SumNet#sn_a];
  assume I[SumNet#sn_a] <= R[SumNet#sn_a];
  assume R[SumNet#sn_a] <= C[SumNet#sn_a];
  assume 0 <= I[SumNet#sn_b];
  assume I[SumNet#sn_b] <= R[SumNet#sn_b];
  assume R[SumNet#sn_b] <= C[SumNet#sn_b];
  assume 0 <= I[SumNet#sn_c];
  assume I[SumNet#sn_c] <= R[SumNet#sn_c];
  assume R[SumNet#sn_c] <= C[SumNet#sn_c];
  assume 0 <= I[SumNet#sn_d];
  assume I[SumNet#sn_d] <= R[SumNet#sn_d];
  assume R[SumNet#sn_d] <= C[SumNet#sn_d];
  assume I[SumNet#sn_d] == R[SumNet#sn_d];
  assume 0 <= I[SumNet#sn_e];
  assume I[SumNet#sn_e] <= R[SumNet#sn_e];
  assume R[SumNet#sn_e] <= C[SumNet#sn_e];
  assume M[SumNet#sn_b][0] == 0;
  assume 0 <= M[SumNet#sn_b][I[SumNet#sn_b]];
  assume I[SumNet#sn_c] == I[SumNet#sn_a];
  assume I[SumNet#sn_c] == I[SumNet#sn_b];
  assume I[SumNet#sn_b] == I[SumNet#sn_e];
  assume I[SumNet#sn_d] == I[SumNet#sn_c];
  assume I[SumNet#sn_e] == I[SumNet#sn_c];
  assume 0 <= M[SumNet#sn_a][I[SumNet#sn_a]];
  assume R[SumNet#sn_a] == C[SumNet#sn_c];
  assume R[SumNet#sn_b] == C[SumNet#sn_c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumNet#sn_c]) ==> (M[SumNet#sn_c][idx$] == (M[SumNet#sn_a][idx$] + M[SumNet#sn_b][idx$]))
  );
  assume R[SumNet#sn_e] == (C[SumNet#sn_b] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[SumNet#sn_b]) ==> (M[SumNet#sn_b][idx$] == M[SumNet#sn_e][idx$ - 1])
  );
  assume R[SumNet#sn_c] == C[SumNet#sn_d];
  assume R[SumNet#sn_c] == C[SumNet#sn_e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumNet#sn_d]) ==> (M[SumNet#sn_d][idx$] == M[SumNet#sn_c][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumNet#sn_e]) ==> (M[SumNet#sn_e][idx$] == M[SumNet#sn_c][idx$])
  );
  assume 1 <= (C[SumNet#sn_e] - R[SumNet#sn_e]);
  in#i := M[SumNet#sn_e][R[SumNet#sn_e]];
  R[SumNet#sn_e] := R[SumNet#sn_e] + 1;
  M[SumNet#sn_b][C[SumNet#sn_b]] := in#i;
  C[SumNet#sn_b] := C[SumNet#sn_b] + 1;
  assume R[SumNet#sn_a] == C[SumNet#sn_c];
  assume R[SumNet#sn_b] == C[SumNet#sn_c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumNet#sn_c]) ==> (M[SumNet#sn_c][idx$] == (M[SumNet#sn_a][idx$] + M[SumNet#sn_b][idx$]))
  );
  assume R[SumNet#sn_e] == (C[SumNet#sn_b] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[SumNet#sn_b]) ==> (M[SumNet#sn_b][idx$] == M[SumNet#sn_e][idx$ - 1])
  );
  assume R[SumNet#sn_c] == C[SumNet#sn_d];
  assume R[SumNet#sn_c] == C[SumNet#sn_e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumNet#sn_d]) ==> (M[SumNet#sn_d][idx$] == M[SumNet#sn_c][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumNet#sn_e]) ==> (M[SumNet#sn_e][idx$] == M[SumNet#sn_c][idx$])
  );
  assert {:msg "31.15: Action at 14.3 ('anon$3') for actor instance 'del' might not preserve the channel invariant (#40)"} M[SumNet#sn_b][0] == 0;
  assert {:msg "32.15: Action at 14.3 ('anon$3') for actor instance 'del' might not preserve the channel invariant (#41)"} 0 <= M[SumNet#sn_b][I[SumNet#sn_b]];
  assert {:msg "Action at 14.3 ('anon$3') for actor instance 'del' might not preserve the channel invariant (#42)"} I[SumNet#sn_c] == I[SumNet#sn_a];
  assert {:msg "Action at 14.3 ('anon$3') for actor instance 'del' might not preserve the channel invariant (#43)"} I[SumNet#sn_c] == I[SumNet#sn_b];
  assert {:msg "Action at 14.3 ('anon$3') for actor instance 'del' might not preserve the channel invariant (#44)"} I[SumNet#sn_b] == I[SumNet#sn_e];
  assert {:msg "Action at 14.3 ('anon$3') for actor instance 'del' might not preserve the channel invariant (#45)"} I[SumNet#sn_d] == I[SumNet#sn_c];
  assert {:msg "Action at 14.3 ('anon$3') for actor instance 'del' might not preserve the channel invariant (#46)"} I[SumNet#sn_e] == I[SumNet#sn_c];
}
procedure SumNet##Split#anon$1#9()
  modifies C, R, M, I;
{
  var SumNet#add: Actor;
  var SumNet#del: Actor;
  var SumNet#spl: Actor;
  var SumNet#sn_a: Chan (int);
  var SumNet#sn_b: Chan (int);
  var SumNet#sn_c: Chan (int);
  var SumNet#sn_d: Chan (int);
  var SumNet#sn_e: Chan (int);
  var in#i: int;
  assume (SumNet#add != SumNet#del) && (SumNet#add != SumNet#spl) && (SumNet#del != SumNet#spl);
  assume (SumNet#sn_a != SumNet#sn_b) && (SumNet#sn_a != SumNet#sn_c) && (SumNet#sn_a != SumNet#sn_d) && (SumNet#sn_a != SumNet#sn_e) && (SumNet#sn_b != SumNet#sn_c) && (SumNet#sn_b != SumNet#sn_d) && (SumNet#sn_b != SumNet#sn_e) && (SumNet#sn_c != SumNet#sn_d) && (SumNet#sn_c != SumNet#sn_e) && (SumNet#sn_d != SumNet#sn_e);
  assume 0 <= I[SumNet#sn_a];
  assume I[SumNet#sn_a] <= R[SumNet#sn_a];
  assume R[SumNet#sn_a] <= C[SumNet#sn_a];
  assume 0 <= I[SumNet#sn_b];
  assume I[SumNet#sn_b] <= R[SumNet#sn_b];
  assume R[SumNet#sn_b] <= C[SumNet#sn_b];
  assume 0 <= I[SumNet#sn_c];
  assume I[SumNet#sn_c] <= R[SumNet#sn_c];
  assume R[SumNet#sn_c] <= C[SumNet#sn_c];
  assume 0 <= I[SumNet#sn_d];
  assume I[SumNet#sn_d] <= R[SumNet#sn_d];
  assume R[SumNet#sn_d] <= C[SumNet#sn_d];
  assume I[SumNet#sn_d] == R[SumNet#sn_d];
  assume 0 <= I[SumNet#sn_e];
  assume I[SumNet#sn_e] <= R[SumNet#sn_e];
  assume R[SumNet#sn_e] <= C[SumNet#sn_e];
  assume M[SumNet#sn_b][0] == 0;
  assume 0 <= M[SumNet#sn_b][I[SumNet#sn_b]];
  assume I[SumNet#sn_c] == I[SumNet#sn_a];
  assume I[SumNet#sn_c] == I[SumNet#sn_b];
  assume I[SumNet#sn_b] == I[SumNet#sn_e];
  assume I[SumNet#sn_d] == I[SumNet#sn_c];
  assume I[SumNet#sn_e] == I[SumNet#sn_c];
  assume 0 <= M[SumNet#sn_a][I[SumNet#sn_a]];
  assume R[SumNet#sn_a] == C[SumNet#sn_c];
  assume R[SumNet#sn_b] == C[SumNet#sn_c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumNet#sn_c]) ==> (M[SumNet#sn_c][idx$] == (M[SumNet#sn_a][idx$] + M[SumNet#sn_b][idx$]))
  );
  assume R[SumNet#sn_e] == (C[SumNet#sn_b] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[SumNet#sn_b]) ==> (M[SumNet#sn_b][idx$] == M[SumNet#sn_e][idx$ - 1])
  );
  assume R[SumNet#sn_c] == C[SumNet#sn_d];
  assume R[SumNet#sn_c] == C[SumNet#sn_e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumNet#sn_d]) ==> (M[SumNet#sn_d][idx$] == M[SumNet#sn_c][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumNet#sn_e]) ==> (M[SumNet#sn_e][idx$] == M[SumNet#sn_c][idx$])
  );
  assume 1 <= (C[SumNet#sn_c] - R[SumNet#sn_c]);
  in#i := M[SumNet#sn_c][R[SumNet#sn_c]];
  R[SumNet#sn_c] := R[SumNet#sn_c] + 1;
  M[SumNet#sn_d][C[SumNet#sn_d]] := in#i;
  C[SumNet#sn_d] := C[SumNet#sn_d] + 1;
  M[SumNet#sn_e][C[SumNet#sn_e]] := in#i;
  C[SumNet#sn_e] := C[SumNet#sn_e] + 1;
  assume R[SumNet#sn_a] == C[SumNet#sn_c];
  assume R[SumNet#sn_b] == C[SumNet#sn_c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumNet#sn_c]) ==> (M[SumNet#sn_c][idx$] == (M[SumNet#sn_a][idx$] + M[SumNet#sn_b][idx$]))
  );
  assume R[SumNet#sn_e] == (C[SumNet#sn_b] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[SumNet#sn_b]) ==> (M[SumNet#sn_b][idx$] == M[SumNet#sn_e][idx$ - 1])
  );
  assume R[SumNet#sn_c] == C[SumNet#sn_d];
  assume R[SumNet#sn_c] == C[SumNet#sn_e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumNet#sn_d]) ==> (M[SumNet#sn_d][idx$] == M[SumNet#sn_c][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumNet#sn_e]) ==> (M[SumNet#sn_e][idx$] == M[SumNet#sn_c][idx$])
  );
  assert {:msg "31.15: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#47)"} M[SumNet#sn_b][0] == 0;
  assert {:msg "32.15: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#48)"} 0 <= M[SumNet#sn_b][I[SumNet#sn_b]];
  assert {:msg "Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#49)"} I[SumNet#sn_c] == I[SumNet#sn_a];
  assert {:msg "Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#50)"} I[SumNet#sn_c] == I[SumNet#sn_b];
  assert {:msg "Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#51)"} I[SumNet#sn_b] == I[SumNet#sn_e];
  assert {:msg "Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#52)"} I[SumNet#sn_d] == I[SumNet#sn_c];
  assert {:msg "Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#53)"} I[SumNet#sn_e] == I[SumNet#sn_c];
}
procedure SumNet#anon$4#input#in#10()
  modifies C, R, M, I;
{
  var SumNet#add: Actor;
  var SumNet#del: Actor;
  var SumNet#spl: Actor;
  var SumNet#sn_a: Chan (int);
  var SumNet#sn_b: Chan (int);
  var SumNet#sn_c: Chan (int);
  var SumNet#sn_d: Chan (int);
  var SumNet#sn_e: Chan (int);
  assume (SumNet#add != SumNet#del) && (SumNet#add != SumNet#spl) && (SumNet#del != SumNet#spl);
  assume (SumNet#sn_a != SumNet#sn_b) && (SumNet#sn_a != SumNet#sn_c) && (SumNet#sn_a != SumNet#sn_d) && (SumNet#sn_a != SumNet#sn_e) && (SumNet#sn_b != SumNet#sn_c) && (SumNet#sn_b != SumNet#sn_d) && (SumNet#sn_b != SumNet#sn_e) && (SumNet#sn_c != SumNet#sn_d) && (SumNet#sn_c != SumNet#sn_e) && (SumNet#sn_d != SumNet#sn_e);
  assume 0 <= I[SumNet#sn_a];
  assume I[SumNet#sn_a] <= R[SumNet#sn_a];
  assume R[SumNet#sn_a] <= C[SumNet#sn_a];
  assume 0 <= I[SumNet#sn_b];
  assume I[SumNet#sn_b] <= R[SumNet#sn_b];
  assume R[SumNet#sn_b] <= C[SumNet#sn_b];
  assume 0 <= I[SumNet#sn_c];
  assume I[SumNet#sn_c] <= R[SumNet#sn_c];
  assume R[SumNet#sn_c] <= C[SumNet#sn_c];
  assume 0 <= I[SumNet#sn_d];
  assume I[SumNet#sn_d] <= R[SumNet#sn_d];
  assume R[SumNet#sn_d] <= C[SumNet#sn_d];
  assume I[SumNet#sn_d] == R[SumNet#sn_d];
  assume 0 <= I[SumNet#sn_e];
  assume I[SumNet#sn_e] <= R[SumNet#sn_e];
  assume R[SumNet#sn_e] <= C[SumNet#sn_e];
  assume (C[SumNet#sn_a] - I[SumNet#sn_a]) < 1;
  assume M[SumNet#sn_b][0] == 0;
  assume 0 <= M[SumNet#sn_b][I[SumNet#sn_b]];
  assume I[SumNet#sn_c] == I[SumNet#sn_a];
  assume I[SumNet#sn_c] == I[SumNet#sn_b];
  assume I[SumNet#sn_b] == I[SumNet#sn_e];
  assume I[SumNet#sn_d] == I[SumNet#sn_c];
  assume I[SumNet#sn_e] == I[SumNet#sn_c];
  assume 0 <= M[SumNet#sn_a][I[SumNet#sn_a]];
  assume R[SumNet#sn_a] == C[SumNet#sn_c];
  assume R[SumNet#sn_b] == C[SumNet#sn_c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumNet#sn_c]) ==> (M[SumNet#sn_c][idx$] == (M[SumNet#sn_a][idx$] + M[SumNet#sn_b][idx$]))
  );
  assume R[SumNet#sn_e] == (C[SumNet#sn_b] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[SumNet#sn_b]) ==> (M[SumNet#sn_b][idx$] == M[SumNet#sn_e][idx$ - 1])
  );
  assume R[SumNet#sn_c] == C[SumNet#sn_d];
  assume R[SumNet#sn_c] == C[SumNet#sn_e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumNet#sn_d]) ==> (M[SumNet#sn_d][idx$] == M[SumNet#sn_c][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumNet#sn_e]) ==> (M[SumNet#sn_e][idx$] == M[SumNet#sn_c][idx$])
  );
  C[SumNet#sn_a] := C[SumNet#sn_a] + 1;
  assume 0 <= M[SumNet#sn_a][I[SumNet#sn_a]];
  assert {:msg "31.15: Channel invariant might be falsified by network input (#54)"} M[SumNet#sn_b][0] == 0;
  assert {:msg "32.15: Channel invariant might be falsified by network input (#55)"} 0 <= M[SumNet#sn_b][I[SumNet#sn_b]];
  assert {:msg "Channel invariant might be falsified by network input (#56)"} I[SumNet#sn_c] == I[SumNet#sn_a];
  assert {:msg "Channel invariant might be falsified by network input (#57)"} I[SumNet#sn_c] == I[SumNet#sn_b];
  assert {:msg "Channel invariant might be falsified by network input (#58)"} I[SumNet#sn_b] == I[SumNet#sn_e];
  assert {:msg "Channel invariant might be falsified by network input (#59)"} I[SumNet#sn_d] == I[SumNet#sn_c];
  assert {:msg "Channel invariant might be falsified by network input (#60)"} I[SumNet#sn_e] == I[SumNet#sn_c];
  assert {:msg "20.14: Channel invariant might be falsified by network input (#61)"} 0 <= M[SumNet#sn_a][I[SumNet#sn_a]];
}
procedure SumNet#anon$4#exit#11()
  modifies C, R, M, I;
{
  var SumNet#add: Actor;
  var SumNet#del: Actor;
  var SumNet#spl: Actor;
  var SumNet#sn_a: Chan (int);
  var SumNet#sn_b: Chan (int);
  var SumNet#sn_c: Chan (int);
  var SumNet#sn_d: Chan (int);
  var SumNet#sn_e: Chan (int);
  assume (SumNet#add != SumNet#del) && (SumNet#add != SumNet#spl) && (SumNet#del != SumNet#spl);
  assume (SumNet#sn_a != SumNet#sn_b) && (SumNet#sn_a != SumNet#sn_c) && (SumNet#sn_a != SumNet#sn_d) && (SumNet#sn_a != SumNet#sn_e) && (SumNet#sn_b != SumNet#sn_c) && (SumNet#sn_b != SumNet#sn_d) && (SumNet#sn_b != SumNet#sn_e) && (SumNet#sn_c != SumNet#sn_d) && (SumNet#sn_c != SumNet#sn_e) && (SumNet#sn_d != SumNet#sn_e);
  assume 0 <= I[SumNet#sn_a];
  assume I[SumNet#sn_a] <= R[SumNet#sn_a];
  assume R[SumNet#sn_a] <= C[SumNet#sn_a];
  assume 0 <= I[SumNet#sn_b];
  assume I[SumNet#sn_b] <= R[SumNet#sn_b];
  assume R[SumNet#sn_b] <= C[SumNet#sn_b];
  assume 0 <= I[SumNet#sn_c];
  assume I[SumNet#sn_c] <= R[SumNet#sn_c];
  assume R[SumNet#sn_c] <= C[SumNet#sn_c];
  assume 0 <= I[SumNet#sn_d];
  assume I[SumNet#sn_d] <= R[SumNet#sn_d];
  assume R[SumNet#sn_d] <= C[SumNet#sn_d];
  assume I[SumNet#sn_d] == R[SumNet#sn_d];
  assume 0 <= I[SumNet#sn_e];
  assume I[SumNet#sn_e] <= R[SumNet#sn_e];
  assume R[SumNet#sn_e] <= C[SumNet#sn_e];
  assume M[SumNet#sn_b][0] == 0;
  assume 0 <= M[SumNet#sn_b][I[SumNet#sn_b]];
  assume I[SumNet#sn_c] == I[SumNet#sn_a];
  assume I[SumNet#sn_c] == I[SumNet#sn_b];
  assume I[SumNet#sn_b] == I[SumNet#sn_e];
  assume I[SumNet#sn_d] == I[SumNet#sn_c];
  assume I[SumNet#sn_e] == I[SumNet#sn_c];
  assume 0 <= M[SumNet#sn_a][I[SumNet#sn_a]];
  assume R[SumNet#sn_a] == C[SumNet#sn_c];
  assume R[SumNet#sn_b] == C[SumNet#sn_c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumNet#sn_c]) ==> (M[SumNet#sn_c][idx$] == (M[SumNet#sn_a][idx$] + M[SumNet#sn_b][idx$]))
  );
  assume R[SumNet#sn_e] == (C[SumNet#sn_b] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[SumNet#sn_b]) ==> (M[SumNet#sn_b][idx$] == M[SumNet#sn_e][idx$ - 1])
  );
  assume R[SumNet#sn_c] == C[SumNet#sn_d];
  assume R[SumNet#sn_c] == C[SumNet#sn_e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumNet#sn_d]) ==> (M[SumNet#sn_d][idx$] == M[SumNet#sn_c][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[SumNet#sn_e]) ==> (M[SumNet#sn_e][idx$] == M[SumNet#sn_c][idx$])
  );
  assume (C[SumNet#sn_a] - I[SumNet#sn_a]) == 1;
  assume 0 <= M[SumNet#sn_a][I[SumNet#sn_a]];
  assume !((1 <= (C[SumNet#sn_a] - R[SumNet#sn_a])) && (1 <= (C[SumNet#sn_b] - R[SumNet#sn_b])));
  assume !(1 <= (C[SumNet#sn_e] - R[SumNet#sn_e]));
  assume !(1 <= (C[SumNet#sn_c] - R[SumNet#sn_c]));
  assert {:msg "21.13: Network action postcondition might not hold (#62)"} M[SumNet#sn_d][0] == M[SumNet#sn_a][0];
  assert {:msg "22.13: Network action postcondition might not hold (#63)"} M[SumNet#sn_d][I[SumNet#sn_d]] >= M[SumNet#sn_a][I[SumNet#sn_a]];
  assert {:msg "23.13: Network action postcondition might not hold (#64)"} (0 < I[SumNet#sn_d]) ==> (M[SumNet#sn_d][I[SumNet#sn_d]] == (M[SumNet#sn_d][I[SumNet#sn_d] - 1] + M[SumNet#sn_a][I[SumNet#sn_a]]));
  R[SumNet#sn_d] := R[SumNet#sn_d] + 1;
  I := R;
  assert {:msg "31.15: The network might not preserve the channel invariant (#65)"} M[SumNet#sn_b][0] == 0;
  assert {:msg "32.15: The network might not preserve the channel invariant (#66)"} 0 <= M[SumNet#sn_b][I[SumNet#sn_b]];
  assert {:msg "The network might not preserve the channel invariant (#67)"} I[SumNet#sn_c] == I[SumNet#sn_a];
  assert {:msg "The network might not preserve the channel invariant (#68)"} I[SumNet#sn_c] == I[SumNet#sn_b];
  assert {:msg "The network might not preserve the channel invariant (#69)"} I[SumNet#sn_b] == I[SumNet#sn_e];
  assert {:msg "The network might not preserve the channel invariant (#70)"} I[SumNet#sn_d] == I[SumNet#sn_c];
  assert {:msg "The network might not preserve the channel invariant (#71)"} I[SumNet#sn_e] == I[SumNet#sn_c];
  assert {:msg "26.13: The network might not preserve the network invariant (#72)"} (C[SumNet#sn_b] - R[SumNet#sn_b]) == 1;
  assert {:msg "27.20: The network might not preserve the network invariant (#73)"} R[SumNet#sn_a] == C[SumNet#sn_d];
  assert {:msg "28.20: The network might not preserve the network invariant (#74)"} (C[SumNet#sn_d] > 0) ==> (M[SumNet#sn_d][0] == M[SumNet#sn_a][0]);
  assert {:msg "29.21: The network might not preserve the network invariant (#75)"} (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[SumNet#sn_d] - 0)) ==> (M[SumNet#sn_d][i] == (M[SumNet#sn_d][i - 1] + M[SumNet#sn_a][i]))
  );
  assert {:msg "19.3: The network might leave unread tokens on channel sn_a (#76)"} (C[SumNet#sn_a] - R[SumNet#sn_a]) == 0;
  assert {:msg "19.3: The network might leave unread tokens on channel sn_c (#77)"} (C[SumNet#sn_c] - R[SumNet#sn_c]) == 0;
  assert {:msg "19.3: The network might not produce the specified number of tokens on output out (#78)"} (C[SumNet#sn_d] - R[SumNet#sn_d]) == 0;
  assert {:msg "19.3: The network might leave unread tokens on channel sn_e (#79)"} (C[SumNet#sn_e] - R[SumNet#sn_e]) == 0;
}
procedure Sum#init#12()
  modifies C, R, M, I;
{
  var x: Chan (int);
  var y: Chan (int);
  var sum: int;
  assume x != y;
  assume R[x] == 0;
  assume C[y] == 0;
  sum := 0;
  assert {:msg "54.13: Initialization might not establish the invariant (#80)"} 0 <= sum;
  assert {:msg "55.13: Initialization might not establish the invariant (#81)"} (R[x] > 0) ==> (sum == M[y][C[y] - 1]);
  assert {:msg "56.13: Initialization might not establish the invariant (#82)"} (C[y] == 0) ==> (sum == 0);
  assert {:msg "58.20: Initialization might not establish the invariant (#83)"} R[x] == C[y];
  assert {:msg "59.20: Initialization might not establish the invariant (#84)"} (C[y] > 0) ==> (M[y][0] == M[x][0]);
  assert {:msg "60.21: Initialization might not establish the invariant (#85)"} (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[y] - 0)) ==> (M[y][i] == (M[y][i - 1] + M[x][i]))
  );
}
procedure Sum#anon$6#13()
  modifies C, R, M, I;
{
  var x: Chan (int);
  var y: Chan (int);
  var sum: int;
  var x#0: int;
  assume x != y;
  assume 0 <= R[x];
  assume 0 <= C[y];
  assume 0 <= sum;
  assume (R[x] > 0) ==> (sum == M[y][C[y] - 1]);
  assume (C[y] == 0) ==> (sum == 0);
  assume R[x] == C[y];
  assume (C[y] > 0) ==> (M[y][0] == M[x][0]);
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[y] - 0)) ==> (M[y][i] == (M[y][i - 1] + M[x][i]))
  );
  x#0 := M[x][R[x]];
  R[x] := R[x] + 1;
  assume 0 <= x#0;
  sum := sum + x#0;
  assert {:msg "68.13: Action postcondition might not hold (#86)"} x#0 <= sum;
  M[y][C[y]] := sum;
  C[y] := C[y] + 1;
  assert {:msg "54.13: Action at 66.3 might not preserve invariant (#87)"} 0 <= sum;
  assert {:msg "55.13: Action at 66.3 might not preserve invariant (#88)"} (R[x] > 0) ==> (sum == M[y][C[y] - 1]);
  assert {:msg "56.13: Action at 66.3 might not preserve invariant (#89)"} (C[y] == 0) ==> (sum == 0);
  assert {:msg "58.20: Action at 66.3 might not preserve invariant (#90)"} R[x] == C[y];
  assert {:msg "59.20: Action at 66.3 might not preserve invariant (#91)"} (C[y] > 0) ==> (M[y][0] == M[x][0]);
  assert {:msg "60.21: Action at 66.3 might not preserve invariant (#92)"} (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[y] - 0)) ==> (M[y][i] == (M[y][i - 1] + M[x][i]))
  );
}
procedure Nested#init#14()
  modifies C, R, M, I;
{
  var Nested#net: Actor;
  var Nested#sum: Actor;
  var Nested#spl: Actor;
  var Nested#a: Chan (int);
  var Nested#b: Chan (int);
  var Nested#c: Chan (int);
  var Nested#d: Chan (int);
  var Nested#e: Chan (int);
  var AV#sum#sum: int;
  assume (Nested#net != Nested#sum) && (Nested#net != Nested#spl) && (Nested#sum != Nested#spl);
  assume (Nested#a != Nested#b) && (Nested#a != Nested#c) && (Nested#a != Nested#d) && (Nested#a != Nested#e) && (Nested#b != Nested#c) && (Nested#b != Nested#d) && (Nested#b != Nested#e) && (Nested#c != Nested#d) && (Nested#c != Nested#e) && (Nested#d != Nested#e);
  assume 0 <= I[Nested#a];
  assume I[Nested#a] <= R[Nested#a];
  assume R[Nested#a] <= C[Nested#a];
  assume 0 <= I[Nested#b];
  assume I[Nested#b] <= R[Nested#b];
  assume R[Nested#b] <= C[Nested#b];
  assume 0 <= I[Nested#c];
  assume I[Nested#c] <= R[Nested#c];
  assume R[Nested#c] <= C[Nested#c];
  assume 0 <= I[Nested#d];
  assume I[Nested#d] <= R[Nested#d];
  assume R[Nested#d] <= C[Nested#d];
  assume I[Nested#d] == R[Nested#d];
  assume 0 <= I[Nested#e];
  assume I[Nested#e] <= R[Nested#e];
  assume R[Nested#e] <= C[Nested#e];
  assume I[Nested#e] == R[Nested#e];
  assume C[Nested#a] == 0;
  assume R[Nested#a] == 0;
  assume C[Nested#b] == 0;
  assume R[Nested#b] == 0;
  assume C[Nested#c] == 0;
  assume R[Nested#c] == 0;
  assume C[Nested#d] == 0;
  assume R[Nested#d] == 0;
  assume C[Nested#e] == 0;
  assume R[Nested#e] == 0;
  assert {:msg "85.15: Initialization of network 'Nested' might not establish the channel invariant (#93)"} I[Nested#d] == I[Nested#b];
  assert {:msg "86.15: Initialization of network 'Nested' might not establish the channel invariant (#94)"} I[Nested#e] == I[Nested#c];
  assert {:msg "87.15: Initialization of network 'Nested' might not establish the channel invariant (#95)"} (C[Nested#a] - I[Nested#a]) <= 1;
  assert {:msg "Initialization of network 'Nested' might not establish the channel invariant (#96)"} I[Nested#b] == I[Nested#a];
  assert {:msg "Initialization of network 'Nested' might not establish the channel invariant (#97)"} I[Nested#c] == I[Nested#a];
  I := R;
  assert {:msg "96.5: The initialization might produce unspecified tokens on channel a (#98)"} (C[Nested#a] - R[Nested#a]) == 0;
  assert {:msg "97.5: The initialization might produce unspecified tokens on channel b (#99)"} (C[Nested#b] - R[Nested#b]) == 0;
  assert {:msg "98.5: The initialization might produce unspecified tokens on channel c (#100)"} (C[Nested#c] - R[Nested#c]) == 0;
  assert {:msg "99.5: The initialization might produce unspecified tokens on channel d (#101)"} (C[Nested#d] - R[Nested#d]) == 0;
  assert {:msg "100.5: The initialization might produce unspecified tokens on channel e (#102)"} (C[Nested#e] - R[Nested#e]) == 0;
}
procedure Nested##SumNet#anon$4#15()
  modifies C, R, M, I;
{
  var Nested#net: Actor;
  var Nested#sum: Actor;
  var Nested#spl: Actor;
  var Nested#a: Chan (int);
  var Nested#b: Chan (int);
  var Nested#c: Chan (int);
  var Nested#d: Chan (int);
  var Nested#e: Chan (int);
  var AV#sum#sum: int;
  var in#inv$0: int;
  assume (Nested#net != Nested#sum) && (Nested#net != Nested#spl) && (Nested#sum != Nested#spl);
  assume (Nested#a != Nested#b) && (Nested#a != Nested#c) && (Nested#a != Nested#d) && (Nested#a != Nested#e) && (Nested#b != Nested#c) && (Nested#b != Nested#d) && (Nested#b != Nested#e) && (Nested#c != Nested#d) && (Nested#c != Nested#e) && (Nested#d != Nested#e);
  assume 0 <= I[Nested#a];
  assume I[Nested#a] <= R[Nested#a];
  assume R[Nested#a] <= C[Nested#a];
  assume 0 <= I[Nested#b];
  assume I[Nested#b] <= R[Nested#b];
  assume R[Nested#b] <= C[Nested#b];
  assume 0 <= I[Nested#c];
  assume I[Nested#c] <= R[Nested#c];
  assume R[Nested#c] <= C[Nested#c];
  assume 0 <= I[Nested#d];
  assume I[Nested#d] <= R[Nested#d];
  assume R[Nested#d] <= C[Nested#d];
  assume I[Nested#d] == R[Nested#d];
  assume 0 <= I[Nested#e];
  assume I[Nested#e] <= R[Nested#e];
  assume R[Nested#e] <= C[Nested#e];
  assume I[Nested#e] == R[Nested#e];
  assume I[Nested#d] == I[Nested#b];
  assume I[Nested#e] == I[Nested#c];
  assume (C[Nested#a] - I[Nested#a]) <= 1;
  assume I[Nested#b] == I[Nested#a];
  assume I[Nested#c] == I[Nested#a];
  assume 0 <= M[Nested#a][I[Nested#a]];
  assume R[Nested#b] == C[Nested#d];
  assume (C[Nested#d] > 0) ==> (M[Nested#d][0] == M[Nested#b][0]);
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[Nested#d] - 0)) ==> (M[Nested#d][i] == (M[Nested#d][i - 1] + M[Nested#b][i]))
  );
  assume R[Nested#c] == C[Nested#e];
  assume (C[Nested#e] > 0) ==> (M[Nested#e][0] == M[Nested#c][0]);
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[Nested#e] - 0)) ==> (M[Nested#e][i] == (M[Nested#e][i - 1] + M[Nested#c][i]))
  );
  assume R[Nested#a] == C[Nested#b];
  assume R[Nested#a] == C[Nested#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Nested#b]) ==> (M[Nested#b][idx$] == M[Nested#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Nested#c]) ==> (M[Nested#c][idx$] == M[Nested#a][idx$])
  );
  assume 1 <= (C[Nested#b] - R[Nested#b]);
  in#inv$0 := M[Nested#b][R[Nested#b]];
  R[Nested#b] := R[Nested#b] + 1;
  assert {:msg "20.14: Precondition might not hold for instance at 90.5 (#103)"} 0 <= M[Nested#b][I[Nested#b]];
  C[Nested#d] := C[Nested#d] + 1;
  assume M[Nested#d][0] == M[Nested#b][0];
  assume M[Nested#d][I[Nested#d]] >= M[Nested#b][I[Nested#b]];
  assume (0 < I[Nested#d]) ==> (M[Nested#d][I[Nested#d]] == (M[Nested#d][I[Nested#d] - 1] + M[Nested#b][I[Nested#b]]));
  assume R[Nested#b] == C[Nested#d];
  assume (C[Nested#d] > 0) ==> (M[Nested#d][0] == M[Nested#b][0]);
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[Nested#d] - 0)) ==> (M[Nested#d][i] == (M[Nested#d][i - 1] + M[Nested#b][i]))
  );
  assume R[Nested#c] == C[Nested#e];
  assume (C[Nested#e] > 0) ==> (M[Nested#e][0] == M[Nested#c][0]);
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[Nested#e] - 0)) ==> (M[Nested#e][i] == (M[Nested#e][i - 1] + M[Nested#c][i]))
  );
  assume R[Nested#a] == C[Nested#b];
  assume R[Nested#a] == C[Nested#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Nested#b]) ==> (M[Nested#b][idx$] == M[Nested#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Nested#c]) ==> (M[Nested#c][idx$] == M[Nested#a][idx$])
  );
  assert {:msg "85.15: Action at 19.3 ('anon$4') for actor instance 'net' might not preserve the channel invariant (#104)"} I[Nested#d] == I[Nested#b];
  assert {:msg "86.15: Action at 19.3 ('anon$4') for actor instance 'net' might not preserve the channel invariant (#105)"} I[Nested#e] == I[Nested#c];
  assert {:msg "87.15: Action at 19.3 ('anon$4') for actor instance 'net' might not preserve the channel invariant (#106)"} (C[Nested#a] - I[Nested#a]) <= 1;
  assert {:msg "Action at 19.3 ('anon$4') for actor instance 'net' might not preserve the channel invariant (#107)"} I[Nested#b] == I[Nested#a];
  assert {:msg "Action at 19.3 ('anon$4') for actor instance 'net' might not preserve the channel invariant (#108)"} I[Nested#c] == I[Nested#a];
}
procedure Nested##Sum#anon$6#16()
  modifies C, R, M, I;
{
  var Nested#net: Actor;
  var Nested#sum: Actor;
  var Nested#spl: Actor;
  var Nested#a: Chan (int);
  var Nested#b: Chan (int);
  var Nested#c: Chan (int);
  var Nested#d: Chan (int);
  var Nested#e: Chan (int);
  var AV#sum#sum: int;
  var x#i: int;
  assume (Nested#net != Nested#sum) && (Nested#net != Nested#spl) && (Nested#sum != Nested#spl);
  assume (Nested#a != Nested#b) && (Nested#a != Nested#c) && (Nested#a != Nested#d) && (Nested#a != Nested#e) && (Nested#b != Nested#c) && (Nested#b != Nested#d) && (Nested#b != Nested#e) && (Nested#c != Nested#d) && (Nested#c != Nested#e) && (Nested#d != Nested#e);
  assume 0 <= I[Nested#a];
  assume I[Nested#a] <= R[Nested#a];
  assume R[Nested#a] <= C[Nested#a];
  assume 0 <= I[Nested#b];
  assume I[Nested#b] <= R[Nested#b];
  assume R[Nested#b] <= C[Nested#b];
  assume 0 <= I[Nested#c];
  assume I[Nested#c] <= R[Nested#c];
  assume R[Nested#c] <= C[Nested#c];
  assume 0 <= I[Nested#d];
  assume I[Nested#d] <= R[Nested#d];
  assume R[Nested#d] <= C[Nested#d];
  assume I[Nested#d] == R[Nested#d];
  assume 0 <= I[Nested#e];
  assume I[Nested#e] <= R[Nested#e];
  assume R[Nested#e] <= C[Nested#e];
  assume I[Nested#e] == R[Nested#e];
  assume I[Nested#d] == I[Nested#b];
  assume I[Nested#e] == I[Nested#c];
  assume (C[Nested#a] - I[Nested#a]) <= 1;
  assume I[Nested#b] == I[Nested#a];
  assume I[Nested#c] == I[Nested#a];
  assume 0 <= M[Nested#a][I[Nested#a]];
  assume R[Nested#b] == C[Nested#d];
  assume (C[Nested#d] > 0) ==> (M[Nested#d][0] == M[Nested#b][0]);
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[Nested#d] - 0)) ==> (M[Nested#d][i] == (M[Nested#d][i - 1] + M[Nested#b][i]))
  );
  assume R[Nested#c] == C[Nested#e];
  assume (C[Nested#e] > 0) ==> (M[Nested#e][0] == M[Nested#c][0]);
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[Nested#e] - 0)) ==> (M[Nested#e][i] == (M[Nested#e][i - 1] + M[Nested#c][i]))
  );
  assume R[Nested#a] == C[Nested#b];
  assume R[Nested#a] == C[Nested#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Nested#b]) ==> (M[Nested#b][idx$] == M[Nested#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Nested#c]) ==> (M[Nested#c][idx$] == M[Nested#a][idx$])
  );
  assume 1 <= (C[Nested#c] - R[Nested#c]);
  x#i := M[Nested#c][R[Nested#c]];
  R[Nested#c] := R[Nested#c] + 1;
  assert {:msg "67.14: Precondition might not hold for instance at 91.5 (#109)"} 0 <= x#i;
  havoc AV#sum#sum;
  M[Nested#e][C[Nested#e]] := AV#sum#sum;
  C[Nested#e] := C[Nested#e] + 1;
  assume x#i <= AV#sum#sum;
  assume R[Nested#b] == C[Nested#d];
  assume (C[Nested#d] > 0) ==> (M[Nested#d][0] == M[Nested#b][0]);
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[Nested#d] - 0)) ==> (M[Nested#d][i] == (M[Nested#d][i - 1] + M[Nested#b][i]))
  );
  assume R[Nested#c] == C[Nested#e];
  assume (C[Nested#e] > 0) ==> (M[Nested#e][0] == M[Nested#c][0]);
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[Nested#e] - 0)) ==> (M[Nested#e][i] == (M[Nested#e][i - 1] + M[Nested#c][i]))
  );
  assume R[Nested#a] == C[Nested#b];
  assume R[Nested#a] == C[Nested#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Nested#b]) ==> (M[Nested#b][idx$] == M[Nested#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Nested#c]) ==> (M[Nested#c][idx$] == M[Nested#a][idx$])
  );
  assert {:msg "85.15: Action at 66.3 ('anon$6') for actor instance 'sum' might not preserve the channel invariant (#110)"} I[Nested#d] == I[Nested#b];
  assert {:msg "86.15: Action at 66.3 ('anon$6') for actor instance 'sum' might not preserve the channel invariant (#111)"} I[Nested#e] == I[Nested#c];
  assert {:msg "87.15: Action at 66.3 ('anon$6') for actor instance 'sum' might not preserve the channel invariant (#112)"} (C[Nested#a] - I[Nested#a]) <= 1;
  assert {:msg "Action at 66.3 ('anon$6') for actor instance 'sum' might not preserve the channel invariant (#113)"} I[Nested#b] == I[Nested#a];
  assert {:msg "Action at 66.3 ('anon$6') for actor instance 'sum' might not preserve the channel invariant (#114)"} I[Nested#c] == I[Nested#a];
}
procedure Nested##Split#anon$1#17()
  modifies C, R, M, I;
{
  var Nested#net: Actor;
  var Nested#sum: Actor;
  var Nested#spl: Actor;
  var Nested#a: Chan (int);
  var Nested#b: Chan (int);
  var Nested#c: Chan (int);
  var Nested#d: Chan (int);
  var Nested#e: Chan (int);
  var AV#sum#sum: int;
  var in#i: int;
  assume (Nested#net != Nested#sum) && (Nested#net != Nested#spl) && (Nested#sum != Nested#spl);
  assume (Nested#a != Nested#b) && (Nested#a != Nested#c) && (Nested#a != Nested#d) && (Nested#a != Nested#e) && (Nested#b != Nested#c) && (Nested#b != Nested#d) && (Nested#b != Nested#e) && (Nested#c != Nested#d) && (Nested#c != Nested#e) && (Nested#d != Nested#e);
  assume 0 <= I[Nested#a];
  assume I[Nested#a] <= R[Nested#a];
  assume R[Nested#a] <= C[Nested#a];
  assume 0 <= I[Nested#b];
  assume I[Nested#b] <= R[Nested#b];
  assume R[Nested#b] <= C[Nested#b];
  assume 0 <= I[Nested#c];
  assume I[Nested#c] <= R[Nested#c];
  assume R[Nested#c] <= C[Nested#c];
  assume 0 <= I[Nested#d];
  assume I[Nested#d] <= R[Nested#d];
  assume R[Nested#d] <= C[Nested#d];
  assume I[Nested#d] == R[Nested#d];
  assume 0 <= I[Nested#e];
  assume I[Nested#e] <= R[Nested#e];
  assume R[Nested#e] <= C[Nested#e];
  assume I[Nested#e] == R[Nested#e];
  assume I[Nested#d] == I[Nested#b];
  assume I[Nested#e] == I[Nested#c];
  assume (C[Nested#a] - I[Nested#a]) <= 1;
  assume I[Nested#b] == I[Nested#a];
  assume I[Nested#c] == I[Nested#a];
  assume 0 <= M[Nested#a][I[Nested#a]];
  assume R[Nested#b] == C[Nested#d];
  assume (C[Nested#d] > 0) ==> (M[Nested#d][0] == M[Nested#b][0]);
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[Nested#d] - 0)) ==> (M[Nested#d][i] == (M[Nested#d][i - 1] + M[Nested#b][i]))
  );
  assume R[Nested#c] == C[Nested#e];
  assume (C[Nested#e] > 0) ==> (M[Nested#e][0] == M[Nested#c][0]);
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[Nested#e] - 0)) ==> (M[Nested#e][i] == (M[Nested#e][i - 1] + M[Nested#c][i]))
  );
  assume R[Nested#a] == C[Nested#b];
  assume R[Nested#a] == C[Nested#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Nested#b]) ==> (M[Nested#b][idx$] == M[Nested#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Nested#c]) ==> (M[Nested#c][idx$] == M[Nested#a][idx$])
  );
  assume 1 <= (C[Nested#a] - R[Nested#a]);
  in#i := M[Nested#a][R[Nested#a]];
  R[Nested#a] := R[Nested#a] + 1;
  M[Nested#b][C[Nested#b]] := in#i;
  C[Nested#b] := C[Nested#b] + 1;
  M[Nested#c][C[Nested#c]] := in#i;
  C[Nested#c] := C[Nested#c] + 1;
  assume R[Nested#b] == C[Nested#d];
  assume (C[Nested#d] > 0) ==> (M[Nested#d][0] == M[Nested#b][0]);
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[Nested#d] - 0)) ==> (M[Nested#d][i] == (M[Nested#d][i - 1] + M[Nested#b][i]))
  );
  assume R[Nested#c] == C[Nested#e];
  assume (C[Nested#e] > 0) ==> (M[Nested#e][0] == M[Nested#c][0]);
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[Nested#e] - 0)) ==> (M[Nested#e][i] == (M[Nested#e][i - 1] + M[Nested#c][i]))
  );
  assume R[Nested#a] == C[Nested#b];
  assume R[Nested#a] == C[Nested#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Nested#b]) ==> (M[Nested#b][idx$] == M[Nested#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Nested#c]) ==> (M[Nested#c][idx$] == M[Nested#a][idx$])
  );
  assert {:msg "85.15: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#115)"} I[Nested#d] == I[Nested#b];
  assert {:msg "86.15: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#116)"} I[Nested#e] == I[Nested#c];
  assert {:msg "87.15: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#117)"} (C[Nested#a] - I[Nested#a]) <= 1;
  assert {:msg "Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#118)"} I[Nested#b] == I[Nested#a];
  assert {:msg "Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#119)"} I[Nested#c] == I[Nested#a];
}
procedure Nested#anon$7#input#in#18()
  modifies C, R, M, I;
{
  var Nested#net: Actor;
  var Nested#sum: Actor;
  var Nested#spl: Actor;
  var Nested#a: Chan (int);
  var Nested#b: Chan (int);
  var Nested#c: Chan (int);
  var Nested#d: Chan (int);
  var Nested#e: Chan (int);
  var AV#sum#sum: int;
  assume (Nested#net != Nested#sum) && (Nested#net != Nested#spl) && (Nested#sum != Nested#spl);
  assume (Nested#a != Nested#b) && (Nested#a != Nested#c) && (Nested#a != Nested#d) && (Nested#a != Nested#e) && (Nested#b != Nested#c) && (Nested#b != Nested#d) && (Nested#b != Nested#e) && (Nested#c != Nested#d) && (Nested#c != Nested#e) && (Nested#d != Nested#e);
  assume 0 <= I[Nested#a];
  assume I[Nested#a] <= R[Nested#a];
  assume R[Nested#a] <= C[Nested#a];
  assume 0 <= I[Nested#b];
  assume I[Nested#b] <= R[Nested#b];
  assume R[Nested#b] <= C[Nested#b];
  assume 0 <= I[Nested#c];
  assume I[Nested#c] <= R[Nested#c];
  assume R[Nested#c] <= C[Nested#c];
  assume 0 <= I[Nested#d];
  assume I[Nested#d] <= R[Nested#d];
  assume R[Nested#d] <= C[Nested#d];
  assume I[Nested#d] == R[Nested#d];
  assume 0 <= I[Nested#e];
  assume I[Nested#e] <= R[Nested#e];
  assume R[Nested#e] <= C[Nested#e];
  assume I[Nested#e] == R[Nested#e];
  assume (C[Nested#a] - I[Nested#a]) < 1;
  assume I[Nested#d] == I[Nested#b];
  assume I[Nested#e] == I[Nested#c];
  assume (C[Nested#a] - I[Nested#a]) <= 1;
  assume I[Nested#b] == I[Nested#a];
  assume I[Nested#c] == I[Nested#a];
  assume 0 <= M[Nested#a][I[Nested#a]];
  assume R[Nested#b] == C[Nested#d];
  assume (C[Nested#d] > 0) ==> (M[Nested#d][0] == M[Nested#b][0]);
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[Nested#d] - 0)) ==> (M[Nested#d][i] == (M[Nested#d][i - 1] + M[Nested#b][i]))
  );
  assume R[Nested#c] == C[Nested#e];
  assume (C[Nested#e] > 0) ==> (M[Nested#e][0] == M[Nested#c][0]);
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[Nested#e] - 0)) ==> (M[Nested#e][i] == (M[Nested#e][i - 1] + M[Nested#c][i]))
  );
  assume R[Nested#a] == C[Nested#b];
  assume R[Nested#a] == C[Nested#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Nested#b]) ==> (M[Nested#b][idx$] == M[Nested#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Nested#c]) ==> (M[Nested#c][idx$] == M[Nested#a][idx$])
  );
  C[Nested#a] := C[Nested#a] + 1;
  assume 0 <= M[Nested#a][I[Nested#a]];
  assert {:msg "85.15: Channel invariant might be falsified by network input (#120)"} I[Nested#d] == I[Nested#b];
  assert {:msg "86.15: Channel invariant might be falsified by network input (#121)"} I[Nested#e] == I[Nested#c];
  assert {:msg "87.15: Channel invariant might be falsified by network input (#122)"} (C[Nested#a] - I[Nested#a]) <= 1;
  assert {:msg "Channel invariant might be falsified by network input (#123)"} I[Nested#b] == I[Nested#a];
  assert {:msg "Channel invariant might be falsified by network input (#124)"} I[Nested#c] == I[Nested#a];
  assert {:msg "78.14: Channel invariant might be falsified by network input (#125)"} 0 <= M[Nested#a][I[Nested#a]];
}
procedure Nested#anon$7#exit#19()
  modifies C, R, M, I;
{
  var Nested#net: Actor;
  var Nested#sum: Actor;
  var Nested#spl: Actor;
  var Nested#a: Chan (int);
  var Nested#b: Chan (int);
  var Nested#c: Chan (int);
  var Nested#d: Chan (int);
  var Nested#e: Chan (int);
  var AV#sum#sum: int;
  assume (Nested#net != Nested#sum) && (Nested#net != Nested#spl) && (Nested#sum != Nested#spl);
  assume (Nested#a != Nested#b) && (Nested#a != Nested#c) && (Nested#a != Nested#d) && (Nested#a != Nested#e) && (Nested#b != Nested#c) && (Nested#b != Nested#d) && (Nested#b != Nested#e) && (Nested#c != Nested#d) && (Nested#c != Nested#e) && (Nested#d != Nested#e);
  assume 0 <= I[Nested#a];
  assume I[Nested#a] <= R[Nested#a];
  assume R[Nested#a] <= C[Nested#a];
  assume 0 <= I[Nested#b];
  assume I[Nested#b] <= R[Nested#b];
  assume R[Nested#b] <= C[Nested#b];
  assume 0 <= I[Nested#c];
  assume I[Nested#c] <= R[Nested#c];
  assume R[Nested#c] <= C[Nested#c];
  assume 0 <= I[Nested#d];
  assume I[Nested#d] <= R[Nested#d];
  assume R[Nested#d] <= C[Nested#d];
  assume I[Nested#d] == R[Nested#d];
  assume 0 <= I[Nested#e];
  assume I[Nested#e] <= R[Nested#e];
  assume R[Nested#e] <= C[Nested#e];
  assume I[Nested#e] == R[Nested#e];
  assume I[Nested#d] == I[Nested#b];
  assume I[Nested#e] == I[Nested#c];
  assume (C[Nested#a] - I[Nested#a]) <= 1;
  assume I[Nested#b] == I[Nested#a];
  assume I[Nested#c] == I[Nested#a];
  assume 0 <= M[Nested#a][I[Nested#a]];
  assume R[Nested#b] == C[Nested#d];
  assume (C[Nested#d] > 0) ==> (M[Nested#d][0] == M[Nested#b][0]);
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[Nested#d] - 0)) ==> (M[Nested#d][i] == (M[Nested#d][i - 1] + M[Nested#b][i]))
  );
  assume R[Nested#c] == C[Nested#e];
  assume (C[Nested#e] > 0) ==> (M[Nested#e][0] == M[Nested#c][0]);
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[Nested#e] - 0)) ==> (M[Nested#e][i] == (M[Nested#e][i - 1] + M[Nested#c][i]))
  );
  assume R[Nested#a] == C[Nested#b];
  assume R[Nested#a] == C[Nested#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Nested#b]) ==> (M[Nested#b][idx$] == M[Nested#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Nested#c]) ==> (M[Nested#c][idx$] == M[Nested#a][idx$])
  );
  assume (C[Nested#a] - I[Nested#a]) == 1;
  assume 0 <= M[Nested#a][I[Nested#a]];
  assume !(1 <= (C[Nested#b] - R[Nested#b]));
  assume !(1 <= (C[Nested#c] - R[Nested#c]));
  assume !(1 <= (C[Nested#a] - R[Nested#a]));
  assert {:msg "79.13: Network action postcondition might not hold (#126)"} M[Nested#d][0] == M[Nested#a][0];
  assert {:msg "80.13: Network action postcondition might not hold (#127)"} M[Nested#e][0] == M[Nested#a][0];
  assert {:msg "81.13: Network action postcondition might not hold (#128)"} (0 < I[Nested#d]) ==> (M[Nested#d][I[Nested#d]] == (M[Nested#d][I[Nested#d] - 1] + M[Nested#a][I[Nested#a]]));
  assert {:msg "82.13: Network action postcondition might not hold (#129)"} (0 < I[Nested#e]) ==> (M[Nested#e][I[Nested#e]] == (M[Nested#e][I[Nested#e] - 1] + M[Nested#a][I[Nested#a]]));
  R[Nested#d] := R[Nested#d] + 1;
  R[Nested#e] := R[Nested#e] + 1;
  I := R;
  assert {:msg "85.15: The network might not preserve the channel invariant (#130)"} I[Nested#d] == I[Nested#b];
  assert {:msg "86.15: The network might not preserve the channel invariant (#131)"} I[Nested#e] == I[Nested#c];
  assert {:msg "87.15: The network might not preserve the channel invariant (#132)"} (C[Nested#a] - I[Nested#a]) <= 1;
  assert {:msg "The network might not preserve the channel invariant (#133)"} I[Nested#b] == I[Nested#a];
  assert {:msg "The network might not preserve the channel invariant (#134)"} I[Nested#c] == I[Nested#a];
  assert {:msg "77.3: The network might leave unread tokens on channel a (#135)"} (C[Nested#a] - R[Nested#a]) == 0;
  assert {:msg "77.3: The network might leave unread tokens on channel b (#136)"} (C[Nested#b] - R[Nested#b]) == 0;
  assert {:msg "77.3: The network might leave unread tokens on channel c (#137)"} (C[Nested#c] - R[Nested#c]) == 0;
  assert {:msg "77.3: The network might not produce the specified number of tokens on output out1 (#138)"} (C[Nested#d] - R[Nested#d]) == 0;
  assert {:msg "77.3: The network might not produce the specified number of tokens on output out2 (#139)"} (C[Nested#e] - R[Nested#e]) == 0;
}

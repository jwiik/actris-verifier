// ---------------------------------------------------------------
// -- Types and global variables ---------------------------------
// ---------------------------------------------------------------
type Ref;
type Chan a;
type Field a;
type Actor;
type CType = <a>[Chan a]int;
type MType = <a>[Chan a][int]a;
type Obj = <a>[Field a]a;
type HType = [Ref]Obj;

var M: MType;
var C: CType;
var R: CType;
var I: CType;
var B: CType;

var H: HType;

const unique this#: Actor;

function AT#Min(x:int, y: int): int { if x <= y then x else y }
function AT#Ite<T>(bool, T, T): T;
axiom (
  forall<T> cond: bool, thn: T, els: T :: { AT#Ite(cond, thn, els) }
    (cond ==> AT#Ite(cond,thn,els) == thn &&
    !cond ==> AT#Ite(cond,thn,els) == els)
);

// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

procedure Add#init#0()
  modifies C, R, M, I, H;
{
  var in1: Chan (int);
  var in2: Chan (int);
  var out: Chan (int);
  assume (in1 != in2) && (in1 != out) && (in2 != out);
  assume R[in1] == 0;
  assume R[in2] == 0;
  assume C[out] == 0;
}
procedure Add#anon$0#1()
  modifies C, R, M, I, H;
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
}
procedure Split#init#2()
  modifies C, R, M, I, H;
{
  var in: Chan (int);
  var out1: Chan (int);
  var out2: Chan (int);
  assume (in != out1) && (in != out2) && (out1 != out2);
  assume R[in] == 0;
  assume C[out1] == 0;
  assume C[out2] == 0;
}
procedure Split#anon$1#3()
  modifies C, R, M, I, H;
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
}
procedure Delay#init#4()
  modifies C, R, M, I, H;
{
  var in: Chan (int);
  var out: Chan (int);
  var k: int;
  assume in != out;
  assume R[in] == 0;
  assume C[out] == 0;
  M[out][C[out]] := k;
  C[out] := C[out] + 1;
}
procedure Delay#anon$3#5()
  modifies C, R, M, I, H;
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
}
procedure SumNet#init#6()
  modifies C, R, M, I, H;
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
  assume (B[SumNet#sn_a] == 1) && (B[SumNet#sn_d] == 1);
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
  assert {:msg "Nested.actor(31.15): Initialization of network 'SumNet' might not establish the channel invariant (#0)"} M[SumNet#sn_b][0] == 0;
  assert {:msg "Nested.actor(32.15): Initialization of network 'SumNet' might not establish the channel invariant (#1)"} 0 <= M[SumNet#sn_b][I[SumNet#sn_b]];
  I := R;
  assert {:msg "Nested.actor(26.13): Initialization of network 'SumNet' might not establish the network invariant (#2)"} (C[SumNet#sn_b] - R[SumNet#sn_b]) == 1;
  assert {:msg "Nested.actor(27.20): Initialization of network 'SumNet' might not establish the network invariant (#3)"} R[SumNet#sn_a] == C[SumNet#sn_d];
  assert {:msg "Nested.actor(28.20): Initialization of network 'SumNet' might not establish the network invariant (#4)"} (C[SumNet#sn_d] > 0) ==> (M[SumNet#sn_d][0] == M[SumNet#sn_a][0]);
  assert {:msg "Nested.actor(29.21): Initialization of network 'SumNet' might not establish the network invariant (#5)"} (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[SumNet#sn_d] - 0)) ==> (M[SumNet#sn_d][i] == (M[SumNet#sn_d][i - 1] + M[SumNet#sn_a][i]))
  );
  assert {:msg "Initialization of network 'SumNet' might not establish the network invariant: Unread tokens might be left on channel sn_a (#6)"} (C[SumNet#sn_a] - R[SumNet#sn_a]) == 0;
  assert {:msg "Initialization of network 'SumNet' might not establish the network invariant: Unread tokens might be left on channel sn_c (#7)"} (C[SumNet#sn_c] - R[SumNet#sn_c]) == 0;
  assert {:msg "Initialization of network 'SumNet' might not establish the network invariant: Unread tokens might be left on channel sn_d (#8)"} (C[SumNet#sn_d] - R[SumNet#sn_d]) == 0;
  assert {:msg "Initialization of network 'SumNet' might not establish the network invariant: Unread tokens might be left on channel sn_e (#9)"} (C[SumNet#sn_e] - R[SumNet#sn_e]) == 0;
}
procedure SumNet##Add#anon$0#7()
  modifies C, R, M, I, H;
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
  assume (B[SumNet#sn_a] == 1) && (B[SumNet#sn_d] == 1);
  assume M[SumNet#sn_b][0] == 0;
  assume 0 <= M[SumNet#sn_b][I[SumNet#sn_b]];
  assume I[SumNet#sn_c] == I[SumNet#sn_a];
  assume I[SumNet#sn_c] == I[SumNet#sn_b];
  assume I[SumNet#sn_b] == I[SumNet#sn_e];
  assume I[SumNet#sn_d] == I[SumNet#sn_c];
  assume I[SumNet#sn_e] == I[SumNet#sn_c];
  assume 0 <= M[SumNet#sn_a][I[SumNet#sn_a]];
  assume (C[SumNet#sn_a] - I[SumNet#sn_a]) <= 1;
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
  assert {:msg "Nested.actor(31.15): Action at Nested.actor(3.3) ('anon$0') for actor instance 'add' might not preserve the channel invariant (#10)"} M[SumNet#sn_b][0] == 0;
  assert {:msg "Nested.actor(32.15): Action at Nested.actor(3.3) ('anon$0') for actor instance 'add' might not preserve the channel invariant (#11)"} 0 <= M[SumNet#sn_b][I[SumNet#sn_b]];
}
procedure SumNet##Delay#anon$3#8()
  modifies C, R, M, I, H;
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
  assume (B[SumNet#sn_a] == 1) && (B[SumNet#sn_d] == 1);
  assume M[SumNet#sn_b][0] == 0;
  assume 0 <= M[SumNet#sn_b][I[SumNet#sn_b]];
  assume I[SumNet#sn_c] == I[SumNet#sn_a];
  assume I[SumNet#sn_c] == I[SumNet#sn_b];
  assume I[SumNet#sn_b] == I[SumNet#sn_e];
  assume I[SumNet#sn_d] == I[SumNet#sn_c];
  assume I[SumNet#sn_e] == I[SumNet#sn_c];
  assume 0 <= M[SumNet#sn_a][I[SumNet#sn_a]];
  assume (C[SumNet#sn_a] - I[SumNet#sn_a]) <= 1;
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
  assert {:msg "Nested.actor(31.15): Action at Nested.actor(14.3) ('anon$3') for actor instance 'del' might not preserve the channel invariant (#12)"} M[SumNet#sn_b][0] == 0;
  assert {:msg "Nested.actor(32.15): Action at Nested.actor(14.3) ('anon$3') for actor instance 'del' might not preserve the channel invariant (#13)"} 0 <= M[SumNet#sn_b][I[SumNet#sn_b]];
}
procedure SumNet##Split#anon$1#9()
  modifies C, R, M, I, H;
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
  assume (B[SumNet#sn_a] == 1) && (B[SumNet#sn_d] == 1);
  assume M[SumNet#sn_b][0] == 0;
  assume 0 <= M[SumNet#sn_b][I[SumNet#sn_b]];
  assume I[SumNet#sn_c] == I[SumNet#sn_a];
  assume I[SumNet#sn_c] == I[SumNet#sn_b];
  assume I[SumNet#sn_b] == I[SumNet#sn_e];
  assume I[SumNet#sn_d] == I[SumNet#sn_c];
  assume I[SumNet#sn_e] == I[SumNet#sn_c];
  assume 0 <= M[SumNet#sn_a][I[SumNet#sn_a]];
  assume (C[SumNet#sn_a] - I[SumNet#sn_a]) <= 1;
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
  assert {:msg "Nested.actor(31.15): Action at Nested.actor(8.3) ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#14)"} M[SumNet#sn_b][0] == 0;
  assert {:msg "Nested.actor(32.15): Action at Nested.actor(8.3) ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#15)"} 0 <= M[SumNet#sn_b][I[SumNet#sn_b]];
}
procedure SumNet#anon$4#input#in#10()
  modifies C, R, M, I, H;
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
  assume (B[SumNet#sn_a] == 1) && (B[SumNet#sn_d] == 1);
  assume (B[SumNet#sn_a] == 1) && (B[SumNet#sn_d] == 1);
  assume (C[SumNet#sn_a] - I[SumNet#sn_a]) < 1;
  assume M[SumNet#sn_b][0] == 0;
  assume 0 <= M[SumNet#sn_b][I[SumNet#sn_b]];
  assume I[SumNet#sn_c] == I[SumNet#sn_a];
  assume I[SumNet#sn_c] == I[SumNet#sn_b];
  assume I[SumNet#sn_b] == I[SumNet#sn_e];
  assume I[SumNet#sn_d] == I[SumNet#sn_c];
  assume I[SumNet#sn_e] == I[SumNet#sn_c];
  assume 0 <= M[SumNet#sn_a][I[SumNet#sn_a]];
  assume (C[SumNet#sn_a] - I[SumNet#sn_a]) <= 1;
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
  assert {:msg "Nested.actor(31.15): Channel invariant might be falsified by network input (#16)"} M[SumNet#sn_b][0] == 0;
  assert {:msg "Nested.actor(32.15): Channel invariant might be falsified by network input (#17)"} 0 <= M[SumNet#sn_b][I[SumNet#sn_b]];
  assert {:msg "Channel invariant might be falsified by network input (#18)"} I[SumNet#sn_c] == I[SumNet#sn_a];
  assert {:msg "Channel invariant might be falsified by network input (#19)"} I[SumNet#sn_c] == I[SumNet#sn_b];
  assert {:msg "Channel invariant might be falsified by network input (#20)"} I[SumNet#sn_b] == I[SumNet#sn_e];
  assert {:msg "Channel invariant might be falsified by network input (#21)"} I[SumNet#sn_d] == I[SumNet#sn_c];
  assert {:msg "Channel invariant might be falsified by network input (#22)"} I[SumNet#sn_e] == I[SumNet#sn_c];
  assert {:msg "Nested.actor(20.14): Channel invariant might be falsified by network input (#23)"} 0 <= M[SumNet#sn_a][I[SumNet#sn_a]];
  assert {:msg "Channel invariant might be falsified by network input (#24)"} (C[SumNet#sn_a] - I[SumNet#sn_a]) <= 1;
}
procedure SumNet#anon$4#exit#11()
  modifies C, R, M, I, H;
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
  assume (B[SumNet#sn_a] == 1) && (B[SumNet#sn_d] == 1);
  assume (B[SumNet#sn_a] == 1) && (B[SumNet#sn_d] == 1);
  assume M[SumNet#sn_b][0] == 0;
  assume 0 <= M[SumNet#sn_b][I[SumNet#sn_b]];
  assume I[SumNet#sn_c] == I[SumNet#sn_a];
  assume I[SumNet#sn_c] == I[SumNet#sn_b];
  assume I[SumNet#sn_b] == I[SumNet#sn_e];
  assume I[SumNet#sn_d] == I[SumNet#sn_c];
  assume I[SumNet#sn_e] == I[SumNet#sn_c];
  assume 0 <= M[SumNet#sn_a][I[SumNet#sn_a]];
  assume (C[SumNet#sn_a] - I[SumNet#sn_a]) <= 1;
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
  assert {:msg "Nested.actor(21.13): Network action postcondition might not hold (#25)"} M[SumNet#sn_d][0] == M[SumNet#sn_a][0];
  assert {:msg "Nested.actor(22.13): Network action postcondition might not hold (#26)"} M[SumNet#sn_d][I[SumNet#sn_d]] >= M[SumNet#sn_a][I[SumNet#sn_a]];
  assert {:msg "Nested.actor(23.13): Network action postcondition might not hold (#27)"} (0 < I[SumNet#sn_d]) ==> (M[SumNet#sn_d][I[SumNet#sn_d]] == (M[SumNet#sn_d][I[SumNet#sn_d] - 1] + M[SumNet#sn_a][I[SumNet#sn_a]]));
  R[SumNet#sn_d] := R[SumNet#sn_d] + 1;
  I := R;
  assert {:msg "Nested.actor(31.15): The network might not preserve the channel invariant (#28)"} M[SumNet#sn_b][0] == 0;
  assert {:msg "Nested.actor(32.15): The network might not preserve the channel invariant (#29)"} 0 <= M[SumNet#sn_b][I[SumNet#sn_b]];
  assert {:msg "Nested.actor(26.13): The network might not preserve the network invariant (#30)"} (C[SumNet#sn_b] - R[SumNet#sn_b]) == 1;
  assert {:msg "Nested.actor(27.20): The network might not preserve the network invariant (#31)"} R[SumNet#sn_a] == C[SumNet#sn_d];
  assert {:msg "Nested.actor(28.20): The network might not preserve the network invariant (#32)"} (C[SumNet#sn_d] > 0) ==> (M[SumNet#sn_d][0] == M[SumNet#sn_a][0]);
  assert {:msg "Nested.actor(29.21): The network might not preserve the network invariant (#33)"} (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[SumNet#sn_d] - 0)) ==> (M[SumNet#sn_d][i] == (M[SumNet#sn_d][i - 1] + M[SumNet#sn_a][i]))
  );
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel sn_a (#34)"} (C[SumNet#sn_a] - R[SumNet#sn_a]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel sn_c (#35)"} (C[SumNet#sn_c] - R[SumNet#sn_c]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel sn_d (#36)"} (C[SumNet#sn_d] - R[SumNet#sn_d]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel sn_e (#37)"} (C[SumNet#sn_e] - R[SumNet#sn_e]) == 0;
}
procedure Sum#init#12()
  modifies C, R, M, I, H;
{
  var x: Chan (int);
  var y: Chan (int);
  var sum: int;
  assume x != y;
  assume R[x] == 0;
  assume C[y] == 0;
  sum := 0;
  assert {:msg "Nested.actor(54.13): Initialization might not establish the invariant (#38)"} 0 <= sum;
  assert {:msg "Nested.actor(55.13): Initialization might not establish the invariant (#39)"} (R[x] > 0) ==> (sum == M[y][C[y] - 1]);
  assert {:msg "Nested.actor(56.13): Initialization might not establish the invariant (#40)"} (C[y] == 0) ==> (sum == 0);
  assert {:msg "Nested.actor(58.20): Initialization might not establish the invariant (#41)"} R[x] == C[y];
  assert {:msg "Nested.actor(59.20): Initialization might not establish the invariant (#42)"} (C[y] > 0) ==> (M[y][0] == M[x][0]);
  assert {:msg "Nested.actor(60.21): Initialization might not establish the invariant (#43)"} (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[y] - 0)) ==> (M[y][i] == (M[y][i - 1] + M[x][i]))
  );
}
procedure Sum#anon$6#13()
  modifies C, R, M, I, H;
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
  assume R[x] == C[y];
  x#0 := M[x][R[x]];
  R[x] := R[x] + 1;
  assume 0 <= x#0;
  sum := sum + x#0;
  assert {:msg "Nested.actor(68.13): Action postcondition might not hold (#44)"} x#0 <= sum;
  M[y][C[y]] := sum;
  C[y] := C[y] + 1;
  assert {:msg "Nested.actor(54.13): Action at Nested.actor(66.3) might not preserve invariant (#45)"} 0 <= sum;
  assert {:msg "Nested.actor(55.13): Action at Nested.actor(66.3) might not preserve invariant (#46)"} (R[x] > 0) ==> (sum == M[y][C[y] - 1]);
  assert {:msg "Nested.actor(56.13): Action at Nested.actor(66.3) might not preserve invariant (#47)"} (C[y] == 0) ==> (sum == 0);
  assert {:msg "Nested.actor(58.20): Action at Nested.actor(66.3) might not preserve invariant (#48)"} R[x] == C[y];
  assert {:msg "Nested.actor(59.20): Action at Nested.actor(66.3) might not preserve invariant (#49)"} (C[y] > 0) ==> (M[y][0] == M[x][0]);
  assert {:msg "Nested.actor(60.21): Action at Nested.actor(66.3) might not preserve invariant (#50)"} (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[y] - 0)) ==> (M[y][i] == (M[y][i - 1] + M[x][i]))
  );
}
procedure Nested#init#14()
  modifies C, R, M, I, H;
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
  assume (B[Nested#a] == 1) && (B[Nested#d] == 1) && (B[Nested#e] == 1);
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
  assert {:msg "Nested.actor(88.16): Initialization of network 'Nested' might not establish the channel invariant (#51)"} (forall i: int :: 
    (0 <= i) && (i < I[Nested#d]) ==> (M[Nested#d][i] == M[Nested#e][i])
  );
  assert {:msg "Nested.actor(89.15): Initialization of network 'Nested' might not establish the channel invariant (#52)"} I[Nested#d] == I[Nested#b];
  assert {:msg "Nested.actor(90.15): Initialization of network 'Nested' might not establish the channel invariant (#53)"} I[Nested#e] == I[Nested#c];
  I := R;
  assert {:msg "Initialization of network 'Nested' might not establish the network invariant: Unread tokens might be left on channel a (#54)"} (C[Nested#a] - R[Nested#a]) == 0;
  assert {:msg "Initialization of network 'Nested' might not establish the network invariant: Unread tokens might be left on channel b (#55)"} (C[Nested#b] - R[Nested#b]) == 0;
  assert {:msg "Initialization of network 'Nested' might not establish the network invariant: Unread tokens might be left on channel c (#56)"} (C[Nested#c] - R[Nested#c]) == 0;
  assert {:msg "Initialization of network 'Nested' might not establish the network invariant: Unread tokens might be left on channel d (#57)"} (C[Nested#d] - R[Nested#d]) == 0;
  assert {:msg "Initialization of network 'Nested' might not establish the network invariant: Unread tokens might be left on channel e (#58)"} (C[Nested#e] - R[Nested#e]) == 0;
}
procedure Nested##SumNet#anon$4#15()
  modifies C, R, M, I, H;
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
  assume (B[Nested#a] == 1) && (B[Nested#d] == 1) && (B[Nested#e] == 1);
  assume (forall i: int :: 
    (0 <= i) && (i < I[Nested#d]) ==> (M[Nested#d][i] == M[Nested#e][i])
  );
  assume I[Nested#d] == I[Nested#b];
  assume I[Nested#e] == I[Nested#c];
  assume I[Nested#d] == I[Nested#b];
  assume I[Nested#e] == I[Nested#c];
  assume I[Nested#b] == I[Nested#a];
  assume I[Nested#c] == I[Nested#a];
  assume 0 <= M[Nested#a][I[Nested#a]];
  assume (C[Nested#a] - I[Nested#a]) <= 1;
  assume R[Nested#b] == C[Nested#d];
  assume (C[Nested#d] > 0) ==> (M[Nested#d][0] == M[Nested#b][0]);
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[Nested#d] - 0)) ==> (M[Nested#d][i] == (M[Nested#d][i - 1] + M[Nested#b][i]))
  );
  assume R[Nested#b] == C[Nested#d];
  assume R[Nested#c] == C[Nested#e];
  assume (C[Nested#e] > 0) ==> (M[Nested#e][0] == M[Nested#c][0]);
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[Nested#e] - 0)) ==> (M[Nested#e][i] == (M[Nested#e][i - 1] + M[Nested#c][i]))
  );
  assume R[Nested#c] == C[Nested#e];
  assume R[Nested#a] == C[Nested#b];
  assume R[Nested#a] == C[Nested#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Nested#b]) ==> (M[Nested#b][idx$] == M[Nested#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Nested#c]) ==> (M[Nested#c][idx$] == M[Nested#a][idx$])
  );
  assume 1 <= (C[Nested#b] - R[Nested#b]);
  R[Nested#b] := R[Nested#b] + 1;
  assert {:msg "Nested.actor(20.14): Precondition might not hold for instance at Nested.actor(93.5) (#59)"} 0 <= M[Nested#b][I[Nested#b]];
  C[Nested#d] := C[Nested#d] + 1;
  assume M[Nested#d][0] == M[Nested#b][0];
  assume M[Nested#d][I[Nested#d]] >= M[Nested#b][I[Nested#b]];
  assume (0 < I[Nested#d]) ==> (M[Nested#d][I[Nested#d]] == (M[Nested#d][I[Nested#d] - 1] + M[Nested#b][I[Nested#b]]));
  assume R[Nested#b] == C[Nested#d];
  assume (C[Nested#d] > 0) ==> (M[Nested#d][0] == M[Nested#b][0]);
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[Nested#d] - 0)) ==> (M[Nested#d][i] == (M[Nested#d][i - 1] + M[Nested#b][i]))
  );
  assume R[Nested#b] == C[Nested#d];
  assume R[Nested#c] == C[Nested#e];
  assume (C[Nested#e] > 0) ==> (M[Nested#e][0] == M[Nested#c][0]);
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[Nested#e] - 0)) ==> (M[Nested#e][i] == (M[Nested#e][i - 1] + M[Nested#c][i]))
  );
  assume R[Nested#c] == C[Nested#e];
  assume R[Nested#a] == C[Nested#b];
  assume R[Nested#a] == C[Nested#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Nested#b]) ==> (M[Nested#b][idx$] == M[Nested#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Nested#c]) ==> (M[Nested#c][idx$] == M[Nested#a][idx$])
  );
  assert {:msg "Nested.actor(88.16): Action at Nested.actor(19.3) ('anon$4') for actor instance 'net' might not preserve the channel invariant (#60)"} (forall i: int :: 
    (0 <= i) && (i < I[Nested#d]) ==> (M[Nested#d][i] == M[Nested#e][i])
  );
  assert {:msg "Nested.actor(89.15): Action at Nested.actor(19.3) ('anon$4') for actor instance 'net' might not preserve the channel invariant (#61)"} I[Nested#d] == I[Nested#b];
  assert {:msg "Nested.actor(90.15): Action at Nested.actor(19.3) ('anon$4') for actor instance 'net' might not preserve the channel invariant (#62)"} I[Nested#e] == I[Nested#c];
}
procedure Nested##Sum#anon$6#16()
  modifies C, R, M, I, H;
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
  assume (B[Nested#a] == 1) && (B[Nested#d] == 1) && (B[Nested#e] == 1);
  assume (forall i: int :: 
    (0 <= i) && (i < I[Nested#d]) ==> (M[Nested#d][i] == M[Nested#e][i])
  );
  assume I[Nested#d] == I[Nested#b];
  assume I[Nested#e] == I[Nested#c];
  assume I[Nested#d] == I[Nested#b];
  assume I[Nested#e] == I[Nested#c];
  assume I[Nested#b] == I[Nested#a];
  assume I[Nested#c] == I[Nested#a];
  assume 0 <= M[Nested#a][I[Nested#a]];
  assume (C[Nested#a] - I[Nested#a]) <= 1;
  assume R[Nested#b] == C[Nested#d];
  assume (C[Nested#d] > 0) ==> (M[Nested#d][0] == M[Nested#b][0]);
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[Nested#d] - 0)) ==> (M[Nested#d][i] == (M[Nested#d][i - 1] + M[Nested#b][i]))
  );
  assume R[Nested#b] == C[Nested#d];
  assume R[Nested#c] == C[Nested#e];
  assume (C[Nested#e] > 0) ==> (M[Nested#e][0] == M[Nested#c][0]);
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[Nested#e] - 0)) ==> (M[Nested#e][i] == (M[Nested#e][i - 1] + M[Nested#c][i]))
  );
  assume R[Nested#c] == C[Nested#e];
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
  assert {:msg "Nested.actor(67.14): Precondition might not hold for instance at Nested.actor(94.5) (#63)"} 0 <= x#i;
  havoc AV#sum#sum;
  M[Nested#e][C[Nested#e]] := AV#sum#sum;
  C[Nested#e] := C[Nested#e] + 1;
  assume x#i <= AV#sum#sum;
  assume R[Nested#b] == C[Nested#d];
  assume (C[Nested#d] > 0) ==> (M[Nested#d][0] == M[Nested#b][0]);
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[Nested#d] - 0)) ==> (M[Nested#d][i] == (M[Nested#d][i - 1] + M[Nested#b][i]))
  );
  assume R[Nested#b] == C[Nested#d];
  assume R[Nested#c] == C[Nested#e];
  assume (C[Nested#e] > 0) ==> (M[Nested#e][0] == M[Nested#c][0]);
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[Nested#e] - 0)) ==> (M[Nested#e][i] == (M[Nested#e][i - 1] + M[Nested#c][i]))
  );
  assume R[Nested#c] == C[Nested#e];
  assume R[Nested#a] == C[Nested#b];
  assume R[Nested#a] == C[Nested#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Nested#b]) ==> (M[Nested#b][idx$] == M[Nested#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Nested#c]) ==> (M[Nested#c][idx$] == M[Nested#a][idx$])
  );
  assert {:msg "Nested.actor(88.16): Action at Nested.actor(66.3) ('anon$6') for actor instance 'sum' might not preserve the channel invariant (#64)"} (forall i: int :: 
    (0 <= i) && (i < I[Nested#d]) ==> (M[Nested#d][i] == M[Nested#e][i])
  );
  assert {:msg "Nested.actor(89.15): Action at Nested.actor(66.3) ('anon$6') for actor instance 'sum' might not preserve the channel invariant (#65)"} I[Nested#d] == I[Nested#b];
  assert {:msg "Nested.actor(90.15): Action at Nested.actor(66.3) ('anon$6') for actor instance 'sum' might not preserve the channel invariant (#66)"} I[Nested#e] == I[Nested#c];
}
procedure Nested##Split#anon$1#17()
  modifies C, R, M, I, H;
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
  assume (B[Nested#a] == 1) && (B[Nested#d] == 1) && (B[Nested#e] == 1);
  assume (forall i: int :: 
    (0 <= i) && (i < I[Nested#d]) ==> (M[Nested#d][i] == M[Nested#e][i])
  );
  assume I[Nested#d] == I[Nested#b];
  assume I[Nested#e] == I[Nested#c];
  assume I[Nested#d] == I[Nested#b];
  assume I[Nested#e] == I[Nested#c];
  assume I[Nested#b] == I[Nested#a];
  assume I[Nested#c] == I[Nested#a];
  assume 0 <= M[Nested#a][I[Nested#a]];
  assume (C[Nested#a] - I[Nested#a]) <= 1;
  assume R[Nested#b] == C[Nested#d];
  assume (C[Nested#d] > 0) ==> (M[Nested#d][0] == M[Nested#b][0]);
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[Nested#d] - 0)) ==> (M[Nested#d][i] == (M[Nested#d][i - 1] + M[Nested#b][i]))
  );
  assume R[Nested#b] == C[Nested#d];
  assume R[Nested#c] == C[Nested#e];
  assume (C[Nested#e] > 0) ==> (M[Nested#e][0] == M[Nested#c][0]);
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[Nested#e] - 0)) ==> (M[Nested#e][i] == (M[Nested#e][i - 1] + M[Nested#c][i]))
  );
  assume R[Nested#c] == C[Nested#e];
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
  assume R[Nested#b] == C[Nested#d];
  assume R[Nested#c] == C[Nested#e];
  assume (C[Nested#e] > 0) ==> (M[Nested#e][0] == M[Nested#c][0]);
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[Nested#e] - 0)) ==> (M[Nested#e][i] == (M[Nested#e][i - 1] + M[Nested#c][i]))
  );
  assume R[Nested#c] == C[Nested#e];
  assume R[Nested#a] == C[Nested#b];
  assume R[Nested#a] == C[Nested#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Nested#b]) ==> (M[Nested#b][idx$] == M[Nested#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Nested#c]) ==> (M[Nested#c][idx$] == M[Nested#a][idx$])
  );
  assert {:msg "Nested.actor(88.16): Action at Nested.actor(8.3) ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#67)"} (forall i: int :: 
    (0 <= i) && (i < I[Nested#d]) ==> (M[Nested#d][i] == M[Nested#e][i])
  );
  assert {:msg "Nested.actor(89.15): Action at Nested.actor(8.3) ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#68)"} I[Nested#d] == I[Nested#b];
  assert {:msg "Nested.actor(90.15): Action at Nested.actor(8.3) ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#69)"} I[Nested#e] == I[Nested#c];
}
procedure Nested#anon$7#input#in#18()
  modifies C, R, M, I, H;
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
  assume (B[Nested#a] == 1) && (B[Nested#d] == 1) && (B[Nested#e] == 1);
  assume (B[Nested#a] == 1) && (B[Nested#d] == 1) && (B[Nested#e] == 1);
  assume (C[Nested#a] - I[Nested#a]) < 1;
  assume (forall i: int :: 
    (0 <= i) && (i < I[Nested#d]) ==> (M[Nested#d][i] == M[Nested#e][i])
  );
  assume I[Nested#d] == I[Nested#b];
  assume I[Nested#e] == I[Nested#c];
  assume I[Nested#d] == I[Nested#b];
  assume I[Nested#e] == I[Nested#c];
  assume I[Nested#b] == I[Nested#a];
  assume I[Nested#c] == I[Nested#a];
  assume 0 <= M[Nested#a][I[Nested#a]];
  assume (C[Nested#a] - I[Nested#a]) <= 1;
  assume R[Nested#b] == C[Nested#d];
  assume (C[Nested#d] > 0) ==> (M[Nested#d][0] == M[Nested#b][0]);
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[Nested#d] - 0)) ==> (M[Nested#d][i] == (M[Nested#d][i - 1] + M[Nested#b][i]))
  );
  assume R[Nested#b] == C[Nested#d];
  assume R[Nested#c] == C[Nested#e];
  assume (C[Nested#e] > 0) ==> (M[Nested#e][0] == M[Nested#c][0]);
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[Nested#e] - 0)) ==> (M[Nested#e][i] == (M[Nested#e][i - 1] + M[Nested#c][i]))
  );
  assume R[Nested#c] == C[Nested#e];
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
  assert {:msg "Nested.actor(88.16): Channel invariant might be falsified by network input (#70)"} (forall i: int :: 
    (0 <= i) && (i < I[Nested#d]) ==> (M[Nested#d][i] == M[Nested#e][i])
  );
  assert {:msg "Nested.actor(89.15): Channel invariant might be falsified by network input (#71)"} I[Nested#d] == I[Nested#b];
  assert {:msg "Nested.actor(90.15): Channel invariant might be falsified by network input (#72)"} I[Nested#e] == I[Nested#c];
  assert {:msg "Channel invariant might be falsified by network input (#73)"} I[Nested#d] == I[Nested#b];
  assert {:msg "Channel invariant might be falsified by network input (#74)"} I[Nested#e] == I[Nested#c];
  assert {:msg "Channel invariant might be falsified by network input (#75)"} I[Nested#b] == I[Nested#a];
  assert {:msg "Channel invariant might be falsified by network input (#76)"} I[Nested#c] == I[Nested#a];
  assert {:msg "Nested.actor(78.14): Channel invariant might be falsified by network input (#77)"} 0 <= M[Nested#a][I[Nested#a]];
  assert {:msg "Channel invariant might be falsified by network input (#78)"} (C[Nested#a] - I[Nested#a]) <= 1;
}
procedure Nested#anon$7#exit#19()
  modifies C, R, M, I, H;
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
  assume (B[Nested#a] == 1) && (B[Nested#d] == 1) && (B[Nested#e] == 1);
  assume (B[Nested#a] == 1) && (B[Nested#d] == 1) && (B[Nested#e] == 1);
  assume (forall i: int :: 
    (0 <= i) && (i < I[Nested#d]) ==> (M[Nested#d][i] == M[Nested#e][i])
  );
  assume I[Nested#d] == I[Nested#b];
  assume I[Nested#e] == I[Nested#c];
  assume I[Nested#d] == I[Nested#b];
  assume I[Nested#e] == I[Nested#c];
  assume I[Nested#b] == I[Nested#a];
  assume I[Nested#c] == I[Nested#a];
  assume 0 <= M[Nested#a][I[Nested#a]];
  assume (C[Nested#a] - I[Nested#a]) <= 1;
  assume R[Nested#b] == C[Nested#d];
  assume (C[Nested#d] > 0) ==> (M[Nested#d][0] == M[Nested#b][0]);
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[Nested#d] - 0)) ==> (M[Nested#d][i] == (M[Nested#d][i - 1] + M[Nested#b][i]))
  );
  assume R[Nested#b] == C[Nested#d];
  assume R[Nested#c] == C[Nested#e];
  assume (C[Nested#e] > 0) ==> (M[Nested#e][0] == M[Nested#c][0]);
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[Nested#e] - 0)) ==> (M[Nested#e][i] == (M[Nested#e][i - 1] + M[Nested#c][i]))
  );
  assume R[Nested#c] == C[Nested#e];
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
  assert {:msg "Nested.actor(79.13): Network action postcondition might not hold (#79)"} M[Nested#d][0] == M[Nested#a][0];
  assert {:msg "Nested.actor(80.13): Network action postcondition might not hold (#80)"} M[Nested#e][0] == M[Nested#a][0];
  assert {:msg "Nested.actor(81.13): Network action postcondition might not hold (#81)"} (0 < I[Nested#d]) ==> (M[Nested#d][I[Nested#d]] == (M[Nested#d][I[Nested#d] - 1] + M[Nested#a][I[Nested#a]]));
  assert {:msg "Nested.actor(82.13): Network action postcondition might not hold (#82)"} (0 < I[Nested#e]) ==> (M[Nested#e][I[Nested#e]] == (M[Nested#e][I[Nested#e] - 1] + M[Nested#a][I[Nested#a]]));
  assert {:msg "Nested.actor(83.13): Network action postcondition might not hold (#83)"} M[Nested#d][I[Nested#d]] == M[Nested#e][I[Nested#e]];
  R[Nested#d] := R[Nested#d] + 1;
  R[Nested#e] := R[Nested#e] + 1;
  I := R;
  assert {:msg "Nested.actor(88.16): The network might not preserve the channel invariant (#84)"} (forall i: int :: 
    (0 <= i) && (i < I[Nested#d]) ==> (M[Nested#d][i] == M[Nested#e][i])
  );
  assert {:msg "Nested.actor(89.15): The network might not preserve the channel invariant (#85)"} I[Nested#d] == I[Nested#b];
  assert {:msg "Nested.actor(90.15): The network might not preserve the channel invariant (#86)"} I[Nested#e] == I[Nested#c];
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel a (#87)"} (C[Nested#a] - R[Nested#a]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel b (#88)"} (C[Nested#b] - R[Nested#b]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel c (#89)"} (C[Nested#c] - R[Nested#c]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel d (#90)"} (C[Nested#d] - R[Nested#d]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel e (#91)"} (C[Nested#e] - R[Nested#e]) == 0;
}

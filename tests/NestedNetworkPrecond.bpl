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
var I#sub: CType;

var H: HType;

const unique this#: Actor;

function AT#Min(x:int, y: int): int { if x <= y then x else y }

// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

procedure A#init#0()
  modifies C, R, M, I, H, I#sub;
{
  var in: Chan (int);
  var out: Chan (int);
  assume in != out;
  assume R[in] == 0;
  assume C[out] == 0;
}
procedure A#anon$0#1()
  modifies C, R, M, I, H, I#sub;
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
  M[out][C[out]] := in#0;
  C[out] := C[out] + 1;
}
procedure B#init#2()
  modifies C, R, M, I, H, I#sub;
{
  var B#a: Actor;
  var B#anon$2: Chan (int);
  var B#anon$3: Chan (int);
  assume 0 <= I[B#anon$2];
  assume I[B#anon$2] <= R[B#anon$2];
  assume R[B#anon$2] <= C[B#anon$2];
  assume 0 <= I[B#anon$3];
  assume I[B#anon$3] <= R[B#anon$3];
  assume R[B#anon$3] <= C[B#anon$3];
  assume I[B#anon$3] == R[B#anon$3];
  assume (B[B#anon$2] == 1) && (B[B#anon$3] == 1);
  assume C[B#anon$2] == 0;
  assume R[B#anon$2] == 0;
  assume C[B#anon$3] == 0;
  assume R[B#anon$3] == 0;
  I := R;
  assert {:msg "NestedNetworkPrecond.actor(12.21): Initialization of network 'B' might not establish the network invariant (#0)"} (forall i: int :: 
    (0 <= i) && (i < C[B#anon$3]) ==> (0 <= M[B#anon$3][i])
  );
  assert {:msg "Initialization of network 'B' might not establish the network invariant: Unread tokens might be left on channel anon$2 (#1)"} (C[B#anon$2] - R[B#anon$2]) == 0;
  assert {:msg "Initialization of network 'B' might not establish the network invariant: Unread tokens might be left on channel anon$3 (#2)"} (C[B#anon$3] - R[B#anon$3]) == 0;
}
procedure B##A#anon$0#3()
  modifies C, R, M, I, H, I#sub;
{
  var B#a: Actor;
  var B#anon$2: Chan (int);
  var B#anon$3: Chan (int);
  var in#i: int;
  assume 0 <= I[B#anon$2];
  assume I[B#anon$2] <= R[B#anon$2];
  assume R[B#anon$2] <= C[B#anon$2];
  assume 0 <= I[B#anon$3];
  assume I[B#anon$3] <= R[B#anon$3];
  assume R[B#anon$3] <= C[B#anon$3];
  assume I[B#anon$3] == R[B#anon$3];
  assume (B[B#anon$2] == 1) && (B[B#anon$3] == 1);
  I#sub[B#anon$2] := R[B#anon$2];
  I#sub[B#anon$3] := C[B#anon$3];
  assume I[B#anon$3] == I[B#anon$2];
  assume 0 <= M[B#anon$2][I[B#anon$2]];
  assume (C[B#anon$2] - I[B#anon$2]) <= 1;
  assume R[B#anon$2] == C[B#anon$3];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[B#anon$3]) ==> (M[B#anon$3][idx$] == M[B#anon$2][idx$])
  );
  assume 1 <= (C[B#anon$2] - R[B#anon$2]);
  in#i := M[B#anon$2][R[B#anon$2]];
  R[B#anon$2] := R[B#anon$2] + 1;
  M[B#anon$3][C[B#anon$3]] := in#i;
  C[B#anon$3] := C[B#anon$3] + 1;
}
procedure B#anon$1#input#in#4()
  modifies C, R, M, I, H, I#sub;
{
  var B#a: Actor;
  var B#anon$2: Chan (int);
  var B#anon$3: Chan (int);
  assume 0 <= I[B#anon$2];
  assume I[B#anon$2] <= R[B#anon$2];
  assume R[B#anon$2] <= C[B#anon$2];
  assume 0 <= I[B#anon$3];
  assume I[B#anon$3] <= R[B#anon$3];
  assume R[B#anon$3] <= C[B#anon$3];
  assume I[B#anon$3] == R[B#anon$3];
  assume (B[B#anon$2] == 1) && (B[B#anon$3] == 1);
  assume (B[B#anon$2] == 1) && (B[B#anon$3] == 1);
  assume (C[B#anon$2] - I[B#anon$2]) < 1;
  assume I[B#anon$3] == I[B#anon$2];
  assume 0 <= M[B#anon$2][I[B#anon$2]];
  assume (C[B#anon$2] - I[B#anon$2]) <= 1;
  assume R[B#anon$2] == C[B#anon$3];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[B#anon$3]) ==> (M[B#anon$3][idx$] == M[B#anon$2][idx$])
  );
  C[B#anon$2] := C[B#anon$2] + 1;
  assume 0 <= M[B#anon$2][I[B#anon$2]];
}
procedure B#anon$1#exit#5()
  modifies C, R, M, I, H, I#sub;
{
  var B#a: Actor;
  var B#anon$2: Chan (int);
  var B#anon$3: Chan (int);
  assume 0 <= I[B#anon$2];
  assume I[B#anon$2] <= R[B#anon$2];
  assume R[B#anon$2] <= C[B#anon$2];
  assume 0 <= I[B#anon$3];
  assume I[B#anon$3] <= R[B#anon$3];
  assume R[B#anon$3] <= C[B#anon$3];
  assume I[B#anon$3] == R[B#anon$3];
  assume (B[B#anon$2] == 1) && (B[B#anon$3] == 1);
  assume (B[B#anon$2] == 1) && (B[B#anon$3] == 1);
  assume I[B#anon$3] == I[B#anon$2];
  assume 0 <= M[B#anon$2][I[B#anon$2]];
  assume (C[B#anon$2] - I[B#anon$2]) <= 1;
  assume R[B#anon$2] == C[B#anon$3];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[B#anon$3]) ==> (M[B#anon$3][idx$] == M[B#anon$2][idx$])
  );
  assume (C[B#anon$2] - I[B#anon$2]) == 1;
  assume 0 <= M[B#anon$2][I[B#anon$2]];
  assume !(1 <= (C[B#anon$2] - R[B#anon$2]));
  assert {:msg "NestedNetworkPrecond.actor(8.13): Network action postcondition might not hold (#3)"} 0 <= M[B#anon$3][I[B#anon$3]];
  R[B#anon$3] := R[B#anon$3] + 1;
  I := R;
  assert {:msg "NestedNetworkPrecond.actor(12.21): The network might not preserve the network invariant (#4)"} (forall i: int :: 
    (0 <= i) && (i < C[B#anon$3]) ==> (0 <= M[B#anon$3][i])
  );
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel anon$2 (#5)"} (C[B#anon$2] - R[B#anon$2]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel anon$3 (#6)"} (C[B#anon$3] - R[B#anon$3]) == 0;
}
procedure C#init#6()
  modifies C, R, M, I, H, I#sub;
{
  var C#b: Actor;
  var C#anon$5: Chan (int);
  var C#anon$6: Chan (int);
  assume 0 <= I[C#anon$5];
  assume I[C#anon$5] <= R[C#anon$5];
  assume R[C#anon$5] <= C[C#anon$5];
  assume 0 <= I[C#anon$6];
  assume I[C#anon$6] <= R[C#anon$6];
  assume R[C#anon$6] <= C[C#anon$6];
  assume I[C#anon$6] == R[C#anon$6];
  assume (B[C#anon$5] == 2) && (B[C#anon$6] == 2);
  assume C[C#anon$5] == 0;
  assume R[C#anon$5] == 0;
  assume C[C#anon$6] == 0;
  assume R[C#anon$6] == 0;
  I := R;
  assert {:msg "Initialization of network 'C' might not establish the network invariant: Unread tokens might be left on channel anon$5 (#7)"} (C[C#anon$5] - R[C#anon$5]) == 0;
  assert {:msg "Initialization of network 'C' might not establish the network invariant: Unread tokens might be left on channel anon$6 (#8)"} (C[C#anon$6] - R[C#anon$6]) == 0;
}
procedure C##B#anon$1#7()
  modifies C, R, M, I, H, I#sub;
{
  var C#b: Actor;
  var C#anon$5: Chan (int);
  var C#anon$6: Chan (int);
  assume 0 <= I[C#anon$5];
  assume I[C#anon$5] <= R[C#anon$5];
  assume R[C#anon$5] <= C[C#anon$5];
  assume 0 <= I[C#anon$6];
  assume I[C#anon$6] <= R[C#anon$6];
  assume R[C#anon$6] <= C[C#anon$6];
  assume I[C#anon$6] == R[C#anon$6];
  assume (B[C#anon$5] == 2) && (B[C#anon$6] == 2);
  I#sub[C#anon$5] := R[C#anon$5];
  I#sub[C#anon$6] := C[C#anon$6];
  assume I[C#anon$6] == I[C#anon$5];
  assume (0 <= M[C#anon$5][I[C#anon$5]]) && (0 <= M[C#anon$5][I[C#anon$5] + 1]);
  assume (C[C#anon$5] - I[C#anon$5]) <= 2;
  assume (forall i: int :: 
    (0 <= i) && (i < C[C#anon$6]) ==> (0 <= M[C#anon$6][i])
  );
  assume R[C#anon$5] == C[C#anon$6];
  assume 1 <= (C[C#anon$5] - R[C#anon$5]);
  R[C#anon$5] := R[C#anon$5] + 1;
  assert {:msg "NestedNetworkPrecond.actor(7.14): Precondition might not hold for instance at NestedNetworkPrecond.actor(23.12) (#9)"} 0 <= M[C#anon$5][I#sub[C#anon$5]];
  C[C#anon$6] := C[C#anon$6] + 1;
  assume 0 <= M[C#anon$6][I#sub[C#anon$6]];
}
procedure C#anon$4#input#in#8()
  modifies C, R, M, I, H, I#sub;
{
  var C#b: Actor;
  var C#anon$5: Chan (int);
  var C#anon$6: Chan (int);
  assume 0 <= I[C#anon$5];
  assume I[C#anon$5] <= R[C#anon$5];
  assume R[C#anon$5] <= C[C#anon$5];
  assume 0 <= I[C#anon$6];
  assume I[C#anon$6] <= R[C#anon$6];
  assume R[C#anon$6] <= C[C#anon$6];
  assume I[C#anon$6] == R[C#anon$6];
  assume (B[C#anon$5] == 2) && (B[C#anon$6] == 2);
  assume (B[C#anon$5] == 2) && (B[C#anon$6] == 2);
  assume (C[C#anon$5] - I[C#anon$5]) < 2;
  assume I[C#anon$6] == I[C#anon$5];
  assume (0 <= M[C#anon$5][I[C#anon$5]]) && (0 <= M[C#anon$5][I[C#anon$5] + 1]);
  assume (C[C#anon$5] - I[C#anon$5]) <= 2;
  assume (forall i: int :: 
    (0 <= i) && (i < C[C#anon$6]) ==> (0 <= M[C#anon$6][i])
  );
  assume R[C#anon$5] == C[C#anon$6];
  C[C#anon$5] := C[C#anon$5] + 1;
  assume (0 <= M[C#anon$5][I[C#anon$5]]) && (0 <= M[C#anon$5][I[C#anon$5] + 1]);
}
procedure C#anon$4#exit#9()
  modifies C, R, M, I, H, I#sub;
{
  var C#b: Actor;
  var C#anon$5: Chan (int);
  var C#anon$6: Chan (int);
  assume 0 <= I[C#anon$5];
  assume I[C#anon$5] <= R[C#anon$5];
  assume R[C#anon$5] <= C[C#anon$5];
  assume 0 <= I[C#anon$6];
  assume I[C#anon$6] <= R[C#anon$6];
  assume R[C#anon$6] <= C[C#anon$6];
  assume I[C#anon$6] == R[C#anon$6];
  assume (B[C#anon$5] == 2) && (B[C#anon$6] == 2);
  assume (B[C#anon$5] == 2) && (B[C#anon$6] == 2);
  assume I[C#anon$6] == I[C#anon$5];
  assume (0 <= M[C#anon$5][I[C#anon$5]]) && (0 <= M[C#anon$5][I[C#anon$5] + 1]);
  assume (C[C#anon$5] - I[C#anon$5]) <= 2;
  assume (forall i: int :: 
    (0 <= i) && (i < C[C#anon$6]) ==> (0 <= M[C#anon$6][i])
  );
  assume R[C#anon$5] == C[C#anon$6];
  assume (C[C#anon$5] - I[C#anon$5]) == 2;
  assume (0 <= M[C#anon$5][I[C#anon$5]]) && (0 <= M[C#anon$5][I[C#anon$5] + 1]);
  assume !(1 <= (C[C#anon$5] - R[C#anon$5]));
  assert {:msg "NestedNetworkPrecond.actor(21.13): Network action postcondition might not hold (#10)"} (0 <= M[C#anon$6][I[C#anon$6]]) && (0 <= M[C#anon$6][I[C#anon$6] + 1]);
  R[C#anon$6] := R[C#anon$6] + 2;
  I := R;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel anon$5 (#11)"} (C[C#anon$5] - R[C#anon$5]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel anon$6 (#12)"} (C[C#anon$6] - R[C#anon$6]) == 0;
}

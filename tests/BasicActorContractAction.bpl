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
// -- Integer division and modulo --------------------------------
// ---------------------------------------------------------------
function AT#Abs(x: int): int { if 0 <= x then x else -x }
function AT#Div(int, int): int;
function AT#Mod(int, int): int;
axiom (forall a,b: int :: AT#Div(a,b)*b + AT#Mod(a,b) == a);
axiom (forall a,b: int :: 0 <= AT#Mod(a,b) && AT#Mod(a,b) < AT#Abs(b));

// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

procedure A#init#0()
  modifies C, R, M, I, H, I#sub;
{
  var in: Chan (int);
  var out: Chan (int);
  assume in != out;
  assume (I[in] == 0) && (R[in] == 0) && (C[in] == 0);
  assume (I[out] == 0) && (R[out] == 0) && (C[out] == 0);
}
procedure A#anon$0#1()
  modifies C, R, M, I, H, I#sub;
{
  var in: Chan (int);
  var out: Chan (int);
  var in#0: int;
  assume in != out;
  assume (0 <= I[in]) && (I[in] <= R[in]) && (R[in] <= C[in]);
  assume (0 <= I[out]) && (I[out] <= R[out]) && (R[out] <= C[out]);
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
  var in: Chan (int);
  var out: Chan (int);
  assume in != out;
  assume (I[in] == 0) && (R[in] == 0) && (C[in] == 0);
  assume (I[out] == 0) && (R[out] == 0) && (C[out] == 0);
  assert {:msg "BasicActorContractAction.actor(14.21): Initialization might not establish the invariant (#0)"} (forall i: int :: 
    (0 <= i) && (i < C[out]) ==> (M[out][i] == M[in][i])
  );
  assert {:msg "BasicActorContractAction.actor(15.20): Initialization might not establish the invariant (#1)"} C[out] == R[in];
  assert {:msg "BasicActorContractAction.actor(17.13): Initialization might not establish the invariant (#2)"} I[in] == I[out];
}
procedure B#anon$2#3()
  modifies C, R, M, I, H, I#sub;
{
  var in: Chan (int);
  var out: Chan (int);
  var in#0: int;
  assume in != out;
  assume (0 <= I[in]) && (I[in] <= R[in]) && (R[in] <= C[in]);
  assume (0 <= I[out]) && (I[out] <= R[out]) && (R[out] <= C[out]);
  assume (forall i: int :: 
    (0 <= i) && (i < C[out]) ==> (M[out][i] == M[in][i])
  );
  assume C[out] == R[in];
  assume I[in] == I[out];
  assume R[in] == C[out];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == M[in][idx$])
  );
  in#0 := M[in][R[in]];
  R[in] := R[in] + 1;
  M[out][C[out]] := in#0;
  C[out] := C[out] + 1;
  assert {:msg "BasicActorContractAction.actor(14.21): Action at BasicActorContractAction.actor(19.3) might not preserve invariant (#3)"} (forall i: int :: 
    (0 <= i) && (i < C[out]) ==> (M[out][i] == M[in][i])
  );
  assert {:msg "BasicActorContractAction.actor(15.20): Action at BasicActorContractAction.actor(19.3) might not preserve invariant (#4)"} C[out] == R[in];
  assert {:msg "BasicActorContractAction.actor(17.13): Action at BasicActorContractAction.actor(19.3) might not preserve invariant (#5)"} I[in] == I[out];
}
procedure B#contract#anon$1#4()
  modifies C, R, M, I, H, I#sub;
{
  var in: Chan (int);
  var out: Chan (int);
  assume in != out;
  assume (0 <= I[in]) && (I[in] <= R[in]) && (R[in] <= C[in]);
  assume (0 <= I[out]) && (I[out] <= R[out]) && (R[out] <= C[out]);
  assume (forall i: int :: 
    (0 <= i) && (i < C[out]) ==> (M[out][i] == M[in][i])
  );
  assume C[out] == R[in];
  assume I[in] == I[out];
  assume R[in] == C[out];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == M[in][idx$])
  );
  assume (C[in] - I[in]) == 2;
  assume !(true && (1 <= (C[in] - R[in])) && true);
  assert {:msg "BasicActorContractAction.actor(9.3): The correct number of tokens might not be produced on output 'out' (#6)"} (C[out] - I[out]) == 2;
  assert {:msg "BasicActorContractAction.actor(10.13): Contract action postcondition might not hold (#7)"} M[out][I[out]] == M[in][I[in]];
  assert {:msg "BasicActorContractAction.actor(11.13): Contract action postcondition might not hold (#8)"} M[out][I[out] + 1] == M[in][I[in] + 1];
}
procedure N#init#5()
  modifies C, R, M, I, H, I#sub;
{
  var N#a: Actor;
  var N#ch_in: Chan (int);
  var N#ch_out: Chan (int);
  assume 0 <= I[N#ch_in];
  assume I[N#ch_in] <= R[N#ch_in];
  assume R[N#ch_in] <= C[N#ch_in];
  assume 0 <= I[N#ch_out];
  assume I[N#ch_out] <= R[N#ch_out];
  assume R[N#ch_out] <= C[N#ch_out];
  assume I[N#ch_out] == R[N#ch_out];
  assume (B[N#ch_in] == 2) && (B[N#ch_out] == 2);
  assume C[N#ch_in] == 0;
  assume R[N#ch_in] == 0;
  assume C[N#ch_out] == 0;
  assume R[N#ch_out] == 0;
  I := R;
  assert {:msg "BasicActorContractAction.actor(30.21): Initialization of network 'N' might not establish the network invariant (#9)"} (forall i: int :: 
    (0 <= i) && (i < C[N#ch_out]) ==> (M[N#ch_out][i] == M[N#ch_in][i])
  );
  assert {:msg "BasicActorContractAction.actor(31.20): Initialization of network 'N' might not establish the network invariant (#10)"} C[N#ch_out] == R[N#ch_in];
  assert {:msg "Initialization of network 'N' might not establish the network invariant: Unread tokens might be left on channel ch_in (#11)"} (C[N#ch_in] - R[N#ch_in]) == 0;
  assert {:msg "Initialization of network 'N' might not establish the network invariant: Unread tokens might be left on channel ch_out (#12)"} (C[N#ch_out] - R[N#ch_out]) == 0;
}
procedure N##A#anon$0#6()
  modifies C, R, M, I, H, I#sub;
{
  var N#a: Actor;
  var N#ch_in: Chan (int);
  var N#ch_out: Chan (int);
  var in#i: int;
  assume 0 <= I[N#ch_in];
  assume I[N#ch_in] <= R[N#ch_in];
  assume R[N#ch_in] <= C[N#ch_in];
  assume 0 <= I[N#ch_out];
  assume I[N#ch_out] <= R[N#ch_out];
  assume R[N#ch_out] <= C[N#ch_out];
  assume I[N#ch_out] == R[N#ch_out];
  assume (B[N#ch_in] == 2) && (B[N#ch_out] == 2);
  I#sub[N#ch_in] := R[N#ch_in];
  I#sub[N#ch_out] := C[N#ch_out];
  assume I[N#ch_out] == I[N#ch_in];
  assume (C[N#ch_in] - I[N#ch_in]) <= 2;
  assume R[N#ch_in] == C[N#ch_out];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[N#ch_out]) ==> (M[N#ch_out][idx$] == M[N#ch_in][idx$])
  );
  assume 1 <= (C[N#ch_in] - R[N#ch_in]);
  in#i := M[N#ch_in][R[N#ch_in]];
  R[N#ch_in] := R[N#ch_in] + 1;
  M[N#ch_out][C[N#ch_out]] := in#i;
  C[N#ch_out] := C[N#ch_out] + 1;
}
procedure N#anon$3#input#in#7()
  modifies C, R, M, I, H, I#sub;
{
  var N#a: Actor;
  var N#ch_in: Chan (int);
  var N#ch_out: Chan (int);
  assume 0 <= I[N#ch_in];
  assume I[N#ch_in] <= R[N#ch_in];
  assume R[N#ch_in] <= C[N#ch_in];
  assume 0 <= I[N#ch_out];
  assume I[N#ch_out] <= R[N#ch_out];
  assume R[N#ch_out] <= C[N#ch_out];
  assume I[N#ch_out] == R[N#ch_out];
  assume (B[N#ch_in] == 2) && (B[N#ch_out] == 2);
  assume (B[N#ch_in] == 2) && (B[N#ch_out] == 2);
  assume (C[N#ch_in] - I[N#ch_in]) < 2;
  assume I[N#ch_out] == I[N#ch_in];
  assume (C[N#ch_in] - I[N#ch_in]) <= 2;
  assume R[N#ch_in] == C[N#ch_out];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[N#ch_out]) ==> (M[N#ch_out][idx$] == M[N#ch_in][idx$])
  );
  C[N#ch_in] := C[N#ch_in] + 1;
}
procedure N#anon$3#exit#8()
  modifies C, R, M, I, H, I#sub;
{
  var N#a: Actor;
  var N#ch_in: Chan (int);
  var N#ch_out: Chan (int);
  assume 0 <= I[N#ch_in];
  assume I[N#ch_in] <= R[N#ch_in];
  assume R[N#ch_in] <= C[N#ch_in];
  assume 0 <= I[N#ch_out];
  assume I[N#ch_out] <= R[N#ch_out];
  assume R[N#ch_out] <= C[N#ch_out];
  assume I[N#ch_out] == R[N#ch_out];
  assume (B[N#ch_in] == 2) && (B[N#ch_out] == 2);
  assume (B[N#ch_in] == 2) && (B[N#ch_out] == 2);
  assume I[N#ch_out] == I[N#ch_in];
  assume (C[N#ch_in] - I[N#ch_in]) <= 2;
  assume R[N#ch_in] == C[N#ch_out];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[N#ch_out]) ==> (M[N#ch_out][idx$] == M[N#ch_in][idx$])
  );
  assume (C[N#ch_in] - I[N#ch_in]) == 2;
  assume !(1 <= (C[N#ch_in] - R[N#ch_in]));
  assert {:msg "BasicActorContractAction.actor(25.3): The correct number of tokens might not be produced on output 'out' (#13)"} (C[N#ch_out] - I[N#ch_out]) == 2;
  assert {:msg "BasicActorContractAction.actor(26.13): Network action postcondition might not hold (#14)"} M[N#ch_out][I[N#ch_out]] == M[N#ch_in][I[N#ch_in]];
  assert {:msg "BasicActorContractAction.actor(27.13): Network action postcondition might not hold (#15)"} M[N#ch_out][I[N#ch_out] + 1] == M[N#ch_in][I[N#ch_in] + 1];
  R[N#ch_out] := R[N#ch_out] + 2;
  I := R;
  assert {:msg "BasicActorContractAction.actor(30.21): The network might not preserve the network invariant (#16)"} (forall i: int :: 
    (0 <= i) && (i < C[N#ch_out]) ==> (M[N#ch_out][i] == M[N#ch_in][i])
  );
  assert {:msg "BasicActorContractAction.actor(31.20): The network might not preserve the network invariant (#17)"} C[N#ch_out] == R[N#ch_in];
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel ch_in (#18)"} (C[N#ch_in] - R[N#ch_in]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel ch_out (#19)"} (C[N#ch_out] - R[N#ch_out]) == 0;
}
procedure N2#init#9()
  modifies C, R, M, I, H, I#sub;
{
  var N2#a: Actor;
  var N2#ch_in: Chan (int);
  var N2#ch_out: Chan (int);
  assume 0 <= I[N2#ch_in];
  assume I[N2#ch_in] <= R[N2#ch_in];
  assume R[N2#ch_in] <= C[N2#ch_in];
  assume 0 <= I[N2#ch_out];
  assume I[N2#ch_out] <= R[N2#ch_out];
  assume R[N2#ch_out] <= C[N2#ch_out];
  assume I[N2#ch_out] == R[N2#ch_out];
  assume (B[N2#ch_in] == 4) && (B[N2#ch_out] == 4);
  assume C[N2#ch_in] == 0;
  assume R[N2#ch_in] == 0;
  assume C[N2#ch_out] == 0;
  assume R[N2#ch_out] == 0;
  assert {:msg "BasicActorContractAction.actor(45.15): Initialization of network 'N2' might not establish the channel invariant (#20)"} AT#Mod(R[N2#ch_in] - I[N2#ch_in], 2) == 0;
  I := R;
  assert {:msg "Initialization of network 'N2' might not establish the network invariant: Unread tokens might be left on channel ch_in (#21)"} (C[N2#ch_in] - R[N2#ch_in]) == 0;
  assert {:msg "Initialization of network 'N2' might not establish the network invariant: Unread tokens might be left on channel ch_out (#22)"} (C[N2#ch_out] - R[N2#ch_out]) == 0;
}
procedure N2##N#anon$3#10()
  modifies C, R, M, I, H, I#sub;
{
  var N2#a: Actor;
  var N2#ch_in: Chan (int);
  var N2#ch_out: Chan (int);
  assume 0 <= I[N2#ch_in];
  assume I[N2#ch_in] <= R[N2#ch_in];
  assume R[N2#ch_in] <= C[N2#ch_in];
  assume 0 <= I[N2#ch_out];
  assume I[N2#ch_out] <= R[N2#ch_out];
  assume R[N2#ch_out] <= C[N2#ch_out];
  assume I[N2#ch_out] == R[N2#ch_out];
  assume (B[N2#ch_in] == 4) && (B[N2#ch_out] == 4);
  I#sub[N2#ch_in] := R[N2#ch_in];
  I#sub[N2#ch_out] := C[N2#ch_out];
  assume AT#Mod(R[N2#ch_in] - I[N2#ch_in], 2) == 0;
  assume (2 * I[N2#ch_out]) == (2 * I[N2#ch_in]);
  assume (C[N2#ch_in] - I[N2#ch_in]) <= 4;
  assume (forall i: int :: 
    (0 <= i) && (i < C[N2#ch_out]) ==> (M[N2#ch_out][i] == M[N2#ch_in][i])
  );
  assume C[N2#ch_out] == R[N2#ch_in];
  assume (2 * R[N2#ch_in]) == (2 * C[N2#ch_out]);
  assume 2 <= (C[N2#ch_in] - R[N2#ch_in]);
  R[N2#ch_in] := R[N2#ch_in] + 2;
  C[N2#ch_out] := C[N2#ch_out] + 2;
  assume M[N2#ch_out][I#sub[N2#ch_out]] == M[N2#ch_in][I#sub[N2#ch_in]];
  assume M[N2#ch_out][I#sub[N2#ch_out] + 1] == M[N2#ch_in][I#sub[N2#ch_in] + 1];
  assert {:msg "BasicActorContractAction.actor(45.15): Action at BasicActorContractAction.actor(25.3) ('anon$3') for actor instance 'a' might not preserve the channel invariant (#23)"} AT#Mod(R[N2#ch_in] - I[N2#ch_in], 2) == 0;
}
procedure N2#anon$4#input#in#11()
  modifies C, R, M, I, H, I#sub;
{
  var N2#a: Actor;
  var N2#ch_in: Chan (int);
  var N2#ch_out: Chan (int);
  assume 0 <= I[N2#ch_in];
  assume I[N2#ch_in] <= R[N2#ch_in];
  assume R[N2#ch_in] <= C[N2#ch_in];
  assume 0 <= I[N2#ch_out];
  assume I[N2#ch_out] <= R[N2#ch_out];
  assume R[N2#ch_out] <= C[N2#ch_out];
  assume I[N2#ch_out] == R[N2#ch_out];
  assume (B[N2#ch_in] == 4) && (B[N2#ch_out] == 4);
  assume (B[N2#ch_in] == 4) && (B[N2#ch_out] == 4);
  assume (C[N2#ch_in] - I[N2#ch_in]) < 4;
  assume AT#Mod(R[N2#ch_in] - I[N2#ch_in], 2) == 0;
  assume (2 * I[N2#ch_out]) == (2 * I[N2#ch_in]);
  assume (C[N2#ch_in] - I[N2#ch_in]) <= 4;
  assume (forall i: int :: 
    (0 <= i) && (i < C[N2#ch_out]) ==> (M[N2#ch_out][i] == M[N2#ch_in][i])
  );
  assume C[N2#ch_out] == R[N2#ch_in];
  assume (2 * R[N2#ch_in]) == (2 * C[N2#ch_out]);
  C[N2#ch_in] := C[N2#ch_in] + 1;
  assert {:msg "BasicActorContractAction.actor(45.15): Channel invariant might be falsified by network input (#24)"} AT#Mod(R[N2#ch_in] - I[N2#ch_in], 2) == 0;
}
procedure N2#anon$4#exit#12()
  modifies C, R, M, I, H, I#sub;
{
  var N2#a: Actor;
  var N2#ch_in: Chan (int);
  var N2#ch_out: Chan (int);
  assume 0 <= I[N2#ch_in];
  assume I[N2#ch_in] <= R[N2#ch_in];
  assume R[N2#ch_in] <= C[N2#ch_in];
  assume 0 <= I[N2#ch_out];
  assume I[N2#ch_out] <= R[N2#ch_out];
  assume R[N2#ch_out] <= C[N2#ch_out];
  assume I[N2#ch_out] == R[N2#ch_out];
  assume (B[N2#ch_in] == 4) && (B[N2#ch_out] == 4);
  assume (B[N2#ch_in] == 4) && (B[N2#ch_out] == 4);
  assume AT#Mod(R[N2#ch_in] - I[N2#ch_in], 2) == 0;
  assume (2 * I[N2#ch_out]) == (2 * I[N2#ch_in]);
  assume (C[N2#ch_in] - I[N2#ch_in]) <= 4;
  assume (forall i: int :: 
    (0 <= i) && (i < C[N2#ch_out]) ==> (M[N2#ch_out][i] == M[N2#ch_in][i])
  );
  assume C[N2#ch_out] == R[N2#ch_in];
  assume (2 * R[N2#ch_in]) == (2 * C[N2#ch_out]);
  assume (C[N2#ch_in] - I[N2#ch_in]) == 4;
  assume !(2 <= (C[N2#ch_in] - R[N2#ch_in]));
  assert {:msg "BasicActorContractAction.actor(41.3): The correct number of tokens might not be produced on output 'out' (#25)"} (C[N2#ch_out] - I[N2#ch_out]) == 4;
  assert {:msg "BasicActorContractAction.actor(42.14): Network action postcondition might not hold (#26)"} (forall i: int :: 
    (0 <= i) && (i < B[N2#ch_out]) ==> (M[N2#ch_out][I[N2#ch_out] + i] == M[N2#ch_in][I[N2#ch_in] + i])
  );
  R[N2#ch_out] := R[N2#ch_out] + 4;
  I := R;
  assert {:msg "BasicActorContractAction.actor(45.15): The network might not preserve the channel invariant (#27)"} AT#Mod(R[N2#ch_in] - I[N2#ch_in], 2) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel ch_in (#28)"} (C[N2#ch_in] - R[N2#ch_in]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel ch_out (#29)"} (C[N2#ch_out] - R[N2#ch_out]) == 0;
}

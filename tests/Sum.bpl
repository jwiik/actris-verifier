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

procedure Sum#init#0()
  modifies C, R, M, I, H;
{
  var x: Chan (int);
  var y: Chan (int);
  var Ch#sum: Chan (int);
  var sum: int;
  assume x != y;
  assume R[x] == 0;
  assume C[y] == 0;
  assume (R[Ch#sum] == 0) && (C[Ch#sum] == 0);
  sum := 0;
  assert {:msg "Sum.actor(4.13): Initialization might not establish the invariant (#0)"} 0 <= sum;
  assert {:msg "Sum.actor(5.13): Initialization might not establish the invariant (#1)"} (R[x] > 0) ==> (sum == M[y][C[y] - 1]);
  assert {:msg "Sum.actor(6.13): Initialization might not establish the invariant (#2)"} (R[x] == 0) ==> (sum == 0);
  assert {:msg "Sum.actor(7.20): Initialization might not establish the invariant (#3)"} R[x] == C[y];
  assert {:msg "Sum.actor(8.20): Initialization might not establish the invariant (#4)"} (C[y] > 0) ==> (M[y][0] == M[x][0]);
  assert {:msg "Sum.actor(9.21): Initialization might not establish the invariant (#5)"} (forall i: int :: 
    (0 <= i) && (i < C[y]) ==> (M[y][i] >= M[x][i])
  );
  assert {:msg "Sum.actor(10.21): Initialization might not establish the invariant (#6)"} (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[y] - 0)) ==> (M[y][i] == (M[y][i - 1] + M[x][i]))
  );
}
procedure Sum#anon$1#1()
  modifies C, R, M, I, H;
{
  var x: Chan (int);
  var y: Chan (int);
  var Ch#sum: Chan (int);
  var sum: int;
  var x#0: int;
  assume x != y;
  assume 0 <= R[x];
  assume 0 <= C[y];
  assume (0 <= R[Ch#sum]) && (C[Ch#sum] == (R[Ch#sum] + 1));
  assume 0 <= sum;
  assume (R[x] > 0) ==> (sum == M[y][C[y] - 1]);
  assume (R[x] == 0) ==> (sum == 0);
  assume R[x] == C[y];
  assume (C[y] > 0) ==> (M[y][0] == M[x][0]);
  assume (forall i: int :: 
    (0 <= i) && (i < C[y]) ==> (M[y][i] >= M[x][i])
  );
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[y] - 0)) ==> (M[y][i] == (M[y][i - 1] + M[x][i]))
  );
  assume R[x] == C[y];
  x#0 := M[x][R[x]];
  R[x] := R[x] + 1;
  assume 0 <= x#0;
  sum := sum + x#0;
  assert {:msg "Sum.actor(17.13): Action postcondition might not hold (#7)"} x#0 <= sum;
  M[y][C[y]] := sum;
  C[y] := C[y] + 1;
  assert {:msg "Sum.actor(4.13): Action at Sum.actor(15.3) might not preserve invariant (#8)"} 0 <= sum;
  assert {:msg "Sum.actor(5.13): Action at Sum.actor(15.3) might not preserve invariant (#9)"} (R[x] > 0) ==> (sum == M[y][C[y] - 1]);
  assert {:msg "Sum.actor(6.13): Action at Sum.actor(15.3) might not preserve invariant (#10)"} (R[x] == 0) ==> (sum == 0);
  assert {:msg "Sum.actor(7.20): Action at Sum.actor(15.3) might not preserve invariant (#11)"} R[x] == C[y];
  assert {:msg "Sum.actor(8.20): Action at Sum.actor(15.3) might not preserve invariant (#12)"} (C[y] > 0) ==> (M[y][0] == M[x][0]);
  assert {:msg "Sum.actor(9.21): Action at Sum.actor(15.3) might not preserve invariant (#13)"} (forall i: int :: 
    (0 <= i) && (i < C[y]) ==> (M[y][i] >= M[x][i])
  );
  assert {:msg "Sum.actor(10.21): Action at Sum.actor(15.3) might not preserve invariant (#14)"} (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[y] - 0)) ==> (M[y][i] == (M[y][i - 1] + M[x][i]))
  );
}
procedure Net#init#2()
  modifies C, R, M, I, H;
{
  var Net#sum: Actor;
  var Net#anon$3: Chan (int);
  var Net#anon$4: Chan (int);
  var AV#sum#sum: int;
  assume 0 <= I[Net#anon$3];
  assume I[Net#anon$3] <= R[Net#anon$3];
  assume R[Net#anon$3] <= C[Net#anon$3];
  assume 0 <= I[Net#anon$4];
  assume I[Net#anon$4] <= R[Net#anon$4];
  assume R[Net#anon$4] <= C[Net#anon$4];
  assume I[Net#anon$4] == R[Net#anon$4];
  assume (B[Net#anon$3] == 1) && (B[Net#anon$4] == 1);
  assume C[Net#anon$3] == 0;
  assume R[Net#anon$3] == 0;
  assume C[Net#anon$4] == 0;
  assume R[Net#anon$4] == 0;
  assert {:msg "Sum.actor(32.15): Initialization of network 'Net' might not establish the channel invariant (#15)"} I[Net#anon$3] == I[Net#anon$4];
  assert {:msg "Sum.actor(33.15): Initialization of network 'Net' might not establish the channel invariant (#16)"} (C[Net#anon$3] - I[Net#anon$3]) <= 1;
  I := R;
  assert {:msg "Initialization of network 'Net' might not establish the network invariant: Unread tokens might be left on channel anon$3 (#17)"} (C[Net#anon$3] - R[Net#anon$3]) == 0;
  assert {:msg "Initialization of network 'Net' might not establish the network invariant: Unread tokens might be left on channel anon$4 (#18)"} (C[Net#anon$4] - R[Net#anon$4]) == 0;
}
procedure Net##Sum#anon$1#3()
  modifies C, R, M, I, H;
{
  var Net#sum: Actor;
  var Net#anon$3: Chan (int);
  var Net#anon$4: Chan (int);
  var AV#sum#sum: int;
  var x#i: int;
  assume 0 <= I[Net#anon$3];
  assume I[Net#anon$3] <= R[Net#anon$3];
  assume R[Net#anon$3] <= C[Net#anon$3];
  assume 0 <= I[Net#anon$4];
  assume I[Net#anon$4] <= R[Net#anon$4];
  assume R[Net#anon$4] <= C[Net#anon$4];
  assume I[Net#anon$4] == R[Net#anon$4];
  assume (B[Net#anon$3] == 1) && (B[Net#anon$4] == 1);
  assume I[Net#anon$3] == I[Net#anon$4];
  assume (C[Net#anon$3] - I[Net#anon$3]) <= 1;
  assume I[Net#anon$4] == I[Net#anon$3];
  assume 0 <= M[Net#anon$3][I[Net#anon$3]];
  assume (C[Net#anon$3] - I[Net#anon$3]) <= 1;
  assume R[Net#anon$3] == C[Net#anon$4];
  assume (C[Net#anon$4] > 0) ==> (M[Net#anon$4][0] == M[Net#anon$3][0]);
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#anon$4]) ==> (M[Net#anon$4][i] >= M[Net#anon$3][i])
  );
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[Net#anon$4] - 0)) ==> (M[Net#anon$4][i] == (M[Net#anon$4][i - 1] + M[Net#anon$3][i]))
  );
  assume R[Net#anon$3] == C[Net#anon$4];
  assume 1 <= (C[Net#anon$3] - R[Net#anon$3]);
  x#i := M[Net#anon$3][R[Net#anon$3]];
  R[Net#anon$3] := R[Net#anon$3] + 1;
  assert {:msg "Sum.actor(16.14): Precondition might not hold for instance at Sum.actor(36.5) (#19)"} 0 <= x#i;
  havoc AV#sum#sum;
  M[Net#anon$4][C[Net#anon$4]] := AV#sum#sum;
  C[Net#anon$4] := C[Net#anon$4] + 1;
  assume x#i <= AV#sum#sum;
  assume R[Net#anon$3] == C[Net#anon$4];
  assume (C[Net#anon$4] > 0) ==> (M[Net#anon$4][0] == M[Net#anon$3][0]);
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#anon$4]) ==> (M[Net#anon$4][i] >= M[Net#anon$3][i])
  );
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[Net#anon$4] - 0)) ==> (M[Net#anon$4][i] == (M[Net#anon$4][i - 1] + M[Net#anon$3][i]))
  );
  assume R[Net#anon$3] == C[Net#anon$4];
  assert {:msg "Sum.actor(32.15): Action at Sum.actor(15.3) ('anon$1') for actor instance 'sum' might not preserve the channel invariant (#20)"} I[Net#anon$3] == I[Net#anon$4];
  assert {:msg "Sum.actor(33.15): Action at Sum.actor(15.3) ('anon$1') for actor instance 'sum' might not preserve the channel invariant (#21)"} (C[Net#anon$3] - I[Net#anon$3]) <= 1;
}
procedure Net#anon$2#input#in#4()
  modifies C, R, M, I, H;
{
  var Net#sum: Actor;
  var Net#anon$3: Chan (int);
  var Net#anon$4: Chan (int);
  var AV#sum#sum: int;
  assume 0 <= I[Net#anon$3];
  assume I[Net#anon$3] <= R[Net#anon$3];
  assume R[Net#anon$3] <= C[Net#anon$3];
  assume 0 <= I[Net#anon$4];
  assume I[Net#anon$4] <= R[Net#anon$4];
  assume R[Net#anon$4] <= C[Net#anon$4];
  assume I[Net#anon$4] == R[Net#anon$4];
  assume (B[Net#anon$3] == 1) && (B[Net#anon$4] == 1);
  assume (B[Net#anon$3] == 1) && (B[Net#anon$4] == 1);
  assume (C[Net#anon$3] - I[Net#anon$3]) < 1;
  assume I[Net#anon$3] == I[Net#anon$4];
  assume (C[Net#anon$3] - I[Net#anon$3]) <= 1;
  assume I[Net#anon$4] == I[Net#anon$3];
  assume 0 <= M[Net#anon$3][I[Net#anon$3]];
  assume (C[Net#anon$3] - I[Net#anon$3]) <= 1;
  assume R[Net#anon$3] == C[Net#anon$4];
  assume (C[Net#anon$4] > 0) ==> (M[Net#anon$4][0] == M[Net#anon$3][0]);
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#anon$4]) ==> (M[Net#anon$4][i] >= M[Net#anon$3][i])
  );
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[Net#anon$4] - 0)) ==> (M[Net#anon$4][i] == (M[Net#anon$4][i - 1] + M[Net#anon$3][i]))
  );
  assume R[Net#anon$3] == C[Net#anon$4];
  C[Net#anon$3] := C[Net#anon$3] + 1;
  assume 0 <= M[Net#anon$3][I[Net#anon$3]];
  assert {:msg "Sum.actor(32.15): Channel invariant might be falsified by network input (#22)"} I[Net#anon$3] == I[Net#anon$4];
  assert {:msg "Sum.actor(33.15): Channel invariant might be falsified by network input (#23)"} (C[Net#anon$3] - I[Net#anon$3]) <= 1;
  assert {:msg "Channel invariant might be falsified by network input (#24)"} I[Net#anon$4] == I[Net#anon$3];
  assert {:msg "Sum.actor(26.14): Channel invariant might be falsified by network input (#25)"} 0 <= M[Net#anon$3][I[Net#anon$3]];
  assert {:msg "Channel invariant might be falsified by network input (#26)"} (C[Net#anon$3] - I[Net#anon$3]) <= 1;
}
procedure Net#anon$2#exit#5()
  modifies C, R, M, I, H;
{
  var Net#sum: Actor;
  var Net#anon$3: Chan (int);
  var Net#anon$4: Chan (int);
  var AV#sum#sum: int;
  assume 0 <= I[Net#anon$3];
  assume I[Net#anon$3] <= R[Net#anon$3];
  assume R[Net#anon$3] <= C[Net#anon$3];
  assume 0 <= I[Net#anon$4];
  assume I[Net#anon$4] <= R[Net#anon$4];
  assume R[Net#anon$4] <= C[Net#anon$4];
  assume I[Net#anon$4] == R[Net#anon$4];
  assume (B[Net#anon$3] == 1) && (B[Net#anon$4] == 1);
  assume (B[Net#anon$3] == 1) && (B[Net#anon$4] == 1);
  assume I[Net#anon$3] == I[Net#anon$4];
  assume (C[Net#anon$3] - I[Net#anon$3]) <= 1;
  assume I[Net#anon$4] == I[Net#anon$3];
  assume 0 <= M[Net#anon$3][I[Net#anon$3]];
  assume (C[Net#anon$3] - I[Net#anon$3]) <= 1;
  assume R[Net#anon$3] == C[Net#anon$4];
  assume (C[Net#anon$4] > 0) ==> (M[Net#anon$4][0] == M[Net#anon$3][0]);
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#anon$4]) ==> (M[Net#anon$4][i] >= M[Net#anon$3][i])
  );
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[Net#anon$4] - 0)) ==> (M[Net#anon$4][i] == (M[Net#anon$4][i - 1] + M[Net#anon$3][i]))
  );
  assume R[Net#anon$3] == C[Net#anon$4];
  assume (C[Net#anon$3] - I[Net#anon$3]) == 1;
  assume 0 <= M[Net#anon$3][I[Net#anon$3]];
  assume !(1 <= (C[Net#anon$3] - R[Net#anon$3]));
  assert {:msg "Sum.actor(27.13): Network action postcondition might not hold (#27)"} M[Net#anon$4][0] == M[Net#anon$3][0];
  assert {:msg "Sum.actor(28.13): Network action postcondition might not hold (#28)"} M[Net#anon$4][I[Net#anon$4]] >= M[Net#anon$3][I[Net#anon$3]];
  assert {:msg "Sum.actor(29.13): Network action postcondition might not hold (#29)"} (0 < I[Net#anon$4]) ==> (M[Net#anon$4][I[Net#anon$4]] == (M[Net#anon$4][I[Net#anon$4] - 1] + M[Net#anon$3][I[Net#anon$3]]));
  R[Net#anon$4] := R[Net#anon$4] + 1;
  I := R;
  assert {:msg "Sum.actor(32.15): The network might not preserve the channel invariant (#30)"} I[Net#anon$3] == I[Net#anon$4];
  assert {:msg "Sum.actor(33.15): The network might not preserve the channel invariant (#31)"} (C[Net#anon$3] - I[Net#anon$3]) <= 1;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel anon$3 (#32)"} (C[Net#anon$3] - R[Net#anon$3]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel anon$4 (#33)"} (C[Net#anon$4] - R[Net#anon$4]) == 0;
}

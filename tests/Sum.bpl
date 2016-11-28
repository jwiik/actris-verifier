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

// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

procedure Sum#init#0()
  modifies C, R, M, I;
{
  var x: Chan (int);
  var y: Chan (int);
  var sum: int;
  assume x != y;
  assume R[x] == 0;
  assume C[y] == 0;
  sum := 0;
  assert {:msg "4.13: Initialization might not establish the invariant (#0)"} 0 <= sum;
  assert {:msg "5.13: Initialization might not establish the invariant (#1)"} R[x] == C[y];
  assert {:msg "7.13: Initialization might not establish the invariant (#2)"} (R[x] > 0) ==> (sum == M[y][C[y] - 1]);
  assert {:msg "10.14: Initialization might not establish the invariant (#3)"} (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[y] - 0)) ==> (M[y][i] == (M[y][i - 1] + M[x][i]))
  );
}
procedure Sum#anon$1#1()
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
  assume R[x] == C[y];
  assume (R[x] > 0) ==> (sum == M[y][C[y] - 1]);
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[y] - 0)) ==> (M[y][i] == (M[y][i - 1] + M[x][i]))
  );
  x#0 := M[x][R[x]];
  R[x] := R[x] + 1;
  assume 0 <= x#0;
  sum := sum + x#0;
  assert {:msg "18.13: Action postcondition might not hold (#4)"} x#0 <= sum;
  M[y][C[y]] := sum;
  C[y] := C[y] + 1;
  assert {:msg "4.13: Action at 16.3 might not preserve invariant (#5)"} 0 <= sum;
  assert {:msg "5.13: Action at 16.3 might not preserve invariant (#6)"} R[x] == C[y];
  assert {:msg "7.13: Action at 16.3 might not preserve invariant (#7)"} (R[x] > 0) ==> (sum == M[y][C[y] - 1]);
  assert {:msg "10.14: Action at 16.3 might not preserve invariant (#8)"} (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[y] - 0)) ==> (M[y][i] == (M[y][i - 1] + M[x][i]))
  );
}
procedure Net#init#2()
  modifies C, R, M, I;
{
  var Net#sum: Actor;
  var Net#anon$3: Chan (int);
  var Net#anon$4: Chan (int);
  var AV#sum#sum: int;
  assume Net#anon$3 != Net#anon$4;
  assume 0 <= I[Net#anon$3];
  assume I[Net#anon$3] <= R[Net#anon$3];
  assume R[Net#anon$3] <= C[Net#anon$3];
  assume 0 <= I[Net#anon$4];
  assume I[Net#anon$4] <= R[Net#anon$4];
  assume R[Net#anon$4] <= C[Net#anon$4];
  assume I[Net#anon$4] == R[Net#anon$4];
  assume C[Net#anon$3] == 0;
  assume R[Net#anon$3] == 0;
  assume C[Net#anon$4] == 0;
  assume R[Net#anon$4] == 0;
  assume 0 <= AV#sum#sum;
  assume R[Net#anon$3] == C[Net#anon$4];
  assume (R[Net#anon$3] > 0) ==> (AV#sum#sum == M[Net#anon$4][C[Net#anon$4] - 1]);
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[Net#anon$4] - 0)) ==> (M[Net#anon$4][i] == (M[Net#anon$4][i - 1] + M[Net#anon$3][i]))
  );
  assert {:msg "33.15: Initialization of network 'Net' might not establish the channel invariant (#9)"} I[Net#anon$3] == I[Net#anon$4];
  assert {:msg "34.15: Initialization of network 'Net' might not establish the channel invariant (#10)"} (C[Net#anon$3] - I[Net#anon$3]) <= 1;
  I := R;
  assert {:msg "41.5: The initialization might produce unspecified tokens on channel anon$3 (#11)"} (C[Net#anon$3] - R[Net#anon$3]) == 0;
  assert {:msg "42.5: The initialization might produce unspecified tokens on channel anon$4 (#12)"} (C[Net#anon$4] - R[Net#anon$4]) == 0;
}
procedure Net##Sum#anon$1#3()
  modifies C, R, M, I;
{
  var Net#sum: Actor;
  var Net#anon$3: Chan (int);
  var Net#anon$4: Chan (int);
  var AV#sum#sum: int;
  var x#i: int;
  assume Net#anon$3 != Net#anon$4;
  assume 0 <= I[Net#anon$3];
  assume I[Net#anon$3] <= R[Net#anon$3];
  assume R[Net#anon$3] <= C[Net#anon$3];
  assume 0 <= I[Net#anon$4];
  assume I[Net#anon$4] <= R[Net#anon$4];
  assume R[Net#anon$4] <= C[Net#anon$4];
  assume I[Net#anon$4] == R[Net#anon$4];
  assume I[Net#anon$3] == I[Net#anon$4];
  assume (C[Net#anon$3] - I[Net#anon$3]) <= 1;
  assume 0 <= M[Net#anon$3][I[Net#anon$3]];
  assume 0 <= AV#sum#sum;
  assume R[Net#anon$3] == C[Net#anon$4];
  assume (R[Net#anon$3] > 0) ==> (AV#sum#sum == M[Net#anon$4][C[Net#anon$4] - 1]);
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[Net#anon$4] - 0)) ==> (M[Net#anon$4][i] == (M[Net#anon$4][i - 1] + M[Net#anon$3][i]))
  );
  assume 1 <= (C[Net#anon$3] - R[Net#anon$3]);
  assume 0 <= AV#sum#sum;
  assume R[Net#anon$3] == C[Net#anon$4];
  assume (R[Net#anon$3] > 0) ==> (AV#sum#sum == M[Net#anon$4][C[Net#anon$4] - 1]);
  assume (forall i: int :: 
    ((0 + 1) <= x#i) && (x#i < (C[Net#anon$4] - 0)) ==> (M[Net#anon$4][x#i] == (M[Net#anon$4][x#i - 1] + M[Net#anon$3][x#i]))
  );
  x#i := M[Net#anon$3][R[Net#anon$3]];
  R[Net#anon$3] := R[Net#anon$3] + 1;
  assert {:msg "17.14: Precondition might not hold for instance at 37.5 (#13)"} 0 <= x#i;
  havoc AV#sum#sum;
  M[Net#anon$4][C[Net#anon$4]] := AV#sum#sum;
  C[Net#anon$4] := C[Net#anon$4] + 1;
  assume x#i <= AV#sum#sum;
  assume 0 <= AV#sum#sum;
  assume R[Net#anon$3] == C[Net#anon$4];
  assume (R[Net#anon$3] > 0) ==> (AV#sum#sum == M[Net#anon$4][C[Net#anon$4] - 1]);
  assume (forall i: int :: 
    ((0 + 1) <= x#i) && (x#i < (C[Net#anon$4] - 0)) ==> (M[Net#anon$4][x#i] == (M[Net#anon$4][x#i - 1] + M[Net#anon$3][x#i]))
  );
  assume 0 <= AV#sum#sum;
  assume R[Net#anon$3] == C[Net#anon$4];
  assume (R[Net#anon$3] > 0) ==> (AV#sum#sum == M[Net#anon$4][C[Net#anon$4] - 1]);
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[Net#anon$4] - 0)) ==> (M[Net#anon$4][i] == (M[Net#anon$4][i - 1] + M[Net#anon$3][i]))
  );
  assert {:msg "33.15: Action at 16.3 ('anon$1') for actor instance 'sum' might not preserve the channel invariant (#14)"} I[Net#anon$3] == I[Net#anon$4];
  assert {:msg "34.15: Action at 16.3 ('anon$1') for actor instance 'sum' might not preserve the channel invariant (#15)"} (C[Net#anon$3] - I[Net#anon$3]) <= 1;
}
procedure Net#entry()
  modifies C, R, M, I;
{
  var Net#sum: Actor;
  var Net#anon$3: Chan (int);
  var Net#anon$4: Chan (int);
  var AV#sum#sum: int;
  assume Net#anon$3 != Net#anon$4;
  assume 0 <= I[Net#anon$3];
  assume I[Net#anon$3] <= R[Net#anon$3];
  assume R[Net#anon$3] <= C[Net#anon$3];
  assume 0 <= I[Net#anon$4];
  assume I[Net#anon$4] <= R[Net#anon$4];
  assume R[Net#anon$4] <= C[Net#anon$4];
  assume I[Net#anon$4] == R[Net#anon$4];
  assume C[Net#anon$3] == R[Net#anon$3];
  assume C[Net#anon$4] == R[Net#anon$4];
  assume I[Net#anon$3] == I[Net#anon$4];
  assume (C[Net#anon$3] - I[Net#anon$3]) <= 1;
  assume 0 <= M[Net#anon$3][I[Net#anon$3]];
  assume 0 <= AV#sum#sum;
  assume R[Net#anon$3] == C[Net#anon$4];
  assume (R[Net#anon$3] > 0) ==> (AV#sum#sum == M[Net#anon$4][C[Net#anon$4] - 1]);
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[Net#anon$4] - 0)) ==> (M[Net#anon$4][i] == (M[Net#anon$4][i - 1] + M[Net#anon$3][i]))
  );
  assert {:msg "24.1: Sub-actors in the network might fire without network input. This is not permitted. (#16)"} !(1 <= (C[Net#anon$3] - R[Net#anon$3]));
}
procedure Net#anon$2#input#in#4()
  modifies C, R, M, I;
{
  var Net#sum: Actor;
  var Net#anon$3: Chan (int);
  var Net#anon$4: Chan (int);
  var AV#sum#sum: int;
  assume Net#anon$3 != Net#anon$4;
  assume 0 <= I[Net#anon$3];
  assume I[Net#anon$3] <= R[Net#anon$3];
  assume R[Net#anon$3] <= C[Net#anon$3];
  assume 0 <= I[Net#anon$4];
  assume I[Net#anon$4] <= R[Net#anon$4];
  assume R[Net#anon$4] <= C[Net#anon$4];
  assume I[Net#anon$4] == R[Net#anon$4];
  assume (C[Net#anon$3] - I[Net#anon$3]) < 1;
  assume I[Net#anon$3] == I[Net#anon$4];
  assume (C[Net#anon$3] - I[Net#anon$3]) <= 1;
  assume 0 <= M[Net#anon$3][I[Net#anon$3]];
  assume 0 <= AV#sum#sum;
  assume R[Net#anon$3] == C[Net#anon$4];
  assume (R[Net#anon$3] > 0) ==> (AV#sum#sum == M[Net#anon$4][C[Net#anon$4] - 1]);
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[Net#anon$4] - 0)) ==> (M[Net#anon$4][i] == (M[Net#anon$4][i - 1] + M[Net#anon$3][i]))
  );
  C[Net#anon$3] := C[Net#anon$3] + 1;
  assume 0 <= M[Net#anon$3][I[Net#anon$3]];
  assert {:msg "33.15: Channel invariant might be falsified by network input (#17)"} I[Net#anon$3] == I[Net#anon$4];
  assert {:msg "34.15: Channel invariant might be falsified by network input (#18)"} (C[Net#anon$3] - I[Net#anon$3]) <= 1;
  assert {:msg "27.14: Channel invariant might be falsified by network input (#19)"} 0 <= M[Net#anon$3][I[Net#anon$3]];
}
procedure Net#anon$2#exit#5()
  modifies C, R, M, I;
{
  var Net#sum: Actor;
  var Net#anon$3: Chan (int);
  var Net#anon$4: Chan (int);
  var AV#sum#sum: int;
  assume Net#anon$3 != Net#anon$4;
  assume 0 <= I[Net#anon$3];
  assume I[Net#anon$3] <= R[Net#anon$3];
  assume R[Net#anon$3] <= C[Net#anon$3];
  assume 0 <= I[Net#anon$4];
  assume I[Net#anon$4] <= R[Net#anon$4];
  assume R[Net#anon$4] <= C[Net#anon$4];
  assume I[Net#anon$4] == R[Net#anon$4];
  assume I[Net#anon$3] == I[Net#anon$4];
  assume (C[Net#anon$3] - I[Net#anon$3]) <= 1;
  assume 0 <= M[Net#anon$3][I[Net#anon$3]];
  assume 0 <= AV#sum#sum;
  assume R[Net#anon$3] == C[Net#anon$4];
  assume (R[Net#anon$3] > 0) ==> (AV#sum#sum == M[Net#anon$4][C[Net#anon$4] - 1]);
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[Net#anon$4] - 0)) ==> (M[Net#anon$4][i] == (M[Net#anon$4][i - 1] + M[Net#anon$3][i]))
  );
  assume (C[Net#anon$3] - I[Net#anon$3]) == 1;
  assume 0 <= M[Net#anon$3][I[Net#anon$3]];
  assume !(1 <= (C[Net#anon$3] - R[Net#anon$3]));
  assert {:msg "30.13: Network action postcondition might not hold (#20)"} (0 < I[Net#anon$4]) ==> (M[Net#anon$4][I[Net#anon$4]] == (M[Net#anon$4][I[Net#anon$4] - 1] + M[Net#anon$3][I[Net#anon$3]]));
  R[Net#anon$4] := R[Net#anon$4] + 1;
  I := R;
  assert {:msg "33.15: The network might not preserve the channel invariant (#21)"} I[Net#anon$3] == I[Net#anon$4];
  assert {:msg "34.15: The network might not preserve the channel invariant (#22)"} (C[Net#anon$3] - I[Net#anon$3]) <= 1;
  assert {:msg "26.3: The network might leave unread tokens on channel anon$3 (#23)"} C[Net#anon$3] == R[Net#anon$3];
  assert {:msg "26.3: The network might not produce the specified number of tokens on output out (#24)"} C[Net#anon$4] == R[Net#anon$4];
}

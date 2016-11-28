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

procedure NonDet#init#0()
  modifies C, R, M, I;
{
  var x: Chan (int);
  var y: Chan (int);
  var n: int;
  assume x != y;
  assume R[x] == 0;
  assume C[y] == 0;
  assert {:msg "2.13: Initialization might not establish the invariant (#0)"} R[x] == C[y];
  assert {:msg "3.14: Initialization might not establish the invariant (#1)"} (forall i: int :: 
    (0 <= i) && (i < C[y]) ==> ((M[y][i] == 1) || (M[y][i] == 2))
  );
}
procedure NonDet#anon$0#1()
  modifies C, R, M, I;
{
  var x: Chan (int);
  var y: Chan (int);
  var n: int;
  var x#0: int;
  assume x != y;
  assume 0 <= R[x];
  assume 0 <= C[y];
  assume R[x] == C[y];
  assume (forall i: int :: 
    (0 <= i) && (i < C[y]) ==> ((M[y][i] == 1) || (M[y][i] == 2))
  );
  x#0 := M[x][R[x]];
  R[x] := R[x] + 1;
  havoc n;
  assume (n == 1) || (n == 2);
  assert {:msg "6.13: Action postcondition might not hold (#2)"} (n == 1) || (n == 2);
  M[y][C[y]] := n;
  C[y] := C[y] + 1;
  assert {:msg "2.13: Action at 5.3 might not preserve invariant (#3)"} R[x] == C[y];
  assert {:msg "3.14: Action at 5.3 might not preserve invariant (#4)"} (forall i: int :: 
    (0 <= i) && (i < C[y]) ==> ((M[y][i] == 1) || (M[y][i] == 2))
  );
}
procedure DetMergeUnbalanced#init#2()
  modifies C, R, M, I;
{
  var x: Chan (int);
  var ctrl: Chan (int);
  var y: Chan (int);
  assume (x != ctrl) && (x != y) && (ctrl != y);
  assume R[x] == 0;
  assume R[ctrl] == 0;
  assume C[y] == 0;
  assert {:msg "14.13: Initialization might not establish the invariant (#5)"} C[y] == R[x];
}
procedure DetMergeUnbalanced#a1#3()
  modifies C, R, M, I;
{
  var x: Chan (int);
  var ctrl: Chan (int);
  var y: Chan (int);
  var x#0: int;
  var ctrl#0: int;
  assume (x != ctrl) && (x != y) && (ctrl != y);
  assume 0 <= R[x];
  assume 0 <= R[ctrl];
  assume 0 <= C[y];
  assume C[y] == R[x];
  x#0 := M[x][R[x]];
  R[x] := R[x] + 1;
  ctrl#0 := M[ctrl][R[ctrl]];
  R[ctrl] := R[ctrl] + 1;
  assume ctrl#0 == 1;
  M[y][C[y]] := x#0;
  C[y] := C[y] + 1;
  assert {:msg "14.13: Action at 15.3 might not preserve invariant (#6)"} C[y] == R[x];
}
procedure DetMergeUnbalanced#a2#4()
  modifies C, R, M, I;
{
  var x: Chan (int);
  var ctrl: Chan (int);
  var y: Chan (int);
  var x#0: int;
  var x#1: int;
  var ctrl#0: int;
  var ctrl#1: int;
  assume (x != ctrl) && (x != y) && (ctrl != y);
  assume 0 <= R[x];
  assume 0 <= R[ctrl];
  assume 0 <= C[y];
  assume C[y] == R[x];
  x#0 := M[x][R[x]];
  R[x] := R[x] + 1;
  x#1 := M[x][R[x]];
  R[x] := R[x] + 1;
  ctrl#0 := M[ctrl][R[ctrl]];
  R[ctrl] := R[ctrl] + 1;
  ctrl#1 := M[ctrl][R[ctrl]];
  R[ctrl] := R[ctrl] + 1;
  assume ctrl#0 == 2;
  M[y][C[y]] := x#0;
  C[y] := C[y] + 1;
  M[y][C[y]] := x#1;
  C[y] := C[y] + 1;
  assert {:msg "14.13: Action at 18.3 might not preserve invariant (#7)"} C[y] == R[x];
}
procedure DetMergeUnbalanced##GuardWD#5()
  modifies C, R, M, I;
{
  var x: Chan (int);
  var ctrl: Chan (int);
  var y: Chan (int);
  var x#0: int;
  var ctrl#0: int;
  var x#1: int;
  var ctrl#1: int;
  assume (x != ctrl) && (x != y) && (ctrl != y);
  assert {:msg "13.1: The actions of actor 'DetMergeUnbalanced' might not have mutually exclusive guards (#8)"} !((1 <= (C[x] - R[x])) && (1 <= (C[ctrl] - R[ctrl])) && (ctrl#0 == 1) && (2 <= (C[x] - R[x])) && (2 <= (C[ctrl] - R[ctrl])) && (ctrl#0 == 2));
}
procedure N#init#6()
  modifies C, R, M, I;
{
  var N#nd: Actor;
  var N#dmu: Actor;
  var N#a: Chan (int);
  var N#c: Chan (int);
  var N#d: Chan (int);
  var N#e: Chan (int);
  var AV#nd#n: int;
  assume N#nd != N#dmu;
  assume (N#a != N#c) && (N#a != N#d) && (N#a != N#e) && (N#c != N#d) && (N#c != N#e) && (N#d != N#e);
  assume 0 <= I[N#a];
  assume I[N#a] <= R[N#a];
  assume R[N#a] <= C[N#a];
  assume 0 <= I[N#c];
  assume I[N#c] <= R[N#c];
  assume R[N#c] <= C[N#c];
  assume 0 <= I[N#d];
  assume I[N#d] <= R[N#d];
  assume R[N#d] <= C[N#d];
  assume 0 <= I[N#e];
  assume I[N#e] <= R[N#e];
  assume R[N#e] <= C[N#e];
  assume I[N#e] == R[N#e];
  assume C[N#a] == 0;
  assume R[N#a] == 0;
  assume C[N#c] == 0;
  assume R[N#c] == 0;
  assume C[N#d] == 0;
  assume R[N#d] == 0;
  assume C[N#e] == 0;
  assume R[N#e] == 0;
  assume R[N#c] == C[N#d];
  assume (forall i: int :: 
    (0 <= i) && (i < C[N#d]) ==> ((M[N#d][i] == 1) || (M[N#d][i] == 2))
  );
  assume C[N#e] == R[N#a];
  assert {:msg "27.15: Initialization of network 'N' might not establish the channel invariant (#9)"} I[N#a] == I[N#c];
  assert {:msg "29.15: Initialization of network 'N' might not establish the channel invariant (#10)"} (C[N#c] - I[N#c]) <= 2;
  assert {:msg "30.15: Initialization of network 'N' might not establish the channel invariant (#11)"} (C[N#a] - I[N#a]) <= 2;
  assert {:msg "32.15: Initialization of network 'N' might not establish the channel invariant (#12)"} I[N#d] == I[N#c];
  assert {:msg "33.15: Initialization of network 'N' might not establish the channel invariant (#13)"} (C[N#d] - I[N#d]) == (R[N#c] - I[N#c]);
  assert {:msg "35.15: Initialization of network 'N' might not establish the channel invariant (#14)"} I[N#e] == I[N#d];
  assert {:msg "36.15: Initialization of network 'N' might not establish the channel invariant (#15)"} (C[N#e] - I[N#e]) == (R[N#d] - I[N#d]);
  assert {:msg "38.15: Initialization of network 'N' might not establish the channel invariant (#16)"} I[N#e] == I[N#a];
  assert {:msg "39.15: Initialization of network 'N' might not establish the channel invariant (#17)"} (C[N#e] - I[N#e]) == (R[N#a] - I[N#a]);
  I := R;
  assert {:msg "46.5: The initialization might produce unspecified tokens on channel a (#18)"} (C[N#a] - R[N#a]) == 0;
  assert {:msg "47.5: The initialization might produce unspecified tokens on channel c (#19)"} (C[N#c] - R[N#c]) == 0;
  assert {:msg "48.5: The initialization might produce unspecified tokens on channel d (#20)"} (C[N#d] - R[N#d]) == 0;
  assert {:msg "49.5: The initialization might produce unspecified tokens on channel e (#21)"} (C[N#e] - R[N#e]) == 0;
}
procedure N##NonDet#anon$0#7()
  modifies C, R, M, I;
{
  var N#nd: Actor;
  var N#dmu: Actor;
  var N#a: Chan (int);
  var N#c: Chan (int);
  var N#d: Chan (int);
  var N#e: Chan (int);
  var AV#nd#n: int;
  var x#i: int;
  assume N#nd != N#dmu;
  assume (N#a != N#c) && (N#a != N#d) && (N#a != N#e) && (N#c != N#d) && (N#c != N#e) && (N#d != N#e);
  assume 0 <= I[N#a];
  assume I[N#a] <= R[N#a];
  assume R[N#a] <= C[N#a];
  assume 0 <= I[N#c];
  assume I[N#c] <= R[N#c];
  assume R[N#c] <= C[N#c];
  assume 0 <= I[N#d];
  assume I[N#d] <= R[N#d];
  assume R[N#d] <= C[N#d];
  assume 0 <= I[N#e];
  assume I[N#e] <= R[N#e];
  assume R[N#e] <= C[N#e];
  assume I[N#e] == R[N#e];
  assume I[N#a] == I[N#c];
  assume (C[N#c] - I[N#c]) <= 2;
  assume (C[N#a] - I[N#a]) <= 2;
  assume I[N#d] == I[N#c];
  assume (C[N#d] - I[N#d]) == (R[N#c] - I[N#c]);
  assume I[N#e] == I[N#d];
  assume (C[N#e] - I[N#e]) == (R[N#d] - I[N#d]);
  assume I[N#e] == I[N#a];
  assume (C[N#e] - I[N#e]) == (R[N#a] - I[N#a]);
  assume R[N#c] == C[N#d];
  assume (forall i: int :: 
    (0 <= i) && (i < C[N#d]) ==> ((M[N#d][i] == 1) || (M[N#d][i] == 2))
  );
  assume C[N#e] == R[N#a];
  assume 1 <= (C[N#c] - R[N#c]);
  assume R[N#c] == C[N#d];
  assume (forall i: int :: 
    (0 <= x#i) && (x#i < C[N#d]) ==> ((M[N#d][x#i] == 1) || (M[N#d][x#i] == 2))
  );
  x#i := M[N#c][R[N#c]];
  R[N#c] := R[N#c] + 1;
  M[N#d][C[N#d]] := AV#nd#n;
  C[N#d] := C[N#d] + 1;
  assume (AV#nd#n == 1) || (AV#nd#n == 2);
  assume R[N#c] == C[N#d];
  assume (forall i: int :: 
    (0 <= x#i) && (x#i < C[N#d]) ==> ((M[N#d][x#i] == 1) || (M[N#d][x#i] == 2))
  );
  assume R[N#c] == C[N#d];
  assume (forall i: int :: 
    (0 <= i) && (i < C[N#d]) ==> ((M[N#d][i] == 1) || (M[N#d][i] == 2))
  );
  assume C[N#e] == R[N#a];
  assert {:msg "27.15: Action at 5.3 ('anon$0') for actor instance 'nd' might not preserve the channel invariant (#22)"} I[N#a] == I[N#c];
  assert {:msg "29.15: Action at 5.3 ('anon$0') for actor instance 'nd' might not preserve the channel invariant (#23)"} (C[N#c] - I[N#c]) <= 2;
  assert {:msg "30.15: Action at 5.3 ('anon$0') for actor instance 'nd' might not preserve the channel invariant (#24)"} (C[N#a] - I[N#a]) <= 2;
  assert {:msg "32.15: Action at 5.3 ('anon$0') for actor instance 'nd' might not preserve the channel invariant (#25)"} I[N#d] == I[N#c];
  assert {:msg "33.15: Action at 5.3 ('anon$0') for actor instance 'nd' might not preserve the channel invariant (#26)"} (C[N#d] - I[N#d]) == (R[N#c] - I[N#c]);
  assert {:msg "35.15: Action at 5.3 ('anon$0') for actor instance 'nd' might not preserve the channel invariant (#27)"} I[N#e] == I[N#d];
  assert {:msg "36.15: Action at 5.3 ('anon$0') for actor instance 'nd' might not preserve the channel invariant (#28)"} (C[N#e] - I[N#e]) == (R[N#d] - I[N#d]);
  assert {:msg "38.15: Action at 5.3 ('anon$0') for actor instance 'nd' might not preserve the channel invariant (#29)"} I[N#e] == I[N#a];
  assert {:msg "39.15: Action at 5.3 ('anon$0') for actor instance 'nd' might not preserve the channel invariant (#30)"} (C[N#e] - I[N#e]) == (R[N#a] - I[N#a]);
}
procedure N##DetMergeUnbalanced#a1#8()
  modifies C, R, M, I;
{
  var N#nd: Actor;
  var N#dmu: Actor;
  var N#a: Chan (int);
  var N#c: Chan (int);
  var N#d: Chan (int);
  var N#e: Chan (int);
  var AV#nd#n: int;
  var x#i: int;
  var ctrl#c: int;
  assume N#nd != N#dmu;
  assume (N#a != N#c) && (N#a != N#d) && (N#a != N#e) && (N#c != N#d) && (N#c != N#e) && (N#d != N#e);
  assume 0 <= I[N#a];
  assume I[N#a] <= R[N#a];
  assume R[N#a] <= C[N#a];
  assume 0 <= I[N#c];
  assume I[N#c] <= R[N#c];
  assume R[N#c] <= C[N#c];
  assume 0 <= I[N#d];
  assume I[N#d] <= R[N#d];
  assume R[N#d] <= C[N#d];
  assume 0 <= I[N#e];
  assume I[N#e] <= R[N#e];
  assume R[N#e] <= C[N#e];
  assume I[N#e] == R[N#e];
  assume I[N#a] == I[N#c];
  assume (C[N#c] - I[N#c]) <= 2;
  assume (C[N#a] - I[N#a]) <= 2;
  assume I[N#d] == I[N#c];
  assume (C[N#d] - I[N#d]) == (R[N#c] - I[N#c]);
  assume I[N#e] == I[N#d];
  assume (C[N#e] - I[N#e]) == (R[N#d] - I[N#d]);
  assume I[N#e] == I[N#a];
  assume (C[N#e] - I[N#e]) == (R[N#a] - I[N#a]);
  assume R[N#c] == C[N#d];
  assume (forall i: int :: 
    (0 <= i) && (i < C[N#d]) ==> ((M[N#d][i] == 1) || (M[N#d][i] == 2))
  );
  assume C[N#e] == R[N#a];
  assume (1 <= (C[N#a] - R[N#a])) && (1 <= (C[N#d] - R[N#d])) && (M[N#d][R[N#d]] == 1);
  assume C[N#e] == R[N#a];
  x#i := M[N#a][R[N#a]];
  R[N#a] := R[N#a] + 1;
  ctrl#c := M[N#d][R[N#d]];
  R[N#d] := R[N#d] + 1;
  M[N#e][C[N#e]] := x#i;
  C[N#e] := C[N#e] + 1;
  assume C[N#e] == R[N#a];
  assume R[N#c] == C[N#d];
  assume (forall i: int :: 
    (0 <= i) && (i < C[N#d]) ==> ((M[N#d][i] == 1) || (M[N#d][i] == 2))
  );
  assume C[N#e] == R[N#a];
  assert {:msg "27.15: Action at 15.3 ('a1') for actor instance 'dmu' might not preserve the channel invariant (#31)"} I[N#a] == I[N#c];
  assert {:msg "29.15: Action at 15.3 ('a1') for actor instance 'dmu' might not preserve the channel invariant (#32)"} (C[N#c] - I[N#c]) <= 2;
  assert {:msg "30.15: Action at 15.3 ('a1') for actor instance 'dmu' might not preserve the channel invariant (#33)"} (C[N#a] - I[N#a]) <= 2;
  assert {:msg "32.15: Action at 15.3 ('a1') for actor instance 'dmu' might not preserve the channel invariant (#34)"} I[N#d] == I[N#c];
  assert {:msg "33.15: Action at 15.3 ('a1') for actor instance 'dmu' might not preserve the channel invariant (#35)"} (C[N#d] - I[N#d]) == (R[N#c] - I[N#c]);
  assert {:msg "35.15: Action at 15.3 ('a1') for actor instance 'dmu' might not preserve the channel invariant (#36)"} I[N#e] == I[N#d];
  assert {:msg "36.15: Action at 15.3 ('a1') for actor instance 'dmu' might not preserve the channel invariant (#37)"} (C[N#e] - I[N#e]) == (R[N#d] - I[N#d]);
  assert {:msg "38.15: Action at 15.3 ('a1') for actor instance 'dmu' might not preserve the channel invariant (#38)"} I[N#e] == I[N#a];
  assert {:msg "39.15: Action at 15.3 ('a1') for actor instance 'dmu' might not preserve the channel invariant (#39)"} (C[N#e] - I[N#e]) == (R[N#a] - I[N#a]);
}
procedure N##DetMergeUnbalanced#a2#9()
  modifies C, R, M, I;
{
  var N#nd: Actor;
  var N#dmu: Actor;
  var N#a: Chan (int);
  var N#c: Chan (int);
  var N#d: Chan (int);
  var N#e: Chan (int);
  var AV#nd#n: int;
  var x#i: int;
  var x#j: int;
  var ctrl#c1: int;
  var ctrl#c2: int;
  assume N#nd != N#dmu;
  assume (N#a != N#c) && (N#a != N#d) && (N#a != N#e) && (N#c != N#d) && (N#c != N#e) && (N#d != N#e);
  assume 0 <= I[N#a];
  assume I[N#a] <= R[N#a];
  assume R[N#a] <= C[N#a];
  assume 0 <= I[N#c];
  assume I[N#c] <= R[N#c];
  assume R[N#c] <= C[N#c];
  assume 0 <= I[N#d];
  assume I[N#d] <= R[N#d];
  assume R[N#d] <= C[N#d];
  assume 0 <= I[N#e];
  assume I[N#e] <= R[N#e];
  assume R[N#e] <= C[N#e];
  assume I[N#e] == R[N#e];
  assume I[N#a] == I[N#c];
  assume (C[N#c] - I[N#c]) <= 2;
  assume (C[N#a] - I[N#a]) <= 2;
  assume I[N#d] == I[N#c];
  assume (C[N#d] - I[N#d]) == (R[N#c] - I[N#c]);
  assume I[N#e] == I[N#d];
  assume (C[N#e] - I[N#e]) == (R[N#d] - I[N#d]);
  assume I[N#e] == I[N#a];
  assume (C[N#e] - I[N#e]) == (R[N#a] - I[N#a]);
  assume R[N#c] == C[N#d];
  assume (forall i: int :: 
    (0 <= i) && (i < C[N#d]) ==> ((M[N#d][i] == 1) || (M[N#d][i] == 2))
  );
  assume C[N#e] == R[N#a];
  assume (2 <= (C[N#a] - R[N#a])) && (2 <= (C[N#d] - R[N#d])) && (M[N#d][R[N#d]] == 2);
  assume C[N#e] == R[N#a];
  x#i := M[N#a][R[N#a]];
  R[N#a] := R[N#a] + 1;
  x#j := M[N#a][R[N#a]];
  R[N#a] := R[N#a] + 1;
  ctrl#c1 := M[N#d][R[N#d]];
  R[N#d] := R[N#d] + 1;
  ctrl#c2 := M[N#d][R[N#d]];
  R[N#d] := R[N#d] + 1;
  M[N#e][C[N#e]] := x#i;
  C[N#e] := C[N#e] + 1;
  M[N#e][C[N#e]] := x#j;
  C[N#e] := C[N#e] + 1;
  assume C[N#e] == R[N#a];
  assume R[N#c] == C[N#d];
  assume (forall i: int :: 
    (0 <= i) && (i < C[N#d]) ==> ((M[N#d][i] == 1) || (M[N#d][i] == 2))
  );
  assume C[N#e] == R[N#a];
  assert {:msg "27.15: Action at 18.3 ('a2') for actor instance 'dmu' might not preserve the channel invariant (#40)"} I[N#a] == I[N#c];
  assert {:msg "29.15: Action at 18.3 ('a2') for actor instance 'dmu' might not preserve the channel invariant (#41)"} (C[N#c] - I[N#c]) <= 2;
  assert {:msg "30.15: Action at 18.3 ('a2') for actor instance 'dmu' might not preserve the channel invariant (#42)"} (C[N#a] - I[N#a]) <= 2;
  assert {:msg "32.15: Action at 18.3 ('a2') for actor instance 'dmu' might not preserve the channel invariant (#43)"} I[N#d] == I[N#c];
  assert {:msg "33.15: Action at 18.3 ('a2') for actor instance 'dmu' might not preserve the channel invariant (#44)"} (C[N#d] - I[N#d]) == (R[N#c] - I[N#c]);
  assert {:msg "35.15: Action at 18.3 ('a2') for actor instance 'dmu' might not preserve the channel invariant (#45)"} I[N#e] == I[N#d];
  assert {:msg "36.15: Action at 18.3 ('a2') for actor instance 'dmu' might not preserve the channel invariant (#46)"} (C[N#e] - I[N#e]) == (R[N#d] - I[N#d]);
  assert {:msg "38.15: Action at 18.3 ('a2') for actor instance 'dmu' might not preserve the channel invariant (#47)"} I[N#e] == I[N#a];
  assert {:msg "39.15: Action at 18.3 ('a2') for actor instance 'dmu' might not preserve the channel invariant (#48)"} (C[N#e] - I[N#e]) == (R[N#a] - I[N#a]);
}
procedure N#entry()
  modifies C, R, M, I;
{
  var N#nd: Actor;
  var N#dmu: Actor;
  var N#a: Chan (int);
  var N#c: Chan (int);
  var N#d: Chan (int);
  var N#e: Chan (int);
  var AV#nd#n: int;
  assume N#nd != N#dmu;
  assume (N#a != N#c) && (N#a != N#d) && (N#a != N#e) && (N#c != N#d) && (N#c != N#e) && (N#d != N#e);
  assume 0 <= I[N#a];
  assume I[N#a] <= R[N#a];
  assume R[N#a] <= C[N#a];
  assume 0 <= I[N#c];
  assume I[N#c] <= R[N#c];
  assume R[N#c] <= C[N#c];
  assume 0 <= I[N#d];
  assume I[N#d] <= R[N#d];
  assume R[N#d] <= C[N#d];
  assume 0 <= I[N#e];
  assume I[N#e] <= R[N#e];
  assume R[N#e] <= C[N#e];
  assume I[N#e] == R[N#e];
  assume C[N#a] == R[N#a];
  assume C[N#c] == R[N#c];
  assume C[N#d] == R[N#d];
  assume C[N#e] == R[N#e];
  assume I[N#a] == I[N#c];
  assume (C[N#c] - I[N#c]) <= 2;
  assume (C[N#a] - I[N#a]) <= 2;
  assume I[N#d] == I[N#c];
  assume (C[N#d] - I[N#d]) == (R[N#c] - I[N#c]);
  assume I[N#e] == I[N#d];
  assume (C[N#e] - I[N#e]) == (R[N#d] - I[N#d]);
  assume I[N#e] == I[N#a];
  assume (C[N#e] - I[N#e]) == (R[N#a] - I[N#a]);
  assume R[N#c] == C[N#d];
  assume (forall i: int :: 
    (0 <= i) && (i < C[N#d]) ==> ((M[N#d][i] == 1) || (M[N#d][i] == 2))
  );
  assume C[N#e] == R[N#a];
  assert {:msg "23.1: Sub-actors in the network might fire without network input. This is not permitted. (#49)"} !(1 <= (C[N#c] - R[N#c]));
  assert {:msg "23.1: Sub-actors in the network might fire without network input. This is not permitted. (#50)"} !((1 <= (C[N#a] - R[N#a])) && (1 <= (C[N#d] - R[N#d])) && (M[N#d][R[N#d]] == 1));
  assert {:msg "23.1: Sub-actors in the network might fire without network input. This is not permitted. (#51)"} !((2 <= (C[N#a] - R[N#a])) && (2 <= (C[N#d] - R[N#d])) && (M[N#d][R[N#d]] == 2));
}
procedure N#anon$1#input#x#10()
  modifies C, R, M, I;
{
  var N#nd: Actor;
  var N#dmu: Actor;
  var N#a: Chan (int);
  var N#c: Chan (int);
  var N#d: Chan (int);
  var N#e: Chan (int);
  var AV#nd#n: int;
  assume N#nd != N#dmu;
  assume (N#a != N#c) && (N#a != N#d) && (N#a != N#e) && (N#c != N#d) && (N#c != N#e) && (N#d != N#e);
  assume 0 <= I[N#a];
  assume I[N#a] <= R[N#a];
  assume R[N#a] <= C[N#a];
  assume 0 <= I[N#c];
  assume I[N#c] <= R[N#c];
  assume R[N#c] <= C[N#c];
  assume 0 <= I[N#d];
  assume I[N#d] <= R[N#d];
  assume R[N#d] <= C[N#d];
  assume 0 <= I[N#e];
  assume I[N#e] <= R[N#e];
  assume R[N#e] <= C[N#e];
  assume I[N#e] == R[N#e];
  assume (C[N#a] - I[N#a]) < 2;
  assume I[N#a] == I[N#c];
  assume (C[N#c] - I[N#c]) <= 2;
  assume (C[N#a] - I[N#a]) <= 2;
  assume I[N#d] == I[N#c];
  assume (C[N#d] - I[N#d]) == (R[N#c] - I[N#c]);
  assume I[N#e] == I[N#d];
  assume (C[N#e] - I[N#e]) == (R[N#d] - I[N#d]);
  assume I[N#e] == I[N#a];
  assume (C[N#e] - I[N#e]) == (R[N#a] - I[N#a]);
  assume R[N#c] == C[N#d];
  assume (forall i: int :: 
    (0 <= i) && (i < C[N#d]) ==> ((M[N#d][i] == 1) || (M[N#d][i] == 2))
  );
  assume C[N#e] == R[N#a];
  C[N#a] := C[N#a] + 1;
  assert {:msg "27.15: Channel invariant might be falsified by network input (#52)"} I[N#a] == I[N#c];
  assert {:msg "29.15: Channel invariant might be falsified by network input (#53)"} (C[N#c] - I[N#c]) <= 2;
  assert {:msg "30.15: Channel invariant might be falsified by network input (#54)"} (C[N#a] - I[N#a]) <= 2;
  assert {:msg "32.15: Channel invariant might be falsified by network input (#55)"} I[N#d] == I[N#c];
  assert {:msg "33.15: Channel invariant might be falsified by network input (#56)"} (C[N#d] - I[N#d]) == (R[N#c] - I[N#c]);
  assert {:msg "35.15: Channel invariant might be falsified by network input (#57)"} I[N#e] == I[N#d];
  assert {:msg "36.15: Channel invariant might be falsified by network input (#58)"} (C[N#e] - I[N#e]) == (R[N#d] - I[N#d]);
  assert {:msg "38.15: Channel invariant might be falsified by network input (#59)"} I[N#e] == I[N#a];
  assert {:msg "39.15: Channel invariant might be falsified by network input (#60)"} (C[N#e] - I[N#e]) == (R[N#a] - I[N#a]);
}
procedure N#anon$1#input#ctrl#11()
  modifies C, R, M, I;
{
  var N#nd: Actor;
  var N#dmu: Actor;
  var N#a: Chan (int);
  var N#c: Chan (int);
  var N#d: Chan (int);
  var N#e: Chan (int);
  var AV#nd#n: int;
  assume N#nd != N#dmu;
  assume (N#a != N#c) && (N#a != N#d) && (N#a != N#e) && (N#c != N#d) && (N#c != N#e) && (N#d != N#e);
  assume 0 <= I[N#a];
  assume I[N#a] <= R[N#a];
  assume R[N#a] <= C[N#a];
  assume 0 <= I[N#c];
  assume I[N#c] <= R[N#c];
  assume R[N#c] <= C[N#c];
  assume 0 <= I[N#d];
  assume I[N#d] <= R[N#d];
  assume R[N#d] <= C[N#d];
  assume 0 <= I[N#e];
  assume I[N#e] <= R[N#e];
  assume R[N#e] <= C[N#e];
  assume I[N#e] == R[N#e];
  assume (C[N#c] - I[N#c]) < 2;
  assume I[N#a] == I[N#c];
  assume (C[N#c] - I[N#c]) <= 2;
  assume (C[N#a] - I[N#a]) <= 2;
  assume I[N#d] == I[N#c];
  assume (C[N#d] - I[N#d]) == (R[N#c] - I[N#c]);
  assume I[N#e] == I[N#d];
  assume (C[N#e] - I[N#e]) == (R[N#d] - I[N#d]);
  assume I[N#e] == I[N#a];
  assume (C[N#e] - I[N#e]) == (R[N#a] - I[N#a]);
  assume R[N#c] == C[N#d];
  assume (forall i: int :: 
    (0 <= i) && (i < C[N#d]) ==> ((M[N#d][i] == 1) || (M[N#d][i] == 2))
  );
  assume C[N#e] == R[N#a];
  C[N#c] := C[N#c] + 1;
  assert {:msg "27.15: Channel invariant might be falsified by network input (#61)"} I[N#a] == I[N#c];
  assert {:msg "29.15: Channel invariant might be falsified by network input (#62)"} (C[N#c] - I[N#c]) <= 2;
  assert {:msg "30.15: Channel invariant might be falsified by network input (#63)"} (C[N#a] - I[N#a]) <= 2;
  assert {:msg "32.15: Channel invariant might be falsified by network input (#64)"} I[N#d] == I[N#c];
  assert {:msg "33.15: Channel invariant might be falsified by network input (#65)"} (C[N#d] - I[N#d]) == (R[N#c] - I[N#c]);
  assert {:msg "35.15: Channel invariant might be falsified by network input (#66)"} I[N#e] == I[N#d];
  assert {:msg "36.15: Channel invariant might be falsified by network input (#67)"} (C[N#e] - I[N#e]) == (R[N#d] - I[N#d]);
  assert {:msg "38.15: Channel invariant might be falsified by network input (#68)"} I[N#e] == I[N#a];
  assert {:msg "39.15: Channel invariant might be falsified by network input (#69)"} (C[N#e] - I[N#e]) == (R[N#a] - I[N#a]);
}
procedure N#anon$1#exit#12()
  modifies C, R, M, I;
{
  var N#nd: Actor;
  var N#dmu: Actor;
  var N#a: Chan (int);
  var N#c: Chan (int);
  var N#d: Chan (int);
  var N#e: Chan (int);
  var AV#nd#n: int;
  assume N#nd != N#dmu;
  assume (N#a != N#c) && (N#a != N#d) && (N#a != N#e) && (N#c != N#d) && (N#c != N#e) && (N#d != N#e);
  assume 0 <= I[N#a];
  assume I[N#a] <= R[N#a];
  assume R[N#a] <= C[N#a];
  assume 0 <= I[N#c];
  assume I[N#c] <= R[N#c];
  assume R[N#c] <= C[N#c];
  assume 0 <= I[N#d];
  assume I[N#d] <= R[N#d];
  assume R[N#d] <= C[N#d];
  assume 0 <= I[N#e];
  assume I[N#e] <= R[N#e];
  assume R[N#e] <= C[N#e];
  assume I[N#e] == R[N#e];
  assume I[N#a] == I[N#c];
  assume (C[N#c] - I[N#c]) <= 2;
  assume (C[N#a] - I[N#a]) <= 2;
  assume I[N#d] == I[N#c];
  assume (C[N#d] - I[N#d]) == (R[N#c] - I[N#c]);
  assume I[N#e] == I[N#d];
  assume (C[N#e] - I[N#e]) == (R[N#d] - I[N#d]);
  assume I[N#e] == I[N#a];
  assume (C[N#e] - I[N#e]) == (R[N#a] - I[N#a]);
  assume R[N#c] == C[N#d];
  assume (forall i: int :: 
    (0 <= i) && (i < C[N#d]) ==> ((M[N#d][i] == 1) || (M[N#d][i] == 2))
  );
  assume C[N#e] == R[N#a];
  assume (C[N#a] - I[N#a]) == 2;
  assume (C[N#c] - I[N#c]) == 2;
  assume !(1 <= (C[N#c] - R[N#c]));
  assume !((1 <= (C[N#a] - R[N#a])) && (1 <= (C[N#d] - R[N#d])) && (M[N#d][R[N#d]] == 1));
  assume !((2 <= (C[N#a] - R[N#a])) && (2 <= (C[N#d] - R[N#d])) && (M[N#d][R[N#d]] == 2));
  R[N#e] := R[N#e] + 2;
  I := R;
  assert {:msg "27.15: The network might not preserve the channel invariant (#70)"} I[N#a] == I[N#c];
  assert {:msg "29.15: The network might not preserve the channel invariant (#71)"} (C[N#c] - I[N#c]) <= 2;
  assert {:msg "30.15: The network might not preserve the channel invariant (#72)"} (C[N#a] - I[N#a]) <= 2;
  assert {:msg "32.15: The network might not preserve the channel invariant (#73)"} I[N#d] == I[N#c];
  assert {:msg "33.15: The network might not preserve the channel invariant (#74)"} (C[N#d] - I[N#d]) == (R[N#c] - I[N#c]);
  assert {:msg "35.15: The network might not preserve the channel invariant (#75)"} I[N#e] == I[N#d];
  assert {:msg "36.15: The network might not preserve the channel invariant (#76)"} (C[N#e] - I[N#e]) == (R[N#d] - I[N#d]);
  assert {:msg "38.15: The network might not preserve the channel invariant (#77)"} I[N#e] == I[N#a];
  assert {:msg "39.15: The network might not preserve the channel invariant (#78)"} (C[N#e] - I[N#e]) == (R[N#a] - I[N#a]);
  assert {:msg "25.3: The network might leave unread tokens on channel a (#79)"} C[N#a] == R[N#a];
  assert {:msg "25.3: The network might leave unread tokens on channel c (#80)"} C[N#c] == R[N#c];
  assert {:msg "25.3: The network might leave unread tokens on channel d (#81)"} C[N#d] == R[N#d];
  assert {:msg "25.3: The network might not produce the specified number of tokens on output y (#82)"} C[N#e] == R[N#e];
}

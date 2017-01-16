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

// -- Sequence numbering for FT ----------------------------------
var SqnCh: <a>[Chan a][int]int;
var SqnAct: [Actor]int;

// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

procedure Adjudicator#init#0()
  modifies C, R, M, I, SqnCh, SqnAct;
{
  var x1: Chan (int);
  var x2: Chan (int);
  var y: Chan (int);
  var c: int;
  assume (x1 != x2) && (x1 != y) && (x2 != y);
  assume R[x1] == 0;
  assume R[x2] == 0;
  assume C[y] == 0;
  SqnAct[this#] := 0;
  c := 0;
  assert {:msg "3.20: Initialization might not establish the invariant (#0)"} C[y] == R[x2];
  assert {:msg "4.20: Initialization might not establish the invariant (#1)"} R[x1] <= R[x2];
  assert {:msg "6.13: Initialization might not establish the invariant (#2)"} R[x2] == c;
  assert {:msg "7.14: Initialization might not establish the invariant (#3)"} (forall i: int :: 
    (0 <= i) && (i < R[x2]) ==> (SqnCh[x2][i] == i)
  );
  assert {:msg "8.14: Initialization might not establish the invariant (#4)"} (forall i: int :: 
    (0 <= i) && (i < C[y]) ==> (SqnCh[y][i] == i)
  );
}
procedure Adjudicator#normal#1()
  modifies C, R, M, I, SqnCh, SqnAct;
{
  var x1: Chan (int);
  var x2: Chan (int);
  var y: Chan (int);
  var c: int;
  var x1#0: int;
  var x1#0#sqn: int;
  var x2#0: int;
  var x2#0#sqn: int;
  assume (x1 != x2) && (x1 != y) && (x2 != y);
  assume 0 <= R[x1];
  assume 0 <= R[x2];
  assume 0 <= C[y];
  assume C[y] == R[x2];
  assume R[x1] <= R[x2];
  assume R[x2] == c;
  assume (forall i: int :: 
    (0 <= i) && (i < R[x2]) ==> (SqnCh[x2][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[y]) ==> (SqnCh[y][i] == i)
  );
  x1#0 := M[x1][R[x1]];
  x1#0#sqn := SqnCh[x1][R[x1]];
  R[x1] := R[x1] + 1;
  x2#0 := M[x2][R[x2]];
  x2#0#sqn := SqnCh[x2][R[x2]];
  R[x2] := R[x2] + 1;
  assume !((1 <= (C[x2] - R[x2])) && (x2#0#sqn == c));
  assume !((1 <= (C[x1] - R[x1])) && (x1#0#sqn < c));
  assume (x1#0#sqn == x2#0#sqn) && (x1#0#sqn == c);
  c := c + 1;
  M[y][C[y]] := x1#0;
  SqnCh[y][C[y]] := SqnAct[this#];
  C[y] := C[y] + 1;
  SqnAct[this#] := SqnAct[this#] + 1;
  assert {:msg "3.20: Action at 12.3 might not preserve invariant (#5)"} C[y] == R[x2];
  assert {:msg "4.20: Action at 12.3 might not preserve invariant (#6)"} R[x1] <= R[x2];
  assert {:msg "6.13: Action at 12.3 might not preserve invariant (#7)"} R[x2] == c;
  assert {:msg "7.14: Action at 12.3 might not preserve invariant (#8)"} (forall i: int :: 
    (0 <= i) && (i < R[x2]) ==> (SqnCh[x2][i] == i)
  );
  assert {:msg "8.14: Action at 12.3 might not preserve invariant (#9)"} (forall i: int :: 
    (0 <= i) && (i < C[y]) ==> (SqnCh[y][i] == i)
  );
}
procedure Adjudicator#timeout#2()
  modifies C, R, M, I, SqnCh, SqnAct;
{
  var x1: Chan (int);
  var x2: Chan (int);
  var y: Chan (int);
  var c: int;
  var x1#0: int;
  var x1#0#sqn: int;
  var x2#0: int;
  var x2#0#sqn: int;
  assume (x1 != x2) && (x1 != y) && (x2 != y);
  assume 0 <= R[x1];
  assume 0 <= R[x2];
  assume 0 <= C[y];
  assume C[y] == R[x2];
  assume R[x1] <= R[x2];
  assume R[x2] == c;
  assume (forall i: int :: 
    (0 <= i) && (i < R[x2]) ==> (SqnCh[x2][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[y]) ==> (SqnCh[y][i] == i)
  );
  x2#0 := M[x2][R[x2]];
  x2#0#sqn := SqnCh[x2][R[x2]];
  R[x2] := R[x2] + 1;
  assume !((1 <= (C[x1] - R[x1])) && (x1#0#sqn < c));
  assume x2#0#sqn == c;
  c := c + 1;
  M[y][C[y]] := x2#0;
  SqnCh[y][C[y]] := SqnAct[this#];
  C[y] := C[y] + 1;
  SqnAct[this#] := SqnAct[this#] + 1;
  assert {:msg "3.20: Action at 17.3 might not preserve invariant (#10)"} C[y] == R[x2];
  assert {:msg "4.20: Action at 17.3 might not preserve invariant (#11)"} R[x1] <= R[x2];
  assert {:msg "6.13: Action at 17.3 might not preserve invariant (#12)"} R[x2] == c;
  assert {:msg "7.14: Action at 17.3 might not preserve invariant (#13)"} (forall i: int :: 
    (0 <= i) && (i < R[x2]) ==> (SqnCh[x2][i] == i)
  );
  assert {:msg "8.14: Action at 17.3 might not preserve invariant (#14)"} (forall i: int :: 
    (0 <= i) && (i < C[y]) ==> (SqnCh[y][i] == i)
  );
}
procedure Adjudicator#readoff#3()
  modifies C, R, M, I, SqnCh, SqnAct;
{
  var x1: Chan (int);
  var x2: Chan (int);
  var y: Chan (int);
  var c: int;
  var x1#0: int;
  var x1#0#sqn: int;
  var x2#0: int;
  var x2#0#sqn: int;
  assume (x1 != x2) && (x1 != y) && (x2 != y);
  assume 0 <= R[x1];
  assume 0 <= R[x2];
  assume 0 <= C[y];
  assume C[y] == R[x2];
  assume R[x1] <= R[x2];
  assume R[x2] == c;
  assume (forall i: int :: 
    (0 <= i) && (i < R[x2]) ==> (SqnCh[x2][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[y]) ==> (SqnCh[y][i] == i)
  );
  x1#0 := M[x1][R[x1]];
  x1#0#sqn := SqnCh[x1][R[x1]];
  R[x1] := R[x1] + 1;
  assume R[x1] < R[x2];
  assume x1#0#sqn < c;
  SqnAct[this#] := SqnAct[this#] + 1;
  assert {:msg "3.20: Action at 22.3 might not preserve invariant (#15)"} C[y] == R[x2];
  assert {:msg "4.20: Action at 22.3 might not preserve invariant (#16)"} R[x1] <= R[x2];
  assert {:msg "6.13: Action at 22.3 might not preserve invariant (#17)"} R[x2] == c;
  assert {:msg "7.14: Action at 22.3 might not preserve invariant (#18)"} (forall i: int :: 
    (0 <= i) && (i < R[x2]) ==> (SqnCh[x2][i] == i)
  );
  assert {:msg "8.14: Action at 22.3 might not preserve invariant (#19)"} (forall i: int :: 
    (0 <= i) && (i < C[y]) ==> (SqnCh[y][i] == i)
  );
}
procedure Adjudicator##GuardWD#4()
  modifies C, R, M, I, SqnCh, SqnAct;
{
  var x1: Chan (int);
  var x2: Chan (int);
  var y: Chan (int);
  var c: int;
  var x1#0: int;
  var x1#0#sqn: int;
  var x2#0: int;
  var x2#0#sqn: int;
  assume (x1 != x2) && (x1 != y) && (x2 != y);
  assert {:msg "1.1: The actions 'normal' and 'timeout' of actor 'Adjudicator' might not have mutually exclusive guards (#20)"} !(true && (!((1 <= (C[x2] - R[x2])) && (x2#0#sqn == c))) && (!((1 <= (C[x1] - R[x1])) && (x1#0#sqn < c))) && (1 <= (C[x1] - R[x1])) && (1 <= (C[x2] - R[x2])) && (x1#0#sqn == x2#0#sqn) && (x1#0#sqn == c) && true && (!((1 <= (C[x1] - R[x1])) && (x1#0#sqn < c))) && (1 <= (C[x2] - R[x2])) && (x2#0#sqn == c));
  assert {:msg "1.1: The actions 'normal' and 'readoff' of actor 'Adjudicator' might not have mutually exclusive guards (#21)"} !(true && (!((1 <= (C[x2] - R[x2])) && (x2#0#sqn == c))) && (!((1 <= (C[x1] - R[x1])) && (x1#0#sqn < c))) && (1 <= (C[x1] - R[x1])) && (1 <= (C[x2] - R[x2])) && (x1#0#sqn == x2#0#sqn) && (x1#0#sqn == c) && true && (1 <= (C[x1] - R[x1])) && (x1#0#sqn < c));
  assert {:msg "1.1: The actions 'timeout' and 'readoff' of actor 'Adjudicator' might not have mutually exclusive guards (#22)"} !(true && (!((1 <= (C[x1] - R[x1])) && (x1#0#sqn < c))) && (1 <= (C[x2] - R[x2])) && (x2#0#sqn == c) && true && (1 <= (C[x1] - R[x1])) && (x1#0#sqn < c));
}

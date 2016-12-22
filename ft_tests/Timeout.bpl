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

// -- Sequence numbering for FT ----------------------------------
var SqnCh: <a>[Chan a][int]int;
var SqnAct: [Actor]int;

// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

procedure Rep#init#0()
  modifies C, R, M, I, SqnCh, SqnAct;
{
  var in: Chan (int);
  var out: Chan (int);
  assume in != out;
  assume R[in] == 0;
  assume C[out] == 0;
  assert {:msg "Initialization might not establish the invariant (#0)"} R[in] == C[out];
  assert {:msg "Initialization might not establish the invariant (#1)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == M[in][idx$])
  );
}
procedure Rep#anon$0#1()
  modifies C, R, M, I, SqnCh, SqnAct;
{
  var in: Chan (int);
  var out: Chan (int);
  var in#0: int;
  var in#0#sqn: int;
  assume in != out;
  assume 0 <= R[in];
  assume 0 <= C[out];
  assume R[in] == C[out];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == M[in][idx$])
  );
  in#0 := M[in][R[in]];
  in#0#sqn := SqnCh[in][R[in]];
  R[in] := R[in] + 1;
  M[out][C[out]] := in#0;
  C[out] := C[out] + 1;
  assert {:msg "Action at 2.3 might not preserve invariant (#2)"} R[in] == C[out];
  assert {:msg "Action at 2.3 might not preserve invariant (#3)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == M[in][idx$])
  );
}
procedure Split#init#2()
  modifies C, R, M, I, SqnCh, SqnAct;
{
  var in: Chan (int);
  var out1: Chan (int);
  var out2: Chan (int);
  assume (in != out1) && (in != out2) && (out1 != out2);
  assume R[in] == 0;
  assume C[out1] == 0;
  assume C[out2] == 0;
  assert {:msg "Initialization might not establish the invariant (#4)"} R[in] == C[out1];
  assert {:msg "Initialization might not establish the invariant (#5)"} R[in] == C[out2];
  assert {:msg "Initialization might not establish the invariant (#6)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out1]) ==> (M[out1][idx$] == M[in][idx$])
  );
  assert {:msg "Initialization might not establish the invariant (#7)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out2]) ==> (M[out2][idx$] == M[in][idx$])
  );
}
procedure Split#anon$1#3()
  modifies C, R, M, I, SqnCh, SqnAct;
{
  var in: Chan (int);
  var out1: Chan (int);
  var out2: Chan (int);
  var in#0: int;
  var in#0#sqn: int;
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
  in#0#sqn := SqnCh[in][R[in]];
  R[in] := R[in] + 1;
  M[out1][C[out1]] := in#0;
  C[out1] := C[out1] + 1;
  M[out2][C[out2]] := in#0;
  C[out2] := C[out2] + 1;
  assert {:msg "Action at 6.3 might not preserve invariant (#8)"} R[in] == C[out1];
  assert {:msg "Action at 6.3 might not preserve invariant (#9)"} R[in] == C[out2];
  assert {:msg "Action at 6.3 might not preserve invariant (#10)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out1]) ==> (M[out1][idx$] == M[in][idx$])
  );
  assert {:msg "Action at 6.3 might not preserve invariant (#11)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out2]) ==> (M[out2][idx$] == M[in][idx$])
  );
}
procedure Adjudicator#init#4()
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
  c := 0;
  assert {:msg "12.20: Initialization might not establish the invariant (#12)"} C[y] == R[x2];
  assert {:msg "13.13: Initialization might not establish the invariant (#13)"} R[x2] == c;
}
procedure Adjudicator#normal#5()
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
  assume R[x2] == c;
  x1#0 := M[x1][R[x1]];
  x1#0#sqn := SqnCh[x1][R[x1]];
  R[x1] := R[x1] + 1;
  x2#0 := M[x2][R[x2]];
  x2#0#sqn := SqnCh[x2][R[x2]];
  R[x2] := R[x2] + 1;
  assume (x1#0#sqn == x2#0#sqn) && (x1#0#sqn == c);
  c := c + 1;
  M[y][C[y]] := x1#0;
  C[y] := C[y] + 1;
  assert {:msg "12.20: Action at 18.3 might not preserve invariant (#14)"} C[y] == R[x2];
  assert {:msg "13.13: Action at 18.3 might not preserve invariant (#15)"} R[x2] == c;
}
procedure Adjudicator#timeout#6()
  modifies C, R, M, I, SqnCh, SqnAct;
{
  var x1: Chan (int);
  var x2: Chan (int);
  var y: Chan (int);
  var c: int;
  var x2#0: int;
  var x2#0#sqn: int;
  assume (x1 != x2) && (x1 != y) && (x2 != y);
  assume 0 <= R[x1];
  assume 0 <= R[x2];
  assume 0 <= C[y];
  assume C[y] == R[x2];
  assume R[x2] == c;
  x2#0 := M[x2][R[x2]];
  x2#0#sqn := SqnCh[x2][R[x2]];
  R[x2] := R[x2] + 1;
  c := c + 1;
  M[y][C[y]] := x2#0;
  C[y] := C[y] + 1;
  assert {:msg "12.20: Action at 23.3 might not preserve invariant (#16)"} C[y] == R[x2];
  assert {:msg "13.13: Action at 23.3 might not preserve invariant (#17)"} R[x2] == c;
}
procedure Adjudicator#readoff#7()
  modifies C, R, M, I, SqnCh, SqnAct;
{
  var x1: Chan (int);
  var x2: Chan (int);
  var y: Chan (int);
  var c: int;
  var x1#0: int;
  var x1#0#sqn: int;
  assume (x1 != x2) && (x1 != y) && (x2 != y);
  assume 0 <= R[x1];
  assume 0 <= R[x2];
  assume 0 <= C[y];
  assume C[y] == R[x2];
  assume R[x2] == c;
  x1#0 := M[x1][R[x1]];
  x1#0#sqn := SqnCh[x1][R[x1]];
  R[x1] := R[x1] + 1;
  assume x1#0#sqn < c;
  assert {:msg "12.20: Action at 27.3 might not preserve invariant (#18)"} C[y] == R[x2];
  assert {:msg "13.13: Action at 27.3 might not preserve invariant (#19)"} R[x2] == c;
}
procedure Adjudicator##GuardWD#8()
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
  assert {:msg "10.1: The actions of actor 'Adjudicator' might not have mutually exclusive guards (#20)"} !((1 <= (C[x1] - R[x1])) && (1 <= (C[x2] - R[x2])) && (x1#0#sqn == x2#0#sqn) && (x1#0#sqn == c) && (1 <= (C[x2] - R[x2])) && true);
  assert {:msg "10.1: The actions of actor 'Adjudicator' might not have mutually exclusive guards (#21)"} !((1 <= (C[x1] - R[x1])) && (1 <= (C[x2] - R[x2])) && (x1#0#sqn == x2#0#sqn) && (x1#0#sqn == c) && (1 <= (C[x1] - R[x1])) && (x1#0#sqn < c));
  assert {:msg "10.1: The actions of actor 'Adjudicator' might not have mutually exclusive guards (#22)"} !((1 <= (C[x2] - R[x2])) && true && (1 <= (C[x1] - R[x1])) && (x1#0#sqn < c));
}
procedure Net#init#9()
  modifies C, R, M, I, SqnCh, SqnAct;
{
  var Net#spl: Actor;
  var Net#pri: Actor;
  var Net#sec: Actor;
  var Net#adj: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (int);
  var Net#d: Chan (int);
  var Net#e: Chan (int);
  var Net#g: Chan (int);
  var AV#adj#c: int;
  assume (Net#spl != Net#pri) && (Net#spl != Net#sec) && (Net#spl != Net#adj) && (Net#pri != Net#sec) && (Net#pri != Net#adj) && (Net#sec != Net#adj);
  assume (Net#a != Net#b) && (Net#a != Net#c) && (Net#a != Net#d) && (Net#a != Net#e) && (Net#a != Net#g) && (Net#b != Net#c) && (Net#b != Net#d) && (Net#b != Net#e) && (Net#b != Net#g) && (Net#c != Net#d) && (Net#c != Net#e) && (Net#c != Net#g) && (Net#d != Net#e) && (Net#d != Net#g) && (Net#e != Net#g);
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume 0 <= I[Net#c];
  assume I[Net#c] <= R[Net#c];
  assume R[Net#c] <= C[Net#c];
  assume 0 <= I[Net#d];
  assume I[Net#d] <= R[Net#d];
  assume R[Net#d] <= C[Net#d];
  assume 0 <= I[Net#e];
  assume I[Net#e] <= R[Net#e];
  assume R[Net#e] <= C[Net#e];
  assume 0 <= I[Net#g];
  assume I[Net#g] <= R[Net#g];
  assume R[Net#g] <= C[Net#g];
  assume I[Net#g] == R[Net#g];
  assume C[Net#a] == 0;
  assume R[Net#a] == 0;
  assume C[Net#b] == 0;
  assume R[Net#b] == 0;
  assume C[Net#c] == 0;
  assume R[Net#c] == 0;
  assume C[Net#d] == 0;
  assume R[Net#d] == 0;
  assume C[Net#e] == 0;
  assume R[Net#e] == 0;
  assume C[Net#g] == 0;
  assume R[Net#g] == 0;
  assume SqnAct[Net#spl] == 0;
  assume SqnAct[Net#pri] == 0;
  assume SqnAct[Net#sec] == 0;
  assume SqnAct[Net#adj] == 0;
  assert {:msg "41.15: Initialization of network 'Net' might not establish the channel invariant (#23)"} I[Net#g] == I[Net#d];
  assert {:msg "42.15: Initialization of network 'Net' might not establish the channel invariant (#24)"} I[Net#g] == I[Net#e];
  assert {:msg "Initialization of network 'Net' might not establish the channel invariant (#25)"} I[Net#b] == I[Net#a];
  assert {:msg "Initialization of network 'Net' might not establish the channel invariant (#26)"} I[Net#c] == I[Net#a];
  assert {:msg "Initialization of network 'Net' might not establish the channel invariant (#27)"} I[Net#d] == I[Net#b];
  assert {:msg "Initialization of network 'Net' might not establish the channel invariant (#28)"} I[Net#e] == I[Net#c];
  I := R;
  assert {:msg "Initialization of network 'Net' might not establish the network invariant: Unread tokens might be left on channel a (#29)"} (C[Net#a] - R[Net#a]) == 0;
  assert {:msg "Initialization of network 'Net' might not establish the network invariant: Unread tokens might be left on channel b (#30)"} (C[Net#b] - R[Net#b]) == 0;
  assert {:msg "Initialization of network 'Net' might not establish the network invariant: Unread tokens might be left on channel c (#31)"} (C[Net#c] - R[Net#c]) == 0;
  assert {:msg "Initialization of network 'Net' might not establish the network invariant: Unread tokens might be left on channel d (#32)"} (C[Net#d] - R[Net#d]) == 0;
  assert {:msg "Initialization of network 'Net' might not establish the network invariant: Unread tokens might be left on channel e (#33)"} (C[Net#e] - R[Net#e]) == 0;
  assert {:msg "Initialization of network 'Net' might not establish the network invariant: Unread tokens might be left on channel g (#34)"} (C[Net#g] - R[Net#g]) == 0;
}
procedure Net##Split#anon$1#10()
  modifies C, R, M, I, SqnCh, SqnAct;
{
  var Net#spl: Actor;
  var Net#pri: Actor;
  var Net#sec: Actor;
  var Net#adj: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (int);
  var Net#d: Chan (int);
  var Net#e: Chan (int);
  var Net#g: Chan (int);
  var AV#adj#c: int;
  var in#i: int;
  assume (Net#spl != Net#pri) && (Net#spl != Net#sec) && (Net#spl != Net#adj) && (Net#pri != Net#sec) && (Net#pri != Net#adj) && (Net#sec != Net#adj);
  assume (Net#a != Net#b) && (Net#a != Net#c) && (Net#a != Net#d) && (Net#a != Net#e) && (Net#a != Net#g) && (Net#b != Net#c) && (Net#b != Net#d) && (Net#b != Net#e) && (Net#b != Net#g) && (Net#c != Net#d) && (Net#c != Net#e) && (Net#c != Net#g) && (Net#d != Net#e) && (Net#d != Net#g) && (Net#e != Net#g);
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume 0 <= I[Net#c];
  assume I[Net#c] <= R[Net#c];
  assume R[Net#c] <= C[Net#c];
  assume 0 <= I[Net#d];
  assume I[Net#d] <= R[Net#d];
  assume R[Net#d] <= C[Net#d];
  assume 0 <= I[Net#e];
  assume I[Net#e] <= R[Net#e];
  assume R[Net#e] <= C[Net#e];
  assume 0 <= I[Net#g];
  assume I[Net#g] <= R[Net#g];
  assume R[Net#g] <= C[Net#g];
  assume I[Net#g] == R[Net#g];
  assume I[Net#g] == I[Net#d];
  assume I[Net#g] == I[Net#e];
  assume I[Net#b] == I[Net#a];
  assume I[Net#c] == I[Net#a];
  assume I[Net#d] == I[Net#b];
  assume I[Net#e] == I[Net#c];
  assume R[Net#a] == C[Net#b];
  assume R[Net#a] == C[Net#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assume R[Net#b] == C[Net#d];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assume R[Net#c] == C[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assume C[Net#g] == R[Net#e];
  assume 1 <= (C[Net#a] - R[Net#a]);
  in#i := M[Net#a][R[Net#a]];
  R[Net#a] := R[Net#a] + 1;
  M[Net#b][C[Net#b]] := in#i;
  SqnCh[Net#b][C[Net#b]] := SqnAct[Net#spl];
  C[Net#b] := C[Net#b] + 1;
  M[Net#c][C[Net#c]] := in#i;
  SqnCh[Net#c][C[Net#c]] := SqnAct[Net#spl];
  C[Net#c] := C[Net#c] + 1;
  SqnAct[Net#spl] := SqnAct[Net#spl] + 1;
  assume R[Net#a] == C[Net#b];
  assume R[Net#a] == C[Net#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assume R[Net#b] == C[Net#d];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assume R[Net#c] == C[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assume C[Net#g] == R[Net#e];
  assert {:msg "41.15: Action at 6.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#35)"} I[Net#g] == I[Net#d];
  assert {:msg "42.15: Action at 6.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#36)"} I[Net#g] == I[Net#e];
  assert {:msg "Action at 6.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#37)"} I[Net#b] == I[Net#a];
  assert {:msg "Action at 6.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#38)"} I[Net#c] == I[Net#a];
  assert {:msg "Action at 6.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#39)"} I[Net#d] == I[Net#b];
  assert {:msg "Action at 6.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#40)"} I[Net#e] == I[Net#c];
}
procedure Net##Rep#anon$0#11()
  modifies C, R, M, I, SqnCh, SqnAct;
{
  var Net#spl: Actor;
  var Net#pri: Actor;
  var Net#sec: Actor;
  var Net#adj: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (int);
  var Net#d: Chan (int);
  var Net#e: Chan (int);
  var Net#g: Chan (int);
  var AV#adj#c: int;
  var in#i: int;
  assume (Net#spl != Net#pri) && (Net#spl != Net#sec) && (Net#spl != Net#adj) && (Net#pri != Net#sec) && (Net#pri != Net#adj) && (Net#sec != Net#adj);
  assume (Net#a != Net#b) && (Net#a != Net#c) && (Net#a != Net#d) && (Net#a != Net#e) && (Net#a != Net#g) && (Net#b != Net#c) && (Net#b != Net#d) && (Net#b != Net#e) && (Net#b != Net#g) && (Net#c != Net#d) && (Net#c != Net#e) && (Net#c != Net#g) && (Net#d != Net#e) && (Net#d != Net#g) && (Net#e != Net#g);
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume 0 <= I[Net#c];
  assume I[Net#c] <= R[Net#c];
  assume R[Net#c] <= C[Net#c];
  assume 0 <= I[Net#d];
  assume I[Net#d] <= R[Net#d];
  assume R[Net#d] <= C[Net#d];
  assume 0 <= I[Net#e];
  assume I[Net#e] <= R[Net#e];
  assume R[Net#e] <= C[Net#e];
  assume 0 <= I[Net#g];
  assume I[Net#g] <= R[Net#g];
  assume R[Net#g] <= C[Net#g];
  assume I[Net#g] == R[Net#g];
  assume I[Net#g] == I[Net#d];
  assume I[Net#g] == I[Net#e];
  assume I[Net#b] == I[Net#a];
  assume I[Net#c] == I[Net#a];
  assume I[Net#d] == I[Net#b];
  assume I[Net#e] == I[Net#c];
  assume R[Net#a] == C[Net#b];
  assume R[Net#a] == C[Net#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assume R[Net#b] == C[Net#d];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assume R[Net#c] == C[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assume C[Net#g] == R[Net#e];
  assume 1 <= (C[Net#b] - R[Net#b]);
  in#i := M[Net#b][R[Net#b]];
  R[Net#b] := R[Net#b] + 1;
  M[Net#d][C[Net#d]] := in#i;
  SqnCh[Net#d][C[Net#d]] := SqnAct[Net#pri];
  C[Net#d] := C[Net#d] + 1;
  SqnAct[Net#pri] := SqnAct[Net#pri] + 1;
  assume R[Net#a] == C[Net#b];
  assume R[Net#a] == C[Net#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assume R[Net#b] == C[Net#d];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assume R[Net#c] == C[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assume C[Net#g] == R[Net#e];
  assert {:msg "41.15: Action at 2.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#41)"} I[Net#g] == I[Net#d];
  assert {:msg "42.15: Action at 2.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#42)"} I[Net#g] == I[Net#e];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#43)"} I[Net#b] == I[Net#a];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#44)"} I[Net#c] == I[Net#a];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#45)"} I[Net#d] == I[Net#b];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#46)"} I[Net#e] == I[Net#c];
}
procedure Net##Rep#anon$0#12()
  modifies C, R, M, I, SqnCh, SqnAct;
{
  var Net#spl: Actor;
  var Net#pri: Actor;
  var Net#sec: Actor;
  var Net#adj: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (int);
  var Net#d: Chan (int);
  var Net#e: Chan (int);
  var Net#g: Chan (int);
  var AV#adj#c: int;
  var in#i: int;
  assume (Net#spl != Net#pri) && (Net#spl != Net#sec) && (Net#spl != Net#adj) && (Net#pri != Net#sec) && (Net#pri != Net#adj) && (Net#sec != Net#adj);
  assume (Net#a != Net#b) && (Net#a != Net#c) && (Net#a != Net#d) && (Net#a != Net#e) && (Net#a != Net#g) && (Net#b != Net#c) && (Net#b != Net#d) && (Net#b != Net#e) && (Net#b != Net#g) && (Net#c != Net#d) && (Net#c != Net#e) && (Net#c != Net#g) && (Net#d != Net#e) && (Net#d != Net#g) && (Net#e != Net#g);
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume 0 <= I[Net#c];
  assume I[Net#c] <= R[Net#c];
  assume R[Net#c] <= C[Net#c];
  assume 0 <= I[Net#d];
  assume I[Net#d] <= R[Net#d];
  assume R[Net#d] <= C[Net#d];
  assume 0 <= I[Net#e];
  assume I[Net#e] <= R[Net#e];
  assume R[Net#e] <= C[Net#e];
  assume 0 <= I[Net#g];
  assume I[Net#g] <= R[Net#g];
  assume R[Net#g] <= C[Net#g];
  assume I[Net#g] == R[Net#g];
  assume I[Net#g] == I[Net#d];
  assume I[Net#g] == I[Net#e];
  assume I[Net#b] == I[Net#a];
  assume I[Net#c] == I[Net#a];
  assume I[Net#d] == I[Net#b];
  assume I[Net#e] == I[Net#c];
  assume R[Net#a] == C[Net#b];
  assume R[Net#a] == C[Net#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assume R[Net#b] == C[Net#d];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assume R[Net#c] == C[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assume C[Net#g] == R[Net#e];
  assume 1 <= (C[Net#c] - R[Net#c]);
  in#i := M[Net#c][R[Net#c]];
  R[Net#c] := R[Net#c] + 1;
  M[Net#e][C[Net#e]] := in#i;
  SqnCh[Net#e][C[Net#e]] := SqnAct[Net#sec];
  C[Net#e] := C[Net#e] + 1;
  SqnAct[Net#sec] := SqnAct[Net#sec] + 1;
  assume R[Net#a] == C[Net#b];
  assume R[Net#a] == C[Net#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assume R[Net#b] == C[Net#d];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assume R[Net#c] == C[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assume C[Net#g] == R[Net#e];
  assert {:msg "41.15: Action at 2.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#47)"} I[Net#g] == I[Net#d];
  assert {:msg "42.15: Action at 2.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#48)"} I[Net#g] == I[Net#e];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#49)"} I[Net#b] == I[Net#a];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#50)"} I[Net#c] == I[Net#a];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#51)"} I[Net#d] == I[Net#b];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#52)"} I[Net#e] == I[Net#c];
}
procedure Net##Adjudicator#normal#13()
  modifies C, R, M, I, SqnCh, SqnAct;
{
  var Net#spl: Actor;
  var Net#pri: Actor;
  var Net#sec: Actor;
  var Net#adj: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (int);
  var Net#d: Chan (int);
  var Net#e: Chan (int);
  var Net#g: Chan (int);
  var AV#adj#c: int;
  var x1#i: int;
  var x2#j: int;
  assume (Net#spl != Net#pri) && (Net#spl != Net#sec) && (Net#spl != Net#adj) && (Net#pri != Net#sec) && (Net#pri != Net#adj) && (Net#sec != Net#adj);
  assume (Net#a != Net#b) && (Net#a != Net#c) && (Net#a != Net#d) && (Net#a != Net#e) && (Net#a != Net#g) && (Net#b != Net#c) && (Net#b != Net#d) && (Net#b != Net#e) && (Net#b != Net#g) && (Net#c != Net#d) && (Net#c != Net#e) && (Net#c != Net#g) && (Net#d != Net#e) && (Net#d != Net#g) && (Net#e != Net#g);
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume 0 <= I[Net#c];
  assume I[Net#c] <= R[Net#c];
  assume R[Net#c] <= C[Net#c];
  assume 0 <= I[Net#d];
  assume I[Net#d] <= R[Net#d];
  assume R[Net#d] <= C[Net#d];
  assume 0 <= I[Net#e];
  assume I[Net#e] <= R[Net#e];
  assume R[Net#e] <= C[Net#e];
  assume 0 <= I[Net#g];
  assume I[Net#g] <= R[Net#g];
  assume R[Net#g] <= C[Net#g];
  assume I[Net#g] == R[Net#g];
  assume I[Net#g] == I[Net#d];
  assume I[Net#g] == I[Net#e];
  assume I[Net#b] == I[Net#a];
  assume I[Net#c] == I[Net#a];
  assume I[Net#d] == I[Net#b];
  assume I[Net#e] == I[Net#c];
  assume R[Net#a] == C[Net#b];
  assume R[Net#a] == C[Net#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assume R[Net#b] == C[Net#d];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assume R[Net#c] == C[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assume C[Net#g] == R[Net#e];
  assume (1 <= (C[Net#d] - R[Net#d])) && (1 <= (C[Net#e] - R[Net#e])) && (SqnCh[Net#d][R[Net#d]] == SqnCh[Net#e][R[Net#e]]) && (SqnCh[Net#d][R[Net#d]] == AV#adj#c);
  x1#i := M[Net#d][R[Net#d]];
  R[Net#d] := R[Net#d] + 1;
  x2#j := M[Net#e][R[Net#e]];
  R[Net#e] := R[Net#e] + 1;
  havoc AV#adj#c;
  M[Net#g][C[Net#g]] := x1#i;
  SqnCh[Net#g][C[Net#g]] := SqnAct[Net#adj];
  C[Net#g] := C[Net#g] + 1;
  SqnAct[Net#adj] := SqnAct[Net#adj] + 1;
  assume R[Net#a] == C[Net#b];
  assume R[Net#a] == C[Net#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assume R[Net#b] == C[Net#d];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assume R[Net#c] == C[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assume C[Net#g] == R[Net#e];
  assert {:msg "41.15: Action at 18.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#53)"} I[Net#g] == I[Net#d];
  assert {:msg "42.15: Action at 18.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#54)"} I[Net#g] == I[Net#e];
  assert {:msg "Action at 18.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#55)"} I[Net#b] == I[Net#a];
  assert {:msg "Action at 18.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#56)"} I[Net#c] == I[Net#a];
  assert {:msg "Action at 18.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#57)"} I[Net#d] == I[Net#b];
  assert {:msg "Action at 18.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#58)"} I[Net#e] == I[Net#c];
}
procedure Net##Adjudicator#timeout#14()
  modifies C, R, M, I, SqnCh, SqnAct;
{
  var Net#spl: Actor;
  var Net#pri: Actor;
  var Net#sec: Actor;
  var Net#adj: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (int);
  var Net#d: Chan (int);
  var Net#e: Chan (int);
  var Net#g: Chan (int);
  var AV#adj#c: int;
  var x2#j: int;
  assume (Net#spl != Net#pri) && (Net#spl != Net#sec) && (Net#spl != Net#adj) && (Net#pri != Net#sec) && (Net#pri != Net#adj) && (Net#sec != Net#adj);
  assume (Net#a != Net#b) && (Net#a != Net#c) && (Net#a != Net#d) && (Net#a != Net#e) && (Net#a != Net#g) && (Net#b != Net#c) && (Net#b != Net#d) && (Net#b != Net#e) && (Net#b != Net#g) && (Net#c != Net#d) && (Net#c != Net#e) && (Net#c != Net#g) && (Net#d != Net#e) && (Net#d != Net#g) && (Net#e != Net#g);
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume 0 <= I[Net#c];
  assume I[Net#c] <= R[Net#c];
  assume R[Net#c] <= C[Net#c];
  assume 0 <= I[Net#d];
  assume I[Net#d] <= R[Net#d];
  assume R[Net#d] <= C[Net#d];
  assume 0 <= I[Net#e];
  assume I[Net#e] <= R[Net#e];
  assume R[Net#e] <= C[Net#e];
  assume 0 <= I[Net#g];
  assume I[Net#g] <= R[Net#g];
  assume R[Net#g] <= C[Net#g];
  assume I[Net#g] == R[Net#g];
  assume I[Net#g] == I[Net#d];
  assume I[Net#g] == I[Net#e];
  assume I[Net#b] == I[Net#a];
  assume I[Net#c] == I[Net#a];
  assume I[Net#d] == I[Net#b];
  assume I[Net#e] == I[Net#c];
  assume R[Net#a] == C[Net#b];
  assume R[Net#a] == C[Net#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assume R[Net#b] == C[Net#d];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assume R[Net#c] == C[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assume C[Net#g] == R[Net#e];
  assume 1 <= (C[Net#e] - R[Net#e]);
  x2#j := M[Net#e][R[Net#e]];
  R[Net#e] := R[Net#e] + 1;
  havoc AV#adj#c;
  M[Net#g][C[Net#g]] := x2#j;
  SqnCh[Net#g][C[Net#g]] := SqnAct[Net#adj];
  C[Net#g] := C[Net#g] + 1;
  SqnAct[Net#adj] := SqnAct[Net#adj] + 1;
  assume R[Net#a] == C[Net#b];
  assume R[Net#a] == C[Net#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assume R[Net#b] == C[Net#d];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assume R[Net#c] == C[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assume C[Net#g] == R[Net#e];
  assert {:msg "41.15: Action at 23.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#59)"} I[Net#g] == I[Net#d];
  assert {:msg "42.15: Action at 23.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#60)"} I[Net#g] == I[Net#e];
  assert {:msg "Action at 23.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#61)"} I[Net#b] == I[Net#a];
  assert {:msg "Action at 23.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#62)"} I[Net#c] == I[Net#a];
  assert {:msg "Action at 23.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#63)"} I[Net#d] == I[Net#b];
  assert {:msg "Action at 23.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#64)"} I[Net#e] == I[Net#c];
}
procedure Net##Adjudicator#readoff#15()
  modifies C, R, M, I, SqnCh, SqnAct;
{
  var Net#spl: Actor;
  var Net#pri: Actor;
  var Net#sec: Actor;
  var Net#adj: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (int);
  var Net#d: Chan (int);
  var Net#e: Chan (int);
  var Net#g: Chan (int);
  var AV#adj#c: int;
  var x1#i: int;
  assume (Net#spl != Net#pri) && (Net#spl != Net#sec) && (Net#spl != Net#adj) && (Net#pri != Net#sec) && (Net#pri != Net#adj) && (Net#sec != Net#adj);
  assume (Net#a != Net#b) && (Net#a != Net#c) && (Net#a != Net#d) && (Net#a != Net#e) && (Net#a != Net#g) && (Net#b != Net#c) && (Net#b != Net#d) && (Net#b != Net#e) && (Net#b != Net#g) && (Net#c != Net#d) && (Net#c != Net#e) && (Net#c != Net#g) && (Net#d != Net#e) && (Net#d != Net#g) && (Net#e != Net#g);
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume 0 <= I[Net#c];
  assume I[Net#c] <= R[Net#c];
  assume R[Net#c] <= C[Net#c];
  assume 0 <= I[Net#d];
  assume I[Net#d] <= R[Net#d];
  assume R[Net#d] <= C[Net#d];
  assume 0 <= I[Net#e];
  assume I[Net#e] <= R[Net#e];
  assume R[Net#e] <= C[Net#e];
  assume 0 <= I[Net#g];
  assume I[Net#g] <= R[Net#g];
  assume R[Net#g] <= C[Net#g];
  assume I[Net#g] == R[Net#g];
  assume I[Net#g] == I[Net#d];
  assume I[Net#g] == I[Net#e];
  assume I[Net#b] == I[Net#a];
  assume I[Net#c] == I[Net#a];
  assume I[Net#d] == I[Net#b];
  assume I[Net#e] == I[Net#c];
  assume R[Net#a] == C[Net#b];
  assume R[Net#a] == C[Net#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assume R[Net#b] == C[Net#d];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assume R[Net#c] == C[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assume C[Net#g] == R[Net#e];
  assume (1 <= (C[Net#d] - R[Net#d])) && (SqnCh[Net#d][R[Net#d]] < AV#adj#c);
  x1#i := M[Net#d][R[Net#d]];
  R[Net#d] := R[Net#d] + 1;
  assume R[Net#a] == C[Net#b];
  assume R[Net#a] == C[Net#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assume R[Net#b] == C[Net#d];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assume R[Net#c] == C[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assume C[Net#g] == R[Net#e];
  assert {:msg "41.15: Action at 27.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#65)"} I[Net#g] == I[Net#d];
  assert {:msg "42.15: Action at 27.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#66)"} I[Net#g] == I[Net#e];
  assert {:msg "Action at 27.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#67)"} I[Net#b] == I[Net#a];
  assert {:msg "Action at 27.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#68)"} I[Net#c] == I[Net#a];
  assert {:msg "Action at 27.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#69)"} I[Net#d] == I[Net#b];
  assert {:msg "Action at 27.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#70)"} I[Net#e] == I[Net#c];
}
procedure Net#anon$3#input#in#16()
  modifies C, R, M, I, SqnCh, SqnAct;
{
  var Net#spl: Actor;
  var Net#pri: Actor;
  var Net#sec: Actor;
  var Net#adj: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (int);
  var Net#d: Chan (int);
  var Net#e: Chan (int);
  var Net#g: Chan (int);
  var AV#adj#c: int;
  assume (Net#spl != Net#pri) && (Net#spl != Net#sec) && (Net#spl != Net#adj) && (Net#pri != Net#sec) && (Net#pri != Net#adj) && (Net#sec != Net#adj);
  assume (Net#a != Net#b) && (Net#a != Net#c) && (Net#a != Net#d) && (Net#a != Net#e) && (Net#a != Net#g) && (Net#b != Net#c) && (Net#b != Net#d) && (Net#b != Net#e) && (Net#b != Net#g) && (Net#c != Net#d) && (Net#c != Net#e) && (Net#c != Net#g) && (Net#d != Net#e) && (Net#d != Net#g) && (Net#e != Net#g);
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume 0 <= I[Net#c];
  assume I[Net#c] <= R[Net#c];
  assume R[Net#c] <= C[Net#c];
  assume 0 <= I[Net#d];
  assume I[Net#d] <= R[Net#d];
  assume R[Net#d] <= C[Net#d];
  assume 0 <= I[Net#e];
  assume I[Net#e] <= R[Net#e];
  assume R[Net#e] <= C[Net#e];
  assume 0 <= I[Net#g];
  assume I[Net#g] <= R[Net#g];
  assume R[Net#g] <= C[Net#g];
  assume I[Net#g] == R[Net#g];
  assume (C[Net#a] - I[Net#a]) < 1;
  assume I[Net#g] == I[Net#d];
  assume I[Net#g] == I[Net#e];
  assume I[Net#b] == I[Net#a];
  assume I[Net#c] == I[Net#a];
  assume I[Net#d] == I[Net#b];
  assume I[Net#e] == I[Net#c];
  assume R[Net#a] == C[Net#b];
  assume R[Net#a] == C[Net#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assume R[Net#b] == C[Net#d];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assume R[Net#c] == C[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assume C[Net#g] == R[Net#e];
  C[Net#a] := C[Net#a] + 1;
  assert {:msg "41.15: Channel invariant might be falsified by network input (#71)"} I[Net#g] == I[Net#d];
  assert {:msg "42.15: Channel invariant might be falsified by network input (#72)"} I[Net#g] == I[Net#e];
  assert {:msg "Channel invariant might be falsified by network input (#73)"} I[Net#b] == I[Net#a];
  assert {:msg "Channel invariant might be falsified by network input (#74)"} I[Net#c] == I[Net#a];
  assert {:msg "Channel invariant might be falsified by network input (#75)"} I[Net#d] == I[Net#b];
  assert {:msg "Channel invariant might be falsified by network input (#76)"} I[Net#e] == I[Net#c];
}
procedure Net#anon$3#exit#17()
  modifies C, R, M, I, SqnCh, SqnAct;
{
  var Net#spl: Actor;
  var Net#pri: Actor;
  var Net#sec: Actor;
  var Net#adj: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (int);
  var Net#d: Chan (int);
  var Net#e: Chan (int);
  var Net#g: Chan (int);
  var AV#adj#c: int;
  assume (Net#spl != Net#pri) && (Net#spl != Net#sec) && (Net#spl != Net#adj) && (Net#pri != Net#sec) && (Net#pri != Net#adj) && (Net#sec != Net#adj);
  assume (Net#a != Net#b) && (Net#a != Net#c) && (Net#a != Net#d) && (Net#a != Net#e) && (Net#a != Net#g) && (Net#b != Net#c) && (Net#b != Net#d) && (Net#b != Net#e) && (Net#b != Net#g) && (Net#c != Net#d) && (Net#c != Net#e) && (Net#c != Net#g) && (Net#d != Net#e) && (Net#d != Net#g) && (Net#e != Net#g);
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume 0 <= I[Net#c];
  assume I[Net#c] <= R[Net#c];
  assume R[Net#c] <= C[Net#c];
  assume 0 <= I[Net#d];
  assume I[Net#d] <= R[Net#d];
  assume R[Net#d] <= C[Net#d];
  assume 0 <= I[Net#e];
  assume I[Net#e] <= R[Net#e];
  assume R[Net#e] <= C[Net#e];
  assume 0 <= I[Net#g];
  assume I[Net#g] <= R[Net#g];
  assume R[Net#g] <= C[Net#g];
  assume I[Net#g] == R[Net#g];
  assume I[Net#g] == I[Net#d];
  assume I[Net#g] == I[Net#e];
  assume I[Net#b] == I[Net#a];
  assume I[Net#c] == I[Net#a];
  assume I[Net#d] == I[Net#b];
  assume I[Net#e] == I[Net#c];
  assume R[Net#a] == C[Net#b];
  assume R[Net#a] == C[Net#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assume R[Net#b] == C[Net#d];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assume R[Net#c] == C[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assume C[Net#g] == R[Net#e];
  assume (C[Net#a] - I[Net#a]) == 1;
  assume !(1 <= (C[Net#a] - R[Net#a]));
  assume !(1 <= (C[Net#b] - R[Net#b]));
  assume !(1 <= (C[Net#c] - R[Net#c]));
  assume !((1 <= (C[Net#d] - R[Net#d])) && (1 <= (C[Net#e] - R[Net#e])) && (SqnCh[Net#d][R[Net#d]] == SqnCh[Net#e][R[Net#e]]) && (SqnCh[Net#d][R[Net#d]] == AV#adj#c));
  assume !(1 <= (C[Net#e] - R[Net#e]));
  assume !((1 <= (C[Net#d] - R[Net#d])) && (SqnCh[Net#d][R[Net#d]] < AV#adj#c));
  R[Net#g] := R[Net#g] + 1;
  I := R;
  assert {:msg "41.15: The network might not preserve the channel invariant (#77)"} I[Net#g] == I[Net#d];
  assert {:msg "42.15: The network might not preserve the channel invariant (#78)"} I[Net#g] == I[Net#e];
  assert {:msg "The network might not preserve the channel invariant (#79)"} I[Net#b] == I[Net#a];
  assert {:msg "The network might not preserve the channel invariant (#80)"} I[Net#c] == I[Net#a];
  assert {:msg "The network might not preserve the channel invariant (#81)"} I[Net#d] == I[Net#b];
  assert {:msg "The network might not preserve the channel invariant (#82)"} I[Net#e] == I[Net#c];
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel a (#83)"} (C[Net#a] - R[Net#a]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel b (#84)"} (C[Net#b] - R[Net#b]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel c (#85)"} (C[Net#c] - R[Net#c]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel d (#86)"} (C[Net#d] - R[Net#d]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel e (#87)"} (C[Net#e] - R[Net#e]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel g (#88)"} (C[Net#g] - R[Net#g]) == 0;
}

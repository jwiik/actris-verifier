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
var St: [Actor]State;

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

procedure Rep#anon$0#0()
  modifies C, R, M, I, St, SqnCh, SqnAct;
{
  var in: Chan (int);
  var out: Chan (int);
  assume true;
}
procedure Split#anon$1#1()
  modifies C, R, M, I, St, SqnCh, SqnAct;
{
  var in: Chan (int);
  var out1: Chan (int);
  var out2: Chan (int);
  assume true;
}
procedure Adjudicator#normal#2()
  modifies C, R, M, I, St, SqnCh, SqnAct;
{
  var x1: Chan (int);
  var x2: Chan (int);
  var c_in: Chan (int);
  var y: Chan (int);
  var c_out: Chan (int);
  assume (SqnCh[x1][0] == SqnCh[x2][0]) && (SqnCh[x1][0] == M[c_in][0]);
  assume true;
}
procedure Adjudicator#timeout#3()
  modifies C, R, M, I, St, SqnCh, SqnAct;
{
  var x1: Chan (int);
  var x2: Chan (int);
  var c_in: Chan (int);
  var y: Chan (int);
  var c_out: Chan (int);
  assume true;
}
procedure Adjudicator#readoff#4()
  modifies C, R, M, I, St, SqnCh, SqnAct;
{
  var x1: Chan (int);
  var x2: Chan (int);
  var c_in: Chan (int);
  var y: Chan (int);
  var c_out: Chan (int);
  assume SqnCh[x1][0] < M[c_in][0];
  assume true;
}
procedure Adjudicator#anon$2#5()
  modifies C, R, M, I, St, SqnCh, SqnAct;
{
  var x1: Chan (int);
  var x2: Chan (int);
  var c_in: Chan (int);
  var y: Chan (int);
  var c_out: Chan (int);
  assume true;
}
procedure Adjudicator##GuardWD#6()
  modifies C, R, M, I, St, SqnCh, SqnAct;
{
  var x2: Chan (int);
  var c_in: Chan (int);
  var y: Chan (int);
  var c_out: Chan (int);
  var x1: Chan (int);
  assert {:msg "12.1: The actions of actor 'Adjudicator' might not have mutually exclusive guards (#0)"} !((1 <= (C[x1] - R[x1])) && (1 <= (C[x2] - R[x2])) && (1 <= (C[c_in] - R[c_in])) && (SqnCh[x1][0] == SqnCh[x2][0]) && (SqnCh[x1][0] == M[c_in][0]) && (1 <= (C[x2] - R[x2])) && (1 <= (C[c_in] - R[c_in])));
  assert {:msg "12.1: The actions of actor 'Adjudicator' might not have mutually exclusive guards (#1)"} !((1 <= (C[x1] - R[x1])) && (1 <= (C[x2] - R[x2])) && (1 <= (C[c_in] - R[c_in])) && (SqnCh[x1][0] == SqnCh[x2][0]) && (SqnCh[x1][0] == M[c_in][0]) && (1 <= (C[x1] - R[x1])) && (1 <= (C[c_in] - R[c_in])) && (SqnCh[x1][0] < M[c_in][0]));
  assert {:msg "12.1: The actions of actor 'Adjudicator' might not have mutually exclusive guards (#2)"} !((1 <= (C[x2] - R[x2])) && (1 <= (C[c_in] - R[c_in])) && (1 <= (C[x1] - R[x1])) && (1 <= (C[c_in] - R[c_in])) && (SqnCh[x1][0] < M[c_in][0]));
}
const unique Net#spl: Actor;
const unique Net#pri: Actor;
const unique Net#sec: Actor;
const unique Net#adj: Actor;
const unique Net#a: Chan (int);
const unique Net#b: Chan (int);
const unique Net#c: Chan (int);
const unique Net#d: Chan (int);
const unique Net#e: Chan (int);
const unique Net#f: Chan (int);
const unique Net#g: Chan (int);
procedure Net#init#7()
  modifies C, R, M, I, St, SqnCh, SqnAct;
{
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
  assume 0 <= I[Net#f];
  assume I[Net#f] <= R[Net#f];
  assume R[Net#f] <= C[Net#f];
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
  assume C[Net#f] == 0;
  assume R[Net#f] == 0;
  assume C[Net#g] == 0;
  assume R[Net#g] == 0;
  assume SqnAct[Net#spl] == 0;
  assume SqnAct[Net#pri] == 0;
  assume SqnAct[Net#sec] == 0;
  assume SqnAct[Net#adj] == 0;
  M[Net#f][C[Net#f]] := 0;
  C[Net#f] := C[Net#f] + 1;
  assert {:msg "41.15: Network initialization might not establish the channel invariant (#3)"} SqnAct[Net#spl] == R[Net#a];
  assert {:msg "42.15: Network initialization might not establish the channel invariant (#4)"} SqnAct[Net#pri] == R[Net#b];
  assert {:msg "43.15: Network initialization might not establish the channel invariant (#5)"} SqnAct[Net#sec] == R[Net#c];
  assert {:msg "44.15: Network initialization might not establish the channel invariant (#6)"} SqnAct[Net#adj] == R[Net#e];
  assert {:msg "46.16: Network initialization might not establish the channel invariant (#7)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#a]) ==> (SqnCh[Net#a][i] == i)
  );
  assert {:msg "47.16: Network initialization might not establish the channel invariant (#8)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#b]) ==> (SqnCh[Net#b][i] == i)
  );
  assert {:msg "48.16: Network initialization might not establish the channel invariant (#9)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#c]) ==> (SqnCh[Net#c][i] == i)
  );
  assert {:msg "49.16: Network initialization might not establish the channel invariant (#10)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#d]) ==> (SqnCh[Net#d][i] == i)
  );
  assert {:msg "50.16: Network initialization might not establish the channel invariant (#11)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#e]) ==> (SqnCh[Net#e][i] == i)
  );
  assert {:msg "51.16: Network initialization might not establish the channel invariant (#12)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#g]) ==> (SqnCh[Net#g][i] == i)
  );
  assert {:msg "53.15: Network initialization might not establish the channel invariant (#13)"} (C[Net#f] - R[Net#f]) == 1;
  assert {:msg "54.15: Network initialization might not establish the channel invariant (#14)"} C[Net#g] == R[Net#e];
  assert {:msg "55.15: Network initialization might not establish the channel invariant (#15)"} R[Net#e] == M[Net#f][R[Net#f]];
  assert {:msg "56.16: Network initialization might not establish the channel invariant (#16)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#g]) ==> (SqnCh[Net#g][i] == i)
  );
  assert {:msg "59.16: Network initialization might not establish the channel invariant (#17)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#g][i] == M[Net#e][i])
  );
  assert {:msg "Network initialization might not establish the channel invariant (#18)"} R[Net#a] == C[Net#b];
  assert {:msg "Network initialization might not establish the channel invariant (#19)"} R[Net#a] == C[Net#c];
  assert {:msg "Network initialization might not establish the channel invariant (#20)"} R[Net#b] == C[Net#d];
  assert {:msg "Network initialization might not establish the channel invariant (#21)"} R[Net#c] == C[Net#e];
  assert {:msg "Network initialization might not establish the channel invariant (#22)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assert {:msg "Network initialization might not establish the channel invariant (#23)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assert {:msg "Network initialization might not establish the channel invariant (#24)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assert {:msg "Network initialization might not establish the channel invariant (#25)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assert {:msg "Network initialization might not establish the channel invariant (#26)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#a]) ==> (SqnCh[Net#a][idx$] == idx$)
  );
  I := R;
  C[Net#f] := C[Net#f] - 1;
  assert {:msg "39.13: Network initialization might not establish the network invariant"} R[Net#e] == M[Net#f][R[Net#f]];
}
procedure Net##Split#anon$1#8()
  modifies C, R, M, I, St, SqnCh, SqnAct;
{
  var St#next: State;
  var in#i: int;
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
  assume 0 <= I[Net#f];
  assume I[Net#f] <= R[Net#f];
  assume R[Net#f] <= C[Net#f];
  assume 0 <= I[Net#g];
  assume I[Net#g] <= R[Net#g];
  assume R[Net#g] <= C[Net#g];
  assume I[Net#g] == R[Net#g];
  assume SqnAct[Net#spl] == R[Net#a];
  assume SqnAct[Net#pri] == R[Net#b];
  assume SqnAct[Net#sec] == R[Net#c];
  assume SqnAct[Net#adj] == R[Net#e];
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#a]) ==> (SqnCh[Net#a][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#b]) ==> (SqnCh[Net#b][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#c]) ==> (SqnCh[Net#c][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#d]) ==> (SqnCh[Net#d][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#e]) ==> (SqnCh[Net#e][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#g]) ==> (SqnCh[Net#g][i] == i)
  );
  assume (C[Net#f] - R[Net#f]) == 1;
  assume C[Net#g] == R[Net#e];
  assume R[Net#e] == M[Net#f][R[Net#f]];
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#g]) ==> (SqnCh[Net#g][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#g][i] == M[Net#e][i])
  );
  assume R[Net#a] == C[Net#b];
  assume R[Net#a] == C[Net#c];
  assume R[Net#b] == C[Net#d];
  assume R[Net#c] == C[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#a]) ==> (SqnCh[Net#a][idx$] == idx$)
  );
  assume true;
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
  assert {:msg "41.15: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#27)"} SqnAct[Net#spl] == R[Net#a];
  assert {:msg "42.15: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#28)"} SqnAct[Net#pri] == R[Net#b];
  assert {:msg "43.15: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#29)"} SqnAct[Net#sec] == R[Net#c];
  assert {:msg "44.15: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#30)"} SqnAct[Net#adj] == R[Net#e];
  assert {:msg "46.16: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#31)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#a]) ==> (SqnCh[Net#a][i] == i)
  );
  assert {:msg "47.16: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#32)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#b]) ==> (SqnCh[Net#b][i] == i)
  );
  assert {:msg "48.16: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#33)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#c]) ==> (SqnCh[Net#c][i] == i)
  );
  assert {:msg "49.16: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#34)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#d]) ==> (SqnCh[Net#d][i] == i)
  );
  assert {:msg "50.16: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#35)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#e]) ==> (SqnCh[Net#e][i] == i)
  );
  assert {:msg "51.16: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#36)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#g]) ==> (SqnCh[Net#g][i] == i)
  );
  assert {:msg "53.15: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#37)"} (C[Net#f] - R[Net#f]) == 1;
  assert {:msg "54.15: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#38)"} C[Net#g] == R[Net#e];
  assert {:msg "55.15: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#39)"} R[Net#e] == M[Net#f][R[Net#f]];
  assert {:msg "56.16: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#40)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#g]) ==> (SqnCh[Net#g][i] == i)
  );
  assert {:msg "59.16: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#41)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#g][i] == M[Net#e][i])
  );
  assert {:msg "Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#42)"} R[Net#a] == C[Net#b];
  assert {:msg "Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#43)"} R[Net#a] == C[Net#c];
  assert {:msg "Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#44)"} R[Net#b] == C[Net#d];
  assert {:msg "Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#45)"} R[Net#c] == C[Net#e];
  assert {:msg "Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#46)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assert {:msg "Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#47)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assert {:msg "Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#48)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assert {:msg "Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#49)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assert {:msg "Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#50)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#a]) ==> (SqnCh[Net#a][idx$] == idx$)
  );
}
procedure Net##Rep#anon$0#9()
  modifies C, R, M, I, St, SqnCh, SqnAct;
{
  var St#next: State;
  var in#i: int;
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
  assume 0 <= I[Net#f];
  assume I[Net#f] <= R[Net#f];
  assume R[Net#f] <= C[Net#f];
  assume 0 <= I[Net#g];
  assume I[Net#g] <= R[Net#g];
  assume R[Net#g] <= C[Net#g];
  assume I[Net#g] == R[Net#g];
  assume SqnAct[Net#spl] == R[Net#a];
  assume SqnAct[Net#pri] == R[Net#b];
  assume SqnAct[Net#sec] == R[Net#c];
  assume SqnAct[Net#adj] == R[Net#e];
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#a]) ==> (SqnCh[Net#a][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#b]) ==> (SqnCh[Net#b][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#c]) ==> (SqnCh[Net#c][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#d]) ==> (SqnCh[Net#d][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#e]) ==> (SqnCh[Net#e][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#g]) ==> (SqnCh[Net#g][i] == i)
  );
  assume (C[Net#f] - R[Net#f]) == 1;
  assume C[Net#g] == R[Net#e];
  assume R[Net#e] == M[Net#f][R[Net#f]];
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#g]) ==> (SqnCh[Net#g][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#g][i] == M[Net#e][i])
  );
  assume R[Net#a] == C[Net#b];
  assume R[Net#a] == C[Net#c];
  assume R[Net#b] == C[Net#d];
  assume R[Net#c] == C[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#a]) ==> (SqnCh[Net#a][idx$] == idx$)
  );
  assume true;
  assume 1 <= (C[Net#b] - R[Net#b]);
  in#i := M[Net#b][R[Net#b]];
  R[Net#b] := R[Net#b] + 1;
  M[Net#d][C[Net#d]] := in#i;
  SqnCh[Net#d][C[Net#d]] := SqnAct[Net#pri];
  C[Net#d] := C[Net#d] + 1;
  SqnAct[Net#pri] := SqnAct[Net#pri] + 1;
  assert {:msg "41.15: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#51)"} SqnAct[Net#spl] == R[Net#a];
  assert {:msg "42.15: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#52)"} SqnAct[Net#pri] == R[Net#b];
  assert {:msg "43.15: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#53)"} SqnAct[Net#sec] == R[Net#c];
  assert {:msg "44.15: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#54)"} SqnAct[Net#adj] == R[Net#e];
  assert {:msg "46.16: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#55)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#a]) ==> (SqnCh[Net#a][i] == i)
  );
  assert {:msg "47.16: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#56)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#b]) ==> (SqnCh[Net#b][i] == i)
  );
  assert {:msg "48.16: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#57)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#c]) ==> (SqnCh[Net#c][i] == i)
  );
  assert {:msg "49.16: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#58)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#d]) ==> (SqnCh[Net#d][i] == i)
  );
  assert {:msg "50.16: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#59)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#e]) ==> (SqnCh[Net#e][i] == i)
  );
  assert {:msg "51.16: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#60)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#g]) ==> (SqnCh[Net#g][i] == i)
  );
  assert {:msg "53.15: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#61)"} (C[Net#f] - R[Net#f]) == 1;
  assert {:msg "54.15: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#62)"} C[Net#g] == R[Net#e];
  assert {:msg "55.15: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#63)"} R[Net#e] == M[Net#f][R[Net#f]];
  assert {:msg "56.16: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#64)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#g]) ==> (SqnCh[Net#g][i] == i)
  );
  assert {:msg "59.16: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#65)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#g][i] == M[Net#e][i])
  );
  assert {:msg "Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#66)"} R[Net#a] == C[Net#b];
  assert {:msg "Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#67)"} R[Net#a] == C[Net#c];
  assert {:msg "Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#68)"} R[Net#b] == C[Net#d];
  assert {:msg "Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#69)"} R[Net#c] == C[Net#e];
  assert {:msg "Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#70)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assert {:msg "Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#71)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assert {:msg "Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#72)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assert {:msg "Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#73)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assert {:msg "Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#74)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#a]) ==> (SqnCh[Net#a][idx$] == idx$)
  );
}
procedure Net##Rep#anon$0#10()
  modifies C, R, M, I, St, SqnCh, SqnAct;
{
  var St#next: State;
  var in#i: int;
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
  assume 0 <= I[Net#f];
  assume I[Net#f] <= R[Net#f];
  assume R[Net#f] <= C[Net#f];
  assume 0 <= I[Net#g];
  assume I[Net#g] <= R[Net#g];
  assume R[Net#g] <= C[Net#g];
  assume I[Net#g] == R[Net#g];
  assume SqnAct[Net#spl] == R[Net#a];
  assume SqnAct[Net#pri] == R[Net#b];
  assume SqnAct[Net#sec] == R[Net#c];
  assume SqnAct[Net#adj] == R[Net#e];
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#a]) ==> (SqnCh[Net#a][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#b]) ==> (SqnCh[Net#b][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#c]) ==> (SqnCh[Net#c][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#d]) ==> (SqnCh[Net#d][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#e]) ==> (SqnCh[Net#e][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#g]) ==> (SqnCh[Net#g][i] == i)
  );
  assume (C[Net#f] - R[Net#f]) == 1;
  assume C[Net#g] == R[Net#e];
  assume R[Net#e] == M[Net#f][R[Net#f]];
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#g]) ==> (SqnCh[Net#g][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#g][i] == M[Net#e][i])
  );
  assume R[Net#a] == C[Net#b];
  assume R[Net#a] == C[Net#c];
  assume R[Net#b] == C[Net#d];
  assume R[Net#c] == C[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#a]) ==> (SqnCh[Net#a][idx$] == idx$)
  );
  assume true;
  assume 1 <= (C[Net#c] - R[Net#c]);
  in#i := M[Net#c][R[Net#c]];
  R[Net#c] := R[Net#c] + 1;
  M[Net#e][C[Net#e]] := in#i;
  SqnCh[Net#e][C[Net#e]] := SqnAct[Net#sec];
  C[Net#e] := C[Net#e] + 1;
  SqnAct[Net#sec] := SqnAct[Net#sec] + 1;
  assert {:msg "41.15: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#75)"} SqnAct[Net#spl] == R[Net#a];
  assert {:msg "42.15: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#76)"} SqnAct[Net#pri] == R[Net#b];
  assert {:msg "43.15: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#77)"} SqnAct[Net#sec] == R[Net#c];
  assert {:msg "44.15: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#78)"} SqnAct[Net#adj] == R[Net#e];
  assert {:msg "46.16: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#79)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#a]) ==> (SqnCh[Net#a][i] == i)
  );
  assert {:msg "47.16: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#80)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#b]) ==> (SqnCh[Net#b][i] == i)
  );
  assert {:msg "48.16: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#81)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#c]) ==> (SqnCh[Net#c][i] == i)
  );
  assert {:msg "49.16: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#82)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#d]) ==> (SqnCh[Net#d][i] == i)
  );
  assert {:msg "50.16: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#83)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#e]) ==> (SqnCh[Net#e][i] == i)
  );
  assert {:msg "51.16: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#84)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#g]) ==> (SqnCh[Net#g][i] == i)
  );
  assert {:msg "53.15: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#85)"} (C[Net#f] - R[Net#f]) == 1;
  assert {:msg "54.15: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#86)"} C[Net#g] == R[Net#e];
  assert {:msg "55.15: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#87)"} R[Net#e] == M[Net#f][R[Net#f]];
  assert {:msg "56.16: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#88)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#g]) ==> (SqnCh[Net#g][i] == i)
  );
  assert {:msg "59.16: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#89)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#g][i] == M[Net#e][i])
  );
  assert {:msg "Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#90)"} R[Net#a] == C[Net#b];
  assert {:msg "Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#91)"} R[Net#a] == C[Net#c];
  assert {:msg "Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#92)"} R[Net#b] == C[Net#d];
  assert {:msg "Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#93)"} R[Net#c] == C[Net#e];
  assert {:msg "Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#94)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assert {:msg "Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#95)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assert {:msg "Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#96)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assert {:msg "Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#97)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assert {:msg "Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#98)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#a]) ==> (SqnCh[Net#a][idx$] == idx$)
  );
}
procedure Net##Adjudicator#readoff#11()
  modifies C, R, M, I, St, SqnCh, SqnAct;
{
  var St#next: State;
  var x1#i: int;
  var c_in#c: int;
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
  assume 0 <= I[Net#f];
  assume I[Net#f] <= R[Net#f];
  assume R[Net#f] <= C[Net#f];
  assume 0 <= I[Net#g];
  assume I[Net#g] <= R[Net#g];
  assume R[Net#g] <= C[Net#g];
  assume I[Net#g] == R[Net#g];
  assume SqnAct[Net#spl] == R[Net#a];
  assume SqnAct[Net#pri] == R[Net#b];
  assume SqnAct[Net#sec] == R[Net#c];
  assume SqnAct[Net#adj] == R[Net#e];
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#a]) ==> (SqnCh[Net#a][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#b]) ==> (SqnCh[Net#b][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#c]) ==> (SqnCh[Net#c][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#d]) ==> (SqnCh[Net#d][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#e]) ==> (SqnCh[Net#e][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#g]) ==> (SqnCh[Net#g][i] == i)
  );
  assume (C[Net#f] - R[Net#f]) == 1;
  assume C[Net#g] == R[Net#e];
  assume R[Net#e] == M[Net#f][R[Net#f]];
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#g]) ==> (SqnCh[Net#g][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#g][i] == M[Net#e][i])
  );
  assume R[Net#a] == C[Net#b];
  assume R[Net#a] == C[Net#c];
  assume R[Net#b] == C[Net#d];
  assume R[Net#c] == C[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#a]) ==> (SqnCh[Net#a][idx$] == idx$)
  );
  assume SqnCh[Net#d][R[Net#d] - 0] < M[Net#f][R[Net#f] - 0];
  assume true;
  assume (1 <= (C[Net#d] - R[Net#d])) && (1 <= (C[Net#f] - R[Net#f])) && (SqnCh[Net#d][R[Net#d] - 0] < M[Net#f][R[Net#f] - 0]);
  x1#i := M[Net#d][R[Net#d]];
  R[Net#d] := R[Net#d] + 1;
  c_in#c := M[Net#f][R[Net#f]];
  R[Net#f] := R[Net#f] + 1;
  M[Net#f][C[Net#f]] := c_in#c;
  SqnCh[Net#f][C[Net#f]] := SqnAct[Net#adj];
  C[Net#f] := C[Net#f] + 1;
  assert {:msg "41.15: Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#99)"} SqnAct[Net#spl] == R[Net#a];
  assert {:msg "42.15: Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#100)"} SqnAct[Net#pri] == R[Net#b];
  assert {:msg "43.15: Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#101)"} SqnAct[Net#sec] == R[Net#c];
  assert {:msg "44.15: Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#102)"} SqnAct[Net#adj] == R[Net#e];
  assert {:msg "46.16: Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#103)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#a]) ==> (SqnCh[Net#a][i] == i)
  );
  assert {:msg "47.16: Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#104)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#b]) ==> (SqnCh[Net#b][i] == i)
  );
  assert {:msg "48.16: Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#105)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#c]) ==> (SqnCh[Net#c][i] == i)
  );
  assert {:msg "49.16: Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#106)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#d]) ==> (SqnCh[Net#d][i] == i)
  );
  assert {:msg "50.16: Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#107)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#e]) ==> (SqnCh[Net#e][i] == i)
  );
  assert {:msg "51.16: Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#108)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#g]) ==> (SqnCh[Net#g][i] == i)
  );
  assert {:msg "53.15: Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#109)"} (C[Net#f] - R[Net#f]) == 1;
  assert {:msg "54.15: Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#110)"} C[Net#g] == R[Net#e];
  assert {:msg "55.15: Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#111)"} R[Net#e] == M[Net#f][R[Net#f]];
  assert {:msg "56.16: Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#112)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#g]) ==> (SqnCh[Net#g][i] == i)
  );
  assert {:msg "59.16: Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#113)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#g][i] == M[Net#e][i])
  );
  assert {:msg "Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#114)"} R[Net#a] == C[Net#b];
  assert {:msg "Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#115)"} R[Net#a] == C[Net#c];
  assert {:msg "Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#116)"} R[Net#b] == C[Net#d];
  assert {:msg "Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#117)"} R[Net#c] == C[Net#e];
  assert {:msg "Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#118)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assert {:msg "Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#119)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assert {:msg "Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#120)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assert {:msg "Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#121)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assert {:msg "Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#122)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#a]) ==> (SqnCh[Net#a][idx$] == idx$)
  );
}
procedure Net##Adjudicator#normal#12()
  modifies C, R, M, I, St, SqnCh, SqnAct;
{
  var St#next: State;
  var x1#i: int;
  var x2#j: int;
  var c_in#c: int;
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
  assume 0 <= I[Net#f];
  assume I[Net#f] <= R[Net#f];
  assume R[Net#f] <= C[Net#f];
  assume 0 <= I[Net#g];
  assume I[Net#g] <= R[Net#g];
  assume R[Net#g] <= C[Net#g];
  assume I[Net#g] == R[Net#g];
  assume SqnAct[Net#spl] == R[Net#a];
  assume SqnAct[Net#pri] == R[Net#b];
  assume SqnAct[Net#sec] == R[Net#c];
  assume SqnAct[Net#adj] == R[Net#e];
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#a]) ==> (SqnCh[Net#a][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#b]) ==> (SqnCh[Net#b][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#c]) ==> (SqnCh[Net#c][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#d]) ==> (SqnCh[Net#d][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#e]) ==> (SqnCh[Net#e][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#g]) ==> (SqnCh[Net#g][i] == i)
  );
  assume (C[Net#f] - R[Net#f]) == 1;
  assume C[Net#g] == R[Net#e];
  assume R[Net#e] == M[Net#f][R[Net#f]];
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#g]) ==> (SqnCh[Net#g][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#g][i] == M[Net#e][i])
  );
  assume R[Net#a] == C[Net#b];
  assume R[Net#a] == C[Net#c];
  assume R[Net#b] == C[Net#d];
  assume R[Net#c] == C[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#a]) ==> (SqnCh[Net#a][idx$] == idx$)
  );
  assume (SqnCh[Net#d][R[Net#d] - 0] == SqnCh[Net#e][R[Net#e] - 0]) && (SqnCh[Net#d][R[Net#d] - 0] == M[Net#f][R[Net#f] - 0]);
  assume true;
  assume (!((1 <= (C[Net#d] - R[Net#d])) && (1 <= (C[Net#f] - R[Net#f])) && (SqnCh[Net#d][R[Net#d] - 0] < M[Net#f][R[Net#f] - 0]))) && (1 <= (C[Net#d] - R[Net#d])) && (1 <= (C[Net#e] - R[Net#e])) && (1 <= (C[Net#f] - R[Net#f])) && (SqnCh[Net#d][R[Net#d] - 0] == SqnCh[Net#e][R[Net#e] - 0]) && (SqnCh[Net#d][R[Net#d] - 0] == M[Net#f][R[Net#f] - 0]);
  x1#i := M[Net#d][R[Net#d]];
  R[Net#d] := R[Net#d] + 1;
  x2#j := M[Net#e][R[Net#e]];
  R[Net#e] := R[Net#e] + 1;
  c_in#c := M[Net#f][R[Net#f]];
  R[Net#f] := R[Net#f] + 1;
  M[Net#g][C[Net#g]] := x1#i;
  SqnCh[Net#g][C[Net#g]] := SqnAct[Net#adj];
  C[Net#g] := C[Net#g] + 1;
  M[Net#f][C[Net#f]] := c_in#c + 1;
  SqnCh[Net#f][C[Net#f]] := SqnAct[Net#adj];
  C[Net#f] := C[Net#f] + 1;
  SqnAct[Net#adj] := SqnAct[Net#adj] + 1;
  assert {:msg "41.15: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#123)"} SqnAct[Net#spl] == R[Net#a];
  assert {:msg "42.15: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#124)"} SqnAct[Net#pri] == R[Net#b];
  assert {:msg "43.15: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#125)"} SqnAct[Net#sec] == R[Net#c];
  assert {:msg "44.15: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#126)"} SqnAct[Net#adj] == R[Net#e];
  assert {:msg "46.16: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#127)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#a]) ==> (SqnCh[Net#a][i] == i)
  );
  assert {:msg "47.16: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#128)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#b]) ==> (SqnCh[Net#b][i] == i)
  );
  assert {:msg "48.16: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#129)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#c]) ==> (SqnCh[Net#c][i] == i)
  );
  assert {:msg "49.16: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#130)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#d]) ==> (SqnCh[Net#d][i] == i)
  );
  assert {:msg "50.16: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#131)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#e]) ==> (SqnCh[Net#e][i] == i)
  );
  assert {:msg "51.16: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#132)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#g]) ==> (SqnCh[Net#g][i] == i)
  );
  assert {:msg "53.15: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#133)"} (C[Net#f] - R[Net#f]) == 1;
  assert {:msg "54.15: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#134)"} C[Net#g] == R[Net#e];
  assert {:msg "55.15: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#135)"} R[Net#e] == M[Net#f][R[Net#f]];
  assert {:msg "56.16: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#136)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#g]) ==> (SqnCh[Net#g][i] == i)
  );
  assert {:msg "59.16: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#137)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#g][i] == M[Net#e][i])
  );
  assert {:msg "Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#138)"} R[Net#a] == C[Net#b];
  assert {:msg "Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#139)"} R[Net#a] == C[Net#c];
  assert {:msg "Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#140)"} R[Net#b] == C[Net#d];
  assert {:msg "Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#141)"} R[Net#c] == C[Net#e];
  assert {:msg "Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#142)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assert {:msg "Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#143)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assert {:msg "Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#144)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assert {:msg "Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#145)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assert {:msg "Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#146)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#a]) ==> (SqnCh[Net#a][idx$] == idx$)
  );
}
procedure Net##Adjudicator#timeout#13()
  modifies C, R, M, I, St, SqnCh, SqnAct;
{
  var St#next: State;
  var x2#j: int;
  var c_in#c: int;
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
  assume 0 <= I[Net#f];
  assume I[Net#f] <= R[Net#f];
  assume R[Net#f] <= C[Net#f];
  assume 0 <= I[Net#g];
  assume I[Net#g] <= R[Net#g];
  assume R[Net#g] <= C[Net#g];
  assume I[Net#g] == R[Net#g];
  assume SqnAct[Net#spl] == R[Net#a];
  assume SqnAct[Net#pri] == R[Net#b];
  assume SqnAct[Net#sec] == R[Net#c];
  assume SqnAct[Net#adj] == R[Net#e];
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#a]) ==> (SqnCh[Net#a][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#b]) ==> (SqnCh[Net#b][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#c]) ==> (SqnCh[Net#c][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#d]) ==> (SqnCh[Net#d][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#e]) ==> (SqnCh[Net#e][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#g]) ==> (SqnCh[Net#g][i] == i)
  );
  assume (C[Net#f] - R[Net#f]) == 1;
  assume C[Net#g] == R[Net#e];
  assume R[Net#e] == M[Net#f][R[Net#f]];
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#g]) ==> (SqnCh[Net#g][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#g][i] == M[Net#e][i])
  );
  assume R[Net#a] == C[Net#b];
  assume R[Net#a] == C[Net#c];
  assume R[Net#b] == C[Net#d];
  assume R[Net#c] == C[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#a]) ==> (SqnCh[Net#a][idx$] == idx$)
  );
  assume true;
  assume (!((1 <= (C[Net#d] - R[Net#d])) && (1 <= (C[Net#f] - R[Net#f])) && (SqnCh[Net#d][R[Net#d] - 0] < M[Net#f][R[Net#f] - 0]))) && (!((1 <= (C[Net#d] - R[Net#d])) && (1 <= (C[Net#e] - R[Net#e])) && (1 <= (C[Net#f] - R[Net#f])) && (SqnCh[Net#d][R[Net#d] - 0] == SqnCh[Net#e][R[Net#e] - 0]) && (SqnCh[Net#d][R[Net#d] - 0] == M[Net#f][R[Net#f] - 0]))) && (1 <= (C[Net#e] - R[Net#e])) && (1 <= (C[Net#f] - R[Net#f]));
  x2#j := M[Net#e][R[Net#e]];
  R[Net#e] := R[Net#e] + 1;
  c_in#c := M[Net#f][R[Net#f]];
  R[Net#f] := R[Net#f] + 1;
  M[Net#g][C[Net#g]] := x2#j;
  SqnCh[Net#g][C[Net#g]] := SqnAct[Net#adj];
  C[Net#g] := C[Net#g] + 1;
  M[Net#f][C[Net#f]] := c_in#c + 1;
  SqnCh[Net#f][C[Net#f]] := SqnAct[Net#adj];
  C[Net#f] := C[Net#f] + 1;
  SqnAct[Net#adj] := SqnAct[Net#adj] + 1;
  assert {:msg "41.15: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#147)"} SqnAct[Net#spl] == R[Net#a];
  assert {:msg "42.15: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#148)"} SqnAct[Net#pri] == R[Net#b];
  assert {:msg "43.15: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#149)"} SqnAct[Net#sec] == R[Net#c];
  assert {:msg "44.15: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#150)"} SqnAct[Net#adj] == R[Net#e];
  assert {:msg "46.16: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#151)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#a]) ==> (SqnCh[Net#a][i] == i)
  );
  assert {:msg "47.16: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#152)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#b]) ==> (SqnCh[Net#b][i] == i)
  );
  assert {:msg "48.16: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#153)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#c]) ==> (SqnCh[Net#c][i] == i)
  );
  assert {:msg "49.16: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#154)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#d]) ==> (SqnCh[Net#d][i] == i)
  );
  assert {:msg "50.16: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#155)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#e]) ==> (SqnCh[Net#e][i] == i)
  );
  assert {:msg "51.16: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#156)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#g]) ==> (SqnCh[Net#g][i] == i)
  );
  assert {:msg "53.15: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#157)"} (C[Net#f] - R[Net#f]) == 1;
  assert {:msg "54.15: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#158)"} C[Net#g] == R[Net#e];
  assert {:msg "55.15: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#159)"} R[Net#e] == M[Net#f][R[Net#f]];
  assert {:msg "56.16: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#160)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#g]) ==> (SqnCh[Net#g][i] == i)
  );
  assert {:msg "59.16: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#161)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#g][i] == M[Net#e][i])
  );
  assert {:msg "Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#162)"} R[Net#a] == C[Net#b];
  assert {:msg "Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#163)"} R[Net#a] == C[Net#c];
  assert {:msg "Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#164)"} R[Net#b] == C[Net#d];
  assert {:msg "Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#165)"} R[Net#c] == C[Net#e];
  assert {:msg "Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#166)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assert {:msg "Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#167)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assert {:msg "Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#168)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assert {:msg "Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#169)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assert {:msg "Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#170)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#a]) ==> (SqnCh[Net#a][idx$] == idx$)
  );
}
procedure Net#anon$3#entry#14()
  modifies C, R, M, I, St, SqnCh, SqnAct;
{
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
  assume 0 <= I[Net#f];
  assume I[Net#f] <= R[Net#f];
  assume R[Net#f] <= C[Net#f];
  assume 0 <= I[Net#g];
  assume I[Net#g] <= R[Net#g];
  assume R[Net#g] <= C[Net#g];
  assume I[Net#g] == R[Net#g];
  assume I == R;
  assume R[Net#a] == C[Net#a];
  assume R[Net#b] == C[Net#b];
  assume R[Net#c] == C[Net#c];
  assume R[Net#d] == C[Net#d];
  assume R[Net#e] == C[Net#e];
  assume R[Net#f] == C[Net#f];
  assume R[Net#g] == C[Net#g];
  C[Net#f] := C[Net#f] + 1;
  assume R[Net#e] == M[Net#f][R[Net#f]];
  assume SqnAct[Net#spl] == R[Net#a];
  assume SqnAct[Net#pri] == R[Net#b];
  assume SqnAct[Net#sec] == R[Net#c];
  assume SqnAct[Net#adj] == R[Net#e];
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#a]) ==> (SqnCh[Net#a][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#b]) ==> (SqnCh[Net#b][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#c]) ==> (SqnCh[Net#c][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#d]) ==> (SqnCh[Net#d][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#e]) ==> (SqnCh[Net#e][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#g]) ==> (SqnCh[Net#g][i] == i)
  );
  assume (C[Net#f] - R[Net#f]) == 1;
  assume C[Net#g] == R[Net#e];
  assume R[Net#e] == M[Net#f][R[Net#f]];
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#g]) ==> (SqnCh[Net#g][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#g][i] == M[Net#e][i])
  );
  assume R[Net#a] == C[Net#b];
  assume R[Net#a] == C[Net#c];
  assume R[Net#b] == C[Net#d];
  assume R[Net#c] == C[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#a]) ==> (SqnCh[Net#a][idx$] == idx$)
  );
}
procedure Net#anon$3#input#in#15()
  modifies C, R, M, I, St, SqnCh, SqnAct;
{
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
  assume 0 <= I[Net#f];
  assume I[Net#f] <= R[Net#f];
  assume R[Net#f] <= C[Net#f];
  assume 0 <= I[Net#g];
  assume I[Net#g] <= R[Net#g];
  assume R[Net#g] <= C[Net#g];
  assume I[Net#g] == R[Net#g];
  assume C[Net#a] < 1;
  assume SqnAct[Net#spl] == R[Net#a];
  assume SqnAct[Net#pri] == R[Net#b];
  assume SqnAct[Net#sec] == R[Net#c];
  assume SqnAct[Net#adj] == R[Net#e];
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#a]) ==> (SqnCh[Net#a][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#b]) ==> (SqnCh[Net#b][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#c]) ==> (SqnCh[Net#c][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#d]) ==> (SqnCh[Net#d][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#e]) ==> (SqnCh[Net#e][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#g]) ==> (SqnCh[Net#g][i] == i)
  );
  assume (C[Net#f] - R[Net#f]) == 1;
  assume C[Net#g] == R[Net#e];
  assume R[Net#e] == M[Net#f][R[Net#f]];
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#g]) ==> (SqnCh[Net#g][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#g][i] == M[Net#e][i])
  );
  assume R[Net#a] == C[Net#b];
  assume R[Net#a] == C[Net#c];
  assume R[Net#b] == C[Net#d];
  assume R[Net#c] == C[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#a]) ==> (SqnCh[Net#a][idx$] == idx$)
  );
  C[Net#a] := C[Net#a] + 1;
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#a]) ==> (SqnCh[Net#a][i] == i)
  );
  assert {:msg "41.15: Channel invariant might be falsified by network input"} SqnAct[Net#spl] == R[Net#a];
  assert {:msg "42.15: Channel invariant might be falsified by network input"} SqnAct[Net#pri] == R[Net#b];
  assert {:msg "43.15: Channel invariant might be falsified by network input"} SqnAct[Net#sec] == R[Net#c];
  assert {:msg "44.15: Channel invariant might be falsified by network input"} SqnAct[Net#adj] == R[Net#e];
  assert {:msg "46.16: Channel invariant might be falsified by network input"} (forall i: int :: 
    (0 <= i) && (i < C[Net#a]) ==> (SqnCh[Net#a][i] == i)
  );
  assert {:msg "47.16: Channel invariant might be falsified by network input"} (forall i: int :: 
    (0 <= i) && (i < C[Net#b]) ==> (SqnCh[Net#b][i] == i)
  );
  assert {:msg "48.16: Channel invariant might be falsified by network input"} (forall i: int :: 
    (0 <= i) && (i < C[Net#c]) ==> (SqnCh[Net#c][i] == i)
  );
  assert {:msg "49.16: Channel invariant might be falsified by network input"} (forall i: int :: 
    (0 <= i) && (i < C[Net#d]) ==> (SqnCh[Net#d][i] == i)
  );
  assert {:msg "50.16: Channel invariant might be falsified by network input"} (forall i: int :: 
    (0 <= i) && (i < C[Net#e]) ==> (SqnCh[Net#e][i] == i)
  );
  assert {:msg "51.16: Channel invariant might be falsified by network input"} (forall i: int :: 
    (0 <= i) && (i < C[Net#g]) ==> (SqnCh[Net#g][i] == i)
  );
  assert {:msg "53.15: Channel invariant might be falsified by network input"} (C[Net#f] - R[Net#f]) == 1;
  assert {:msg "54.15: Channel invariant might be falsified by network input"} C[Net#g] == R[Net#e];
  assert {:msg "55.15: Channel invariant might be falsified by network input"} R[Net#e] == M[Net#f][R[Net#f]];
  assert {:msg "56.16: Channel invariant might be falsified by network input"} (forall i: int :: 
    (0 <= i) && (i < C[Net#g]) ==> (SqnCh[Net#g][i] == i)
  );
  assert {:msg "59.16: Channel invariant might be falsified by network input"} (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#g][i] == M[Net#e][i])
  );
  assert {:msg "Channel invariant might be falsified by network input"} R[Net#a] == C[Net#b];
  assert {:msg "Channel invariant might be falsified by network input"} R[Net#a] == C[Net#c];
  assert {:msg "Channel invariant might be falsified by network input"} R[Net#b] == C[Net#d];
  assert {:msg "Channel invariant might be falsified by network input"} R[Net#c] == C[Net#e];
  assert {:msg "Channel invariant might be falsified by network input"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assert {:msg "Channel invariant might be falsified by network input"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assert {:msg "Channel invariant might be falsified by network input"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assert {:msg "Channel invariant might be falsified by network input"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assert {:msg "Channel invariant might be falsified by network input"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#a]) ==> (SqnCh[Net#a][idx$] == idx$)
  );
}
procedure Net#anon$3#exit#16()
  modifies C, R, M, I, St, SqnCh, SqnAct;
{
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
  assume 0 <= I[Net#f];
  assume I[Net#f] <= R[Net#f];
  assume R[Net#f] <= C[Net#f];
  assume 0 <= I[Net#g];
  assume I[Net#g] <= R[Net#g];
  assume R[Net#g] <= C[Net#g];
  assume I[Net#g] == R[Net#g];
  assume SqnAct[Net#spl] == R[Net#a];
  assume SqnAct[Net#pri] == R[Net#b];
  assume SqnAct[Net#sec] == R[Net#c];
  assume SqnAct[Net#adj] == R[Net#e];
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#a]) ==> (SqnCh[Net#a][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#b]) ==> (SqnCh[Net#b][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#c]) ==> (SqnCh[Net#c][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#d]) ==> (SqnCh[Net#d][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#e]) ==> (SqnCh[Net#e][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#g]) ==> (SqnCh[Net#g][i] == i)
  );
  assume (C[Net#f] - R[Net#f]) == 1;
  assume C[Net#g] == R[Net#e];
  assume R[Net#e] == M[Net#f][R[Net#f]];
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#g]) ==> (SqnCh[Net#g][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#g][i] == M[Net#e][i])
  );
  assume R[Net#a] == C[Net#b];
  assume R[Net#a] == C[Net#c];
  assume R[Net#b] == C[Net#d];
  assume R[Net#c] == C[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#a]) ==> (SqnCh[Net#a][idx$] == idx$)
  );
  assume (C[Net#a] - I[Net#a]) == 1;
  assume !(1 <= (C[Net#a] - R[Net#a]));
  assume !(1 <= (C[Net#b] - R[Net#b]));
  assume !(1 <= (C[Net#c] - R[Net#c]));
  assume !((!((1 <= (C[Net#d] - R[Net#d])) && (1 <= (C[Net#f] - R[Net#f])) && (SqnCh[Net#d][R[Net#d] - 0] < M[Net#f][R[Net#f] - 0]))) && (1 <= (C[Net#d] - R[Net#d])) && (1 <= (C[Net#e] - R[Net#e])) && (1 <= (C[Net#f] - R[Net#f])) && (SqnCh[Net#d][R[Net#d] - 0] == SqnCh[Net#e][R[Net#e] - 0]) && (SqnCh[Net#d][R[Net#d] - 0] == M[Net#f][R[Net#f] - 0]));
  assume !((!((1 <= (C[Net#d] - R[Net#d])) && (1 <= (C[Net#f] - R[Net#f])) && (SqnCh[Net#d][R[Net#d] - 0] < M[Net#f][R[Net#f] - 0]))) && (!((1 <= (C[Net#d] - R[Net#d])) && (1 <= (C[Net#e] - R[Net#e])) && (1 <= (C[Net#f] - R[Net#f])) && (SqnCh[Net#d][R[Net#d] - 0] == SqnCh[Net#e][R[Net#e] - 0]) && (SqnCh[Net#d][R[Net#d] - 0] == M[Net#f][R[Net#f] - 0]))) && (1 <= (C[Net#e] - R[Net#e])) && (1 <= (C[Net#f] - R[Net#f])));
  assume !((1 <= (C[Net#d] - R[Net#d])) && (1 <= (C[Net#f] - R[Net#f])) && (SqnCh[Net#d][R[Net#d] - 0] < M[Net#f][R[Net#f] - 0]));
  assert {:msg "34.14: Network action postcondition might not hold"} (forall i: int :: 
    (0 <= i) && (i < C[Net#g]) ==> (SqnCh[Net#g][i] == i)
  );
  assert {:msg "35.14: Network action postcondition might not hold"} (forall i: int :: 
    (0 <= i) && (i < C[Net#g]) ==> (M[Net#g][i] == M[Net#a][i])
  );
  R[Net#g] := R[Net#g] + 1;
  I := R;
  assert {:msg "41.15: The network might not preserve the channel invariant (#171)"} SqnAct[Net#spl] == R[Net#a];
  assert {:msg "42.15: The network might not preserve the channel invariant (#172)"} SqnAct[Net#pri] == R[Net#b];
  assert {:msg "43.15: The network might not preserve the channel invariant (#173)"} SqnAct[Net#sec] == R[Net#c];
  assert {:msg "44.15: The network might not preserve the channel invariant (#174)"} SqnAct[Net#adj] == R[Net#e];
  assert {:msg "46.16: The network might not preserve the channel invariant (#175)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#a]) ==> (SqnCh[Net#a][i] == i)
  );
  assert {:msg "47.16: The network might not preserve the channel invariant (#176)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#b]) ==> (SqnCh[Net#b][i] == i)
  );
  assert {:msg "48.16: The network might not preserve the channel invariant (#177)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#c]) ==> (SqnCh[Net#c][i] == i)
  );
  assert {:msg "49.16: The network might not preserve the channel invariant (#178)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#d]) ==> (SqnCh[Net#d][i] == i)
  );
  assert {:msg "50.16: The network might not preserve the channel invariant (#179)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#e]) ==> (SqnCh[Net#e][i] == i)
  );
  assert {:msg "51.16: The network might not preserve the channel invariant (#180)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#g]) ==> (SqnCh[Net#g][i] == i)
  );
  assert {:msg "53.15: The network might not preserve the channel invariant (#181)"} (C[Net#f] - R[Net#f]) == 1;
  assert {:msg "54.15: The network might not preserve the channel invariant (#182)"} C[Net#g] == R[Net#e];
  assert {:msg "55.15: The network might not preserve the channel invariant (#183)"} R[Net#e] == M[Net#f][R[Net#f]];
  assert {:msg "56.16: The network might not preserve the channel invariant (#184)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#g]) ==> (SqnCh[Net#g][i] == i)
  );
  assert {:msg "59.16: The network might not preserve the channel invariant (#185)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#g][i] == M[Net#e][i])
  );
  assert {:msg "The network might not preserve the channel invariant (#186)"} R[Net#a] == C[Net#b];
  assert {:msg "The network might not preserve the channel invariant (#187)"} R[Net#a] == C[Net#c];
  assert {:msg "The network might not preserve the channel invariant (#188)"} R[Net#b] == C[Net#d];
  assert {:msg "The network might not preserve the channel invariant (#189)"} R[Net#c] == C[Net#e];
  assert {:msg "The network might not preserve the channel invariant (#190)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assert {:msg "The network might not preserve the channel invariant (#191)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assert {:msg "The network might not preserve the channel invariant (#192)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assert {:msg "The network might not preserve the channel invariant (#193)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assert {:msg "The network might not preserve the channel invariant (#194)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#a]) ==> (SqnCh[Net#a][idx$] == idx$)
  );
  C[Net#f] := C[Net#f] - 1;
  assert {:msg "39.13: The network might not preserve the network invariant"} R[Net#e] == M[Net#f][R[Net#f]];
  assert {:msg "32.3: The network might leave unread tokens on channel a"} C[Net#a] == R[Net#a];
  assert {:msg "32.3: The network might leave unread tokens on channel b"} C[Net#b] == R[Net#b];
  assert {:msg "32.3: The network might leave unread tokens on channel c"} C[Net#c] == R[Net#c];
  assert {:msg "32.3: The network might leave unread tokens on channel d"} C[Net#d] == R[Net#d];
  assert {:msg "32.3: The network might leave unread tokens on channel e"} C[Net#e] == R[Net#e];
  assert {:msg "32.3: The network might leave unread tokens on channel f"} C[Net#f] == R[Net#f];
  assert {:msg "32.3: The network might not produce the specified number of tokens on output out"} C[Net#g] == R[Net#g];
}

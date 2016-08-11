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
var L: CType;
var St: [Actor]State;
const Base#L: int;
axiom 1 <= Base#L;

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

axiom Base#L == 1;
procedure Rep#anon$0#0()
  modifies C, R, M, St, SqnCh, SqnAct;
{
  var in: Chan (int);
  var out: Chan (int);
  assume true;
  assume true;
}
procedure Split#anon$1#1()
  modifies C, R, M, St, SqnCh, SqnAct;
{
  var in: Chan (int);
  var out1: Chan (int);
  var out2: Chan (int);
  assume true;
  assume true;
}
procedure Adjudicator#normal#2()
  modifies C, R, M, St, SqnCh, SqnAct;
{
  var x1: Chan (int);
  var x2: Chan (int);
  var c_in: Chan (int);
  var y: Chan (int);
  var c_out: Chan (int);
  assume true;
  assume (SqnCh[x1][0] == SqnCh[x2][0]) && (SqnCh[x1][0] == M[c_in][0]);
  assume true;
}
procedure Adjudicator#timeout#3()
  modifies C, R, M, St, SqnCh, SqnAct;
{
  var x1: Chan (int);
  var x2: Chan (int);
  var c_in: Chan (int);
  var y: Chan (int);
  var c_out: Chan (int);
  assume true;
  assume true;
}
procedure Adjudicator#readoff#4()
  modifies C, R, M, St, SqnCh, SqnAct;
{
  var x1: Chan (int);
  var x2: Chan (int);
  var c_in: Chan (int);
  var y: Chan (int);
  var c_out: Chan (int);
  assume true;
  assume SqnCh[x1][0] < M[c_in][0];
  assume true;
}
procedure Adjudicator#anon$2#5()
  modifies C, R, M, St, SqnCh, SqnAct;
{
  var x1: Chan (int);
  var x2: Chan (int);
  var c_in: Chan (int);
  var y: Chan (int);
  var c_out: Chan (int);
  assume true;
  assume true;
}
procedure Net#init#6()
  modifies C, R, M, St, SqnCh, SqnAct;
{
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
  M[Net#f][R[Net#f] + C[Net#f]] := 0;
  C[Net#f] := C[Net#f] + 1;
  assert {:msg "  Network initialization might not establish the channel invariant"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  Network initialization might not establish the channel invariant"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Network initialization might not establish the channel invariant"} R[Net#b] == (R[Net#d] + C[Net#d]);
  assert {:msg "  Network initialization might not establish the channel invariant"} R[Net#c] == (R[Net#e] + C[Net#e]);
  assert {:msg "  Network initialization might not establish the channel invariant"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Network initialization might not establish the channel invariant"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Network initialization might not establish the channel invariant"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assert {:msg "  Network initialization might not establish the channel invariant"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#e] + C[Net#e])) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assert {:msg "  Network initialization might not establish the channel invariant"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][idx$] == idx$)
  );
  assert {:msg "  40.15: Network initialization might not establish the channel invariant"} SqnAct[Net#spl] == R[Net#a];
  assert {:msg "  41.15: Network initialization might not establish the channel invariant"} SqnAct[Net#pri] == R[Net#b];
  assert {:msg "  42.15: Network initialization might not establish the channel invariant"} SqnAct[Net#sec] == R[Net#c];
  assert {:msg "  43.15: Network initialization might not establish the channel invariant"} SqnAct[Net#adj] == R[Net#e];
  assert {:msg "  45.16: Network initialization might not establish the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][i] == i)
  );
  assert {:msg "  46.16: Network initialization might not establish the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (SqnCh[Net#b][i] == i)
  );
  assert {:msg "  47.16: Network initialization might not establish the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (SqnCh[Net#c][i] == i)
  );
  assert {:msg "  48.16: Network initialization might not establish the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (SqnCh[Net#d][i] == i)
  );
  assert {:msg "  49.16: Network initialization might not establish the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (SqnCh[Net#e][i] == i)
  );
  assert {:msg "  50.16: Network initialization might not establish the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#g] + C[Net#g])) ==> (SqnCh[Net#g][i] == i)
  );
  assert {:msg "  52.15: Network initialization might not establish the channel invariant"} C[Net#f] == 1;
  assert {:msg "  53.15: Network initialization might not establish the channel invariant"} (R[Net#g] + C[Net#g]) == R[Net#e];
  assert {:msg "  54.15: Network initialization might not establish the channel invariant"} R[Net#e] == M[Net#f][R[Net#f]];
  assert {:msg "  55.16: Network initialization might not establish the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#g] + C[Net#g])) ==> (SqnCh[Net#g][i] == i)
  );
  if ((0 < R[Net#d]) && (0 < R[Net#e])) {
    assert {:msg "  57.42: Network initialization might not establish the channel invariant"} M[Net#d][R[Net#d] - 1] <= M[Net#e][R[Net#e] - 1];
  }
  assert {:msg "  58.16: Network initialization might not establish the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#g][i] == M[Net#e][i])
  );
  C[Net#f] := C[Net#f] - 1;
  assert {:msg "  38.13: Network initialization might not establish the network invariant"} R[Net#e] == M[Net#f][R[Net#f]];
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
procedure Net#anon$3#entry#7()
  modifies C, R, M, St, SqnCh, SqnAct;
{
  assume L[Net#a] == (1 * Base#L);
  assume C[Net#a] == 0;
  assume C[Net#b] == 0;
  assume C[Net#c] == 0;
  assume C[Net#d] == 0;
  assume C[Net#e] == 0;
  assume C[Net#f] == 0;
  assume C[Net#g] == 0;
  C[Net#f] := C[Net#f] + 1;
  assume R[Net#e] == M[Net#f][R[Net#f]];
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) <= L[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume 0 <= R[Net#d];
  assume 0 <= C[Net#d];
  assume 0 <= R[Net#e];
  assume 0 <= C[Net#e];
  assume 0 <= R[Net#f];
  assume 0 <= C[Net#f];
  assume 0 <= R[Net#g];
  assume 0 <= C[Net#g];
  assume R[Net#g] == 0;
  assume R[Net#a] == (R[Net#b] + C[Net#b]);
  assume R[Net#a] == (R[Net#c] + C[Net#c]);
  assume R[Net#b] == (R[Net#d] + C[Net#d]);
  assume R[Net#c] == (R[Net#e] + C[Net#e]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#e] + C[Net#e])) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][idx$] == idx$)
  );
  assume SqnAct[Net#spl] == R[Net#a];
  assume SqnAct[Net#pri] == R[Net#b];
  assume SqnAct[Net#sec] == R[Net#c];
  assume SqnAct[Net#adj] == R[Net#e];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (SqnCh[Net#b][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (SqnCh[Net#c][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (SqnCh[Net#d][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (SqnCh[Net#e][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#g] + C[Net#g])) ==> (SqnCh[Net#g][i] == i)
  );
  assume C[Net#f] == 1;
  assume (R[Net#g] + C[Net#g]) == R[Net#e];
  assume R[Net#e] == M[Net#f][R[Net#f]];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#g] + C[Net#g])) ==> (SqnCh[Net#g][i] == i)
  );
  if ((0 < R[Net#d]) && (0 < R[Net#e])) {
    assume M[Net#d][R[Net#d] - 1] <= M[Net#e][R[Net#e] - 1];
  }
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#g][i] == M[Net#e][i])
  );
  assert {:msg "  Channel invariant might not hold on action entry (#0)"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  Channel invariant might not hold on action entry (#1)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Channel invariant might not hold on action entry (#2)"} R[Net#b] == (R[Net#d] + C[Net#d]);
  assert {:msg "  Channel invariant might not hold on action entry (#3)"} R[Net#c] == (R[Net#e] + C[Net#e]);
  assert {:msg "  Channel invariant might not hold on action entry (#4)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Channel invariant might not hold on action entry (#5)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Channel invariant might not hold on action entry (#6)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assert {:msg "  Channel invariant might not hold on action entry (#7)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#e] + C[Net#e])) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assert {:msg "  Channel invariant might not hold on action entry (#8)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][idx$] == idx$)
  );
  assert {:msg "  40.15: Channel invariant might not hold on action entry (#9)"} SqnAct[Net#spl] == R[Net#a];
  assert {:msg "  41.15: Channel invariant might not hold on action entry (#10)"} SqnAct[Net#pri] == R[Net#b];
  assert {:msg "  42.15: Channel invariant might not hold on action entry (#11)"} SqnAct[Net#sec] == R[Net#c];
  assert {:msg "  43.15: Channel invariant might not hold on action entry (#12)"} SqnAct[Net#adj] == R[Net#e];
  assert {:msg "  45.16: Channel invariant might not hold on action entry (#13)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][i] == i)
  );
  assert {:msg "  46.16: Channel invariant might not hold on action entry (#14)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (SqnCh[Net#b][i] == i)
  );
  assert {:msg "  47.16: Channel invariant might not hold on action entry (#15)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (SqnCh[Net#c][i] == i)
  );
  assert {:msg "  48.16: Channel invariant might not hold on action entry (#16)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (SqnCh[Net#d][i] == i)
  );
  assert {:msg "  49.16: Channel invariant might not hold on action entry (#17)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (SqnCh[Net#e][i] == i)
  );
  assert {:msg "  50.16: Channel invariant might not hold on action entry (#18)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#g] + C[Net#g])) ==> (SqnCh[Net#g][i] == i)
  );
  assert {:msg "  52.15: Channel invariant might not hold on action entry (#19)"} C[Net#f] == 1;
  assert {:msg "  53.15: Channel invariant might not hold on action entry (#20)"} (R[Net#g] + C[Net#g]) == R[Net#e];
  assert {:msg "  54.15: Channel invariant might not hold on action entry (#21)"} R[Net#e] == M[Net#f][R[Net#f]];
  assert {:msg "  55.16: Channel invariant might not hold on action entry (#22)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#g] + C[Net#g])) ==> (SqnCh[Net#g][i] == i)
  );
  if ((0 < R[Net#d]) && (0 < R[Net#e])) {
    assert {:msg "  57.42: Channel invariant might not hold on action entry (#23)"} M[Net#d][R[Net#d] - 1] <= M[Net#e][R[Net#e] - 1];
  }
  assert {:msg "  58.16: Channel invariant might not hold on action entry (#24)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#g][i] == M[Net#e][i])
  );
}
procedure Net#anon$3#Split#anon$1#8()
  modifies C, R, M, St, SqnCh, SqnAct;
{
  var St#next: State;
  var in#i: int;
  assume L[Net#a] == (1 * Base#L);
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) <= L[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume 0 <= R[Net#d];
  assume 0 <= C[Net#d];
  assume 0 <= R[Net#e];
  assume 0 <= C[Net#e];
  assume 0 <= R[Net#f];
  assume 0 <= C[Net#f];
  assume 0 <= R[Net#g];
  assume 0 <= C[Net#g];
  assume R[Net#g] == 0;
  assume R[Net#a] == (R[Net#b] + C[Net#b]);
  assume R[Net#a] == (R[Net#c] + C[Net#c]);
  assume R[Net#b] == (R[Net#d] + C[Net#d]);
  assume R[Net#c] == (R[Net#e] + C[Net#e]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#e] + C[Net#e])) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][idx$] == idx$)
  );
  assume SqnAct[Net#spl] == R[Net#a];
  assume SqnAct[Net#pri] == R[Net#b];
  assume SqnAct[Net#sec] == R[Net#c];
  assume SqnAct[Net#adj] == R[Net#e];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (SqnCh[Net#b][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (SqnCh[Net#c][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (SqnCh[Net#d][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (SqnCh[Net#e][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#g] + C[Net#g])) ==> (SqnCh[Net#g][i] == i)
  );
  assume C[Net#f] == 1;
  assume (R[Net#g] + C[Net#g]) == R[Net#e];
  assume R[Net#e] == M[Net#f][R[Net#f]];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#g] + C[Net#g])) ==> (SqnCh[Net#g][i] == i)
  );
  if ((0 < R[Net#d]) && (0 < R[Net#e])) {
    assume M[Net#d][R[Net#d] - 1] <= M[Net#e][R[Net#e] - 1];
  }
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#g][i] == M[Net#e][i])
  );
  assume true;
  assume 1 <= C[Net#a];
  in#i := M[Net#a][R[Net#a]];
  R[Net#a] := R[Net#a] + 1;
  C[Net#a] := C[Net#a] - 1;
  M[Net#b][R[Net#b] + C[Net#b]] := in#i;
  SqnCh[Net#b][R[Net#b] + C[Net#b]] := SqnAct[Net#spl];
  C[Net#b] := C[Net#b] + 1;
  M[Net#c][R[Net#c] + C[Net#c]] := in#i;
  SqnCh[Net#c][R[Net#c] + C[Net#c]] := SqnAct[Net#spl];
  C[Net#c] := C[Net#c] + 1;
  SqnAct[Net#spl] := SqnAct[Net#spl] + 1;
  assert {:msg "  Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#25)"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#26)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#27)"} R[Net#b] == (R[Net#d] + C[Net#d]);
  assert {:msg "  Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#28)"} R[Net#c] == (R[Net#e] + C[Net#e]);
  assert {:msg "  Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#29)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#30)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#31)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assert {:msg "  Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#32)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#e] + C[Net#e])) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assert {:msg "  Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#33)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][idx$] == idx$)
  );
  assert {:msg "  40.15: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#34)"} SqnAct[Net#spl] == R[Net#a];
  assert {:msg "  41.15: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#35)"} SqnAct[Net#pri] == R[Net#b];
  assert {:msg "  42.15: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#36)"} SqnAct[Net#sec] == R[Net#c];
  assert {:msg "  43.15: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#37)"} SqnAct[Net#adj] == R[Net#e];
  assert {:msg "  45.16: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#38)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][i] == i)
  );
  assert {:msg "  46.16: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#39)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (SqnCh[Net#b][i] == i)
  );
  assert {:msg "  47.16: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#40)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (SqnCh[Net#c][i] == i)
  );
  assert {:msg "  48.16: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#41)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (SqnCh[Net#d][i] == i)
  );
  assert {:msg "  49.16: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#42)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (SqnCh[Net#e][i] == i)
  );
  assert {:msg "  50.16: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#43)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#g] + C[Net#g])) ==> (SqnCh[Net#g][i] == i)
  );
  assert {:msg "  52.15: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#44)"} C[Net#f] == 1;
  assert {:msg "  53.15: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#45)"} (R[Net#g] + C[Net#g]) == R[Net#e];
  assert {:msg "  54.15: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#46)"} R[Net#e] == M[Net#f][R[Net#f]];
  assert {:msg "  55.16: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#47)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#g] + C[Net#g])) ==> (SqnCh[Net#g][i] == i)
  );
  if ((0 < R[Net#d]) && (0 < R[Net#e])) {
    assert {:msg "  57.42: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#48)"} M[Net#d][R[Net#d] - 1] <= M[Net#e][R[Net#e] - 1];
  }
  assert {:msg "  58.16: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#49)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#g][i] == M[Net#e][i])
  );
}
procedure Net#anon$3#Rep#anon$0#9()
  modifies C, R, M, St, SqnCh, SqnAct;
{
  var St#next: State;
  var in#i: int;
  assume L[Net#a] == (1 * Base#L);
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) <= L[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume 0 <= R[Net#d];
  assume 0 <= C[Net#d];
  assume 0 <= R[Net#e];
  assume 0 <= C[Net#e];
  assume 0 <= R[Net#f];
  assume 0 <= C[Net#f];
  assume 0 <= R[Net#g];
  assume 0 <= C[Net#g];
  assume R[Net#g] == 0;
  assume R[Net#a] == (R[Net#b] + C[Net#b]);
  assume R[Net#a] == (R[Net#c] + C[Net#c]);
  assume R[Net#b] == (R[Net#d] + C[Net#d]);
  assume R[Net#c] == (R[Net#e] + C[Net#e]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#e] + C[Net#e])) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][idx$] == idx$)
  );
  assume SqnAct[Net#spl] == R[Net#a];
  assume SqnAct[Net#pri] == R[Net#b];
  assume SqnAct[Net#sec] == R[Net#c];
  assume SqnAct[Net#adj] == R[Net#e];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (SqnCh[Net#b][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (SqnCh[Net#c][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (SqnCh[Net#d][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (SqnCh[Net#e][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#g] + C[Net#g])) ==> (SqnCh[Net#g][i] == i)
  );
  assume C[Net#f] == 1;
  assume (R[Net#g] + C[Net#g]) == R[Net#e];
  assume R[Net#e] == M[Net#f][R[Net#f]];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#g] + C[Net#g])) ==> (SqnCh[Net#g][i] == i)
  );
  if ((0 < R[Net#d]) && (0 < R[Net#e])) {
    assume M[Net#d][R[Net#d] - 1] <= M[Net#e][R[Net#e] - 1];
  }
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#g][i] == M[Net#e][i])
  );
  assume true;
  assume 1 <= C[Net#b];
  in#i := M[Net#b][R[Net#b]];
  R[Net#b] := R[Net#b] + 1;
  C[Net#b] := C[Net#b] - 1;
  M[Net#d][R[Net#d] + C[Net#d]] := in#i;
  SqnCh[Net#d][R[Net#d] + C[Net#d]] := SqnAct[Net#pri];
  C[Net#d] := C[Net#d] + 1;
  SqnAct[Net#pri] := SqnAct[Net#pri] + 1;
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#50)"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#51)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#52)"} R[Net#b] == (R[Net#d] + C[Net#d]);
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#53)"} R[Net#c] == (R[Net#e] + C[Net#e]);
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#54)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#55)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#56)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#57)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#e] + C[Net#e])) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#58)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][idx$] == idx$)
  );
  assert {:msg "  40.15: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#59)"} SqnAct[Net#spl] == R[Net#a];
  assert {:msg "  41.15: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#60)"} SqnAct[Net#pri] == R[Net#b];
  assert {:msg "  42.15: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#61)"} SqnAct[Net#sec] == R[Net#c];
  assert {:msg "  43.15: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#62)"} SqnAct[Net#adj] == R[Net#e];
  assert {:msg "  45.16: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#63)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][i] == i)
  );
  assert {:msg "  46.16: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#64)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (SqnCh[Net#b][i] == i)
  );
  assert {:msg "  47.16: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#65)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (SqnCh[Net#c][i] == i)
  );
  assert {:msg "  48.16: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#66)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (SqnCh[Net#d][i] == i)
  );
  assert {:msg "  49.16: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#67)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (SqnCh[Net#e][i] == i)
  );
  assert {:msg "  50.16: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#68)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#g] + C[Net#g])) ==> (SqnCh[Net#g][i] == i)
  );
  assert {:msg "  52.15: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#69)"} C[Net#f] == 1;
  assert {:msg "  53.15: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#70)"} (R[Net#g] + C[Net#g]) == R[Net#e];
  assert {:msg "  54.15: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#71)"} R[Net#e] == M[Net#f][R[Net#f]];
  assert {:msg "  55.16: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#72)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#g] + C[Net#g])) ==> (SqnCh[Net#g][i] == i)
  );
  if ((0 < R[Net#d]) && (0 < R[Net#e])) {
    assert {:msg "  57.42: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#73)"} M[Net#d][R[Net#d] - 1] <= M[Net#e][R[Net#e] - 1];
  }
  assert {:msg "  58.16: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#74)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#g][i] == M[Net#e][i])
  );
}
procedure Net#anon$3#Rep#anon$0#10()
  modifies C, R, M, St, SqnCh, SqnAct;
{
  var St#next: State;
  var in#i: int;
  assume L[Net#a] == (1 * Base#L);
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) <= L[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume 0 <= R[Net#d];
  assume 0 <= C[Net#d];
  assume 0 <= R[Net#e];
  assume 0 <= C[Net#e];
  assume 0 <= R[Net#f];
  assume 0 <= C[Net#f];
  assume 0 <= R[Net#g];
  assume 0 <= C[Net#g];
  assume R[Net#g] == 0;
  assume R[Net#a] == (R[Net#b] + C[Net#b]);
  assume R[Net#a] == (R[Net#c] + C[Net#c]);
  assume R[Net#b] == (R[Net#d] + C[Net#d]);
  assume R[Net#c] == (R[Net#e] + C[Net#e]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#e] + C[Net#e])) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][idx$] == idx$)
  );
  assume SqnAct[Net#spl] == R[Net#a];
  assume SqnAct[Net#pri] == R[Net#b];
  assume SqnAct[Net#sec] == R[Net#c];
  assume SqnAct[Net#adj] == R[Net#e];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (SqnCh[Net#b][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (SqnCh[Net#c][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (SqnCh[Net#d][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (SqnCh[Net#e][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#g] + C[Net#g])) ==> (SqnCh[Net#g][i] == i)
  );
  assume C[Net#f] == 1;
  assume (R[Net#g] + C[Net#g]) == R[Net#e];
  assume R[Net#e] == M[Net#f][R[Net#f]];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#g] + C[Net#g])) ==> (SqnCh[Net#g][i] == i)
  );
  if ((0 < R[Net#d]) && (0 < R[Net#e])) {
    assume M[Net#d][R[Net#d] - 1] <= M[Net#e][R[Net#e] - 1];
  }
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#g][i] == M[Net#e][i])
  );
  assume true;
  assume 1 <= C[Net#c];
  in#i := M[Net#c][R[Net#c]];
  R[Net#c] := R[Net#c] + 1;
  C[Net#c] := C[Net#c] - 1;
  M[Net#e][R[Net#e] + C[Net#e]] := in#i;
  SqnCh[Net#e][R[Net#e] + C[Net#e]] := SqnAct[Net#sec];
  C[Net#e] := C[Net#e] + 1;
  SqnAct[Net#sec] := SqnAct[Net#sec] + 1;
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#75)"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#76)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#77)"} R[Net#b] == (R[Net#d] + C[Net#d]);
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#78)"} R[Net#c] == (R[Net#e] + C[Net#e]);
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#79)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#80)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#81)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#82)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#e] + C[Net#e])) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#83)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][idx$] == idx$)
  );
  assert {:msg "  40.15: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#84)"} SqnAct[Net#spl] == R[Net#a];
  assert {:msg "  41.15: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#85)"} SqnAct[Net#pri] == R[Net#b];
  assert {:msg "  42.15: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#86)"} SqnAct[Net#sec] == R[Net#c];
  assert {:msg "  43.15: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#87)"} SqnAct[Net#adj] == R[Net#e];
  assert {:msg "  45.16: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#88)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][i] == i)
  );
  assert {:msg "  46.16: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#89)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (SqnCh[Net#b][i] == i)
  );
  assert {:msg "  47.16: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#90)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (SqnCh[Net#c][i] == i)
  );
  assert {:msg "  48.16: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#91)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (SqnCh[Net#d][i] == i)
  );
  assert {:msg "  49.16: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#92)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (SqnCh[Net#e][i] == i)
  );
  assert {:msg "  50.16: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#93)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#g] + C[Net#g])) ==> (SqnCh[Net#g][i] == i)
  );
  assert {:msg "  52.15: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#94)"} C[Net#f] == 1;
  assert {:msg "  53.15: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#95)"} (R[Net#g] + C[Net#g]) == R[Net#e];
  assert {:msg "  54.15: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#96)"} R[Net#e] == M[Net#f][R[Net#f]];
  assert {:msg "  55.16: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#97)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#g] + C[Net#g])) ==> (SqnCh[Net#g][i] == i)
  );
  if ((0 < R[Net#d]) && (0 < R[Net#e])) {
    assert {:msg "  57.42: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#98)"} M[Net#d][R[Net#d] - 1] <= M[Net#e][R[Net#e] - 1];
  }
  assert {:msg "  58.16: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#99)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#g][i] == M[Net#e][i])
  );
}
procedure Net#anon$3#Adjudicator#readoff#11()
  modifies C, R, M, St, SqnCh, SqnAct;
{
  var St#next: State;
  var x1#i: int;
  var c_in#c: int;
  assume L[Net#a] == (1 * Base#L);
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) <= L[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume 0 <= R[Net#d];
  assume 0 <= C[Net#d];
  assume 0 <= R[Net#e];
  assume 0 <= C[Net#e];
  assume 0 <= R[Net#f];
  assume 0 <= C[Net#f];
  assume 0 <= R[Net#g];
  assume 0 <= C[Net#g];
  assume R[Net#g] == 0;
  assume R[Net#a] == (R[Net#b] + C[Net#b]);
  assume R[Net#a] == (R[Net#c] + C[Net#c]);
  assume R[Net#b] == (R[Net#d] + C[Net#d]);
  assume R[Net#c] == (R[Net#e] + C[Net#e]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#e] + C[Net#e])) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][idx$] == idx$)
  );
  assume SqnAct[Net#spl] == R[Net#a];
  assume SqnAct[Net#pri] == R[Net#b];
  assume SqnAct[Net#sec] == R[Net#c];
  assume SqnAct[Net#adj] == R[Net#e];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (SqnCh[Net#b][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (SqnCh[Net#c][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (SqnCh[Net#d][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (SqnCh[Net#e][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#g] + C[Net#g])) ==> (SqnCh[Net#g][i] == i)
  );
  assume C[Net#f] == 1;
  assume (R[Net#g] + C[Net#g]) == R[Net#e];
  assume R[Net#e] == M[Net#f][R[Net#f]];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#g] + C[Net#g])) ==> (SqnCh[Net#g][i] == i)
  );
  if ((0 < R[Net#d]) && (0 < R[Net#e])) {
    assume M[Net#d][R[Net#d] - 1] <= M[Net#e][R[Net#e] - 1];
  }
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#g][i] == M[Net#e][i])
  );
  assume SqnCh[Net#d][R[Net#d] - 0] < M[Net#f][R[Net#f] - 0];
  assume true;
  assume (1 <= C[Net#d]) && (1 <= C[Net#f]) && (SqnCh[Net#d][R[Net#d] - 0] < M[Net#f][R[Net#f] - 0]);
  x1#i := M[Net#d][R[Net#d]];
  R[Net#d] := R[Net#d] + 1;
  C[Net#d] := C[Net#d] - 1;
  c_in#c := M[Net#f][R[Net#f]];
  R[Net#f] := R[Net#f] + 1;
  C[Net#f] := C[Net#f] - 1;
  M[Net#f][R[Net#f] + C[Net#f]] := c_in#c;
  SqnCh[Net#f][R[Net#f] + C[Net#f]] := SqnAct[Net#adj];
  C[Net#f] := C[Net#f] + 1;
  assert {:msg "  Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#100)"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#101)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#102)"} R[Net#b] == (R[Net#d] + C[Net#d]);
  assert {:msg "  Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#103)"} R[Net#c] == (R[Net#e] + C[Net#e]);
  assert {:msg "  Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#104)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#105)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#106)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assert {:msg "  Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#107)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#e] + C[Net#e])) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assert {:msg "  Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#108)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][idx$] == idx$)
  );
  assert {:msg "  40.15: Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#109)"} SqnAct[Net#spl] == R[Net#a];
  assert {:msg "  41.15: Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#110)"} SqnAct[Net#pri] == R[Net#b];
  assert {:msg "  42.15: Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#111)"} SqnAct[Net#sec] == R[Net#c];
  assert {:msg "  43.15: Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#112)"} SqnAct[Net#adj] == R[Net#e];
  assert {:msg "  45.16: Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#113)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][i] == i)
  );
  assert {:msg "  46.16: Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#114)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (SqnCh[Net#b][i] == i)
  );
  assert {:msg "  47.16: Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#115)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (SqnCh[Net#c][i] == i)
  );
  assert {:msg "  48.16: Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#116)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (SqnCh[Net#d][i] == i)
  );
  assert {:msg "  49.16: Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#117)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (SqnCh[Net#e][i] == i)
  );
  assert {:msg "  50.16: Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#118)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#g] + C[Net#g])) ==> (SqnCh[Net#g][i] == i)
  );
  assert {:msg "  52.15: Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#119)"} C[Net#f] == 1;
  assert {:msg "  53.15: Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#120)"} (R[Net#g] + C[Net#g]) == R[Net#e];
  assert {:msg "  54.15: Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#121)"} R[Net#e] == M[Net#f][R[Net#f]];
  assert {:msg "  55.16: Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#122)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#g] + C[Net#g])) ==> (SqnCh[Net#g][i] == i)
  );
  if ((0 < R[Net#d]) && (0 < R[Net#e])) {
    assert {:msg "  57.42: Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#123)"} M[Net#d][R[Net#d] - 1] <= M[Net#e][R[Net#e] - 1];
  }
  assert {:msg "  58.16: Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#124)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#g][i] == M[Net#e][i])
  );
}
procedure Net#anon$3#Adjudicator#normal#12()
  modifies C, R, M, St, SqnCh, SqnAct;
{
  var St#next: State;
  var x1#i: int;
  var x2#j: int;
  var c_in#c: int;
  assume L[Net#a] == (1 * Base#L);
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) <= L[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume 0 <= R[Net#d];
  assume 0 <= C[Net#d];
  assume 0 <= R[Net#e];
  assume 0 <= C[Net#e];
  assume 0 <= R[Net#f];
  assume 0 <= C[Net#f];
  assume 0 <= R[Net#g];
  assume 0 <= C[Net#g];
  assume R[Net#g] == 0;
  assume R[Net#a] == (R[Net#b] + C[Net#b]);
  assume R[Net#a] == (R[Net#c] + C[Net#c]);
  assume R[Net#b] == (R[Net#d] + C[Net#d]);
  assume R[Net#c] == (R[Net#e] + C[Net#e]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#e] + C[Net#e])) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][idx$] == idx$)
  );
  assume SqnAct[Net#spl] == R[Net#a];
  assume SqnAct[Net#pri] == R[Net#b];
  assume SqnAct[Net#sec] == R[Net#c];
  assume SqnAct[Net#adj] == R[Net#e];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (SqnCh[Net#b][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (SqnCh[Net#c][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (SqnCh[Net#d][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (SqnCh[Net#e][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#g] + C[Net#g])) ==> (SqnCh[Net#g][i] == i)
  );
  assume C[Net#f] == 1;
  assume (R[Net#g] + C[Net#g]) == R[Net#e];
  assume R[Net#e] == M[Net#f][R[Net#f]];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#g] + C[Net#g])) ==> (SqnCh[Net#g][i] == i)
  );
  if ((0 < R[Net#d]) && (0 < R[Net#e])) {
    assume M[Net#d][R[Net#d] - 1] <= M[Net#e][R[Net#e] - 1];
  }
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#g][i] == M[Net#e][i])
  );
  assume (SqnCh[Net#d][R[Net#d] - 0] == SqnCh[Net#e][R[Net#e] - 0]) && (SqnCh[Net#d][R[Net#d] - 0] == M[Net#f][R[Net#f] - 0]);
  assume true;
  assume (!((1 <= C[Net#d]) && (1 <= C[Net#f]) && (SqnCh[Net#d][R[Net#d] - 0] < M[Net#f][R[Net#f] - 0]))) && (1 <= C[Net#d]) && (1 <= C[Net#e]) && (1 <= C[Net#f]) && (SqnCh[Net#d][R[Net#d] - 0] == SqnCh[Net#e][R[Net#e] - 0]) && (SqnCh[Net#d][R[Net#d] - 0] == M[Net#f][R[Net#f] - 0]);
  x1#i := M[Net#d][R[Net#d]];
  R[Net#d] := R[Net#d] + 1;
  C[Net#d] := C[Net#d] - 1;
  x2#j := M[Net#e][R[Net#e]];
  R[Net#e] := R[Net#e] + 1;
  C[Net#e] := C[Net#e] - 1;
  c_in#c := M[Net#f][R[Net#f]];
  R[Net#f] := R[Net#f] + 1;
  C[Net#f] := C[Net#f] - 1;
  M[Net#g][R[Net#g] + C[Net#g]] := x1#i;
  SqnCh[Net#g][R[Net#g] + C[Net#g]] := SqnAct[Net#adj];
  C[Net#g] := C[Net#g] + 1;
  M[Net#f][R[Net#f] + C[Net#f]] := c_in#c + 1;
  SqnCh[Net#f][R[Net#f] + C[Net#f]] := SqnAct[Net#adj];
  C[Net#f] := C[Net#f] + 1;
  SqnAct[Net#adj] := SqnAct[Net#adj] + 1;
  assert {:msg "  Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#125)"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#126)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#127)"} R[Net#b] == (R[Net#d] + C[Net#d]);
  assert {:msg "  Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#128)"} R[Net#c] == (R[Net#e] + C[Net#e]);
  assert {:msg "  Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#129)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#130)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#131)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assert {:msg "  Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#132)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#e] + C[Net#e])) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assert {:msg "  Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#133)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][idx$] == idx$)
  );
  assert {:msg "  40.15: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#134)"} SqnAct[Net#spl] == R[Net#a];
  assert {:msg "  41.15: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#135)"} SqnAct[Net#pri] == R[Net#b];
  assert {:msg "  42.15: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#136)"} SqnAct[Net#sec] == R[Net#c];
  assert {:msg "  43.15: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#137)"} SqnAct[Net#adj] == R[Net#e];
  assert {:msg "  45.16: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#138)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][i] == i)
  );
  assert {:msg "  46.16: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#139)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (SqnCh[Net#b][i] == i)
  );
  assert {:msg "  47.16: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#140)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (SqnCh[Net#c][i] == i)
  );
  assert {:msg "  48.16: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#141)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (SqnCh[Net#d][i] == i)
  );
  assert {:msg "  49.16: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#142)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (SqnCh[Net#e][i] == i)
  );
  assert {:msg "  50.16: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#143)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#g] + C[Net#g])) ==> (SqnCh[Net#g][i] == i)
  );
  assert {:msg "  52.15: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#144)"} C[Net#f] == 1;
  assert {:msg "  53.15: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#145)"} (R[Net#g] + C[Net#g]) == R[Net#e];
  assert {:msg "  54.15: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#146)"} R[Net#e] == M[Net#f][R[Net#f]];
  assert {:msg "  55.16: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#147)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#g] + C[Net#g])) ==> (SqnCh[Net#g][i] == i)
  );
  if ((0 < R[Net#d]) && (0 < R[Net#e])) {
    assert {:msg "  57.42: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#148)"} M[Net#d][R[Net#d] - 1] <= M[Net#e][R[Net#e] - 1];
  }
  assert {:msg "  58.16: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#149)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#g][i] == M[Net#e][i])
  );
}
procedure Net#anon$3#Adjudicator#timeout#13()
  modifies C, R, M, St, SqnCh, SqnAct;
{
  var St#next: State;
  var x2#j: int;
  var c_in#c: int;
  assume L[Net#a] == (1 * Base#L);
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) <= L[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume 0 <= R[Net#d];
  assume 0 <= C[Net#d];
  assume 0 <= R[Net#e];
  assume 0 <= C[Net#e];
  assume 0 <= R[Net#f];
  assume 0 <= C[Net#f];
  assume 0 <= R[Net#g];
  assume 0 <= C[Net#g];
  assume R[Net#g] == 0;
  assume R[Net#a] == (R[Net#b] + C[Net#b]);
  assume R[Net#a] == (R[Net#c] + C[Net#c]);
  assume R[Net#b] == (R[Net#d] + C[Net#d]);
  assume R[Net#c] == (R[Net#e] + C[Net#e]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#e] + C[Net#e])) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][idx$] == idx$)
  );
  assume SqnAct[Net#spl] == R[Net#a];
  assume SqnAct[Net#pri] == R[Net#b];
  assume SqnAct[Net#sec] == R[Net#c];
  assume SqnAct[Net#adj] == R[Net#e];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (SqnCh[Net#b][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (SqnCh[Net#c][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (SqnCh[Net#d][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (SqnCh[Net#e][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#g] + C[Net#g])) ==> (SqnCh[Net#g][i] == i)
  );
  assume C[Net#f] == 1;
  assume (R[Net#g] + C[Net#g]) == R[Net#e];
  assume R[Net#e] == M[Net#f][R[Net#f]];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#g] + C[Net#g])) ==> (SqnCh[Net#g][i] == i)
  );
  if ((0 < R[Net#d]) && (0 < R[Net#e])) {
    assume M[Net#d][R[Net#d] - 1] <= M[Net#e][R[Net#e] - 1];
  }
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#g][i] == M[Net#e][i])
  );
  assume true;
  assume (!((1 <= C[Net#d]) && (1 <= C[Net#f]) && (SqnCh[Net#d][R[Net#d] - 0] < M[Net#f][R[Net#f] - 0]))) && (!((1 <= C[Net#d]) && (1 <= C[Net#e]) && (1 <= C[Net#f]) && (SqnCh[Net#d][R[Net#d] - 0] == SqnCh[Net#e][R[Net#e] - 0]) && (SqnCh[Net#d][R[Net#d] - 0] == M[Net#f][R[Net#f] - 0]))) && (1 <= C[Net#e]) && (1 <= C[Net#f]);
  x2#j := M[Net#e][R[Net#e]];
  R[Net#e] := R[Net#e] + 1;
  C[Net#e] := C[Net#e] - 1;
  c_in#c := M[Net#f][R[Net#f]];
  R[Net#f] := R[Net#f] + 1;
  C[Net#f] := C[Net#f] - 1;
  M[Net#g][R[Net#g] + C[Net#g]] := x2#j;
  SqnCh[Net#g][R[Net#g] + C[Net#g]] := SqnAct[Net#adj];
  C[Net#g] := C[Net#g] + 1;
  M[Net#f][R[Net#f] + C[Net#f]] := c_in#c + 1;
  SqnCh[Net#f][R[Net#f] + C[Net#f]] := SqnAct[Net#adj];
  C[Net#f] := C[Net#f] + 1;
  SqnAct[Net#adj] := SqnAct[Net#adj] + 1;
  assert {:msg "  Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#150)"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#151)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#152)"} R[Net#b] == (R[Net#d] + C[Net#d]);
  assert {:msg "  Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#153)"} R[Net#c] == (R[Net#e] + C[Net#e]);
  assert {:msg "  Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#154)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#155)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#156)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assert {:msg "  Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#157)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#e] + C[Net#e])) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assert {:msg "  Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#158)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][idx$] == idx$)
  );
  assert {:msg "  40.15: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#159)"} SqnAct[Net#spl] == R[Net#a];
  assert {:msg "  41.15: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#160)"} SqnAct[Net#pri] == R[Net#b];
  assert {:msg "  42.15: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#161)"} SqnAct[Net#sec] == R[Net#c];
  assert {:msg "  43.15: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#162)"} SqnAct[Net#adj] == R[Net#e];
  assert {:msg "  45.16: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#163)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][i] == i)
  );
  assert {:msg "  46.16: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#164)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (SqnCh[Net#b][i] == i)
  );
  assert {:msg "  47.16: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#165)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (SqnCh[Net#c][i] == i)
  );
  assert {:msg "  48.16: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#166)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (SqnCh[Net#d][i] == i)
  );
  assert {:msg "  49.16: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#167)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (SqnCh[Net#e][i] == i)
  );
  assert {:msg "  50.16: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#168)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#g] + C[Net#g])) ==> (SqnCh[Net#g][i] == i)
  );
  assert {:msg "  52.15: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#169)"} C[Net#f] == 1;
  assert {:msg "  53.15: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#170)"} (R[Net#g] + C[Net#g]) == R[Net#e];
  assert {:msg "  54.15: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#171)"} R[Net#e] == M[Net#f][R[Net#f]];
  assert {:msg "  55.16: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#172)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#g] + C[Net#g])) ==> (SqnCh[Net#g][i] == i)
  );
  if ((0 < R[Net#d]) && (0 < R[Net#e])) {
    assert {:msg "  57.42: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#173)"} M[Net#d][R[Net#d] - 1] <= M[Net#e][R[Net#e] - 1];
  }
  assert {:msg "  58.16: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#174)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#g][i] == M[Net#e][i])
  );
}
procedure Net#anon$3#exit#14()
  modifies C, R, M, St, SqnCh, SqnAct;
{
  assume L[Net#a] == (1 * Base#L);
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) <= L[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume 0 <= R[Net#d];
  assume 0 <= C[Net#d];
  assume 0 <= R[Net#e];
  assume 0 <= C[Net#e];
  assume 0 <= R[Net#f];
  assume 0 <= C[Net#f];
  assume 0 <= R[Net#g];
  assume 0 <= C[Net#g];
  assume R[Net#g] == 0;
  assume R[Net#a] == (R[Net#b] + C[Net#b]);
  assume R[Net#a] == (R[Net#c] + C[Net#c]);
  assume R[Net#b] == (R[Net#d] + C[Net#d]);
  assume R[Net#c] == (R[Net#e] + C[Net#e]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#e] + C[Net#e])) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][idx$] == idx$)
  );
  assume SqnAct[Net#spl] == R[Net#a];
  assume SqnAct[Net#pri] == R[Net#b];
  assume SqnAct[Net#sec] == R[Net#c];
  assume SqnAct[Net#adj] == R[Net#e];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (SqnCh[Net#b][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (SqnCh[Net#c][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (SqnCh[Net#d][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (SqnCh[Net#e][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#g] + C[Net#g])) ==> (SqnCh[Net#g][i] == i)
  );
  assume C[Net#f] == 1;
  assume (R[Net#g] + C[Net#g]) == R[Net#e];
  assume R[Net#e] == M[Net#f][R[Net#f]];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#g] + C[Net#g])) ==> (SqnCh[Net#g][i] == i)
  );
  if ((0 < R[Net#d]) && (0 < R[Net#e])) {
    assume M[Net#d][R[Net#d] - 1] <= M[Net#e][R[Net#e] - 1];
  }
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#g][i] == M[Net#e][i])
  );
  assume !((R[Net#a] + C[Net#a]) < L[Net#a]);
  assume !(1 <= C[Net#a]);
  assume !(1 <= C[Net#b]);
  assume !(1 <= C[Net#c]);
  assume !((!((1 <= C[Net#d]) && (1 <= C[Net#f]) && (SqnCh[Net#d][R[Net#d] - 0] < M[Net#f][R[Net#f] - 0]))) && (1 <= C[Net#d]) && (1 <= C[Net#e]) && (1 <= C[Net#f]) && (SqnCh[Net#d][R[Net#d] - 0] == SqnCh[Net#e][R[Net#e] - 0]) && (SqnCh[Net#d][R[Net#d] - 0] == M[Net#f][R[Net#f] - 0]));
  assume !((!((1 <= C[Net#d]) && (1 <= C[Net#f]) && (SqnCh[Net#d][R[Net#d] - 0] < M[Net#f][R[Net#f] - 0]))) && (!((1 <= C[Net#d]) && (1 <= C[Net#e]) && (1 <= C[Net#f]) && (SqnCh[Net#d][R[Net#d] - 0] == SqnCh[Net#e][R[Net#e] - 0]) && (SqnCh[Net#d][R[Net#d] - 0] == M[Net#f][R[Net#f] - 0]))) && (1 <= C[Net#e]) && (1 <= C[Net#f]));
  assume !((1 <= C[Net#d]) && (1 <= C[Net#f]) && (SqnCh[Net#d][R[Net#d] - 0] < M[Net#f][R[Net#f] - 0]));
  assert {:msg "  33.14: Network action postcondition might not hold"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#g] + C[Net#g])) ==> (SqnCh[Net#g][i] == i)
  );
  assert {:msg "  34.14: Network action postcondition might not hold"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#g] + C[Net#g])) ==> (M[Net#g][i] == M[Net#a][i])
  );
  R[Net#g] := R[Net#g] + C[Net#g];
  C[Net#g] := C[Net#g] - (1 * Base#L);
  assert {:msg "  The network might not preserve the channel invariant"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  The network might not preserve the channel invariant"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  The network might not preserve the channel invariant"} R[Net#b] == (R[Net#d] + C[Net#d]);
  assert {:msg "  The network might not preserve the channel invariant"} R[Net#c] == (R[Net#e] + C[Net#e]);
  assert {:msg "  The network might not preserve the channel invariant"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  The network might not preserve the channel invariant"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  The network might not preserve the channel invariant"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assert {:msg "  The network might not preserve the channel invariant"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#e] + C[Net#e])) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assert {:msg "  The network might not preserve the channel invariant"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][idx$] == idx$)
  );
  assert {:msg "  40.15: The network might not preserve the channel invariant"} SqnAct[Net#spl] == R[Net#a];
  assert {:msg "  41.15: The network might not preserve the channel invariant"} SqnAct[Net#pri] == R[Net#b];
  assert {:msg "  42.15: The network might not preserve the channel invariant"} SqnAct[Net#sec] == R[Net#c];
  assert {:msg "  43.15: The network might not preserve the channel invariant"} SqnAct[Net#adj] == R[Net#e];
  assert {:msg "  45.16: The network might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][i] == i)
  );
  assert {:msg "  46.16: The network might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (SqnCh[Net#b][i] == i)
  );
  assert {:msg "  47.16: The network might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (SqnCh[Net#c][i] == i)
  );
  assert {:msg "  48.16: The network might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (SqnCh[Net#d][i] == i)
  );
  assert {:msg "  49.16: The network might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (SqnCh[Net#e][i] == i)
  );
  assert {:msg "  50.16: The network might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#g] + C[Net#g])) ==> (SqnCh[Net#g][i] == i)
  );
  assert {:msg "  52.15: The network might not preserve the channel invariant"} C[Net#f] == 1;
  assert {:msg "  53.15: The network might not preserve the channel invariant"} (R[Net#g] + C[Net#g]) == R[Net#e];
  assert {:msg "  54.15: The network might not preserve the channel invariant"} R[Net#e] == M[Net#f][R[Net#f]];
  assert {:msg "  55.16: The network might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#g] + C[Net#g])) ==> (SqnCh[Net#g][i] == i)
  );
  if ((0 < R[Net#d]) && (0 < R[Net#e])) {
    assert {:msg "  57.42: The network might not preserve the channel invariant"} M[Net#d][R[Net#d] - 1] <= M[Net#e][R[Net#e] - 1];
  }
  assert {:msg "  58.16: The network might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#g][i] == M[Net#e][i])
  );
  C[Net#f] := C[Net#f] - 1;
  assert {:msg "  38.13: The network might not preserve the network invariant"} R[Net#e] == M[Net#f][R[Net#f]];
  assert {:msg "  32.3: The network might leave unread tokens on channel a"} C[Net#a] == 0;
  assert {:msg "  32.3: The network might leave unread tokens on channel b"} C[Net#b] == 0;
  assert {:msg "  32.3: The network might leave unread tokens on channel c"} C[Net#c] == 0;
  assert {:msg "  32.3: The network might leave unread tokens on channel d"} C[Net#d] == 0;
  assert {:msg "  32.3: The network might leave unread tokens on channel e"} C[Net#e] == 0;
  assert {:msg "  32.3: The network might leave unread tokens on channel f"} C[Net#f] == 0;
  assert {:msg "  32.3: The network might not produce the specified number of tokens on output out"} C[Net#g] == 0;
}

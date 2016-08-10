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
  M[Net#f][R[Net#f] + C[Net#f]] := 0;
  C[Net#f] := C[Net#f] + 1;
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
  assume SqnAct[Net#spl] == 0;
  assume SqnAct[Net#pri] == 0;
  assume SqnAct[Net#sec] == 0;
  assume SqnAct[Net#adj] == 0;
  assume L[Net#a] == (1 * Base#L);
  assume R[Net#a] == 0;
  assume C[Net#a] == 0;
  assume R[Net#b] == 0;
  assume C[Net#b] == 0;
  assume R[Net#c] == 0;
  assume C[Net#c] == 0;
  assume R[Net#d] == 0;
  assume C[Net#d] == 0;
  assume R[Net#e] == 0;
  assume C[Net#e] == 0;
  assume R[Net#f] == 0;
  assume C[Net#f] == 0;
  assume R[Net#g] == 0;
  assume C[Net#g] == 0;
  C[Net#f] := C[Net#f] + 1;
  assume R[Net#e] == M[Net#f][R[Net#f]];
  assert {:msg "  38.13: Invariant might not hold"} R[Net#e] == M[Net#f][R[Net#f]];
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
  assert {:msg "  Channel invariant might not hold on action entry (#16)"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  Channel invariant might not hold on action entry (#17)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Channel invariant might not hold on action entry (#18)"} R[Net#b] == (R[Net#d] + C[Net#d]);
  assert {:msg "  Channel invariant might not hold on action entry (#19)"} R[Net#c] == (R[Net#e] + C[Net#e]);
  assert {:msg "  Channel invariant might not hold on action entry (#20)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Channel invariant might not hold on action entry (#21)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Channel invariant might not hold on action entry (#22)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assert {:msg "  Channel invariant might not hold on action entry (#23)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#e] + C[Net#e])) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assert {:msg "  Channel invariant might not hold on action entry (#24)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][idx$] == idx$)
  );
  assert {:msg "  40.3: Channel invariant might not hold on action entry (#25)"} SqnAct[Net#spl] == R[Net#a];
  assert {:msg "  41.3: Channel invariant might not hold on action entry (#26)"} SqnAct[Net#pri] == R[Net#b];
  assert {:msg "  42.3: Channel invariant might not hold on action entry (#27)"} SqnAct[Net#sec] == R[Net#c];
  assert {:msg "  43.3: Channel invariant might not hold on action entry (#28)"} SqnAct[Net#adj] == R[Net#e];
  assert {:msg "  45.3: Channel invariant might not hold on action entry (#29)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][i] == i)
  );
  assert {:msg "  46.3: Channel invariant might not hold on action entry (#30)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (SqnCh[Net#b][i] == i)
  );
  assert {:msg "  47.3: Channel invariant might not hold on action entry (#31)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (SqnCh[Net#c][i] == i)
  );
  assert {:msg "  48.3: Channel invariant might not hold on action entry (#32)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (SqnCh[Net#d][i] == i)
  );
  assert {:msg "  49.3: Channel invariant might not hold on action entry (#33)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (SqnCh[Net#e][i] == i)
  );
  assert {:msg "  50.3: Channel invariant might not hold on action entry (#34)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#g] + C[Net#g])) ==> (SqnCh[Net#g][i] == i)
  );
  assert {:msg "  52.3: Channel invariant might not hold on action entry (#35)"} C[Net#f] == 1;
  assert {:msg "  53.3: Channel invariant might not hold on action entry (#36)"} C[Net#g] == R[Net#e];
  assert {:msg "  54.3: Channel invariant might not hold on action entry (#37)"} R[Net#e] == M[Net#f][R[Net#f]];
  assert {:msg "  55.3: Channel invariant might not hold on action entry (#38)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#g] + C[Net#g])) ==> (SqnCh[Net#g][i] == i)
  );
  assert {:msg "  59.3: Channel invariant might not hold on action entry (#39)"} (0 < R[Net#d]) && (0 < R[Net#e]) ==> (M[Net#d][R[Net#d] - 1] <= M[Net#e][R[Net#e] - 1]);
  assert {:msg "  60.3: Channel invariant might not hold on action entry (#40)"} (forall i: int :: 
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
  assume C[Net#g] == R[Net#e];
  assume R[Net#e] == M[Net#f][R[Net#f]];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#g] + C[Net#g])) ==> (SqnCh[Net#g][i] == i)
  );
  assume (0 < R[Net#d]) && (0 < R[Net#e]) ==> (M[Net#d][R[Net#d] - 1] <= M[Net#e][R[Net#e] - 1]);
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
  assert {:msg "  Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#57)"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#58)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#59)"} R[Net#b] == (R[Net#d] + C[Net#d]);
  assert {:msg "  Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#60)"} R[Net#c] == (R[Net#e] + C[Net#e]);
  assert {:msg "  Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#61)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#62)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#63)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assert {:msg "  Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#64)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#e] + C[Net#e])) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assert {:msg "  Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#65)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][idx$] == idx$)
  );
  assert {:msg "  40.3: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#66)"} SqnAct[Net#spl] == R[Net#a];
  assert {:msg "  41.3: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#67)"} SqnAct[Net#pri] == R[Net#b];
  assert {:msg "  42.3: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#68)"} SqnAct[Net#sec] == R[Net#c];
  assert {:msg "  43.3: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#69)"} SqnAct[Net#adj] == R[Net#e];
  assert {:msg "  45.3: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#70)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][i] == i)
  );
  assert {:msg "  46.3: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#71)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (SqnCh[Net#b][i] == i)
  );
  assert {:msg "  47.3: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#72)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (SqnCh[Net#c][i] == i)
  );
  assert {:msg "  48.3: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#73)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (SqnCh[Net#d][i] == i)
  );
  assert {:msg "  49.3: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#74)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (SqnCh[Net#e][i] == i)
  );
  assert {:msg "  50.3: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#75)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#g] + C[Net#g])) ==> (SqnCh[Net#g][i] == i)
  );
  assert {:msg "  52.3: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#76)"} C[Net#f] == 1;
  assert {:msg "  53.3: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#77)"} C[Net#g] == R[Net#e];
  assert {:msg "  54.3: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#78)"} R[Net#e] == M[Net#f][R[Net#f]];
  assert {:msg "  55.3: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#79)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#g] + C[Net#g])) ==> (SqnCh[Net#g][i] == i)
  );
  assert {:msg "  59.3: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#80)"} (0 < R[Net#d]) && (0 < R[Net#e]) ==> (M[Net#d][R[Net#d] - 1] <= M[Net#e][R[Net#e] - 1]);
  assert {:msg "  60.3: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#81)"} (forall i: int :: 
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
  assume C[Net#g] == R[Net#e];
  assume R[Net#e] == M[Net#f][R[Net#f]];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#g] + C[Net#g])) ==> (SqnCh[Net#g][i] == i)
  );
  assume (0 < R[Net#d]) && (0 < R[Net#e]) ==> (M[Net#d][R[Net#d] - 1] <= M[Net#e][R[Net#e] - 1]);
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
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#98)"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#99)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#100)"} R[Net#b] == (R[Net#d] + C[Net#d]);
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#101)"} R[Net#c] == (R[Net#e] + C[Net#e]);
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#102)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#103)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#104)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#105)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#e] + C[Net#e])) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#106)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][idx$] == idx$)
  );
  assert {:msg "  40.3: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#107)"} SqnAct[Net#spl] == R[Net#a];
  assert {:msg "  41.3: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#108)"} SqnAct[Net#pri] == R[Net#b];
  assert {:msg "  42.3: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#109)"} SqnAct[Net#sec] == R[Net#c];
  assert {:msg "  43.3: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#110)"} SqnAct[Net#adj] == R[Net#e];
  assert {:msg "  45.3: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#111)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][i] == i)
  );
  assert {:msg "  46.3: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#112)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (SqnCh[Net#b][i] == i)
  );
  assert {:msg "  47.3: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#113)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (SqnCh[Net#c][i] == i)
  );
  assert {:msg "  48.3: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#114)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (SqnCh[Net#d][i] == i)
  );
  assert {:msg "  49.3: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#115)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (SqnCh[Net#e][i] == i)
  );
  assert {:msg "  50.3: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#116)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#g] + C[Net#g])) ==> (SqnCh[Net#g][i] == i)
  );
  assert {:msg "  52.3: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#117)"} C[Net#f] == 1;
  assert {:msg "  53.3: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#118)"} C[Net#g] == R[Net#e];
  assert {:msg "  54.3: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#119)"} R[Net#e] == M[Net#f][R[Net#f]];
  assert {:msg "  55.3: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#120)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#g] + C[Net#g])) ==> (SqnCh[Net#g][i] == i)
  );
  assert {:msg "  59.3: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#121)"} (0 < R[Net#d]) && (0 < R[Net#e]) ==> (M[Net#d][R[Net#d] - 1] <= M[Net#e][R[Net#e] - 1]);
  assert {:msg "  60.3: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#122)"} (forall i: int :: 
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
  assume C[Net#g] == R[Net#e];
  assume R[Net#e] == M[Net#f][R[Net#f]];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#g] + C[Net#g])) ==> (SqnCh[Net#g][i] == i)
  );
  assume (0 < R[Net#d]) && (0 < R[Net#e]) ==> (M[Net#d][R[Net#d] - 1] <= M[Net#e][R[Net#e] - 1]);
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
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#139)"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#140)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#141)"} R[Net#b] == (R[Net#d] + C[Net#d]);
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#142)"} R[Net#c] == (R[Net#e] + C[Net#e]);
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#143)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#144)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#145)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#146)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#e] + C[Net#e])) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#147)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][idx$] == idx$)
  );
  assert {:msg "  40.3: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#148)"} SqnAct[Net#spl] == R[Net#a];
  assert {:msg "  41.3: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#149)"} SqnAct[Net#pri] == R[Net#b];
  assert {:msg "  42.3: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#150)"} SqnAct[Net#sec] == R[Net#c];
  assert {:msg "  43.3: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#151)"} SqnAct[Net#adj] == R[Net#e];
  assert {:msg "  45.3: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#152)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][i] == i)
  );
  assert {:msg "  46.3: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#153)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (SqnCh[Net#b][i] == i)
  );
  assert {:msg "  47.3: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#154)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (SqnCh[Net#c][i] == i)
  );
  assert {:msg "  48.3: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#155)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (SqnCh[Net#d][i] == i)
  );
  assert {:msg "  49.3: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#156)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (SqnCh[Net#e][i] == i)
  );
  assert {:msg "  50.3: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#157)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#g] + C[Net#g])) ==> (SqnCh[Net#g][i] == i)
  );
  assert {:msg "  52.3: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#158)"} C[Net#f] == 1;
  assert {:msg "  53.3: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#159)"} C[Net#g] == R[Net#e];
  assert {:msg "  54.3: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#160)"} R[Net#e] == M[Net#f][R[Net#f]];
  assert {:msg "  55.3: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#161)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#g] + C[Net#g])) ==> (SqnCh[Net#g][i] == i)
  );
  assert {:msg "  59.3: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#162)"} (0 < R[Net#d]) && (0 < R[Net#e]) ==> (M[Net#d][R[Net#d] - 1] <= M[Net#e][R[Net#e] - 1]);
  assert {:msg "  60.3: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#163)"} (forall i: int :: 
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
  assume C[Net#g] == R[Net#e];
  assume R[Net#e] == M[Net#f][R[Net#f]];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#g] + C[Net#g])) ==> (SqnCh[Net#g][i] == i)
  );
  assume (0 < R[Net#d]) && (0 < R[Net#e]) ==> (M[Net#d][R[Net#d] - 1] <= M[Net#e][R[Net#e] - 1]);
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
  assert {:msg "  Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#180)"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#181)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#182)"} R[Net#b] == (R[Net#d] + C[Net#d]);
  assert {:msg "  Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#183)"} R[Net#c] == (R[Net#e] + C[Net#e]);
  assert {:msg "  Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#184)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#185)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#186)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assert {:msg "  Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#187)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#e] + C[Net#e])) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assert {:msg "  Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#188)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][idx$] == idx$)
  );
  assert {:msg "  40.3: Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#189)"} SqnAct[Net#spl] == R[Net#a];
  assert {:msg "  41.3: Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#190)"} SqnAct[Net#pri] == R[Net#b];
  assert {:msg "  42.3: Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#191)"} SqnAct[Net#sec] == R[Net#c];
  assert {:msg "  43.3: Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#192)"} SqnAct[Net#adj] == R[Net#e];
  assert {:msg "  45.3: Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#193)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][i] == i)
  );
  assert {:msg "  46.3: Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#194)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (SqnCh[Net#b][i] == i)
  );
  assert {:msg "  47.3: Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#195)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (SqnCh[Net#c][i] == i)
  );
  assert {:msg "  48.3: Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#196)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (SqnCh[Net#d][i] == i)
  );
  assert {:msg "  49.3: Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#197)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (SqnCh[Net#e][i] == i)
  );
  assert {:msg "  50.3: Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#198)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#g] + C[Net#g])) ==> (SqnCh[Net#g][i] == i)
  );
  assert {:msg "  52.3: Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#199)"} C[Net#f] == 1;
  assert {:msg "  53.3: Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#200)"} C[Net#g] == R[Net#e];
  assert {:msg "  54.3: Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#201)"} R[Net#e] == M[Net#f][R[Net#f]];
  assert {:msg "  55.3: Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#202)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#g] + C[Net#g])) ==> (SqnCh[Net#g][i] == i)
  );
  assert {:msg "  59.3: Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#203)"} (0 < R[Net#d]) && (0 < R[Net#e]) ==> (M[Net#d][R[Net#d] - 1] <= M[Net#e][R[Net#e] - 1]);
  assert {:msg "  60.3: Action at 20.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#204)"} (forall i: int :: 
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
  assume C[Net#g] == R[Net#e];
  assume R[Net#e] == M[Net#f][R[Net#f]];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#g] + C[Net#g])) ==> (SqnCh[Net#g][i] == i)
  );
  assume (0 < R[Net#d]) && (0 < R[Net#e]) ==> (M[Net#d][R[Net#d] - 1] <= M[Net#e][R[Net#e] - 1]);
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
  assert {:msg "  Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#221)"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#222)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#223)"} R[Net#b] == (R[Net#d] + C[Net#d]);
  assert {:msg "  Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#224)"} R[Net#c] == (R[Net#e] + C[Net#e]);
  assert {:msg "  Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#225)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#226)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#227)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assert {:msg "  Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#228)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#e] + C[Net#e])) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assert {:msg "  Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#229)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][idx$] == idx$)
  );
  assert {:msg "  40.3: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#230)"} SqnAct[Net#spl] == R[Net#a];
  assert {:msg "  41.3: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#231)"} SqnAct[Net#pri] == R[Net#b];
  assert {:msg "  42.3: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#232)"} SqnAct[Net#sec] == R[Net#c];
  assert {:msg "  43.3: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#233)"} SqnAct[Net#adj] == R[Net#e];
  assert {:msg "  45.3: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#234)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][i] == i)
  );
  assert {:msg "  46.3: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#235)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (SqnCh[Net#b][i] == i)
  );
  assert {:msg "  47.3: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#236)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (SqnCh[Net#c][i] == i)
  );
  assert {:msg "  48.3: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#237)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (SqnCh[Net#d][i] == i)
  );
  assert {:msg "  49.3: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#238)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (SqnCh[Net#e][i] == i)
  );
  assert {:msg "  50.3: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#239)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#g] + C[Net#g])) ==> (SqnCh[Net#g][i] == i)
  );
  assert {:msg "  52.3: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#240)"} C[Net#f] == 1;
  assert {:msg "  53.3: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#241)"} C[Net#g] == R[Net#e];
  assert {:msg "  54.3: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#242)"} R[Net#e] == M[Net#f][R[Net#f]];
  assert {:msg "  55.3: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#243)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#g] + C[Net#g])) ==> (SqnCh[Net#g][i] == i)
  );
  assert {:msg "  59.3: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#244)"} (0 < R[Net#d]) && (0 < R[Net#e]) ==> (M[Net#d][R[Net#d] - 1] <= M[Net#e][R[Net#e] - 1]);
  assert {:msg "  60.3: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#245)"} (forall i: int :: 
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
  assume C[Net#g] == R[Net#e];
  assume R[Net#e] == M[Net#f][R[Net#f]];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#g] + C[Net#g])) ==> (SqnCh[Net#g][i] == i)
  );
  assume (0 < R[Net#d]) && (0 < R[Net#e]) ==> (M[Net#d][R[Net#d] - 1] <= M[Net#e][R[Net#e] - 1]);
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
  assert {:msg "  Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#262)"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#263)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#264)"} R[Net#b] == (R[Net#d] + C[Net#d]);
  assert {:msg "  Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#265)"} R[Net#c] == (R[Net#e] + C[Net#e]);
  assert {:msg "  Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#266)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#267)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#268)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assert {:msg "  Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#269)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#e] + C[Net#e])) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assert {:msg "  Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#270)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][idx$] == idx$)
  );
  assert {:msg "  40.3: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#271)"} SqnAct[Net#spl] == R[Net#a];
  assert {:msg "  41.3: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#272)"} SqnAct[Net#pri] == R[Net#b];
  assert {:msg "  42.3: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#273)"} SqnAct[Net#sec] == R[Net#c];
  assert {:msg "  43.3: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#274)"} SqnAct[Net#adj] == R[Net#e];
  assert {:msg "  45.3: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#275)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][i] == i)
  );
  assert {:msg "  46.3: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#276)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (SqnCh[Net#b][i] == i)
  );
  assert {:msg "  47.3: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#277)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (SqnCh[Net#c][i] == i)
  );
  assert {:msg "  48.3: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#278)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (SqnCh[Net#d][i] == i)
  );
  assert {:msg "  49.3: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#279)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (SqnCh[Net#e][i] == i)
  );
  assert {:msg "  50.3: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#280)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#g] + C[Net#g])) ==> (SqnCh[Net#g][i] == i)
  );
  assert {:msg "  52.3: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#281)"} C[Net#f] == 1;
  assert {:msg "  53.3: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#282)"} C[Net#g] == R[Net#e];
  assert {:msg "  54.3: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#283)"} R[Net#e] == M[Net#f][R[Net#f]];
  assert {:msg "  55.3: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#284)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#g] + C[Net#g])) ==> (SqnCh[Net#g][i] == i)
  );
  assert {:msg "  59.3: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#285)"} (0 < R[Net#d]) && (0 < R[Net#e]) ==> (M[Net#d][R[Net#d] - 1] <= M[Net#e][R[Net#e] - 1]);
  assert {:msg "  60.3: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#286)"} (forall i: int :: 
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
  assume C[Net#g] == R[Net#e];
  assume R[Net#e] == M[Net#f][R[Net#f]];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#g] + C[Net#g])) ==> (SqnCh[Net#g][i] == i)
  );
  assume (0 < R[Net#d]) && (0 < R[Net#e]) ==> (M[Net#d][R[Net#d] - 1] <= M[Net#e][R[Net#e] - 1]);
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

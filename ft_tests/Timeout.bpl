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
  assume (M[x1][0] == M[x2][0]) && (M[x1][0] == M[c_in][0]);
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
  assume M[x1][0] < M[c_in][0];
  assume true;
}
procedure Net#init#5()
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
  C[Net#f] := C[Net#f] - 1;
  assume M[Net#f][R[Net#f]] == 0;
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
procedure Net#anon$2#entry#6()
  modifies C, R, M, St, SqnCh, SqnAct;
{
  var ActionPH#y1: int;
  var ActionPH#y2: int;
  var ActionPH#y3: int;
  assume SqnAct[Net#spl] == 0;
  assume SqnAct[Net#pri] == 0;
  assume SqnAct[Net#sec] == 0;
  assume SqnAct[Net#adj] == 0;
  assume L[Net#a] == (3 * Base#L);
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
  assume M[Net#f][R[Net#f]] == 0;
  assume (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
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
  assert {:msg "  Channel invariant might not hold on action entry (#16)"} (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
  assert {:msg "  Channel invariant might not hold on action entry (#17)"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  Channel invariant might not hold on action entry (#18)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Channel invariant might not hold on action entry (#19)"} R[Net#b] == (R[Net#d] + C[Net#d]);
  assert {:msg "  Channel invariant might not hold on action entry (#20)"} R[Net#c] == (R[Net#e] + C[Net#e]);
  assert {:msg "  Channel invariant might not hold on action entry (#21)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Channel invariant might not hold on action entry (#22)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Channel invariant might not hold on action entry (#23)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assert {:msg "  Channel invariant might not hold on action entry (#24)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#e] + C[Net#e])) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assert {:msg "  Channel invariant might not hold on action entry (#25)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][idx$] == idx$)
  );
  assert {:msg "  40.3: Channel invariant might not hold on action entry (#26)"} (R[Net#a] + C[Net#a]) <= 3;
  assert {:msg "  47.3: Channel invariant might not hold on action entry (#27)"} C[Net#f] == 1;
  assert {:msg "  48.3: Channel invariant might not hold on action entry (#28)"} C[Net#g] == R[Net#e];
  assert {:msg "  49.3: Channel invariant might not hold on action entry (#29)"} R[Net#e] == M[Net#f][R[Net#f]];
  assert {:msg "  50.3: Channel invariant might not hold on action entry (#30)"} R[Net#d] <= R[Net#e];
  assert {:msg "  51.3: Channel invariant might not hold on action entry (#31)"} (0 < R[Net#d]) && (0 < R[Net#e]) ==> (M[Net#d][R[Net#d] - 1] <= M[Net#e][R[Net#e] - 1]);
  assert {:msg "  52.3: Channel invariant might not hold on action entry (#32)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#g][i] == M[Net#e][i])
  );
}
procedure Net#anon$2#Split#anon$1#7()
  modifies C, R, M, St, SqnCh, SqnAct;
{
  var ActionPH#y1: int;
  var ActionPH#y2: int;
  var ActionPH#y3: int;
  var St#next: State;
  var in#i: int;
  assume L[Net#a] == (3 * Base#L);
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
  assume (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
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
  assume (R[Net#a] + C[Net#a]) <= 3;
  assume C[Net#f] == 1;
  assume C[Net#g] == R[Net#e];
  assume R[Net#e] == M[Net#f][R[Net#f]];
  assume R[Net#d] <= R[Net#e];
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
  assert {:msg "  Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#49)"} (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
  assert {:msg "  Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#50)"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#51)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#52)"} R[Net#b] == (R[Net#d] + C[Net#d]);
  assert {:msg "  Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#53)"} R[Net#c] == (R[Net#e] + C[Net#e]);
  assert {:msg "  Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#54)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#55)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#56)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assert {:msg "  Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#57)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#e] + C[Net#e])) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assert {:msg "  Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#58)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][idx$] == idx$)
  );
  assert {:msg "  40.3: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#59)"} (R[Net#a] + C[Net#a]) <= 3;
  assert {:msg "  47.3: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#60)"} C[Net#f] == 1;
  assert {:msg "  48.3: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#61)"} C[Net#g] == R[Net#e];
  assert {:msg "  49.3: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#62)"} R[Net#e] == M[Net#f][R[Net#f]];
  assert {:msg "  50.3: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#63)"} R[Net#d] <= R[Net#e];
  assert {:msg "  51.3: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#64)"} (0 < R[Net#d]) && (0 < R[Net#e]) ==> (M[Net#d][R[Net#d] - 1] <= M[Net#e][R[Net#e] - 1]);
  assert {:msg "  52.3: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#65)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#g][i] == M[Net#e][i])
  );
}
procedure Net#anon$2#Rep#anon$0#8()
  modifies C, R, M, St, SqnCh, SqnAct;
{
  var ActionPH#y1: int;
  var ActionPH#y2: int;
  var ActionPH#y3: int;
  var St#next: State;
  var in#i: int;
  assume L[Net#a] == (3 * Base#L);
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
  assume (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
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
  assume (R[Net#a] + C[Net#a]) <= 3;
  assume C[Net#f] == 1;
  assume C[Net#g] == R[Net#e];
  assume R[Net#e] == M[Net#f][R[Net#f]];
  assume R[Net#d] <= R[Net#e];
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
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#82)"} (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#83)"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#84)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#85)"} R[Net#b] == (R[Net#d] + C[Net#d]);
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#86)"} R[Net#c] == (R[Net#e] + C[Net#e]);
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#87)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#88)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#89)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#90)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#e] + C[Net#e])) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#91)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][idx$] == idx$)
  );
  assert {:msg "  40.3: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#92)"} (R[Net#a] + C[Net#a]) <= 3;
  assert {:msg "  47.3: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#93)"} C[Net#f] == 1;
  assert {:msg "  48.3: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#94)"} C[Net#g] == R[Net#e];
  assert {:msg "  49.3: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#95)"} R[Net#e] == M[Net#f][R[Net#f]];
  assert {:msg "  50.3: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#96)"} R[Net#d] <= R[Net#e];
  assert {:msg "  51.3: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#97)"} (0 < R[Net#d]) && (0 < R[Net#e]) ==> (M[Net#d][R[Net#d] - 1] <= M[Net#e][R[Net#e] - 1]);
  assert {:msg "  52.3: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#98)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#g][i] == M[Net#e][i])
  );
}
procedure Net#anon$2#Rep#anon$0#9()
  modifies C, R, M, St, SqnCh, SqnAct;
{
  var ActionPH#y1: int;
  var ActionPH#y2: int;
  var ActionPH#y3: int;
  var St#next: State;
  var in#i: int;
  assume L[Net#a] == (3 * Base#L);
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
  assume (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
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
  assume (R[Net#a] + C[Net#a]) <= 3;
  assume C[Net#f] == 1;
  assume C[Net#g] == R[Net#e];
  assume R[Net#e] == M[Net#f][R[Net#f]];
  assume R[Net#d] <= R[Net#e];
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
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#115)"} (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#116)"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#117)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#118)"} R[Net#b] == (R[Net#d] + C[Net#d]);
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#119)"} R[Net#c] == (R[Net#e] + C[Net#e]);
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#120)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#121)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#122)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#123)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#e] + C[Net#e])) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#124)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][idx$] == idx$)
  );
  assert {:msg "  40.3: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#125)"} (R[Net#a] + C[Net#a]) <= 3;
  assert {:msg "  47.3: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#126)"} C[Net#f] == 1;
  assert {:msg "  48.3: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#127)"} C[Net#g] == R[Net#e];
  assert {:msg "  49.3: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#128)"} R[Net#e] == M[Net#f][R[Net#f]];
  assert {:msg "  50.3: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#129)"} R[Net#d] <= R[Net#e];
  assert {:msg "  51.3: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#130)"} (0 < R[Net#d]) && (0 < R[Net#e]) ==> (M[Net#d][R[Net#d] - 1] <= M[Net#e][R[Net#e] - 1]);
  assert {:msg "  52.3: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#131)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#g][i] == M[Net#e][i])
  );
}
procedure Net#anon$2#Adjudicator#readoff#10()
  modifies C, R, M, St, SqnCh, SqnAct;
{
  var ActionPH#y1: int;
  var ActionPH#y2: int;
  var ActionPH#y3: int;
  var St#next: State;
  var x1#i: int;
  var c_in#c: int;
  assume L[Net#a] == (3 * Base#L);
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
  assume (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
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
  assume (R[Net#a] + C[Net#a]) <= 3;
  assume C[Net#f] == 1;
  assume C[Net#g] == R[Net#e];
  assume R[Net#e] == M[Net#f][R[Net#f]];
  assume R[Net#d] <= R[Net#e];
  assume (0 < R[Net#d]) && (0 < R[Net#e]) ==> (M[Net#d][R[Net#d] - 1] <= M[Net#e][R[Net#e] - 1]);
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#g][i] == M[Net#e][i])
  );
  assume M[Net#d][R[Net#d] - 0] < M[Net#f][R[Net#f] - 0];
  assume true;
  assume (1 <= C[Net#d]) && (1 <= C[Net#f]) && (M[Net#d][R[Net#d] - 0] < M[Net#f][R[Net#f] - 0]);
  x1#i := M[Net#d][R[Net#d]];
  R[Net#d] := R[Net#d] + 1;
  C[Net#d] := C[Net#d] - 1;
  c_in#c := M[Net#f][R[Net#f]];
  R[Net#f] := R[Net#f] + 1;
  C[Net#f] := C[Net#f] - 1;
  M[Net#f][R[Net#f] + C[Net#f]] := c_in#c;
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
  assert {:msg "  Action at 22.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#148)"} (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
  assert {:msg "  Action at 22.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#149)"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  Action at 22.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#150)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Action at 22.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#151)"} R[Net#b] == (R[Net#d] + C[Net#d]);
  assert {:msg "  Action at 22.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#152)"} R[Net#c] == (R[Net#e] + C[Net#e]);
  assert {:msg "  Action at 22.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#153)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 22.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#154)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 22.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#155)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assert {:msg "  Action at 22.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#156)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#e] + C[Net#e])) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assert {:msg "  Action at 22.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#157)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][idx$] == idx$)
  );
  assert {:msg "  40.3: Action at 22.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#158)"} (R[Net#a] + C[Net#a]) <= 3;
  assert {:msg "  47.3: Action at 22.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#159)"} C[Net#f] == 1;
  assert {:msg "  48.3: Action at 22.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#160)"} C[Net#g] == R[Net#e];
  assert {:msg "  49.3: Action at 22.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#161)"} R[Net#e] == M[Net#f][R[Net#f]];
  assert {:msg "  50.3: Action at 22.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#162)"} R[Net#d] <= R[Net#e];
  assert {:msg "  51.3: Action at 22.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#163)"} (0 < R[Net#d]) && (0 < R[Net#e]) ==> (M[Net#d][R[Net#d] - 1] <= M[Net#e][R[Net#e] - 1]);
  assert {:msg "  52.3: Action at 22.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#164)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#g][i] == M[Net#e][i])
  );
}
procedure Net#anon$2#Adjudicator#normal#11()
  modifies C, R, M, St, SqnCh, SqnAct;
{
  var ActionPH#y1: int;
  var ActionPH#y2: int;
  var ActionPH#y3: int;
  var St#next: State;
  var x1#i: int;
  var x2#j: int;
  var c_in#c: int;
  assume L[Net#a] == (3 * Base#L);
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
  assume (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
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
  assume (R[Net#a] + C[Net#a]) <= 3;
  assume C[Net#f] == 1;
  assume C[Net#g] == R[Net#e];
  assume R[Net#e] == M[Net#f][R[Net#f]];
  assume R[Net#d] <= R[Net#e];
  assume (0 < R[Net#d]) && (0 < R[Net#e]) ==> (M[Net#d][R[Net#d] - 1] <= M[Net#e][R[Net#e] - 1]);
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#g][i] == M[Net#e][i])
  );
  assume (M[Net#d][R[Net#d] - 0] == M[Net#e][R[Net#e] - 0]) && (M[Net#d][R[Net#d] - 0] == M[Net#f][R[Net#f] - 0]);
  assume true;
  assume (!((1 <= C[Net#d]) && (1 <= C[Net#f]) && (M[Net#d][R[Net#d] - 0] < M[Net#f][R[Net#f] - 0]))) && (1 <= C[Net#d]) && (1 <= C[Net#e]) && (1 <= C[Net#f]) && (M[Net#d][R[Net#d] - 0] == M[Net#e][R[Net#e] - 0]) && (M[Net#d][R[Net#d] - 0] == M[Net#f][R[Net#f] - 0]);
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
  assert {:msg "  Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#181)"} (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
  assert {:msg "  Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#182)"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#183)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#184)"} R[Net#b] == (R[Net#d] + C[Net#d]);
  assert {:msg "  Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#185)"} R[Net#c] == (R[Net#e] + C[Net#e]);
  assert {:msg "  Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#186)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#187)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#188)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assert {:msg "  Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#189)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#e] + C[Net#e])) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assert {:msg "  Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#190)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][idx$] == idx$)
  );
  assert {:msg "  40.3: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#191)"} (R[Net#a] + C[Net#a]) <= 3;
  assert {:msg "  47.3: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#192)"} C[Net#f] == 1;
  assert {:msg "  48.3: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#193)"} C[Net#g] == R[Net#e];
  assert {:msg "  49.3: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#194)"} R[Net#e] == M[Net#f][R[Net#f]];
  assert {:msg "  50.3: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#195)"} R[Net#d] <= R[Net#e];
  assert {:msg "  51.3: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#196)"} (0 < R[Net#d]) && (0 < R[Net#e]) ==> (M[Net#d][R[Net#d] - 1] <= M[Net#e][R[Net#e] - 1]);
  assert {:msg "  52.3: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#197)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#g][i] == M[Net#e][i])
  );
}
procedure Net#anon$2#Adjudicator#timeout#12()
  modifies C, R, M, St, SqnCh, SqnAct;
{
  var ActionPH#y1: int;
  var ActionPH#y2: int;
  var ActionPH#y3: int;
  var St#next: State;
  var x2#j: int;
  var c_in#c: int;
  assume L[Net#a] == (3 * Base#L);
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
  assume (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
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
  assume (R[Net#a] + C[Net#a]) <= 3;
  assume C[Net#f] == 1;
  assume C[Net#g] == R[Net#e];
  assume R[Net#e] == M[Net#f][R[Net#f]];
  assume R[Net#d] <= R[Net#e];
  assume (0 < R[Net#d]) && (0 < R[Net#e]) ==> (M[Net#d][R[Net#d] - 1] <= M[Net#e][R[Net#e] - 1]);
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#g][i] == M[Net#e][i])
  );
  assume true;
  assume (!((1 <= C[Net#d]) && (1 <= C[Net#f]) && (M[Net#d][R[Net#d] - 0] < M[Net#f][R[Net#f] - 0]))) && (!((1 <= C[Net#d]) && (1 <= C[Net#e]) && (1 <= C[Net#f]) && (M[Net#d][R[Net#d] - 0] == M[Net#e][R[Net#e] - 0]) && (M[Net#d][R[Net#d] - 0] == M[Net#f][R[Net#f] - 0]))) && (1 <= C[Net#e]) && (1 <= C[Net#f]);
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
  assert {:msg "  Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#214)"} (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
  assert {:msg "  Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#215)"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#216)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#217)"} R[Net#b] == (R[Net#d] + C[Net#d]);
  assert {:msg "  Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#218)"} R[Net#c] == (R[Net#e] + C[Net#e]);
  assert {:msg "  Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#219)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#220)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#221)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assert {:msg "  Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#222)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#e] + C[Net#e])) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assert {:msg "  Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#223)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][idx$] == idx$)
  );
  assert {:msg "  40.3: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#224)"} (R[Net#a] + C[Net#a]) <= 3;
  assert {:msg "  47.3: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#225)"} C[Net#f] == 1;
  assert {:msg "  48.3: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#226)"} C[Net#g] == R[Net#e];
  assert {:msg "  49.3: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#227)"} R[Net#e] == M[Net#f][R[Net#f]];
  assert {:msg "  50.3: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#228)"} R[Net#d] <= R[Net#e];
  assert {:msg "  51.3: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#229)"} (0 < R[Net#d]) && (0 < R[Net#e]) ==> (M[Net#d][R[Net#d] - 1] <= M[Net#e][R[Net#e] - 1]);
  assert {:msg "  52.3: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#230)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#g][i] == M[Net#e][i])
  );
}
procedure Net#anon$2#exit#13()
  modifies C, R, M, St, SqnCh, SqnAct;
{
  var ActionPH#y1: int;
  var ActionPH#y2: int;
  var ActionPH#y3: int;
  assume L[Net#a] == (3 * Base#L);
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
  assume (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
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
  assume (R[Net#a] + C[Net#a]) <= 3;
  assume C[Net#f] == 1;
  assume C[Net#g] == R[Net#e];
  assume R[Net#e] == M[Net#f][R[Net#f]];
  assume R[Net#d] <= R[Net#e];
  assume (0 < R[Net#d]) && (0 < R[Net#e]) ==> (M[Net#d][R[Net#d] - 1] <= M[Net#e][R[Net#e] - 1]);
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#g][i] == M[Net#e][i])
  );
  assume !((R[Net#a] + C[Net#a]) < L[Net#a]);
  assume !(1 <= C[Net#a]);
  assume !(1 <= C[Net#b]);
  assume !(1 <= C[Net#c]);
  assume !((!((1 <= C[Net#d]) && (1 <= C[Net#f]) && (M[Net#d][R[Net#d] - 0] < M[Net#f][R[Net#f] - 0]))) && (1 <= C[Net#d]) && (1 <= C[Net#e]) && (1 <= C[Net#f]) && (M[Net#d][R[Net#d] - 0] == M[Net#e][R[Net#e] - 0]) && (M[Net#d][R[Net#d] - 0] == M[Net#f][R[Net#f] - 0]));
  assume !((1 <= C[Net#d]) && (1 <= C[Net#f]) && (M[Net#d][R[Net#d] - 0] < M[Net#f][R[Net#f] - 0]));
  assume !((!((1 <= C[Net#d]) && (1 <= C[Net#f]) && (M[Net#d][R[Net#d] - 0] < M[Net#f][R[Net#f] - 0]))) && (!((1 <= C[Net#d]) && (1 <= C[Net#e]) && (1 <= C[Net#f]) && (M[Net#d][R[Net#d] - 0] == M[Net#e][R[Net#e] - 0]) && (M[Net#d][R[Net#d] - 0] == M[Net#f][R[Net#f] - 0]))) && (1 <= C[Net#e]) && (1 <= C[Net#f]));
  ActionPH#y1 := M[Net#g][0];
  ActionPH#y2 := M[Net#g][1];
  ActionPH#y3 := M[Net#g][2];
  assert {:msg "  34.13: Network action postcondition might not hold"} (ActionPH#y1 == M[Net#a][0]) && (ActionPH#y2 == M[Net#a][1]) && (ActionPH#y3 == M[Net#a][2]);
  R[Net#g] := R[Net#g] + C[Net#g];
  C[Net#g] := C[Net#g] - (3 * Base#L);
  C[Net#f] := C[Net#f] - 1;
  assume M[Net#f][R[Net#f]] == 0;
  assert {:msg "  32.3: The network might leave unread tokens on channel a"} C[Net#a] == 0;
  assert {:msg "  32.3: The network might leave unread tokens on channel b"} C[Net#b] == 0;
  assert {:msg "  32.3: The network might leave unread tokens on channel c"} C[Net#c] == 0;
  assert {:msg "  32.3: The network might leave unread tokens on channel d"} C[Net#d] == 0;
  assert {:msg "  32.3: The network might leave unread tokens on channel e"} C[Net#e] == 0;
  assert {:msg "  32.3: The network might leave unread tokens on channel f"} C[Net#f] == 0;
  assert {:msg "  32.3: The network might not produce the specified number of tokens on output out"} C[Net#g] == 0;
}

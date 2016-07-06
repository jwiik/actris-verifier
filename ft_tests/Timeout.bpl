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

// -- Types and global variables ---------------------------------
type SeqType = <a>[Chan a][int]int;
var Seq: SeqType;

// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

axiom Base#L == 1;
procedure Rep#anon$0#0()
  modifies C, R, M, St;
{
  var in: Chan (int);
  var out: Chan (int);
  assume true;
  assume true;
}
procedure Split#anon$1#1()
  modifies C, R, M, St;
{
  var in: Chan (int);
  var out1: Chan (int);
  var out2: Chan (int);
  assume true;
  assume true;
}
procedure Adjudicator#normal#2()
  modifies C, R, M, St;
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
  modifies C, R, M, St;
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
  modifies C, R, M, St;
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
  modifies C, R, M, St;
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
  modifies C, R, M, St;
{
  var ActionPH#y1: int;
  var ActionPH#y2: int;
  var ActionPH#y3: int;
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
  assert {:msg "  40.3: Channel invariant might not hold on action entry (#25)"} (R[Net#a] + C[Net#a]) <= 3;
  assert {:msg "  47.3: Channel invariant might not hold on action entry (#26)"} C[Net#f] == 1;
  assert {:msg "  48.3: Channel invariant might not hold on action entry (#27)"} C[Net#g] == R[Net#e];
  assert {:msg "  49.3: Channel invariant might not hold on action entry (#28)"} R[Net#e] == M[Net#f][R[Net#f]];
  assert {:msg "  50.3: Channel invariant might not hold on action entry (#29)"} R[Net#d] <= R[Net#e];
  assert {:msg "  51.3: Channel invariant might not hold on action entry (#30)"} (0 < R[Net#d]) && (0 < R[Net#e]) ==> (M[Net#d][R[Net#d] - 1] <= M[Net#e][R[Net#e] - 1]);
  assert {:msg "  52.3: Channel invariant might not hold on action entry (#31)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#g][i] == M[Net#e][i])
  );
}
procedure Net#anon$2#Split#anon$1#7()
  modifies C, R, M, St;
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
  C[Net#b] := C[Net#b] + 1;
  M[Net#c][R[Net#c] + C[Net#c]] := in#i;
  C[Net#c] := C[Net#c] + 1;
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
  assert {:msg "  Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#48)"} (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
  assert {:msg "  Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#49)"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#50)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#51)"} R[Net#b] == (R[Net#d] + C[Net#d]);
  assert {:msg "  Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#52)"} R[Net#c] == (R[Net#e] + C[Net#e]);
  assert {:msg "  Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#53)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#54)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#55)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assert {:msg "  Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#56)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#e] + C[Net#e])) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assert {:msg "  40.3: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#57)"} (R[Net#a] + C[Net#a]) <= 3;
  assert {:msg "  47.3: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#58)"} C[Net#f] == 1;
  assert {:msg "  48.3: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#59)"} C[Net#g] == R[Net#e];
  assert {:msg "  49.3: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#60)"} R[Net#e] == M[Net#f][R[Net#f]];
  assert {:msg "  50.3: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#61)"} R[Net#d] <= R[Net#e];
  assert {:msg "  51.3: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#62)"} (0 < R[Net#d]) && (0 < R[Net#e]) ==> (M[Net#d][R[Net#d] - 1] <= M[Net#e][R[Net#e] - 1]);
  assert {:msg "  52.3: Action at 8.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#63)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#g][i] == M[Net#e][i])
  );
}
procedure Net#anon$2#Rep#anon$0#8()
  modifies C, R, M, St;
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
  C[Net#d] := C[Net#d] + 1;
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
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#80)"} (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#81)"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#82)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#83)"} R[Net#b] == (R[Net#d] + C[Net#d]);
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#84)"} R[Net#c] == (R[Net#e] + C[Net#e]);
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#85)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#86)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#87)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#88)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#e] + C[Net#e])) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assert {:msg "  40.3: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#89)"} (R[Net#a] + C[Net#a]) <= 3;
  assert {:msg "  47.3: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#90)"} C[Net#f] == 1;
  assert {:msg "  48.3: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#91)"} C[Net#g] == R[Net#e];
  assert {:msg "  49.3: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#92)"} R[Net#e] == M[Net#f][R[Net#f]];
  assert {:msg "  50.3: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#93)"} R[Net#d] <= R[Net#e];
  assert {:msg "  51.3: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#94)"} (0 < R[Net#d]) && (0 < R[Net#e]) ==> (M[Net#d][R[Net#d] - 1] <= M[Net#e][R[Net#e] - 1]);
  assert {:msg "  52.3: Action at 3.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#95)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#g][i] == M[Net#e][i])
  );
}
procedure Net#anon$2#Rep#anon$0#9()
  modifies C, R, M, St;
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
  C[Net#e] := C[Net#e] + 1;
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
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#112)"} (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#113)"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#114)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#115)"} R[Net#b] == (R[Net#d] + C[Net#d]);
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#116)"} R[Net#c] == (R[Net#e] + C[Net#e]);
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#117)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#118)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#119)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#120)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#e] + C[Net#e])) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assert {:msg "  40.3: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#121)"} (R[Net#a] + C[Net#a]) <= 3;
  assert {:msg "  47.3: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#122)"} C[Net#f] == 1;
  assert {:msg "  48.3: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#123)"} C[Net#g] == R[Net#e];
  assert {:msg "  49.3: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#124)"} R[Net#e] == M[Net#f][R[Net#f]];
  assert {:msg "  50.3: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#125)"} R[Net#d] <= R[Net#e];
  assert {:msg "  51.3: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#126)"} (0 < R[Net#d]) && (0 < R[Net#e]) ==> (M[Net#d][R[Net#d] - 1] <= M[Net#e][R[Net#e] - 1]);
  assert {:msg "  52.3: Action at 3.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#127)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#g][i] == M[Net#e][i])
  );
}
procedure Net#anon$2#Adjudicator#readoff#10()
  modifies C, R, M, St;
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
  assert {:msg "  Action at 22.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#144)"} (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
  assert {:msg "  Action at 22.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#145)"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  Action at 22.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#146)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Action at 22.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#147)"} R[Net#b] == (R[Net#d] + C[Net#d]);
  assert {:msg "  Action at 22.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#148)"} R[Net#c] == (R[Net#e] + C[Net#e]);
  assert {:msg "  Action at 22.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#149)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 22.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#150)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 22.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#151)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assert {:msg "  Action at 22.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#152)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#e] + C[Net#e])) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assert {:msg "  40.3: Action at 22.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#153)"} (R[Net#a] + C[Net#a]) <= 3;
  assert {:msg "  47.3: Action at 22.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#154)"} C[Net#f] == 1;
  assert {:msg "  48.3: Action at 22.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#155)"} C[Net#g] == R[Net#e];
  assert {:msg "  49.3: Action at 22.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#156)"} R[Net#e] == M[Net#f][R[Net#f]];
  assert {:msg "  50.3: Action at 22.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#157)"} R[Net#d] <= R[Net#e];
  assert {:msg "  51.3: Action at 22.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#158)"} (0 < R[Net#d]) && (0 < R[Net#e]) ==> (M[Net#d][R[Net#d] - 1] <= M[Net#e][R[Net#e] - 1]);
  assert {:msg "  52.3: Action at 22.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#159)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#g][i] == M[Net#e][i])
  );
}
procedure Net#anon$2#Adjudicator#normal#11()
  modifies C, R, M, St;
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
  C[Net#g] := C[Net#g] + 1;
  M[Net#f][R[Net#f] + C[Net#f]] := c_in#c + 1;
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
  assert {:msg "  Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#176)"} (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
  assert {:msg "  Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#177)"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#178)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#179)"} R[Net#b] == (R[Net#d] + C[Net#d]);
  assert {:msg "  Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#180)"} R[Net#c] == (R[Net#e] + C[Net#e]);
  assert {:msg "  Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#181)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#182)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#183)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assert {:msg "  Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#184)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#e] + C[Net#e])) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assert {:msg "  40.3: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#185)"} (R[Net#a] + C[Net#a]) <= 3;
  assert {:msg "  47.3: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#186)"} C[Net#f] == 1;
  assert {:msg "  48.3: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#187)"} C[Net#g] == R[Net#e];
  assert {:msg "  49.3: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#188)"} R[Net#e] == M[Net#f][R[Net#f]];
  assert {:msg "  50.3: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#189)"} R[Net#d] <= R[Net#e];
  assert {:msg "  51.3: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#190)"} (0 < R[Net#d]) && (0 < R[Net#e]) ==> (M[Net#d][R[Net#d] - 1] <= M[Net#e][R[Net#e] - 1]);
  assert {:msg "  52.3: Action at 14.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#191)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#g][i] == M[Net#e][i])
  );
}
procedure Net#anon$2#Adjudicator#timeout#12()
  modifies C, R, M, St;
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
  C[Net#g] := C[Net#g] + 1;
  M[Net#f][R[Net#f] + C[Net#f]] := c_in#c + 1;
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
  assert {:msg "  Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#208)"} (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
  assert {:msg "  Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#209)"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#210)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#211)"} R[Net#b] == (R[Net#d] + C[Net#d]);
  assert {:msg "  Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#212)"} R[Net#c] == (R[Net#e] + C[Net#e]);
  assert {:msg "  Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#213)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#214)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#215)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assert {:msg "  Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#216)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#e] + C[Net#e])) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assert {:msg "  40.3: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#217)"} (R[Net#a] + C[Net#a]) <= 3;
  assert {:msg "  47.3: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#218)"} C[Net#f] == 1;
  assert {:msg "  48.3: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#219)"} C[Net#g] == R[Net#e];
  assert {:msg "  49.3: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#220)"} R[Net#e] == M[Net#f][R[Net#f]];
  assert {:msg "  50.3: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#221)"} R[Net#d] <= R[Net#e];
  assert {:msg "  51.3: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#222)"} (0 < R[Net#d]) && (0 < R[Net#e]) ==> (M[Net#d][R[Net#d] - 1] <= M[Net#e][R[Net#e] - 1]);
  assert {:msg "  52.3: Action at 18.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#223)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#g][i] == M[Net#e][i])
  );
}
procedure Net#anon$2#exit#13()
  modifies C, R, M, St;
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

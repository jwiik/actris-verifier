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


// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

procedure Add#anon$0#0()
  modifies C, R, M, St;
{
  var IV#in1#0: int;
  var IV#in2#0: int;
  assume true;
  assume true;
}
procedure Sub#anon$1#1()
  modifies C, R, M, St;
{
  var IV#in1#0: int;
  var IV#in2#0: int;
  assume true;
  assume true;
}
procedure Select#anon$2#2()
  modifies C, R, M, St;
{
  var IV#sel#0: bool;
  var IV#in1#0: int;
  var IV#in2#0: int;
  assume true;
  assume IV#sel#0;
  assume true;
}
procedure Select#anon$3#3()
  modifies C, R, M, St;
{
  var IV#sel#0: bool;
  var IV#in1#0: int;
  var IV#in2#0: int;
  assume true;
  assume !IV#sel#0;
  assume true;
}
procedure Delay#anon$4#4()
  modifies C, R, M, St;
{
  assume true;
  assume true;
}
procedure Delay#anon$5#5()
  modifies C, R, M, St;
{
  var IV#in#0: int;
  assume true;
  assume true;
}
procedure Split#anon$6#6()
  modifies C, R, M, St;
{
  var IV#in#0: int;
  assume true;
  assume true;
}
procedure Net#init#7()
  modifies C, R, M, St;
{
  var ActorParam#del#k: int;
  assume C[Net#a] == 0;
  assume R[Net#a] == 0;
  assume C[Net#b] == 0;
  assume R[Net#b] == 0;
  assume C[Net#c] == 0;
  assume R[Net#c] == 0;
  assume C[Net#d] == 0;
  assume R[Net#d] == 0;
  assume C[Net#f] == 0;
  assume R[Net#f] == 0;
  assume C[Net#g] == 0;
  assume R[Net#g] == 0;
  assume C[Net#h] == 0;
  assume R[Net#h] == 0;
  assume C[Net#i] == 0;
  assume R[Net#i] == 0;
  assume C[Net#j] == 0;
  assume R[Net#j] == 0;
  assume C[Net#k] == 0;
  assume R[Net#k] == 0;
  assume ActorParam#del#k == 0;
  M[Net#d][R[Net#d] + C[Net#d]] := ActorParam#del#k;
  C[Net#d] := C[Net#d] + 1;
  M[Net#h][R[Net#h] + C[Net#h]] := ActorParam#del#k;
  C[Net#h] := C[Net#h] + 1;
  C[Net#d] := C[Net#d] - 1;
  C[Net#h] := C[Net#h] - 1;
  assert {:msg "  40.13: Network initialization might not establish the network invariant"} 0 <= M[Net#d][R[Net#d]];
  assert {:msg "  41.13: Network initialization might not establish the network invariant"} 0 <= M[Net#h][R[Net#h]];
}
const unique Net#spl: Actor;
const unique Net#add: Actor;
const unique Net#del: Actor;
const unique Net#sub: Actor;
const unique Net#sel: Actor;
const unique Net#a: Chan (int);
const unique Net#b: Chan (int);
const unique Net#c: Chan (int);
const unique Net#d: Chan (int);
const unique Net#f: Chan (int);
const unique Net#g: Chan (int);
const unique Net#h: Chan (int);
const unique Net#i: Chan (int);
const unique Net#j: Chan (bool);
const unique Net#k: Chan (int);
procedure Net#anon$7#entry#8()
  modifies C, R, M, St;
{
  var ActionPH#y: int;
  assume L[Net#a] == (1 * Base#L);
  assume L[Net#j] == (1 * Base#L);
  assume R[Net#a] == 0;
  assume C[Net#a] == 0;
  assume R[Net#b] == 0;
  assume C[Net#b] == 0;
  assume R[Net#c] == 0;
  assume C[Net#c] == 0;
  assume R[Net#d] == 0;
  assume C[Net#d] == 0;
  assume R[Net#f] == 0;
  assume C[Net#f] == 0;
  assume R[Net#g] == 0;
  assume C[Net#g] == 0;
  assume R[Net#h] == 0;
  assume C[Net#h] == 0;
  assume R[Net#i] == 0;
  assume C[Net#i] == 0;
  assume R[Net#j] == 0;
  assume C[Net#j] == 0;
  assume R[Net#k] == 0;
  assume C[Net#k] == 0;
  C[Net#d] := C[Net#d] + 1;
  C[Net#h] := C[Net#h] + 1;
  assume 0 <= M[Net#d][R[Net#d]];
  assume 0 <= M[Net#h][R[Net#h]];
  assume (forall ind: int :: 
    (0 <= ind) && (ind < (R[Net#a] + C[Net#a])) ==> (0 < M[Net#a][ind])
  );
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) <= L[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume 0 <= R[Net#d];
  assume 0 <= C[Net#d];
  assume 0 <= R[Net#f];
  assume 0 <= C[Net#f];
  assume 0 <= R[Net#g];
  assume 0 <= C[Net#g];
  assume 0 <= R[Net#h];
  assume 0 <= C[Net#h];
  assume 0 <= R[Net#i];
  assume 0 <= C[Net#i];
  assume 0 <= R[Net#j];
  assume 0 <= C[Net#j];
  assume (R[Net#j] + C[Net#j]) <= L[Net#j];
  assume 0 <= R[Net#k];
  assume 0 <= C[Net#k];
  assume R[Net#k] == 0;
  assert {:msg "  Channel invariant might not hold on action entry (#23)"} (forall ind: int :: 
    (0 <= ind) && (ind < (R[Net#a] + C[Net#a])) ==> (0 < M[Net#a][ind])
  );
  assert {:msg "  Channel invariant might not hold on action entry (#24)"} (forall ind: int :: 
    (0 <= ind) && (ind < (R[Net#a] + C[Net#a])) ==> (0 < M[Net#a][ind])
  );
  assert {:msg "  Channel invariant might not hold on action entry (#25)"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  Channel invariant might not hold on action entry (#26)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Channel invariant might not hold on action entry (#27)"} R[Net#b] == (R[Net#f] + C[Net#f]);
  assert {:msg "  Channel invariant might not hold on action entry (#28)"} R[Net#d] == (R[Net#f] + C[Net#f]);
  assert {:msg "  Channel invariant might not hold on action entry (#29)"} R[Net#b] == (R[Net#g] + C[Net#g]);
  assert {:msg "  Channel invariant might not hold on action entry (#30)"} R[Net#d] == (R[Net#g] + C[Net#g]);
  assert {:msg "  Channel invariant might not hold on action entry (#31)"} R[Net#g] == ((R[Net#d] + C[Net#d]) - 1);
  assert {:msg "  Channel invariant might not hold on action entry (#32)"} R[Net#g] == ((R[Net#h] + C[Net#h]) - 1);
  assert {:msg "  Channel invariant might not hold on action entry (#33)"} R[Net#c] == (R[Net#i] + C[Net#i]);
  assert {:msg "  Channel invariant might not hold on action entry (#34)"} R[Net#h] == (R[Net#i] + C[Net#i]);
  assert {:msg "  Channel invariant might not hold on action entry (#35)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Channel invariant might not hold on action entry (#36)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Channel invariant might not hold on action entry (#37)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#f] + C[Net#f])) ==> (M[Net#f][idx$] == (M[Net#b][idx$] + M[Net#d][idx$]))
  );
  assert {:msg "  Channel invariant might not hold on action entry (#38)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#g] + C[Net#g])) ==> (M[Net#g][idx$] == (M[Net#b][idx$] + M[Net#d][idx$]))
  );
  assert {:msg "  Channel invariant might not hold on action entry (#39)"} (forall idx$: int :: 
    (1 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#g][idx$ - 1])
  );
  assert {:msg "  Channel invariant might not hold on action entry (#40)"} (forall idx$: int :: 
    (1 <= idx$) && (idx$ < (R[Net#h] + C[Net#h])) ==> (M[Net#h][idx$] == M[Net#g][idx$ - 1])
  );
  assert {:msg "  Channel invariant might not hold on action entry (#41)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#i] + C[Net#i])) ==> (M[Net#i][idx$] == (M[Net#c][idx$] - M[Net#h][idx$]))
  );
  assert {:msg "  43.3: Channel invariant might not hold on action entry (#42)"} 0 <= M[Net#d][0];
  assert {:msg "  44.3: Channel invariant might not hold on action entry (#43)"} 0 <= M[Net#h][0];
  assert {:msg "  45.3: Channel invariant might not hold on action entry (#44)"} (R[Net#k] + C[Net#k]) == R[Net#f];
  assert {:msg "  46.3: Channel invariant might not hold on action entry (#45)"} (R[Net#k] + C[Net#k]) == R[Net#i];
  assert {:msg "  47.3: Channel invariant might not hold on action entry (#46)"} (R[Net#k] + C[Net#k]) == R[Net#j];
  assert {:msg "  48.3: Channel invariant might not hold on action entry (#47)"} (forall ind: int :: 
    (0 <= ind) && (ind < (R[Net#k] + C[Net#k])) ==> ((!M[Net#j][ind]) ==> (M[Net#k][ind] == M[Net#i][ind]))
  );
  assert {:msg "  49.3: Channel invariant might not hold on action entry (#48)"} (forall ind: int :: 
    (0 <= ind) && (ind < (R[Net#k] + C[Net#k])) ==> (M[Net#j][ind] ==> (M[Net#k][ind] == M[Net#f][ind]))
  );
}
procedure Net#anon$7#Split#anon$6#9()
  modifies C, R, M, St;
{
  var ActionPH#y: int;
  var St#next: State;
  var in#i: int;
  assume L[Net#a] == (1 * Base#L);
  assume L[Net#j] == (1 * Base#L);
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) <= L[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume 0 <= R[Net#d];
  assume 0 <= C[Net#d];
  assume 0 <= R[Net#f];
  assume 0 <= C[Net#f];
  assume 0 <= R[Net#g];
  assume 0 <= C[Net#g];
  assume 0 <= R[Net#h];
  assume 0 <= C[Net#h];
  assume 0 <= R[Net#i];
  assume 0 <= C[Net#i];
  assume 0 <= R[Net#j];
  assume 0 <= C[Net#j];
  assume (R[Net#j] + C[Net#j]) <= L[Net#j];
  assume 0 <= R[Net#k];
  assume 0 <= C[Net#k];
  assume R[Net#k] == 0;
  assume (forall ind: int :: 
    (0 <= ind) && (ind < (R[Net#a] + C[Net#a])) ==> (0 < M[Net#a][ind])
  );
  assume (forall ind: int :: 
    (0 <= ind) && (ind < (R[Net#a] + C[Net#a])) ==> (0 < M[Net#a][ind])
  );
  assume R[Net#a] == (R[Net#b] + C[Net#b]);
  assume R[Net#a] == (R[Net#c] + C[Net#c]);
  assume R[Net#b] == (R[Net#f] + C[Net#f]);
  assume R[Net#d] == (R[Net#f] + C[Net#f]);
  assume R[Net#b] == (R[Net#g] + C[Net#g]);
  assume R[Net#d] == (R[Net#g] + C[Net#g]);
  assume R[Net#g] == ((R[Net#d] + C[Net#d]) - 1);
  assume R[Net#g] == ((R[Net#h] + C[Net#h]) - 1);
  assume R[Net#c] == (R[Net#i] + C[Net#i]);
  assume R[Net#h] == (R[Net#i] + C[Net#i]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#f] + C[Net#f])) ==> (M[Net#f][idx$] == (M[Net#b][idx$] + M[Net#d][idx$]))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#g] + C[Net#g])) ==> (M[Net#g][idx$] == (M[Net#b][idx$] + M[Net#d][idx$]))
  );
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#g][idx$ - 1])
  );
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < (R[Net#h] + C[Net#h])) ==> (M[Net#h][idx$] == M[Net#g][idx$ - 1])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#i] + C[Net#i])) ==> (M[Net#i][idx$] == (M[Net#c][idx$] - M[Net#h][idx$]))
  );
  assume 0 <= M[Net#d][0];
  assume 0 <= M[Net#h][0];
  assume (R[Net#k] + C[Net#k]) == R[Net#f];
  assume (R[Net#k] + C[Net#k]) == R[Net#i];
  assume (R[Net#k] + C[Net#k]) == R[Net#j];
  assume (forall ind: int :: 
    (0 <= ind) && (ind < (R[Net#k] + C[Net#k])) ==> ((!M[Net#j][ind]) ==> (M[Net#k][ind] == M[Net#i][ind]))
  );
  assume (forall ind: int :: 
    (0 <= ind) && (ind < (R[Net#k] + C[Net#k])) ==> (M[Net#j][ind] ==> (M[Net#k][ind] == M[Net#f][ind]))
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
  assume 0 <= R[Net#f];
  assume 0 <= C[Net#f];
  assume 0 <= R[Net#g];
  assume 0 <= C[Net#g];
  assume 0 <= R[Net#h];
  assume 0 <= C[Net#h];
  assume 0 <= R[Net#i];
  assume 0 <= C[Net#i];
  assume 0 <= R[Net#j];
  assume 0 <= C[Net#j];
  assume (R[Net#j] + C[Net#j]) <= L[Net#j];
  assume 0 <= R[Net#k];
  assume 0 <= C[Net#k];
  assume R[Net#k] == 0;
  assert {:msg "  Action at 28.3 ('anon$6') for actor instance 'spl' might not preserve the channel invariant (#72)"} (forall ind: int :: 
    (0 <= ind) && (ind < (R[Net#a] + C[Net#a])) ==> (0 < M[Net#a][ind])
  );
  assert {:msg "  Action at 28.3 ('anon$6') for actor instance 'spl' might not preserve the channel invariant (#73)"} (forall ind: int :: 
    (0 <= ind) && (ind < (R[Net#a] + C[Net#a])) ==> (0 < M[Net#a][ind])
  );
  assert {:msg "  Action at 28.3 ('anon$6') for actor instance 'spl' might not preserve the channel invariant (#74)"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  Action at 28.3 ('anon$6') for actor instance 'spl' might not preserve the channel invariant (#75)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Action at 28.3 ('anon$6') for actor instance 'spl' might not preserve the channel invariant (#76)"} R[Net#b] == (R[Net#f] + C[Net#f]);
  assert {:msg "  Action at 28.3 ('anon$6') for actor instance 'spl' might not preserve the channel invariant (#77)"} R[Net#d] == (R[Net#f] + C[Net#f]);
  assert {:msg "  Action at 28.3 ('anon$6') for actor instance 'spl' might not preserve the channel invariant (#78)"} R[Net#b] == (R[Net#g] + C[Net#g]);
  assert {:msg "  Action at 28.3 ('anon$6') for actor instance 'spl' might not preserve the channel invariant (#79)"} R[Net#d] == (R[Net#g] + C[Net#g]);
  assert {:msg "  Action at 28.3 ('anon$6') for actor instance 'spl' might not preserve the channel invariant (#80)"} R[Net#g] == ((R[Net#d] + C[Net#d]) - 1);
  assert {:msg "  Action at 28.3 ('anon$6') for actor instance 'spl' might not preserve the channel invariant (#81)"} R[Net#g] == ((R[Net#h] + C[Net#h]) - 1);
  assert {:msg "  Action at 28.3 ('anon$6') for actor instance 'spl' might not preserve the channel invariant (#82)"} R[Net#c] == (R[Net#i] + C[Net#i]);
  assert {:msg "  Action at 28.3 ('anon$6') for actor instance 'spl' might not preserve the channel invariant (#83)"} R[Net#h] == (R[Net#i] + C[Net#i]);
  assert {:msg "  Action at 28.3 ('anon$6') for actor instance 'spl' might not preserve the channel invariant (#84)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 28.3 ('anon$6') for actor instance 'spl' might not preserve the channel invariant (#85)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 28.3 ('anon$6') for actor instance 'spl' might not preserve the channel invariant (#86)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#f] + C[Net#f])) ==> (M[Net#f][idx$] == (M[Net#b][idx$] + M[Net#d][idx$]))
  );
  assert {:msg "  Action at 28.3 ('anon$6') for actor instance 'spl' might not preserve the channel invariant (#87)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#g] + C[Net#g])) ==> (M[Net#g][idx$] == (M[Net#b][idx$] + M[Net#d][idx$]))
  );
  assert {:msg "  Action at 28.3 ('anon$6') for actor instance 'spl' might not preserve the channel invariant (#88)"} (forall idx$: int :: 
    (1 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#g][idx$ - 1])
  );
  assert {:msg "  Action at 28.3 ('anon$6') for actor instance 'spl' might not preserve the channel invariant (#89)"} (forall idx$: int :: 
    (1 <= idx$) && (idx$ < (R[Net#h] + C[Net#h])) ==> (M[Net#h][idx$] == M[Net#g][idx$ - 1])
  );
  assert {:msg "  Action at 28.3 ('anon$6') for actor instance 'spl' might not preserve the channel invariant (#90)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#i] + C[Net#i])) ==> (M[Net#i][idx$] == (M[Net#c][idx$] - M[Net#h][idx$]))
  );
  assert {:msg "  43.3: Action at 28.3 ('anon$6') for actor instance 'spl' might not preserve the channel invariant (#91)"} 0 <= M[Net#d][0];
  assert {:msg "  44.3: Action at 28.3 ('anon$6') for actor instance 'spl' might not preserve the channel invariant (#92)"} 0 <= M[Net#h][0];
  assert {:msg "  45.3: Action at 28.3 ('anon$6') for actor instance 'spl' might not preserve the channel invariant (#93)"} (R[Net#k] + C[Net#k]) == R[Net#f];
  assert {:msg "  46.3: Action at 28.3 ('anon$6') for actor instance 'spl' might not preserve the channel invariant (#94)"} (R[Net#k] + C[Net#k]) == R[Net#i];
  assert {:msg "  47.3: Action at 28.3 ('anon$6') for actor instance 'spl' might not preserve the channel invariant (#95)"} (R[Net#k] + C[Net#k]) == R[Net#j];
  assert {:msg "  48.3: Action at 28.3 ('anon$6') for actor instance 'spl' might not preserve the channel invariant (#96)"} (forall ind: int :: 
    (0 <= ind) && (ind < (R[Net#k] + C[Net#k])) ==> ((!M[Net#j][ind]) ==> (M[Net#k][ind] == M[Net#i][ind]))
  );
  assert {:msg "  49.3: Action at 28.3 ('anon$6') for actor instance 'spl' might not preserve the channel invariant (#97)"} (forall ind: int :: 
    (0 <= ind) && (ind < (R[Net#k] + C[Net#k])) ==> (M[Net#j][ind] ==> (M[Net#k][ind] == M[Net#f][ind]))
  );
}
procedure Net#anon$7#Add#anon$0#10()
  modifies C, R, M, St;
{
  var ActionPH#y: int;
  var St#next: State;
  var in1#i: int;
  var in2#j: int;
  assume L[Net#a] == (1 * Base#L);
  assume L[Net#j] == (1 * Base#L);
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) <= L[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume 0 <= R[Net#d];
  assume 0 <= C[Net#d];
  assume 0 <= R[Net#f];
  assume 0 <= C[Net#f];
  assume 0 <= R[Net#g];
  assume 0 <= C[Net#g];
  assume 0 <= R[Net#h];
  assume 0 <= C[Net#h];
  assume 0 <= R[Net#i];
  assume 0 <= C[Net#i];
  assume 0 <= R[Net#j];
  assume 0 <= C[Net#j];
  assume (R[Net#j] + C[Net#j]) <= L[Net#j];
  assume 0 <= R[Net#k];
  assume 0 <= C[Net#k];
  assume R[Net#k] == 0;
  assume (forall ind: int :: 
    (0 <= ind) && (ind < (R[Net#a] + C[Net#a])) ==> (0 < M[Net#a][ind])
  );
  assume (forall ind: int :: 
    (0 <= ind) && (ind < (R[Net#a] + C[Net#a])) ==> (0 < M[Net#a][ind])
  );
  assume R[Net#a] == (R[Net#b] + C[Net#b]);
  assume R[Net#a] == (R[Net#c] + C[Net#c]);
  assume R[Net#b] == (R[Net#f] + C[Net#f]);
  assume R[Net#d] == (R[Net#f] + C[Net#f]);
  assume R[Net#b] == (R[Net#g] + C[Net#g]);
  assume R[Net#d] == (R[Net#g] + C[Net#g]);
  assume R[Net#g] == ((R[Net#d] + C[Net#d]) - 1);
  assume R[Net#g] == ((R[Net#h] + C[Net#h]) - 1);
  assume R[Net#c] == (R[Net#i] + C[Net#i]);
  assume R[Net#h] == (R[Net#i] + C[Net#i]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#f] + C[Net#f])) ==> (M[Net#f][idx$] == (M[Net#b][idx$] + M[Net#d][idx$]))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#g] + C[Net#g])) ==> (M[Net#g][idx$] == (M[Net#b][idx$] + M[Net#d][idx$]))
  );
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#g][idx$ - 1])
  );
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < (R[Net#h] + C[Net#h])) ==> (M[Net#h][idx$] == M[Net#g][idx$ - 1])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#i] + C[Net#i])) ==> (M[Net#i][idx$] == (M[Net#c][idx$] - M[Net#h][idx$]))
  );
  assume 0 <= M[Net#d][0];
  assume 0 <= M[Net#h][0];
  assume (R[Net#k] + C[Net#k]) == R[Net#f];
  assume (R[Net#k] + C[Net#k]) == R[Net#i];
  assume (R[Net#k] + C[Net#k]) == R[Net#j];
  assume (forall ind: int :: 
    (0 <= ind) && (ind < (R[Net#k] + C[Net#k])) ==> ((!M[Net#j][ind]) ==> (M[Net#k][ind] == M[Net#i][ind]))
  );
  assume (forall ind: int :: 
    (0 <= ind) && (ind < (R[Net#k] + C[Net#k])) ==> (M[Net#j][ind] ==> (M[Net#k][ind] == M[Net#f][ind]))
  );
  assume true;
  assume (1 <= C[Net#b]) && (1 <= C[Net#d]);
  in1#i := M[Net#b][R[Net#b]];
  R[Net#b] := R[Net#b] + 1;
  C[Net#b] := C[Net#b] - 1;
  in2#j := M[Net#d][R[Net#d]];
  R[Net#d] := R[Net#d] + 1;
  C[Net#d] := C[Net#d] - 1;
  M[Net#f][R[Net#f] + C[Net#f]] := in1#i + in2#j;
  C[Net#f] := C[Net#f] + 1;
  M[Net#g][R[Net#g] + C[Net#g]] := in1#i + in2#j;
  C[Net#g] := C[Net#g] + 1;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) <= L[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume 0 <= R[Net#d];
  assume 0 <= C[Net#d];
  assume 0 <= R[Net#f];
  assume 0 <= C[Net#f];
  assume 0 <= R[Net#g];
  assume 0 <= C[Net#g];
  assume 0 <= R[Net#h];
  assume 0 <= C[Net#h];
  assume 0 <= R[Net#i];
  assume 0 <= C[Net#i];
  assume 0 <= R[Net#j];
  assume 0 <= C[Net#j];
  assume (R[Net#j] + C[Net#j]) <= L[Net#j];
  assume 0 <= R[Net#k];
  assume 0 <= C[Net#k];
  assume R[Net#k] == 0;
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#121)"} (forall ind: int :: 
    (0 <= ind) && (ind < (R[Net#a] + C[Net#a])) ==> (0 < M[Net#a][ind])
  );
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#122)"} (forall ind: int :: 
    (0 <= ind) && (ind < (R[Net#a] + C[Net#a])) ==> (0 < M[Net#a][ind])
  );
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#123)"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#124)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#125)"} R[Net#b] == (R[Net#f] + C[Net#f]);
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#126)"} R[Net#d] == (R[Net#f] + C[Net#f]);
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#127)"} R[Net#b] == (R[Net#g] + C[Net#g]);
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#128)"} R[Net#d] == (R[Net#g] + C[Net#g]);
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#129)"} R[Net#g] == ((R[Net#d] + C[Net#d]) - 1);
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#130)"} R[Net#g] == ((R[Net#h] + C[Net#h]) - 1);
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#131)"} R[Net#c] == (R[Net#i] + C[Net#i]);
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#132)"} R[Net#h] == (R[Net#i] + C[Net#i]);
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#133)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#134)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#135)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#f] + C[Net#f])) ==> (M[Net#f][idx$] == (M[Net#b][idx$] + M[Net#d][idx$]))
  );
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#136)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#g] + C[Net#g])) ==> (M[Net#g][idx$] == (M[Net#b][idx$] + M[Net#d][idx$]))
  );
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#137)"} (forall idx$: int :: 
    (1 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#g][idx$ - 1])
  );
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#138)"} (forall idx$: int :: 
    (1 <= idx$) && (idx$ < (R[Net#h] + C[Net#h])) ==> (M[Net#h][idx$] == M[Net#g][idx$ - 1])
  );
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#139)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#i] + C[Net#i])) ==> (M[Net#i][idx$] == (M[Net#c][idx$] - M[Net#h][idx$]))
  );
  assert {:msg "  43.3: Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#140)"} 0 <= M[Net#d][0];
  assert {:msg "  44.3: Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#141)"} 0 <= M[Net#h][0];
  assert {:msg "  45.3: Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#142)"} (R[Net#k] + C[Net#k]) == R[Net#f];
  assert {:msg "  46.3: Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#143)"} (R[Net#k] + C[Net#k]) == R[Net#i];
  assert {:msg "  47.3: Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#144)"} (R[Net#k] + C[Net#k]) == R[Net#j];
  assert {:msg "  48.3: Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#145)"} (forall ind: int :: 
    (0 <= ind) && (ind < (R[Net#k] + C[Net#k])) ==> ((!M[Net#j][ind]) ==> (M[Net#k][ind] == M[Net#i][ind]))
  );
  assert {:msg "  49.3: Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#146)"} (forall ind: int :: 
    (0 <= ind) && (ind < (R[Net#k] + C[Net#k])) ==> (M[Net#j][ind] ==> (M[Net#k][ind] == M[Net#f][ind]))
  );
}
procedure Net#anon$7#Delay#anon$5#11()
  modifies C, R, M, St;
{
  var ActionPH#y: int;
  var ActorParam#k: int;
  var St#next: State;
  var in#i: int;
  assume ActorParam#k == 0;
  assume L[Net#a] == (1 * Base#L);
  assume L[Net#j] == (1 * Base#L);
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) <= L[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume 0 <= R[Net#d];
  assume 0 <= C[Net#d];
  assume 0 <= R[Net#f];
  assume 0 <= C[Net#f];
  assume 0 <= R[Net#g];
  assume 0 <= C[Net#g];
  assume 0 <= R[Net#h];
  assume 0 <= C[Net#h];
  assume 0 <= R[Net#i];
  assume 0 <= C[Net#i];
  assume 0 <= R[Net#j];
  assume 0 <= C[Net#j];
  assume (R[Net#j] + C[Net#j]) <= L[Net#j];
  assume 0 <= R[Net#k];
  assume 0 <= C[Net#k];
  assume R[Net#k] == 0;
  assume (forall ind: int :: 
    (0 <= ind) && (ind < (R[Net#a] + C[Net#a])) ==> (0 < M[Net#a][ind])
  );
  assume (forall ind: int :: 
    (0 <= ind) && (ind < (R[Net#a] + C[Net#a])) ==> (0 < M[Net#a][ind])
  );
  assume R[Net#a] == (R[Net#b] + C[Net#b]);
  assume R[Net#a] == (R[Net#c] + C[Net#c]);
  assume R[Net#b] == (R[Net#f] + C[Net#f]);
  assume R[Net#d] == (R[Net#f] + C[Net#f]);
  assume R[Net#b] == (R[Net#g] + C[Net#g]);
  assume R[Net#d] == (R[Net#g] + C[Net#g]);
  assume R[Net#g] == ((R[Net#d] + C[Net#d]) - 1);
  assume R[Net#g] == ((R[Net#h] + C[Net#h]) - 1);
  assume R[Net#c] == (R[Net#i] + C[Net#i]);
  assume R[Net#h] == (R[Net#i] + C[Net#i]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#f] + C[Net#f])) ==> (M[Net#f][idx$] == (M[Net#b][idx$] + M[Net#d][idx$]))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#g] + C[Net#g])) ==> (M[Net#g][idx$] == (M[Net#b][idx$] + M[Net#d][idx$]))
  );
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#g][idx$ - 1])
  );
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < (R[Net#h] + C[Net#h])) ==> (M[Net#h][idx$] == M[Net#g][idx$ - 1])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#i] + C[Net#i])) ==> (M[Net#i][idx$] == (M[Net#c][idx$] - M[Net#h][idx$]))
  );
  assume 0 <= M[Net#d][0];
  assume 0 <= M[Net#h][0];
  assume (R[Net#k] + C[Net#k]) == R[Net#f];
  assume (R[Net#k] + C[Net#k]) == R[Net#i];
  assume (R[Net#k] + C[Net#k]) == R[Net#j];
  assume (forall ind: int :: 
    (0 <= ind) && (ind < (R[Net#k] + C[Net#k])) ==> ((!M[Net#j][ind]) ==> (M[Net#k][ind] == M[Net#i][ind]))
  );
  assume (forall ind: int :: 
    (0 <= ind) && (ind < (R[Net#k] + C[Net#k])) ==> (M[Net#j][ind] ==> (M[Net#k][ind] == M[Net#f][ind]))
  );
  assume true;
  assume 1 <= C[Net#g];
  in#i := M[Net#g][R[Net#g]];
  R[Net#g] := R[Net#g] + 1;
  C[Net#g] := C[Net#g] - 1;
  M[Net#d][R[Net#d] + C[Net#d]] := in#i;
  C[Net#d] := C[Net#d] + 1;
  M[Net#h][R[Net#h] + C[Net#h]] := in#i;
  C[Net#h] := C[Net#h] + 1;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) <= L[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume 0 <= R[Net#d];
  assume 0 <= C[Net#d];
  assume 0 <= R[Net#f];
  assume 0 <= C[Net#f];
  assume 0 <= R[Net#g];
  assume 0 <= C[Net#g];
  assume 0 <= R[Net#h];
  assume 0 <= C[Net#h];
  assume 0 <= R[Net#i];
  assume 0 <= C[Net#i];
  assume 0 <= R[Net#j];
  assume 0 <= C[Net#j];
  assume (R[Net#j] + C[Net#j]) <= L[Net#j];
  assume 0 <= R[Net#k];
  assume 0 <= C[Net#k];
  assume R[Net#k] == 0;
  assert {:msg "  Action at 23.3 ('anon$5') for actor instance 'del' might not preserve the channel invariant (#170)"} (forall ind: int :: 
    (0 <= ind) && (ind < (R[Net#a] + C[Net#a])) ==> (0 < M[Net#a][ind])
  );
  assert {:msg "  Action at 23.3 ('anon$5') for actor instance 'del' might not preserve the channel invariant (#171)"} (forall ind: int :: 
    (0 <= ind) && (ind < (R[Net#a] + C[Net#a])) ==> (0 < M[Net#a][ind])
  );
  assert {:msg "  Action at 23.3 ('anon$5') for actor instance 'del' might not preserve the channel invariant (#172)"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  Action at 23.3 ('anon$5') for actor instance 'del' might not preserve the channel invariant (#173)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Action at 23.3 ('anon$5') for actor instance 'del' might not preserve the channel invariant (#174)"} R[Net#b] == (R[Net#f] + C[Net#f]);
  assert {:msg "  Action at 23.3 ('anon$5') for actor instance 'del' might not preserve the channel invariant (#175)"} R[Net#d] == (R[Net#f] + C[Net#f]);
  assert {:msg "  Action at 23.3 ('anon$5') for actor instance 'del' might not preserve the channel invariant (#176)"} R[Net#b] == (R[Net#g] + C[Net#g]);
  assert {:msg "  Action at 23.3 ('anon$5') for actor instance 'del' might not preserve the channel invariant (#177)"} R[Net#d] == (R[Net#g] + C[Net#g]);
  assert {:msg "  Action at 23.3 ('anon$5') for actor instance 'del' might not preserve the channel invariant (#178)"} R[Net#g] == ((R[Net#d] + C[Net#d]) - 1);
  assert {:msg "  Action at 23.3 ('anon$5') for actor instance 'del' might not preserve the channel invariant (#179)"} R[Net#g] == ((R[Net#h] + C[Net#h]) - 1);
  assert {:msg "  Action at 23.3 ('anon$5') for actor instance 'del' might not preserve the channel invariant (#180)"} R[Net#c] == (R[Net#i] + C[Net#i]);
  assert {:msg "  Action at 23.3 ('anon$5') for actor instance 'del' might not preserve the channel invariant (#181)"} R[Net#h] == (R[Net#i] + C[Net#i]);
  assert {:msg "  Action at 23.3 ('anon$5') for actor instance 'del' might not preserve the channel invariant (#182)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 23.3 ('anon$5') for actor instance 'del' might not preserve the channel invariant (#183)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 23.3 ('anon$5') for actor instance 'del' might not preserve the channel invariant (#184)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#f] + C[Net#f])) ==> (M[Net#f][idx$] == (M[Net#b][idx$] + M[Net#d][idx$]))
  );
  assert {:msg "  Action at 23.3 ('anon$5') for actor instance 'del' might not preserve the channel invariant (#185)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#g] + C[Net#g])) ==> (M[Net#g][idx$] == (M[Net#b][idx$] + M[Net#d][idx$]))
  );
  assert {:msg "  Action at 23.3 ('anon$5') for actor instance 'del' might not preserve the channel invariant (#186)"} (forall idx$: int :: 
    (1 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#g][idx$ - 1])
  );
  assert {:msg "  Action at 23.3 ('anon$5') for actor instance 'del' might not preserve the channel invariant (#187)"} (forall idx$: int :: 
    (1 <= idx$) && (idx$ < (R[Net#h] + C[Net#h])) ==> (M[Net#h][idx$] == M[Net#g][idx$ - 1])
  );
  assert {:msg "  Action at 23.3 ('anon$5') for actor instance 'del' might not preserve the channel invariant (#188)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#i] + C[Net#i])) ==> (M[Net#i][idx$] == (M[Net#c][idx$] - M[Net#h][idx$]))
  );
  assert {:msg "  43.3: Action at 23.3 ('anon$5') for actor instance 'del' might not preserve the channel invariant (#189)"} 0 <= M[Net#d][0];
  assert {:msg "  44.3: Action at 23.3 ('anon$5') for actor instance 'del' might not preserve the channel invariant (#190)"} 0 <= M[Net#h][0];
  assert {:msg "  45.3: Action at 23.3 ('anon$5') for actor instance 'del' might not preserve the channel invariant (#191)"} (R[Net#k] + C[Net#k]) == R[Net#f];
  assert {:msg "  46.3: Action at 23.3 ('anon$5') for actor instance 'del' might not preserve the channel invariant (#192)"} (R[Net#k] + C[Net#k]) == R[Net#i];
  assert {:msg "  47.3: Action at 23.3 ('anon$5') for actor instance 'del' might not preserve the channel invariant (#193)"} (R[Net#k] + C[Net#k]) == R[Net#j];
  assert {:msg "  48.3: Action at 23.3 ('anon$5') for actor instance 'del' might not preserve the channel invariant (#194)"} (forall ind: int :: 
    (0 <= ind) && (ind < (R[Net#k] + C[Net#k])) ==> ((!M[Net#j][ind]) ==> (M[Net#k][ind] == M[Net#i][ind]))
  );
  assert {:msg "  49.3: Action at 23.3 ('anon$5') for actor instance 'del' might not preserve the channel invariant (#195)"} (forall ind: int :: 
    (0 <= ind) && (ind < (R[Net#k] + C[Net#k])) ==> (M[Net#j][ind] ==> (M[Net#k][ind] == M[Net#f][ind]))
  );
}
procedure Net#anon$7#Sub#anon$1#12()
  modifies C, R, M, St;
{
  var ActionPH#y: int;
  var St#next: State;
  var in1#i: int;
  var in2#j: int;
  assume L[Net#a] == (1 * Base#L);
  assume L[Net#j] == (1 * Base#L);
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) <= L[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume 0 <= R[Net#d];
  assume 0 <= C[Net#d];
  assume 0 <= R[Net#f];
  assume 0 <= C[Net#f];
  assume 0 <= R[Net#g];
  assume 0 <= C[Net#g];
  assume 0 <= R[Net#h];
  assume 0 <= C[Net#h];
  assume 0 <= R[Net#i];
  assume 0 <= C[Net#i];
  assume 0 <= R[Net#j];
  assume 0 <= C[Net#j];
  assume (R[Net#j] + C[Net#j]) <= L[Net#j];
  assume 0 <= R[Net#k];
  assume 0 <= C[Net#k];
  assume R[Net#k] == 0;
  assume (forall ind: int :: 
    (0 <= ind) && (ind < (R[Net#a] + C[Net#a])) ==> (0 < M[Net#a][ind])
  );
  assume (forall ind: int :: 
    (0 <= ind) && (ind < (R[Net#a] + C[Net#a])) ==> (0 < M[Net#a][ind])
  );
  assume R[Net#a] == (R[Net#b] + C[Net#b]);
  assume R[Net#a] == (R[Net#c] + C[Net#c]);
  assume R[Net#b] == (R[Net#f] + C[Net#f]);
  assume R[Net#d] == (R[Net#f] + C[Net#f]);
  assume R[Net#b] == (R[Net#g] + C[Net#g]);
  assume R[Net#d] == (R[Net#g] + C[Net#g]);
  assume R[Net#g] == ((R[Net#d] + C[Net#d]) - 1);
  assume R[Net#g] == ((R[Net#h] + C[Net#h]) - 1);
  assume R[Net#c] == (R[Net#i] + C[Net#i]);
  assume R[Net#h] == (R[Net#i] + C[Net#i]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#f] + C[Net#f])) ==> (M[Net#f][idx$] == (M[Net#b][idx$] + M[Net#d][idx$]))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#g] + C[Net#g])) ==> (M[Net#g][idx$] == (M[Net#b][idx$] + M[Net#d][idx$]))
  );
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#g][idx$ - 1])
  );
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < (R[Net#h] + C[Net#h])) ==> (M[Net#h][idx$] == M[Net#g][idx$ - 1])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#i] + C[Net#i])) ==> (M[Net#i][idx$] == (M[Net#c][idx$] - M[Net#h][idx$]))
  );
  assume 0 <= M[Net#d][0];
  assume 0 <= M[Net#h][0];
  assume (R[Net#k] + C[Net#k]) == R[Net#f];
  assume (R[Net#k] + C[Net#k]) == R[Net#i];
  assume (R[Net#k] + C[Net#k]) == R[Net#j];
  assume (forall ind: int :: 
    (0 <= ind) && (ind < (R[Net#k] + C[Net#k])) ==> ((!M[Net#j][ind]) ==> (M[Net#k][ind] == M[Net#i][ind]))
  );
  assume (forall ind: int :: 
    (0 <= ind) && (ind < (R[Net#k] + C[Net#k])) ==> (M[Net#j][ind] ==> (M[Net#k][ind] == M[Net#f][ind]))
  );
  assume true;
  assume (1 <= C[Net#c]) && (1 <= C[Net#h]);
  in1#i := M[Net#c][R[Net#c]];
  R[Net#c] := R[Net#c] + 1;
  C[Net#c] := C[Net#c] - 1;
  in2#j := M[Net#h][R[Net#h]];
  R[Net#h] := R[Net#h] + 1;
  C[Net#h] := C[Net#h] - 1;
  M[Net#i][R[Net#i] + C[Net#i]] := in1#i - in2#j;
  C[Net#i] := C[Net#i] + 1;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) <= L[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume 0 <= R[Net#d];
  assume 0 <= C[Net#d];
  assume 0 <= R[Net#f];
  assume 0 <= C[Net#f];
  assume 0 <= R[Net#g];
  assume 0 <= C[Net#g];
  assume 0 <= R[Net#h];
  assume 0 <= C[Net#h];
  assume 0 <= R[Net#i];
  assume 0 <= C[Net#i];
  assume 0 <= R[Net#j];
  assume 0 <= C[Net#j];
  assume (R[Net#j] + C[Net#j]) <= L[Net#j];
  assume 0 <= R[Net#k];
  assume 0 <= C[Net#k];
  assume R[Net#k] == 0;
  assert {:msg "  Action at 8.3 ('anon$1') for actor instance 'sub' might not preserve the channel invariant (#219)"} (forall ind: int :: 
    (0 <= ind) && (ind < (R[Net#a] + C[Net#a])) ==> (0 < M[Net#a][ind])
  );
  assert {:msg "  Action at 8.3 ('anon$1') for actor instance 'sub' might not preserve the channel invariant (#220)"} (forall ind: int :: 
    (0 <= ind) && (ind < (R[Net#a] + C[Net#a])) ==> (0 < M[Net#a][ind])
  );
  assert {:msg "  Action at 8.3 ('anon$1') for actor instance 'sub' might not preserve the channel invariant (#221)"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  Action at 8.3 ('anon$1') for actor instance 'sub' might not preserve the channel invariant (#222)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Action at 8.3 ('anon$1') for actor instance 'sub' might not preserve the channel invariant (#223)"} R[Net#b] == (R[Net#f] + C[Net#f]);
  assert {:msg "  Action at 8.3 ('anon$1') for actor instance 'sub' might not preserve the channel invariant (#224)"} R[Net#d] == (R[Net#f] + C[Net#f]);
  assert {:msg "  Action at 8.3 ('anon$1') for actor instance 'sub' might not preserve the channel invariant (#225)"} R[Net#b] == (R[Net#g] + C[Net#g]);
  assert {:msg "  Action at 8.3 ('anon$1') for actor instance 'sub' might not preserve the channel invariant (#226)"} R[Net#d] == (R[Net#g] + C[Net#g]);
  assert {:msg "  Action at 8.3 ('anon$1') for actor instance 'sub' might not preserve the channel invariant (#227)"} R[Net#g] == ((R[Net#d] + C[Net#d]) - 1);
  assert {:msg "  Action at 8.3 ('anon$1') for actor instance 'sub' might not preserve the channel invariant (#228)"} R[Net#g] == ((R[Net#h] + C[Net#h]) - 1);
  assert {:msg "  Action at 8.3 ('anon$1') for actor instance 'sub' might not preserve the channel invariant (#229)"} R[Net#c] == (R[Net#i] + C[Net#i]);
  assert {:msg "  Action at 8.3 ('anon$1') for actor instance 'sub' might not preserve the channel invariant (#230)"} R[Net#h] == (R[Net#i] + C[Net#i]);
  assert {:msg "  Action at 8.3 ('anon$1') for actor instance 'sub' might not preserve the channel invariant (#231)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 8.3 ('anon$1') for actor instance 'sub' might not preserve the channel invariant (#232)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 8.3 ('anon$1') for actor instance 'sub' might not preserve the channel invariant (#233)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#f] + C[Net#f])) ==> (M[Net#f][idx$] == (M[Net#b][idx$] + M[Net#d][idx$]))
  );
  assert {:msg "  Action at 8.3 ('anon$1') for actor instance 'sub' might not preserve the channel invariant (#234)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#g] + C[Net#g])) ==> (M[Net#g][idx$] == (M[Net#b][idx$] + M[Net#d][idx$]))
  );
  assert {:msg "  Action at 8.3 ('anon$1') for actor instance 'sub' might not preserve the channel invariant (#235)"} (forall idx$: int :: 
    (1 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#g][idx$ - 1])
  );
  assert {:msg "  Action at 8.3 ('anon$1') for actor instance 'sub' might not preserve the channel invariant (#236)"} (forall idx$: int :: 
    (1 <= idx$) && (idx$ < (R[Net#h] + C[Net#h])) ==> (M[Net#h][idx$] == M[Net#g][idx$ - 1])
  );
  assert {:msg "  Action at 8.3 ('anon$1') for actor instance 'sub' might not preserve the channel invariant (#237)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#i] + C[Net#i])) ==> (M[Net#i][idx$] == (M[Net#c][idx$] - M[Net#h][idx$]))
  );
  assert {:msg "  43.3: Action at 8.3 ('anon$1') for actor instance 'sub' might not preserve the channel invariant (#238)"} 0 <= M[Net#d][0];
  assert {:msg "  44.3: Action at 8.3 ('anon$1') for actor instance 'sub' might not preserve the channel invariant (#239)"} 0 <= M[Net#h][0];
  assert {:msg "  45.3: Action at 8.3 ('anon$1') for actor instance 'sub' might not preserve the channel invariant (#240)"} (R[Net#k] + C[Net#k]) == R[Net#f];
  assert {:msg "  46.3: Action at 8.3 ('anon$1') for actor instance 'sub' might not preserve the channel invariant (#241)"} (R[Net#k] + C[Net#k]) == R[Net#i];
  assert {:msg "  47.3: Action at 8.3 ('anon$1') for actor instance 'sub' might not preserve the channel invariant (#242)"} (R[Net#k] + C[Net#k]) == R[Net#j];
  assert {:msg "  48.3: Action at 8.3 ('anon$1') for actor instance 'sub' might not preserve the channel invariant (#243)"} (forall ind: int :: 
    (0 <= ind) && (ind < (R[Net#k] + C[Net#k])) ==> ((!M[Net#j][ind]) ==> (M[Net#k][ind] == M[Net#i][ind]))
  );
  assert {:msg "  49.3: Action at 8.3 ('anon$1') for actor instance 'sub' might not preserve the channel invariant (#244)"} (forall ind: int :: 
    (0 <= ind) && (ind < (R[Net#k] + C[Net#k])) ==> (M[Net#j][ind] ==> (M[Net#k][ind] == M[Net#f][ind]))
  );
}
procedure Net#anon$7#Select#anon$2#13()
  modifies C, R, M, St;
{
  var ActionPH#y: int;
  var St#next: State;
  var sel#t: bool;
  var in1#i: int;
  var in2#j: int;
  assume L[Net#a] == (1 * Base#L);
  assume L[Net#j] == (1 * Base#L);
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) <= L[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume 0 <= R[Net#d];
  assume 0 <= C[Net#d];
  assume 0 <= R[Net#f];
  assume 0 <= C[Net#f];
  assume 0 <= R[Net#g];
  assume 0 <= C[Net#g];
  assume 0 <= R[Net#h];
  assume 0 <= C[Net#h];
  assume 0 <= R[Net#i];
  assume 0 <= C[Net#i];
  assume 0 <= R[Net#j];
  assume 0 <= C[Net#j];
  assume (R[Net#j] + C[Net#j]) <= L[Net#j];
  assume 0 <= R[Net#k];
  assume 0 <= C[Net#k];
  assume R[Net#k] == 0;
  assume (forall ind: int :: 
    (0 <= ind) && (ind < (R[Net#a] + C[Net#a])) ==> (0 < M[Net#a][ind])
  );
  assume (forall ind: int :: 
    (0 <= ind) && (ind < (R[Net#a] + C[Net#a])) ==> (0 < M[Net#a][ind])
  );
  assume R[Net#a] == (R[Net#b] + C[Net#b]);
  assume R[Net#a] == (R[Net#c] + C[Net#c]);
  assume R[Net#b] == (R[Net#f] + C[Net#f]);
  assume R[Net#d] == (R[Net#f] + C[Net#f]);
  assume R[Net#b] == (R[Net#g] + C[Net#g]);
  assume R[Net#d] == (R[Net#g] + C[Net#g]);
  assume R[Net#g] == ((R[Net#d] + C[Net#d]) - 1);
  assume R[Net#g] == ((R[Net#h] + C[Net#h]) - 1);
  assume R[Net#c] == (R[Net#i] + C[Net#i]);
  assume R[Net#h] == (R[Net#i] + C[Net#i]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#f] + C[Net#f])) ==> (M[Net#f][idx$] == (M[Net#b][idx$] + M[Net#d][idx$]))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#g] + C[Net#g])) ==> (M[Net#g][idx$] == (M[Net#b][idx$] + M[Net#d][idx$]))
  );
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#g][idx$ - 1])
  );
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < (R[Net#h] + C[Net#h])) ==> (M[Net#h][idx$] == M[Net#g][idx$ - 1])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#i] + C[Net#i])) ==> (M[Net#i][idx$] == (M[Net#c][idx$] - M[Net#h][idx$]))
  );
  assume 0 <= M[Net#d][0];
  assume 0 <= M[Net#h][0];
  assume (R[Net#k] + C[Net#k]) == R[Net#f];
  assume (R[Net#k] + C[Net#k]) == R[Net#i];
  assume (R[Net#k] + C[Net#k]) == R[Net#j];
  assume (forall ind: int :: 
    (0 <= ind) && (ind < (R[Net#k] + C[Net#k])) ==> ((!M[Net#j][ind]) ==> (M[Net#k][ind] == M[Net#i][ind]))
  );
  assume (forall ind: int :: 
    (0 <= ind) && (ind < (R[Net#k] + C[Net#k])) ==> (M[Net#j][ind] ==> (M[Net#k][ind] == M[Net#f][ind]))
  );
  assume M[Net#j][R[Net#j] - 0];
  assume true;
  assume (1 <= C[Net#j]) && (1 <= C[Net#f]) && (1 <= C[Net#i]) && M[Net#j][R[Net#j] - 0];
  sel#t := M[Net#j][R[Net#j]];
  R[Net#j] := R[Net#j] + 1;
  C[Net#j] := C[Net#j] - 1;
  in1#i := M[Net#f][R[Net#f]];
  R[Net#f] := R[Net#f] + 1;
  C[Net#f] := C[Net#f] - 1;
  in2#j := M[Net#i][R[Net#i]];
  R[Net#i] := R[Net#i] + 1;
  C[Net#i] := C[Net#i] - 1;
  M[Net#k][R[Net#k] + C[Net#k]] := in1#i;
  C[Net#k] := C[Net#k] + 1;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) <= L[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume 0 <= R[Net#d];
  assume 0 <= C[Net#d];
  assume 0 <= R[Net#f];
  assume 0 <= C[Net#f];
  assume 0 <= R[Net#g];
  assume 0 <= C[Net#g];
  assume 0 <= R[Net#h];
  assume 0 <= C[Net#h];
  assume 0 <= R[Net#i];
  assume 0 <= C[Net#i];
  assume 0 <= R[Net#j];
  assume 0 <= C[Net#j];
  assume (R[Net#j] + C[Net#j]) <= L[Net#j];
  assume 0 <= R[Net#k];
  assume 0 <= C[Net#k];
  assume R[Net#k] == 0;
  assert {:msg "  Action at 12.3 ('anon$2') for actor instance 'sel' might not preserve the channel invariant (#268)"} (forall ind: int :: 
    (0 <= ind) && (ind < (R[Net#a] + C[Net#a])) ==> (0 < M[Net#a][ind])
  );
  assert {:msg "  Action at 12.3 ('anon$2') for actor instance 'sel' might not preserve the channel invariant (#269)"} (forall ind: int :: 
    (0 <= ind) && (ind < (R[Net#a] + C[Net#a])) ==> (0 < M[Net#a][ind])
  );
  assert {:msg "  Action at 12.3 ('anon$2') for actor instance 'sel' might not preserve the channel invariant (#270)"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  Action at 12.3 ('anon$2') for actor instance 'sel' might not preserve the channel invariant (#271)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Action at 12.3 ('anon$2') for actor instance 'sel' might not preserve the channel invariant (#272)"} R[Net#b] == (R[Net#f] + C[Net#f]);
  assert {:msg "  Action at 12.3 ('anon$2') for actor instance 'sel' might not preserve the channel invariant (#273)"} R[Net#d] == (R[Net#f] + C[Net#f]);
  assert {:msg "  Action at 12.3 ('anon$2') for actor instance 'sel' might not preserve the channel invariant (#274)"} R[Net#b] == (R[Net#g] + C[Net#g]);
  assert {:msg "  Action at 12.3 ('anon$2') for actor instance 'sel' might not preserve the channel invariant (#275)"} R[Net#d] == (R[Net#g] + C[Net#g]);
  assert {:msg "  Action at 12.3 ('anon$2') for actor instance 'sel' might not preserve the channel invariant (#276)"} R[Net#g] == ((R[Net#d] + C[Net#d]) - 1);
  assert {:msg "  Action at 12.3 ('anon$2') for actor instance 'sel' might not preserve the channel invariant (#277)"} R[Net#g] == ((R[Net#h] + C[Net#h]) - 1);
  assert {:msg "  Action at 12.3 ('anon$2') for actor instance 'sel' might not preserve the channel invariant (#278)"} R[Net#c] == (R[Net#i] + C[Net#i]);
  assert {:msg "  Action at 12.3 ('anon$2') for actor instance 'sel' might not preserve the channel invariant (#279)"} R[Net#h] == (R[Net#i] + C[Net#i]);
  assert {:msg "  Action at 12.3 ('anon$2') for actor instance 'sel' might not preserve the channel invariant (#280)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 12.3 ('anon$2') for actor instance 'sel' might not preserve the channel invariant (#281)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 12.3 ('anon$2') for actor instance 'sel' might not preserve the channel invariant (#282)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#f] + C[Net#f])) ==> (M[Net#f][idx$] == (M[Net#b][idx$] + M[Net#d][idx$]))
  );
  assert {:msg "  Action at 12.3 ('anon$2') for actor instance 'sel' might not preserve the channel invariant (#283)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#g] + C[Net#g])) ==> (M[Net#g][idx$] == (M[Net#b][idx$] + M[Net#d][idx$]))
  );
  assert {:msg "  Action at 12.3 ('anon$2') for actor instance 'sel' might not preserve the channel invariant (#284)"} (forall idx$: int :: 
    (1 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#g][idx$ - 1])
  );
  assert {:msg "  Action at 12.3 ('anon$2') for actor instance 'sel' might not preserve the channel invariant (#285)"} (forall idx$: int :: 
    (1 <= idx$) && (idx$ < (R[Net#h] + C[Net#h])) ==> (M[Net#h][idx$] == M[Net#g][idx$ - 1])
  );
  assert {:msg "  Action at 12.3 ('anon$2') for actor instance 'sel' might not preserve the channel invariant (#286)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#i] + C[Net#i])) ==> (M[Net#i][idx$] == (M[Net#c][idx$] - M[Net#h][idx$]))
  );
  assert {:msg "  43.3: Action at 12.3 ('anon$2') for actor instance 'sel' might not preserve the channel invariant (#287)"} 0 <= M[Net#d][0];
  assert {:msg "  44.3: Action at 12.3 ('anon$2') for actor instance 'sel' might not preserve the channel invariant (#288)"} 0 <= M[Net#h][0];
  assert {:msg "  45.3: Action at 12.3 ('anon$2') for actor instance 'sel' might not preserve the channel invariant (#289)"} (R[Net#k] + C[Net#k]) == R[Net#f];
  assert {:msg "  46.3: Action at 12.3 ('anon$2') for actor instance 'sel' might not preserve the channel invariant (#290)"} (R[Net#k] + C[Net#k]) == R[Net#i];
  assert {:msg "  47.3: Action at 12.3 ('anon$2') for actor instance 'sel' might not preserve the channel invariant (#291)"} (R[Net#k] + C[Net#k]) == R[Net#j];
  assert {:msg "  48.3: Action at 12.3 ('anon$2') for actor instance 'sel' might not preserve the channel invariant (#292)"} (forall ind: int :: 
    (0 <= ind) && (ind < (R[Net#k] + C[Net#k])) ==> ((!M[Net#j][ind]) ==> (M[Net#k][ind] == M[Net#i][ind]))
  );
  assert {:msg "  49.3: Action at 12.3 ('anon$2') for actor instance 'sel' might not preserve the channel invariant (#293)"} (forall ind: int :: 
    (0 <= ind) && (ind < (R[Net#k] + C[Net#k])) ==> (M[Net#j][ind] ==> (M[Net#k][ind] == M[Net#f][ind]))
  );
}
procedure Net#anon$7#Select#anon$3#14()
  modifies C, R, M, St;
{
  var ActionPH#y: int;
  var St#next: State;
  var sel#t: bool;
  var in1#i: int;
  var in2#j: int;
  assume L[Net#a] == (1 * Base#L);
  assume L[Net#j] == (1 * Base#L);
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) <= L[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume 0 <= R[Net#d];
  assume 0 <= C[Net#d];
  assume 0 <= R[Net#f];
  assume 0 <= C[Net#f];
  assume 0 <= R[Net#g];
  assume 0 <= C[Net#g];
  assume 0 <= R[Net#h];
  assume 0 <= C[Net#h];
  assume 0 <= R[Net#i];
  assume 0 <= C[Net#i];
  assume 0 <= R[Net#j];
  assume 0 <= C[Net#j];
  assume (R[Net#j] + C[Net#j]) <= L[Net#j];
  assume 0 <= R[Net#k];
  assume 0 <= C[Net#k];
  assume R[Net#k] == 0;
  assume (forall ind: int :: 
    (0 <= ind) && (ind < (R[Net#a] + C[Net#a])) ==> (0 < M[Net#a][ind])
  );
  assume (forall ind: int :: 
    (0 <= ind) && (ind < (R[Net#a] + C[Net#a])) ==> (0 < M[Net#a][ind])
  );
  assume R[Net#a] == (R[Net#b] + C[Net#b]);
  assume R[Net#a] == (R[Net#c] + C[Net#c]);
  assume R[Net#b] == (R[Net#f] + C[Net#f]);
  assume R[Net#d] == (R[Net#f] + C[Net#f]);
  assume R[Net#b] == (R[Net#g] + C[Net#g]);
  assume R[Net#d] == (R[Net#g] + C[Net#g]);
  assume R[Net#g] == ((R[Net#d] + C[Net#d]) - 1);
  assume R[Net#g] == ((R[Net#h] + C[Net#h]) - 1);
  assume R[Net#c] == (R[Net#i] + C[Net#i]);
  assume R[Net#h] == (R[Net#i] + C[Net#i]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#f] + C[Net#f])) ==> (M[Net#f][idx$] == (M[Net#b][idx$] + M[Net#d][idx$]))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#g] + C[Net#g])) ==> (M[Net#g][idx$] == (M[Net#b][idx$] + M[Net#d][idx$]))
  );
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#g][idx$ - 1])
  );
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < (R[Net#h] + C[Net#h])) ==> (M[Net#h][idx$] == M[Net#g][idx$ - 1])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#i] + C[Net#i])) ==> (M[Net#i][idx$] == (M[Net#c][idx$] - M[Net#h][idx$]))
  );
  assume 0 <= M[Net#d][0];
  assume 0 <= M[Net#h][0];
  assume (R[Net#k] + C[Net#k]) == R[Net#f];
  assume (R[Net#k] + C[Net#k]) == R[Net#i];
  assume (R[Net#k] + C[Net#k]) == R[Net#j];
  assume (forall ind: int :: 
    (0 <= ind) && (ind < (R[Net#k] + C[Net#k])) ==> ((!M[Net#j][ind]) ==> (M[Net#k][ind] == M[Net#i][ind]))
  );
  assume (forall ind: int :: 
    (0 <= ind) && (ind < (R[Net#k] + C[Net#k])) ==> (M[Net#j][ind] ==> (M[Net#k][ind] == M[Net#f][ind]))
  );
  assume !M[Net#j][R[Net#j] - 0];
  assume true;
  assume (1 <= C[Net#j]) && (1 <= C[Net#f]) && (1 <= C[Net#i]) && (!M[Net#j][R[Net#j] - 0]);
  sel#t := M[Net#j][R[Net#j]];
  R[Net#j] := R[Net#j] + 1;
  C[Net#j] := C[Net#j] - 1;
  in1#i := M[Net#f][R[Net#f]];
  R[Net#f] := R[Net#f] + 1;
  C[Net#f] := C[Net#f] - 1;
  in2#j := M[Net#i][R[Net#i]];
  R[Net#i] := R[Net#i] + 1;
  C[Net#i] := C[Net#i] - 1;
  M[Net#k][R[Net#k] + C[Net#k]] := in2#j;
  C[Net#k] := C[Net#k] + 1;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) <= L[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume 0 <= R[Net#d];
  assume 0 <= C[Net#d];
  assume 0 <= R[Net#f];
  assume 0 <= C[Net#f];
  assume 0 <= R[Net#g];
  assume 0 <= C[Net#g];
  assume 0 <= R[Net#h];
  assume 0 <= C[Net#h];
  assume 0 <= R[Net#i];
  assume 0 <= C[Net#i];
  assume 0 <= R[Net#j];
  assume 0 <= C[Net#j];
  assume (R[Net#j] + C[Net#j]) <= L[Net#j];
  assume 0 <= R[Net#k];
  assume 0 <= C[Net#k];
  assume R[Net#k] == 0;
  assert {:msg "  Action at 15.3 ('anon$3') for actor instance 'sel' might not preserve the channel invariant (#317)"} (forall ind: int :: 
    (0 <= ind) && (ind < (R[Net#a] + C[Net#a])) ==> (0 < M[Net#a][ind])
  );
  assert {:msg "  Action at 15.3 ('anon$3') for actor instance 'sel' might not preserve the channel invariant (#318)"} (forall ind: int :: 
    (0 <= ind) && (ind < (R[Net#a] + C[Net#a])) ==> (0 < M[Net#a][ind])
  );
  assert {:msg "  Action at 15.3 ('anon$3') for actor instance 'sel' might not preserve the channel invariant (#319)"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  Action at 15.3 ('anon$3') for actor instance 'sel' might not preserve the channel invariant (#320)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Action at 15.3 ('anon$3') for actor instance 'sel' might not preserve the channel invariant (#321)"} R[Net#b] == (R[Net#f] + C[Net#f]);
  assert {:msg "  Action at 15.3 ('anon$3') for actor instance 'sel' might not preserve the channel invariant (#322)"} R[Net#d] == (R[Net#f] + C[Net#f]);
  assert {:msg "  Action at 15.3 ('anon$3') for actor instance 'sel' might not preserve the channel invariant (#323)"} R[Net#b] == (R[Net#g] + C[Net#g]);
  assert {:msg "  Action at 15.3 ('anon$3') for actor instance 'sel' might not preserve the channel invariant (#324)"} R[Net#d] == (R[Net#g] + C[Net#g]);
  assert {:msg "  Action at 15.3 ('anon$3') for actor instance 'sel' might not preserve the channel invariant (#325)"} R[Net#g] == ((R[Net#d] + C[Net#d]) - 1);
  assert {:msg "  Action at 15.3 ('anon$3') for actor instance 'sel' might not preserve the channel invariant (#326)"} R[Net#g] == ((R[Net#h] + C[Net#h]) - 1);
  assert {:msg "  Action at 15.3 ('anon$3') for actor instance 'sel' might not preserve the channel invariant (#327)"} R[Net#c] == (R[Net#i] + C[Net#i]);
  assert {:msg "  Action at 15.3 ('anon$3') for actor instance 'sel' might not preserve the channel invariant (#328)"} R[Net#h] == (R[Net#i] + C[Net#i]);
  assert {:msg "  Action at 15.3 ('anon$3') for actor instance 'sel' might not preserve the channel invariant (#329)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 15.3 ('anon$3') for actor instance 'sel' might not preserve the channel invariant (#330)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Action at 15.3 ('anon$3') for actor instance 'sel' might not preserve the channel invariant (#331)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#f] + C[Net#f])) ==> (M[Net#f][idx$] == (M[Net#b][idx$] + M[Net#d][idx$]))
  );
  assert {:msg "  Action at 15.3 ('anon$3') for actor instance 'sel' might not preserve the channel invariant (#332)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#g] + C[Net#g])) ==> (M[Net#g][idx$] == (M[Net#b][idx$] + M[Net#d][idx$]))
  );
  assert {:msg "  Action at 15.3 ('anon$3') for actor instance 'sel' might not preserve the channel invariant (#333)"} (forall idx$: int :: 
    (1 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#g][idx$ - 1])
  );
  assert {:msg "  Action at 15.3 ('anon$3') for actor instance 'sel' might not preserve the channel invariant (#334)"} (forall idx$: int :: 
    (1 <= idx$) && (idx$ < (R[Net#h] + C[Net#h])) ==> (M[Net#h][idx$] == M[Net#g][idx$ - 1])
  );
  assert {:msg "  Action at 15.3 ('anon$3') for actor instance 'sel' might not preserve the channel invariant (#335)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#i] + C[Net#i])) ==> (M[Net#i][idx$] == (M[Net#c][idx$] - M[Net#h][idx$]))
  );
  assert {:msg "  43.3: Action at 15.3 ('anon$3') for actor instance 'sel' might not preserve the channel invariant (#336)"} 0 <= M[Net#d][0];
  assert {:msg "  44.3: Action at 15.3 ('anon$3') for actor instance 'sel' might not preserve the channel invariant (#337)"} 0 <= M[Net#h][0];
  assert {:msg "  45.3: Action at 15.3 ('anon$3') for actor instance 'sel' might not preserve the channel invariant (#338)"} (R[Net#k] + C[Net#k]) == R[Net#f];
  assert {:msg "  46.3: Action at 15.3 ('anon$3') for actor instance 'sel' might not preserve the channel invariant (#339)"} (R[Net#k] + C[Net#k]) == R[Net#i];
  assert {:msg "  47.3: Action at 15.3 ('anon$3') for actor instance 'sel' might not preserve the channel invariant (#340)"} (R[Net#k] + C[Net#k]) == R[Net#j];
  assert {:msg "  48.3: Action at 15.3 ('anon$3') for actor instance 'sel' might not preserve the channel invariant (#341)"} (forall ind: int :: 
    (0 <= ind) && (ind < (R[Net#k] + C[Net#k])) ==> ((!M[Net#j][ind]) ==> (M[Net#k][ind] == M[Net#i][ind]))
  );
  assert {:msg "  49.3: Action at 15.3 ('anon$3') for actor instance 'sel' might not preserve the channel invariant (#342)"} (forall ind: int :: 
    (0 <= ind) && (ind < (R[Net#k] + C[Net#k])) ==> (M[Net#j][ind] ==> (M[Net#k][ind] == M[Net#f][ind]))
  );
}
procedure Net#anon$7#exit#15()
  modifies C, R, M, St;
{
  var ActionPH#y: int;
  assume L[Net#a] == (1 * Base#L);
  assume L[Net#j] == (1 * Base#L);
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) <= L[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume 0 <= R[Net#d];
  assume 0 <= C[Net#d];
  assume 0 <= R[Net#f];
  assume 0 <= C[Net#f];
  assume 0 <= R[Net#g];
  assume 0 <= C[Net#g];
  assume 0 <= R[Net#h];
  assume 0 <= C[Net#h];
  assume 0 <= R[Net#i];
  assume 0 <= C[Net#i];
  assume 0 <= R[Net#j];
  assume 0 <= C[Net#j];
  assume (R[Net#j] + C[Net#j]) <= L[Net#j];
  assume 0 <= R[Net#k];
  assume 0 <= C[Net#k];
  assume R[Net#k] == 0;
  assume (forall ind: int :: 
    (0 <= ind) && (ind < (R[Net#a] + C[Net#a])) ==> (0 < M[Net#a][ind])
  );
  assume (forall ind: int :: 
    (0 <= ind) && (ind < (R[Net#a] + C[Net#a])) ==> (0 < M[Net#a][ind])
  );
  assume R[Net#a] == (R[Net#b] + C[Net#b]);
  assume R[Net#a] == (R[Net#c] + C[Net#c]);
  assume R[Net#b] == (R[Net#f] + C[Net#f]);
  assume R[Net#d] == (R[Net#f] + C[Net#f]);
  assume R[Net#b] == (R[Net#g] + C[Net#g]);
  assume R[Net#d] == (R[Net#g] + C[Net#g]);
  assume R[Net#g] == ((R[Net#d] + C[Net#d]) - 1);
  assume R[Net#g] == ((R[Net#h] + C[Net#h]) - 1);
  assume R[Net#c] == (R[Net#i] + C[Net#i]);
  assume R[Net#h] == (R[Net#i] + C[Net#i]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#f] + C[Net#f])) ==> (M[Net#f][idx$] == (M[Net#b][idx$] + M[Net#d][idx$]))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#g] + C[Net#g])) ==> (M[Net#g][idx$] == (M[Net#b][idx$] + M[Net#d][idx$]))
  );
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#g][idx$ - 1])
  );
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < (R[Net#h] + C[Net#h])) ==> (M[Net#h][idx$] == M[Net#g][idx$ - 1])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#i] + C[Net#i])) ==> (M[Net#i][idx$] == (M[Net#c][idx$] - M[Net#h][idx$]))
  );
  assume 0 <= M[Net#d][0];
  assume 0 <= M[Net#h][0];
  assume (R[Net#k] + C[Net#k]) == R[Net#f];
  assume (R[Net#k] + C[Net#k]) == R[Net#i];
  assume (R[Net#k] + C[Net#k]) == R[Net#j];
  assume (forall ind: int :: 
    (0 <= ind) && (ind < (R[Net#k] + C[Net#k])) ==> ((!M[Net#j][ind]) ==> (M[Net#k][ind] == M[Net#i][ind]))
  );
  assume (forall ind: int :: 
    (0 <= ind) && (ind < (R[Net#k] + C[Net#k])) ==> (M[Net#j][ind] ==> (M[Net#k][ind] == M[Net#f][ind]))
  );
  assume !((R[Net#a] + C[Net#a]) < L[Net#a]);
  assume !((R[Net#j] + C[Net#j]) < L[Net#j]);
  assume !(1 <= C[Net#a]);
  assume !((1 <= C[Net#b]) && (1 <= C[Net#d]));
  assume !(1 <= C[Net#g]);
  assume !((1 <= C[Net#c]) && (1 <= C[Net#h]));
  assume !((1 <= C[Net#j]) && (1 <= C[Net#f]) && (1 <= C[Net#i]) && M[Net#j][R[Net#j] - 0]);
  assume !((1 <= C[Net#j]) && (1 <= C[Net#f]) && (1 <= C[Net#i]) && (!M[Net#j][R[Net#j] - 0]));
  ActionPH#y := M[Net#k][0];
  R[Net#k] := R[Net#k] + C[Net#k];
  C[Net#k] := C[Net#k] - (1 * Base#L);
  C[Net#d] := C[Net#d] - 1;
  C[Net#h] := C[Net#h] - 1;
  assert {:msg "  40.13: The network might not preserve the network invariant"} 0 <= M[Net#d][R[Net#d]];
  assert {:msg "  41.13: The network might not preserve the network invariant"} 0 <= M[Net#h][R[Net#h]];
  assert {:msg "  33.3: The network might leave unread tokens on channel a"} C[Net#a] == 0;
  assert {:msg "  33.3: The network might leave unread tokens on channel b"} C[Net#b] == 0;
  assert {:msg "  33.3: The network might leave unread tokens on channel c"} C[Net#c] == 0;
  assert {:msg "  33.3: The network might leave unread tokens on channel d"} C[Net#d] == 0;
  assert {:msg "  33.3: The network might leave unread tokens on channel f"} C[Net#f] == 0;
  assert {:msg "  33.3: The network might leave unread tokens on channel g"} C[Net#g] == 0;
  assert {:msg "  33.3: The network might leave unread tokens on channel h"} C[Net#h] == 0;
  assert {:msg "  33.3: The network might leave unread tokens on channel i"} C[Net#i] == 0;
  assert {:msg "  33.3: The network might leave unread tokens on channel j"} C[Net#j] == 0;
  assert {:msg "  33.3: The network might not produce the specified number of tokens on output out"} C[Net#k] == 0;
}

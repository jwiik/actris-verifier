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
var C#init: CType;
var St: [Actor]State;

const unique this#: Actor;

type List a = [int]a;
var AT#intlst: List int;

function AT#Min(x:int, y: int): int { if x <= y then x else y }


// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

procedure F#n#0()
  modifies C, R, M, St;
{
  var IV#in#i: int;
  assume true;
}
procedure F#fail1#1()
  modifies C, R, M, St;
{
  var IV#in#i: int;
  var IV#f#t: bool;
  assume true;
}
procedure Split#anon$0#2()
  modifies C, R, M, St;
{
  var IV#in#i: int;
  var IV#fb#t: int;
  assume true;
}
procedure Split#anon$1#3()
  modifies C, R, M, St;
{
  var IV#in#i: int;
  var IV#fb#t: int;
  assume true;
}
procedure Merge#read1#4()
  modifies C, R, M, St;
{
  var IV#in1#i: int;
  var IV#s_in#s: int;
  assume IV#s_in#s == IV#in1#i;
  assume true;
}
procedure Merge#read2#5()
  modifies C, R, M, St;
{
  var IV#in2#i: int;
  var IV#s_in#s: int;
  assume IV#s_in#s == IV#in2#i;
  assume true;
}
procedure Merge#discard1#6()
  modifies C, R, M, St;
{
  var IV#in1#i: int;
  var IV#s_in#s: int;
  assume IV#s_in#s > IV#in1#i;
  assume true;
}
procedure Merge#discard2#7()
  modifies C, R, M, St;
{
  var IV#in2#i: int;
  var IV#s_in#s: int;
  assume IV#s_in#s > IV#in2#i;
  assume true;
}
procedure Net#init#8()
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
  assume C[Net#h] == 0;
  assume R[Net#h] == 0;
  assume C[Net#m] == 0;
  assume R[Net#m] == 0;
  assume C[Net#n] == 0;
  assume R[Net#n] == 0;
  C[Net#m] := C[Net#m] - 1;
  assume M[Net#m][R[Net#m]] == 0;
  C[Net#n] := C[Net#n] - 1;
}
const unique Net#spl: Actor;
const unique Net#f1: Actor;
const unique Net#f2: Actor;
const unique Net#mrg: Actor;
const unique Net#a: Chan (int);
const unique Net#b: Chan (int);
const unique Net#c: Chan (int);
const unique Net#d: Chan (int);
const unique Net#e: Chan (int);
const unique Net#f: Chan (int);
const unique Net#g: Chan (bool);
const unique Net#h: Chan (bool);
const unique Net#m: Chan (int);
const unique Net#n: Chan (int);
procedure Net#anon$2#entry#9()
  modifies C, R, M, St;
{
  var ActionPH#y1: int;
  var ActionPH#y2: int;
  assume C#init[Net#a] == 2;
  assume C#init[Net#b] == 0;
  assume C#init[Net#c] == 0;
  assume C#init[Net#d] == 0;
  assume C#init[Net#e] == 0;
  assume C#init[Net#f] == 0;
  assume C#init[Net#g] == 0;
  assume C#init[Net#h] == 0;
  assume C#init[Net#m] == 0;
  assume C#init[Net#n] == 0;
  assume R[Net#a] == 0;
  assume R[Net#b] == 0;
  assume R[Net#c] == 0;
  assume R[Net#d] == 0;
  assume R[Net#e] == 0;
  assume R[Net#f] == 0;
  assume R[Net#g] == 0;
  assume R[Net#h] == 0;
  assume R[Net#m] == 0;
  assume R[Net#n] == 0;
  assume C#init == C;
  C[Net#m] := C[Net#m] + 1;
  assume M[Net#m][R[Net#m]] == 0;
  C[Net#n] := C[Net#n] + 1;
  assume (M[Net#a][0] == 0) && (M[Net#a][1] == 1);
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) == C#init[Net#a];
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
  assume R[Net#f] == 0;
  assume 0 <= R[Net#g];
  assume 0 <= C[Net#g];
  assume 0 <= R[Net#h];
  assume 0 <= C[Net#h];
  assume 0 <= R[Net#m];
  assume 0 <= C[Net#m];
  assume 0 <= R[Net#n];
  assume 0 <= C[Net#n];
  assert {:msg "  Channel invariant might not hold on action entry (#22)"} (M[Net#a][0] == 0) && (M[Net#a][1] == 1);
  assert {:msg "  35.3: Channel invariant might not hold on action entry (#23)"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  36.3: Channel invariant might not hold on action entry (#24)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  38.3: Channel invariant might not hold on action entry (#25)"} (R[Net#a] + C[Net#a]) == 2;
  assert {:msg "  39.3: Channel invariant might not hold on action entry (#26)"} R[Net#a] <= 2;
  assert {:msg "  40.3: Channel invariant might not hold on action entry (#27)"} ((R[Net#g] + C[Net#g]) + (R[Net#h] + C[Net#h])) <= R[Net#a];
  assert {:msg "  41.3: Channel invariant might not hold on action entry (#28)"} (C[Net#g] + C[Net#h]) <= 1;
  assert {:msg "  42.3: Channel invariant might not hold on action entry (#29)"} C[Net#b] >= C[Net#g];
  assert {:msg "  43.3: Channel invariant might not hold on action entry (#30)"} C[Net#c] >= C[Net#h];
  assert {:msg "  45.3: Channel invariant might not hold on action entry (#31)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == i)
  );
  assert {:msg "  46.3: Channel invariant might not hold on action entry (#32)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#a]) ==> (M[Net#b][i] == M[Net#a][i]) && (M[Net#c][i] == M[Net#a][i])
  );
  assert {:msg "  48.3: Channel invariant might not hold on action entry (#33)"} (R[Net#d] + C[Net#d]) <= R[Net#b];
  assert {:msg "  49.3: Channel invariant might not hold on action entry (#34)"} (R[Net#e] + C[Net#e]) <= R[Net#c];
  assert {:msg "  50.3: Channel invariant might not hold on action entry (#35)"} R[Net#b] == ((R[Net#d] + C[Net#d]) + R[Net#g]);
  assert {:msg "  51.3: Channel invariant might not hold on action entry (#36)"} R[Net#c] == ((R[Net#e] + C[Net#e]) + R[Net#h]);
  assert {:msg "  53.3: Channel invariant might not hold on action entry (#37)"} ((R[Net#b] + R[Net#c]) == 2) ==> (((R[Net#d] + C[Net#d]) + (R[Net#e] + C[Net#e])) >= 1);
  assert {:msg "  54.3: Channel invariant might not hold on action entry (#38)"} ((R[Net#d] + C[Net#d]) > 0) ==> (M[Net#d][0] == 0);
  assert {:msg "  55.3: Channel invariant might not hold on action entry (#39)"} ((R[Net#e] + C[Net#e]) > 0) ==> (M[Net#e][0] == 0);
  assert {:msg "  57.3: Channel invariant might not hold on action entry (#40)"} C[Net#m] == 1;
  assert {:msg "  58.3: Channel invariant might not hold on action entry (#41)"} (R[Net#f] + C[Net#f]) == M[Net#m][R[Net#m]];
  assert {:msg "  60.3: Channel invariant might not hold on action entry (#42)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#d]) ==> (M[Net#d][i] < M[Net#m][R[Net#m]])
  );
  assert {:msg "  61.3: Channel invariant might not hold on action entry (#43)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#e][i] < M[Net#m][R[Net#m]])
  );
  assert {:msg "  63.3: Channel invariant might not hold on action entry (#44)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#f] + C[Net#f])) ==> (M[Net#f][i] == i)
  );
  assert {:msg "  65.3: Channel invariant might not hold on action entry (#45)"} (R[Net#n] + C[Net#n]) == ((R[Net#f] + C[Net#f]) + 1);
  assert {:msg "  66.3: Channel invariant might not hold on action entry (#46)"} R[Net#n] == R[Net#a];
}
procedure Net#anon$2#Split#anon$0#10()
  modifies C, R, M, St;
{
  var ActionPH#y1: int;
  var ActionPH#y2: int;
  var St#next: State;
  var in#i: int;
  var fb#t: int;
  assume C#init[Net#a] == 2;
  assume C#init[Net#b] == 0;
  assume C#init[Net#c] == 0;
  assume C#init[Net#d] == 0;
  assume C#init[Net#e] == 0;
  assume C#init[Net#f] == 0;
  assume C#init[Net#g] == 0;
  assume C#init[Net#h] == 0;
  assume C#init[Net#m] == 0;
  assume C#init[Net#n] == 0;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) == C#init[Net#a];
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
  assume R[Net#f] == 0;
  assume 0 <= R[Net#g];
  assume 0 <= C[Net#g];
  assume 0 <= R[Net#h];
  assume 0 <= C[Net#h];
  assume 0 <= R[Net#m];
  assume 0 <= C[Net#m];
  assume 0 <= R[Net#n];
  assume 0 <= C[Net#n];
  assume (M[Net#a][0] == 0) && (M[Net#a][1] == 1);
  assume R[Net#a] == (R[Net#b] + C[Net#b]);
  assume R[Net#a] == (R[Net#c] + C[Net#c]);
  assume (R[Net#a] + C[Net#a]) == 2;
  assume R[Net#a] <= 2;
  assume ((R[Net#g] + C[Net#g]) + (R[Net#h] + C[Net#h])) <= R[Net#a];
  assume (C[Net#g] + C[Net#h]) <= 1;
  assume C[Net#b] >= C[Net#g];
  assume C[Net#c] >= C[Net#h];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#a]) ==> (M[Net#b][i] == M[Net#a][i]) && (M[Net#c][i] == M[Net#a][i])
  );
  assume (R[Net#d] + C[Net#d]) <= R[Net#b];
  assume (R[Net#e] + C[Net#e]) <= R[Net#c];
  assume R[Net#b] == ((R[Net#d] + C[Net#d]) + R[Net#g]);
  assume R[Net#c] == ((R[Net#e] + C[Net#e]) + R[Net#h]);
  assume ((R[Net#b] + R[Net#c]) == 2) ==> (((R[Net#d] + C[Net#d]) + (R[Net#e] + C[Net#e])) >= 1);
  assume ((R[Net#d] + C[Net#d]) > 0) ==> (M[Net#d][0] == 0);
  assume ((R[Net#e] + C[Net#e]) > 0) ==> (M[Net#e][0] == 0);
  assume C[Net#m] == 1;
  assume (R[Net#f] + C[Net#f]) == M[Net#m][R[Net#m]];
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#d]) ==> (M[Net#d][i] < M[Net#m][R[Net#m]])
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#e][i] < M[Net#m][R[Net#m]])
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#f] + C[Net#f])) ==> (M[Net#f][i] == i)
  );
  assume (R[Net#n] + C[Net#n]) == ((R[Net#f] + C[Net#f]) + 1);
  assume R[Net#n] == R[Net#a];
  assume true;
  assume (1 <= C[Net#a]) && (1 <= C[Net#n]);
  in#i := M[Net#a][R[Net#a]];
  R[Net#a] := R[Net#a] + 1;
  C[Net#a] := C[Net#a] - 1;
  fb#t := M[Net#n][R[Net#n]];
  R[Net#n] := R[Net#n] + 1;
  C[Net#n] := C[Net#n] - 1;
  M[Net#b][R[Net#b] + C[Net#b]] := in#i;
  C[Net#b] := C[Net#b] + 1;
  M[Net#c][R[Net#c] + C[Net#c]] := in#i;
  C[Net#c] := C[Net#c] + 1;
  M[Net#g][R[Net#g] + C[Net#g]] := true;
  C[Net#g] := C[Net#g] + 1;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) == C#init[Net#a];
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
  assume R[Net#f] == 0;
  assume 0 <= R[Net#g];
  assume 0 <= C[Net#g];
  assume 0 <= R[Net#h];
  assume 0 <= C[Net#h];
  assume 0 <= R[Net#m];
  assume 0 <= C[Net#m];
  assume 0 <= R[Net#n];
  assume 0 <= C[Net#n];
  assert {:msg "  Action at 8.3 ('anon$0') for actor instance 'spl' might not preserve the channel invariant (#69)"} (M[Net#a][0] == 0) && (M[Net#a][1] == 1);
  assert {:msg "  35.3: Action at 8.3 ('anon$0') for actor instance 'spl' might not preserve the channel invariant (#70)"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  36.3: Action at 8.3 ('anon$0') for actor instance 'spl' might not preserve the channel invariant (#71)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  38.3: Action at 8.3 ('anon$0') for actor instance 'spl' might not preserve the channel invariant (#72)"} (R[Net#a] + C[Net#a]) == 2;
  assert {:msg "  39.3: Action at 8.3 ('anon$0') for actor instance 'spl' might not preserve the channel invariant (#73)"} R[Net#a] <= 2;
  assert {:msg "  40.3: Action at 8.3 ('anon$0') for actor instance 'spl' might not preserve the channel invariant (#74)"} ((R[Net#g] + C[Net#g]) + (R[Net#h] + C[Net#h])) <= R[Net#a];
  assert {:msg "  41.3: Action at 8.3 ('anon$0') for actor instance 'spl' might not preserve the channel invariant (#75)"} (C[Net#g] + C[Net#h]) <= 1;
  assert {:msg "  42.3: Action at 8.3 ('anon$0') for actor instance 'spl' might not preserve the channel invariant (#76)"} C[Net#b] >= C[Net#g];
  assert {:msg "  43.3: Action at 8.3 ('anon$0') for actor instance 'spl' might not preserve the channel invariant (#77)"} C[Net#c] >= C[Net#h];
  assert {:msg "  45.3: Action at 8.3 ('anon$0') for actor instance 'spl' might not preserve the channel invariant (#78)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == i)
  );
  assert {:msg "  46.3: Action at 8.3 ('anon$0') for actor instance 'spl' might not preserve the channel invariant (#79)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#a]) ==> (M[Net#b][i] == M[Net#a][i]) && (M[Net#c][i] == M[Net#a][i])
  );
  assert {:msg "  48.3: Action at 8.3 ('anon$0') for actor instance 'spl' might not preserve the channel invariant (#80)"} (R[Net#d] + C[Net#d]) <= R[Net#b];
  assert {:msg "  49.3: Action at 8.3 ('anon$0') for actor instance 'spl' might not preserve the channel invariant (#81)"} (R[Net#e] + C[Net#e]) <= R[Net#c];
  assert {:msg "  50.3: Action at 8.3 ('anon$0') for actor instance 'spl' might not preserve the channel invariant (#82)"} R[Net#b] == ((R[Net#d] + C[Net#d]) + R[Net#g]);
  assert {:msg "  51.3: Action at 8.3 ('anon$0') for actor instance 'spl' might not preserve the channel invariant (#83)"} R[Net#c] == ((R[Net#e] + C[Net#e]) + R[Net#h]);
  assert {:msg "  53.3: Action at 8.3 ('anon$0') for actor instance 'spl' might not preserve the channel invariant (#84)"} ((R[Net#b] + R[Net#c]) == 2) ==> (((R[Net#d] + C[Net#d]) + (R[Net#e] + C[Net#e])) >= 1);
  assert {:msg "  54.3: Action at 8.3 ('anon$0') for actor instance 'spl' might not preserve the channel invariant (#85)"} ((R[Net#d] + C[Net#d]) > 0) ==> (M[Net#d][0] == 0);
  assert {:msg "  55.3: Action at 8.3 ('anon$0') for actor instance 'spl' might not preserve the channel invariant (#86)"} ((R[Net#e] + C[Net#e]) > 0) ==> (M[Net#e][0] == 0);
  assert {:msg "  57.3: Action at 8.3 ('anon$0') for actor instance 'spl' might not preserve the channel invariant (#87)"} C[Net#m] == 1;
  assert {:msg "  58.3: Action at 8.3 ('anon$0') for actor instance 'spl' might not preserve the channel invariant (#88)"} (R[Net#f] + C[Net#f]) == M[Net#m][R[Net#m]];
  assert {:msg "  60.3: Action at 8.3 ('anon$0') for actor instance 'spl' might not preserve the channel invariant (#89)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#d]) ==> (M[Net#d][i] < M[Net#m][R[Net#m]])
  );
  assert {:msg "  61.3: Action at 8.3 ('anon$0') for actor instance 'spl' might not preserve the channel invariant (#90)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#e][i] < M[Net#m][R[Net#m]])
  );
  assert {:msg "  63.3: Action at 8.3 ('anon$0') for actor instance 'spl' might not preserve the channel invariant (#91)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#f] + C[Net#f])) ==> (M[Net#f][i] == i)
  );
  assert {:msg "  65.3: Action at 8.3 ('anon$0') for actor instance 'spl' might not preserve the channel invariant (#92)"} (R[Net#n] + C[Net#n]) == ((R[Net#f] + C[Net#f]) + 1);
  assert {:msg "  66.3: Action at 8.3 ('anon$0') for actor instance 'spl' might not preserve the channel invariant (#93)"} R[Net#n] == R[Net#a];
}
procedure Net#anon$2#Split#anon$1#11()
  modifies C, R, M, St;
{
  var ActionPH#y1: int;
  var ActionPH#y2: int;
  var St#next: State;
  var in#i: int;
  var fb#t: int;
  assume C#init[Net#a] == 2;
  assume C#init[Net#b] == 0;
  assume C#init[Net#c] == 0;
  assume C#init[Net#d] == 0;
  assume C#init[Net#e] == 0;
  assume C#init[Net#f] == 0;
  assume C#init[Net#g] == 0;
  assume C#init[Net#h] == 0;
  assume C#init[Net#m] == 0;
  assume C#init[Net#n] == 0;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) == C#init[Net#a];
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
  assume R[Net#f] == 0;
  assume 0 <= R[Net#g];
  assume 0 <= C[Net#g];
  assume 0 <= R[Net#h];
  assume 0 <= C[Net#h];
  assume 0 <= R[Net#m];
  assume 0 <= C[Net#m];
  assume 0 <= R[Net#n];
  assume 0 <= C[Net#n];
  assume (M[Net#a][0] == 0) && (M[Net#a][1] == 1);
  assume R[Net#a] == (R[Net#b] + C[Net#b]);
  assume R[Net#a] == (R[Net#c] + C[Net#c]);
  assume (R[Net#a] + C[Net#a]) == 2;
  assume R[Net#a] <= 2;
  assume ((R[Net#g] + C[Net#g]) + (R[Net#h] + C[Net#h])) <= R[Net#a];
  assume (C[Net#g] + C[Net#h]) <= 1;
  assume C[Net#b] >= C[Net#g];
  assume C[Net#c] >= C[Net#h];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#a]) ==> (M[Net#b][i] == M[Net#a][i]) && (M[Net#c][i] == M[Net#a][i])
  );
  assume (R[Net#d] + C[Net#d]) <= R[Net#b];
  assume (R[Net#e] + C[Net#e]) <= R[Net#c];
  assume R[Net#b] == ((R[Net#d] + C[Net#d]) + R[Net#g]);
  assume R[Net#c] == ((R[Net#e] + C[Net#e]) + R[Net#h]);
  assume ((R[Net#b] + R[Net#c]) == 2) ==> (((R[Net#d] + C[Net#d]) + (R[Net#e] + C[Net#e])) >= 1);
  assume ((R[Net#d] + C[Net#d]) > 0) ==> (M[Net#d][0] == 0);
  assume ((R[Net#e] + C[Net#e]) > 0) ==> (M[Net#e][0] == 0);
  assume C[Net#m] == 1;
  assume (R[Net#f] + C[Net#f]) == M[Net#m][R[Net#m]];
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#d]) ==> (M[Net#d][i] < M[Net#m][R[Net#m]])
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#e][i] < M[Net#m][R[Net#m]])
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#f] + C[Net#f])) ==> (M[Net#f][i] == i)
  );
  assume (R[Net#n] + C[Net#n]) == ((R[Net#f] + C[Net#f]) + 1);
  assume R[Net#n] == R[Net#a];
  assume true;
  assume (1 <= C[Net#a]) && (1 <= C[Net#n]);
  in#i := M[Net#a][R[Net#a]];
  R[Net#a] := R[Net#a] + 1;
  C[Net#a] := C[Net#a] - 1;
  fb#t := M[Net#n][R[Net#n]];
  R[Net#n] := R[Net#n] + 1;
  C[Net#n] := C[Net#n] - 1;
  M[Net#b][R[Net#b] + C[Net#b]] := in#i;
  C[Net#b] := C[Net#b] + 1;
  M[Net#c][R[Net#c] + C[Net#c]] := in#i;
  C[Net#c] := C[Net#c] + 1;
  M[Net#h][R[Net#h] + C[Net#h]] := true;
  C[Net#h] := C[Net#h] + 1;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) == C#init[Net#a];
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
  assume R[Net#f] == 0;
  assume 0 <= R[Net#g];
  assume 0 <= C[Net#g];
  assume 0 <= R[Net#h];
  assume 0 <= C[Net#h];
  assume 0 <= R[Net#m];
  assume 0 <= C[Net#m];
  assume 0 <= R[Net#n];
  assume 0 <= C[Net#n];
  assert {:msg "  Action at 9.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#116)"} (M[Net#a][0] == 0) && (M[Net#a][1] == 1);
  assert {:msg "  35.3: Action at 9.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#117)"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  36.3: Action at 9.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#118)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  38.3: Action at 9.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#119)"} (R[Net#a] + C[Net#a]) == 2;
  assert {:msg "  39.3: Action at 9.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#120)"} R[Net#a] <= 2;
  assert {:msg "  40.3: Action at 9.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#121)"} ((R[Net#g] + C[Net#g]) + (R[Net#h] + C[Net#h])) <= R[Net#a];
  assert {:msg "  41.3: Action at 9.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#122)"} (C[Net#g] + C[Net#h]) <= 1;
  assert {:msg "  42.3: Action at 9.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#123)"} C[Net#b] >= C[Net#g];
  assert {:msg "  43.3: Action at 9.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#124)"} C[Net#c] >= C[Net#h];
  assert {:msg "  45.3: Action at 9.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#125)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == i)
  );
  assert {:msg "  46.3: Action at 9.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#126)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#a]) ==> (M[Net#b][i] == M[Net#a][i]) && (M[Net#c][i] == M[Net#a][i])
  );
  assert {:msg "  48.3: Action at 9.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#127)"} (R[Net#d] + C[Net#d]) <= R[Net#b];
  assert {:msg "  49.3: Action at 9.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#128)"} (R[Net#e] + C[Net#e]) <= R[Net#c];
  assert {:msg "  50.3: Action at 9.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#129)"} R[Net#b] == ((R[Net#d] + C[Net#d]) + R[Net#g]);
  assert {:msg "  51.3: Action at 9.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#130)"} R[Net#c] == ((R[Net#e] + C[Net#e]) + R[Net#h]);
  assert {:msg "  53.3: Action at 9.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#131)"} ((R[Net#b] + R[Net#c]) == 2) ==> (((R[Net#d] + C[Net#d]) + (R[Net#e] + C[Net#e])) >= 1);
  assert {:msg "  54.3: Action at 9.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#132)"} ((R[Net#d] + C[Net#d]) > 0) ==> (M[Net#d][0] == 0);
  assert {:msg "  55.3: Action at 9.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#133)"} ((R[Net#e] + C[Net#e]) > 0) ==> (M[Net#e][0] == 0);
  assert {:msg "  57.3: Action at 9.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#134)"} C[Net#m] == 1;
  assert {:msg "  58.3: Action at 9.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#135)"} (R[Net#f] + C[Net#f]) == M[Net#m][R[Net#m]];
  assert {:msg "  60.3: Action at 9.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#136)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#d]) ==> (M[Net#d][i] < M[Net#m][R[Net#m]])
  );
  assert {:msg "  61.3: Action at 9.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#137)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#e][i] < M[Net#m][R[Net#m]])
  );
  assert {:msg "  63.3: Action at 9.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#138)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#f] + C[Net#f])) ==> (M[Net#f][i] == i)
  );
  assert {:msg "  65.3: Action at 9.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#139)"} (R[Net#n] + C[Net#n]) == ((R[Net#f] + C[Net#f]) + 1);
  assert {:msg "  66.3: Action at 9.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#140)"} R[Net#n] == R[Net#a];
}
procedure Net#anon$2#F#fail1#12()
  modifies C, R, M, St;
{
  var ActionPH#y1: int;
  var ActionPH#y2: int;
  var St#next: State;
  var in#i: int;
  var f#t: bool;
  assume C#init[Net#a] == 2;
  assume C#init[Net#b] == 0;
  assume C#init[Net#c] == 0;
  assume C#init[Net#d] == 0;
  assume C#init[Net#e] == 0;
  assume C#init[Net#f] == 0;
  assume C#init[Net#g] == 0;
  assume C#init[Net#h] == 0;
  assume C#init[Net#m] == 0;
  assume C#init[Net#n] == 0;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) == C#init[Net#a];
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
  assume R[Net#f] == 0;
  assume 0 <= R[Net#g];
  assume 0 <= C[Net#g];
  assume 0 <= R[Net#h];
  assume 0 <= C[Net#h];
  assume 0 <= R[Net#m];
  assume 0 <= C[Net#m];
  assume 0 <= R[Net#n];
  assume 0 <= C[Net#n];
  assume (M[Net#a][0] == 0) && (M[Net#a][1] == 1);
  assume R[Net#a] == (R[Net#b] + C[Net#b]);
  assume R[Net#a] == (R[Net#c] + C[Net#c]);
  assume (R[Net#a] + C[Net#a]) == 2;
  assume R[Net#a] <= 2;
  assume ((R[Net#g] + C[Net#g]) + (R[Net#h] + C[Net#h])) <= R[Net#a];
  assume (C[Net#g] + C[Net#h]) <= 1;
  assume C[Net#b] >= C[Net#g];
  assume C[Net#c] >= C[Net#h];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#a]) ==> (M[Net#b][i] == M[Net#a][i]) && (M[Net#c][i] == M[Net#a][i])
  );
  assume (R[Net#d] + C[Net#d]) <= R[Net#b];
  assume (R[Net#e] + C[Net#e]) <= R[Net#c];
  assume R[Net#b] == ((R[Net#d] + C[Net#d]) + R[Net#g]);
  assume R[Net#c] == ((R[Net#e] + C[Net#e]) + R[Net#h]);
  assume ((R[Net#b] + R[Net#c]) == 2) ==> (((R[Net#d] + C[Net#d]) + (R[Net#e] + C[Net#e])) >= 1);
  assume ((R[Net#d] + C[Net#d]) > 0) ==> (M[Net#d][0] == 0);
  assume ((R[Net#e] + C[Net#e]) > 0) ==> (M[Net#e][0] == 0);
  assume C[Net#m] == 1;
  assume (R[Net#f] + C[Net#f]) == M[Net#m][R[Net#m]];
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#d]) ==> (M[Net#d][i] < M[Net#m][R[Net#m]])
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#e][i] < M[Net#m][R[Net#m]])
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#f] + C[Net#f])) ==> (M[Net#f][i] == i)
  );
  assume (R[Net#n] + C[Net#n]) == ((R[Net#f] + C[Net#f]) + 1);
  assume R[Net#n] == R[Net#a];
  assume true;
  assume (1 <= C[Net#b]) && (1 <= C[Net#g]);
  in#i := M[Net#b][R[Net#b]];
  R[Net#b] := R[Net#b] + 1;
  C[Net#b] := C[Net#b] - 1;
  f#t := M[Net#g][R[Net#g]];
  R[Net#g] := R[Net#g] + 1;
  C[Net#g] := C[Net#g] - 1;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) == C#init[Net#a];
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
  assume R[Net#f] == 0;
  assume 0 <= R[Net#g];
  assume 0 <= C[Net#g];
  assume 0 <= R[Net#h];
  assume 0 <= C[Net#h];
  assume 0 <= R[Net#m];
  assume 0 <= C[Net#m];
  assume 0 <= R[Net#n];
  assume 0 <= C[Net#n];
  assert {:msg "  Action at 3.3 ('fail1') for actor instance 'f1' might not preserve the channel invariant (#163)"} (M[Net#a][0] == 0) && (M[Net#a][1] == 1);
  assert {:msg "  35.3: Action at 3.3 ('fail1') for actor instance 'f1' might not preserve the channel invariant (#164)"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  36.3: Action at 3.3 ('fail1') for actor instance 'f1' might not preserve the channel invariant (#165)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  38.3: Action at 3.3 ('fail1') for actor instance 'f1' might not preserve the channel invariant (#166)"} (R[Net#a] + C[Net#a]) == 2;
  assert {:msg "  39.3: Action at 3.3 ('fail1') for actor instance 'f1' might not preserve the channel invariant (#167)"} R[Net#a] <= 2;
  assert {:msg "  40.3: Action at 3.3 ('fail1') for actor instance 'f1' might not preserve the channel invariant (#168)"} ((R[Net#g] + C[Net#g]) + (R[Net#h] + C[Net#h])) <= R[Net#a];
  assert {:msg "  41.3: Action at 3.3 ('fail1') for actor instance 'f1' might not preserve the channel invariant (#169)"} (C[Net#g] + C[Net#h]) <= 1;
  assert {:msg "  42.3: Action at 3.3 ('fail1') for actor instance 'f1' might not preserve the channel invariant (#170)"} C[Net#b] >= C[Net#g];
  assert {:msg "  43.3: Action at 3.3 ('fail1') for actor instance 'f1' might not preserve the channel invariant (#171)"} C[Net#c] >= C[Net#h];
  assert {:msg "  45.3: Action at 3.3 ('fail1') for actor instance 'f1' might not preserve the channel invariant (#172)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == i)
  );
  assert {:msg "  46.3: Action at 3.3 ('fail1') for actor instance 'f1' might not preserve the channel invariant (#173)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#a]) ==> (M[Net#b][i] == M[Net#a][i]) && (M[Net#c][i] == M[Net#a][i])
  );
  assert {:msg "  48.3: Action at 3.3 ('fail1') for actor instance 'f1' might not preserve the channel invariant (#174)"} (R[Net#d] + C[Net#d]) <= R[Net#b];
  assert {:msg "  49.3: Action at 3.3 ('fail1') for actor instance 'f1' might not preserve the channel invariant (#175)"} (R[Net#e] + C[Net#e]) <= R[Net#c];
  assert {:msg "  50.3: Action at 3.3 ('fail1') for actor instance 'f1' might not preserve the channel invariant (#176)"} R[Net#b] == ((R[Net#d] + C[Net#d]) + R[Net#g]);
  assert {:msg "  51.3: Action at 3.3 ('fail1') for actor instance 'f1' might not preserve the channel invariant (#177)"} R[Net#c] == ((R[Net#e] + C[Net#e]) + R[Net#h]);
  assert {:msg "  53.3: Action at 3.3 ('fail1') for actor instance 'f1' might not preserve the channel invariant (#178)"} ((R[Net#b] + R[Net#c]) == 2) ==> (((R[Net#d] + C[Net#d]) + (R[Net#e] + C[Net#e])) >= 1);
  assert {:msg "  54.3: Action at 3.3 ('fail1') for actor instance 'f1' might not preserve the channel invariant (#179)"} ((R[Net#d] + C[Net#d]) > 0) ==> (M[Net#d][0] == 0);
  assert {:msg "  55.3: Action at 3.3 ('fail1') for actor instance 'f1' might not preserve the channel invariant (#180)"} ((R[Net#e] + C[Net#e]) > 0) ==> (M[Net#e][0] == 0);
  assert {:msg "  57.3: Action at 3.3 ('fail1') for actor instance 'f1' might not preserve the channel invariant (#181)"} C[Net#m] == 1;
  assert {:msg "  58.3: Action at 3.3 ('fail1') for actor instance 'f1' might not preserve the channel invariant (#182)"} (R[Net#f] + C[Net#f]) == M[Net#m][R[Net#m]];
  assert {:msg "  60.3: Action at 3.3 ('fail1') for actor instance 'f1' might not preserve the channel invariant (#183)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#d]) ==> (M[Net#d][i] < M[Net#m][R[Net#m]])
  );
  assert {:msg "  61.3: Action at 3.3 ('fail1') for actor instance 'f1' might not preserve the channel invariant (#184)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#e][i] < M[Net#m][R[Net#m]])
  );
  assert {:msg "  63.3: Action at 3.3 ('fail1') for actor instance 'f1' might not preserve the channel invariant (#185)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#f] + C[Net#f])) ==> (M[Net#f][i] == i)
  );
  assert {:msg "  65.3: Action at 3.3 ('fail1') for actor instance 'f1' might not preserve the channel invariant (#186)"} (R[Net#n] + C[Net#n]) == ((R[Net#f] + C[Net#f]) + 1);
  assert {:msg "  66.3: Action at 3.3 ('fail1') for actor instance 'f1' might not preserve the channel invariant (#187)"} R[Net#n] == R[Net#a];
}
procedure Net#anon$2#F#n#13()
  modifies C, R, M, St;
{
  var ActionPH#y1: int;
  var ActionPH#y2: int;
  var St#next: State;
  var in#i: int;
  assume C#init[Net#a] == 2;
  assume C#init[Net#b] == 0;
  assume C#init[Net#c] == 0;
  assume C#init[Net#d] == 0;
  assume C#init[Net#e] == 0;
  assume C#init[Net#f] == 0;
  assume C#init[Net#g] == 0;
  assume C#init[Net#h] == 0;
  assume C#init[Net#m] == 0;
  assume C#init[Net#n] == 0;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) == C#init[Net#a];
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
  assume R[Net#f] == 0;
  assume 0 <= R[Net#g];
  assume 0 <= C[Net#g];
  assume 0 <= R[Net#h];
  assume 0 <= C[Net#h];
  assume 0 <= R[Net#m];
  assume 0 <= C[Net#m];
  assume 0 <= R[Net#n];
  assume 0 <= C[Net#n];
  assume (M[Net#a][0] == 0) && (M[Net#a][1] == 1);
  assume R[Net#a] == (R[Net#b] + C[Net#b]);
  assume R[Net#a] == (R[Net#c] + C[Net#c]);
  assume (R[Net#a] + C[Net#a]) == 2;
  assume R[Net#a] <= 2;
  assume ((R[Net#g] + C[Net#g]) + (R[Net#h] + C[Net#h])) <= R[Net#a];
  assume (C[Net#g] + C[Net#h]) <= 1;
  assume C[Net#b] >= C[Net#g];
  assume C[Net#c] >= C[Net#h];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#a]) ==> (M[Net#b][i] == M[Net#a][i]) && (M[Net#c][i] == M[Net#a][i])
  );
  assume (R[Net#d] + C[Net#d]) <= R[Net#b];
  assume (R[Net#e] + C[Net#e]) <= R[Net#c];
  assume R[Net#b] == ((R[Net#d] + C[Net#d]) + R[Net#g]);
  assume R[Net#c] == ((R[Net#e] + C[Net#e]) + R[Net#h]);
  assume ((R[Net#b] + R[Net#c]) == 2) ==> (((R[Net#d] + C[Net#d]) + (R[Net#e] + C[Net#e])) >= 1);
  assume ((R[Net#d] + C[Net#d]) > 0) ==> (M[Net#d][0] == 0);
  assume ((R[Net#e] + C[Net#e]) > 0) ==> (M[Net#e][0] == 0);
  assume C[Net#m] == 1;
  assume (R[Net#f] + C[Net#f]) == M[Net#m][R[Net#m]];
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#d]) ==> (M[Net#d][i] < M[Net#m][R[Net#m]])
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#e][i] < M[Net#m][R[Net#m]])
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#f] + C[Net#f])) ==> (M[Net#f][i] == i)
  );
  assume (R[Net#n] + C[Net#n]) == ((R[Net#f] + C[Net#f]) + 1);
  assume R[Net#n] == R[Net#a];
  assume true;
  assume (!((1 <= C[Net#b]) && (1 <= C[Net#g]))) && (1 <= C[Net#b]);
  in#i := M[Net#b][R[Net#b]];
  R[Net#b] := R[Net#b] + 1;
  C[Net#b] := C[Net#b] - 1;
  M[Net#d][R[Net#d] + C[Net#d]] := in#i;
  C[Net#d] := C[Net#d] + 1;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) == C#init[Net#a];
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
  assume R[Net#f] == 0;
  assume 0 <= R[Net#g];
  assume 0 <= C[Net#g];
  assume 0 <= R[Net#h];
  assume 0 <= C[Net#h];
  assume 0 <= R[Net#m];
  assume 0 <= C[Net#m];
  assume 0 <= R[Net#n];
  assume 0 <= C[Net#n];
  assert {:msg "  Action at 2.3 ('n') for actor instance 'f1' might not preserve the channel invariant (#210)"} (M[Net#a][0] == 0) && (M[Net#a][1] == 1);
  assert {:msg "  35.3: Action at 2.3 ('n') for actor instance 'f1' might not preserve the channel invariant (#211)"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  36.3: Action at 2.3 ('n') for actor instance 'f1' might not preserve the channel invariant (#212)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  38.3: Action at 2.3 ('n') for actor instance 'f1' might not preserve the channel invariant (#213)"} (R[Net#a] + C[Net#a]) == 2;
  assert {:msg "  39.3: Action at 2.3 ('n') for actor instance 'f1' might not preserve the channel invariant (#214)"} R[Net#a] <= 2;
  assert {:msg "  40.3: Action at 2.3 ('n') for actor instance 'f1' might not preserve the channel invariant (#215)"} ((R[Net#g] + C[Net#g]) + (R[Net#h] + C[Net#h])) <= R[Net#a];
  assert {:msg "  41.3: Action at 2.3 ('n') for actor instance 'f1' might not preserve the channel invariant (#216)"} (C[Net#g] + C[Net#h]) <= 1;
  assert {:msg "  42.3: Action at 2.3 ('n') for actor instance 'f1' might not preserve the channel invariant (#217)"} C[Net#b] >= C[Net#g];
  assert {:msg "  43.3: Action at 2.3 ('n') for actor instance 'f1' might not preserve the channel invariant (#218)"} C[Net#c] >= C[Net#h];
  assert {:msg "  45.3: Action at 2.3 ('n') for actor instance 'f1' might not preserve the channel invariant (#219)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == i)
  );
  assert {:msg "  46.3: Action at 2.3 ('n') for actor instance 'f1' might not preserve the channel invariant (#220)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#a]) ==> (M[Net#b][i] == M[Net#a][i]) && (M[Net#c][i] == M[Net#a][i])
  );
  assert {:msg "  48.3: Action at 2.3 ('n') for actor instance 'f1' might not preserve the channel invariant (#221)"} (R[Net#d] + C[Net#d]) <= R[Net#b];
  assert {:msg "  49.3: Action at 2.3 ('n') for actor instance 'f1' might not preserve the channel invariant (#222)"} (R[Net#e] + C[Net#e]) <= R[Net#c];
  assert {:msg "  50.3: Action at 2.3 ('n') for actor instance 'f1' might not preserve the channel invariant (#223)"} R[Net#b] == ((R[Net#d] + C[Net#d]) + R[Net#g]);
  assert {:msg "  51.3: Action at 2.3 ('n') for actor instance 'f1' might not preserve the channel invariant (#224)"} R[Net#c] == ((R[Net#e] + C[Net#e]) + R[Net#h]);
  assert {:msg "  53.3: Action at 2.3 ('n') for actor instance 'f1' might not preserve the channel invariant (#225)"} ((R[Net#b] + R[Net#c]) == 2) ==> (((R[Net#d] + C[Net#d]) + (R[Net#e] + C[Net#e])) >= 1);
  assert {:msg "  54.3: Action at 2.3 ('n') for actor instance 'f1' might not preserve the channel invariant (#226)"} ((R[Net#d] + C[Net#d]) > 0) ==> (M[Net#d][0] == 0);
  assert {:msg "  55.3: Action at 2.3 ('n') for actor instance 'f1' might not preserve the channel invariant (#227)"} ((R[Net#e] + C[Net#e]) > 0) ==> (M[Net#e][0] == 0);
  assert {:msg "  57.3: Action at 2.3 ('n') for actor instance 'f1' might not preserve the channel invariant (#228)"} C[Net#m] == 1;
  assert {:msg "  58.3: Action at 2.3 ('n') for actor instance 'f1' might not preserve the channel invariant (#229)"} (R[Net#f] + C[Net#f]) == M[Net#m][R[Net#m]];
  assert {:msg "  60.3: Action at 2.3 ('n') for actor instance 'f1' might not preserve the channel invariant (#230)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#d]) ==> (M[Net#d][i] < M[Net#m][R[Net#m]])
  );
  assert {:msg "  61.3: Action at 2.3 ('n') for actor instance 'f1' might not preserve the channel invariant (#231)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#e][i] < M[Net#m][R[Net#m]])
  );
  assert {:msg "  63.3: Action at 2.3 ('n') for actor instance 'f1' might not preserve the channel invariant (#232)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#f] + C[Net#f])) ==> (M[Net#f][i] == i)
  );
  assert {:msg "  65.3: Action at 2.3 ('n') for actor instance 'f1' might not preserve the channel invariant (#233)"} (R[Net#n] + C[Net#n]) == ((R[Net#f] + C[Net#f]) + 1);
  assert {:msg "  66.3: Action at 2.3 ('n') for actor instance 'f1' might not preserve the channel invariant (#234)"} R[Net#n] == R[Net#a];
}
procedure Net#anon$2#F#fail1#14()
  modifies C, R, M, St;
{
  var ActionPH#y1: int;
  var ActionPH#y2: int;
  var St#next: State;
  var in#i: int;
  var f#t: bool;
  assume C#init[Net#a] == 2;
  assume C#init[Net#b] == 0;
  assume C#init[Net#c] == 0;
  assume C#init[Net#d] == 0;
  assume C#init[Net#e] == 0;
  assume C#init[Net#f] == 0;
  assume C#init[Net#g] == 0;
  assume C#init[Net#h] == 0;
  assume C#init[Net#m] == 0;
  assume C#init[Net#n] == 0;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) == C#init[Net#a];
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
  assume R[Net#f] == 0;
  assume 0 <= R[Net#g];
  assume 0 <= C[Net#g];
  assume 0 <= R[Net#h];
  assume 0 <= C[Net#h];
  assume 0 <= R[Net#m];
  assume 0 <= C[Net#m];
  assume 0 <= R[Net#n];
  assume 0 <= C[Net#n];
  assume (M[Net#a][0] == 0) && (M[Net#a][1] == 1);
  assume R[Net#a] == (R[Net#b] + C[Net#b]);
  assume R[Net#a] == (R[Net#c] + C[Net#c]);
  assume (R[Net#a] + C[Net#a]) == 2;
  assume R[Net#a] <= 2;
  assume ((R[Net#g] + C[Net#g]) + (R[Net#h] + C[Net#h])) <= R[Net#a];
  assume (C[Net#g] + C[Net#h]) <= 1;
  assume C[Net#b] >= C[Net#g];
  assume C[Net#c] >= C[Net#h];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#a]) ==> (M[Net#b][i] == M[Net#a][i]) && (M[Net#c][i] == M[Net#a][i])
  );
  assume (R[Net#d] + C[Net#d]) <= R[Net#b];
  assume (R[Net#e] + C[Net#e]) <= R[Net#c];
  assume R[Net#b] == ((R[Net#d] + C[Net#d]) + R[Net#g]);
  assume R[Net#c] == ((R[Net#e] + C[Net#e]) + R[Net#h]);
  assume ((R[Net#b] + R[Net#c]) == 2) ==> (((R[Net#d] + C[Net#d]) + (R[Net#e] + C[Net#e])) >= 1);
  assume ((R[Net#d] + C[Net#d]) > 0) ==> (M[Net#d][0] == 0);
  assume ((R[Net#e] + C[Net#e]) > 0) ==> (M[Net#e][0] == 0);
  assume C[Net#m] == 1;
  assume (R[Net#f] + C[Net#f]) == M[Net#m][R[Net#m]];
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#d]) ==> (M[Net#d][i] < M[Net#m][R[Net#m]])
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#e][i] < M[Net#m][R[Net#m]])
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#f] + C[Net#f])) ==> (M[Net#f][i] == i)
  );
  assume (R[Net#n] + C[Net#n]) == ((R[Net#f] + C[Net#f]) + 1);
  assume R[Net#n] == R[Net#a];
  assume true;
  assume (1 <= C[Net#c]) && (1 <= C[Net#h]);
  in#i := M[Net#c][R[Net#c]];
  R[Net#c] := R[Net#c] + 1;
  C[Net#c] := C[Net#c] - 1;
  f#t := M[Net#h][R[Net#h]];
  R[Net#h] := R[Net#h] + 1;
  C[Net#h] := C[Net#h] - 1;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) == C#init[Net#a];
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
  assume R[Net#f] == 0;
  assume 0 <= R[Net#g];
  assume 0 <= C[Net#g];
  assume 0 <= R[Net#h];
  assume 0 <= C[Net#h];
  assume 0 <= R[Net#m];
  assume 0 <= C[Net#m];
  assume 0 <= R[Net#n];
  assume 0 <= C[Net#n];
  assert {:msg "  Action at 3.3 ('fail1') for actor instance 'f2' might not preserve the channel invariant (#257)"} (M[Net#a][0] == 0) && (M[Net#a][1] == 1);
  assert {:msg "  35.3: Action at 3.3 ('fail1') for actor instance 'f2' might not preserve the channel invariant (#258)"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  36.3: Action at 3.3 ('fail1') for actor instance 'f2' might not preserve the channel invariant (#259)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  38.3: Action at 3.3 ('fail1') for actor instance 'f2' might not preserve the channel invariant (#260)"} (R[Net#a] + C[Net#a]) == 2;
  assert {:msg "  39.3: Action at 3.3 ('fail1') for actor instance 'f2' might not preserve the channel invariant (#261)"} R[Net#a] <= 2;
  assert {:msg "  40.3: Action at 3.3 ('fail1') for actor instance 'f2' might not preserve the channel invariant (#262)"} ((R[Net#g] + C[Net#g]) + (R[Net#h] + C[Net#h])) <= R[Net#a];
  assert {:msg "  41.3: Action at 3.3 ('fail1') for actor instance 'f2' might not preserve the channel invariant (#263)"} (C[Net#g] + C[Net#h]) <= 1;
  assert {:msg "  42.3: Action at 3.3 ('fail1') for actor instance 'f2' might not preserve the channel invariant (#264)"} C[Net#b] >= C[Net#g];
  assert {:msg "  43.3: Action at 3.3 ('fail1') for actor instance 'f2' might not preserve the channel invariant (#265)"} C[Net#c] >= C[Net#h];
  assert {:msg "  45.3: Action at 3.3 ('fail1') for actor instance 'f2' might not preserve the channel invariant (#266)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == i)
  );
  assert {:msg "  46.3: Action at 3.3 ('fail1') for actor instance 'f2' might not preserve the channel invariant (#267)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#a]) ==> (M[Net#b][i] == M[Net#a][i]) && (M[Net#c][i] == M[Net#a][i])
  );
  assert {:msg "  48.3: Action at 3.3 ('fail1') for actor instance 'f2' might not preserve the channel invariant (#268)"} (R[Net#d] + C[Net#d]) <= R[Net#b];
  assert {:msg "  49.3: Action at 3.3 ('fail1') for actor instance 'f2' might not preserve the channel invariant (#269)"} (R[Net#e] + C[Net#e]) <= R[Net#c];
  assert {:msg "  50.3: Action at 3.3 ('fail1') for actor instance 'f2' might not preserve the channel invariant (#270)"} R[Net#b] == ((R[Net#d] + C[Net#d]) + R[Net#g]);
  assert {:msg "  51.3: Action at 3.3 ('fail1') for actor instance 'f2' might not preserve the channel invariant (#271)"} R[Net#c] == ((R[Net#e] + C[Net#e]) + R[Net#h]);
  assert {:msg "  53.3: Action at 3.3 ('fail1') for actor instance 'f2' might not preserve the channel invariant (#272)"} ((R[Net#b] + R[Net#c]) == 2) ==> (((R[Net#d] + C[Net#d]) + (R[Net#e] + C[Net#e])) >= 1);
  assert {:msg "  54.3: Action at 3.3 ('fail1') for actor instance 'f2' might not preserve the channel invariant (#273)"} ((R[Net#d] + C[Net#d]) > 0) ==> (M[Net#d][0] == 0);
  assert {:msg "  55.3: Action at 3.3 ('fail1') for actor instance 'f2' might not preserve the channel invariant (#274)"} ((R[Net#e] + C[Net#e]) > 0) ==> (M[Net#e][0] == 0);
  assert {:msg "  57.3: Action at 3.3 ('fail1') for actor instance 'f2' might not preserve the channel invariant (#275)"} C[Net#m] == 1;
  assert {:msg "  58.3: Action at 3.3 ('fail1') for actor instance 'f2' might not preserve the channel invariant (#276)"} (R[Net#f] + C[Net#f]) == M[Net#m][R[Net#m]];
  assert {:msg "  60.3: Action at 3.3 ('fail1') for actor instance 'f2' might not preserve the channel invariant (#277)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#d]) ==> (M[Net#d][i] < M[Net#m][R[Net#m]])
  );
  assert {:msg "  61.3: Action at 3.3 ('fail1') for actor instance 'f2' might not preserve the channel invariant (#278)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#e][i] < M[Net#m][R[Net#m]])
  );
  assert {:msg "  63.3: Action at 3.3 ('fail1') for actor instance 'f2' might not preserve the channel invariant (#279)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#f] + C[Net#f])) ==> (M[Net#f][i] == i)
  );
  assert {:msg "  65.3: Action at 3.3 ('fail1') for actor instance 'f2' might not preserve the channel invariant (#280)"} (R[Net#n] + C[Net#n]) == ((R[Net#f] + C[Net#f]) + 1);
  assert {:msg "  66.3: Action at 3.3 ('fail1') for actor instance 'f2' might not preserve the channel invariant (#281)"} R[Net#n] == R[Net#a];
}
procedure Net#anon$2#F#n#15()
  modifies C, R, M, St;
{
  var ActionPH#y1: int;
  var ActionPH#y2: int;
  var St#next: State;
  var in#i: int;
  assume C#init[Net#a] == 2;
  assume C#init[Net#b] == 0;
  assume C#init[Net#c] == 0;
  assume C#init[Net#d] == 0;
  assume C#init[Net#e] == 0;
  assume C#init[Net#f] == 0;
  assume C#init[Net#g] == 0;
  assume C#init[Net#h] == 0;
  assume C#init[Net#m] == 0;
  assume C#init[Net#n] == 0;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) == C#init[Net#a];
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
  assume R[Net#f] == 0;
  assume 0 <= R[Net#g];
  assume 0 <= C[Net#g];
  assume 0 <= R[Net#h];
  assume 0 <= C[Net#h];
  assume 0 <= R[Net#m];
  assume 0 <= C[Net#m];
  assume 0 <= R[Net#n];
  assume 0 <= C[Net#n];
  assume (M[Net#a][0] == 0) && (M[Net#a][1] == 1);
  assume R[Net#a] == (R[Net#b] + C[Net#b]);
  assume R[Net#a] == (R[Net#c] + C[Net#c]);
  assume (R[Net#a] + C[Net#a]) == 2;
  assume R[Net#a] <= 2;
  assume ((R[Net#g] + C[Net#g]) + (R[Net#h] + C[Net#h])) <= R[Net#a];
  assume (C[Net#g] + C[Net#h]) <= 1;
  assume C[Net#b] >= C[Net#g];
  assume C[Net#c] >= C[Net#h];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#a]) ==> (M[Net#b][i] == M[Net#a][i]) && (M[Net#c][i] == M[Net#a][i])
  );
  assume (R[Net#d] + C[Net#d]) <= R[Net#b];
  assume (R[Net#e] + C[Net#e]) <= R[Net#c];
  assume R[Net#b] == ((R[Net#d] + C[Net#d]) + R[Net#g]);
  assume R[Net#c] == ((R[Net#e] + C[Net#e]) + R[Net#h]);
  assume ((R[Net#b] + R[Net#c]) == 2) ==> (((R[Net#d] + C[Net#d]) + (R[Net#e] + C[Net#e])) >= 1);
  assume ((R[Net#d] + C[Net#d]) > 0) ==> (M[Net#d][0] == 0);
  assume ((R[Net#e] + C[Net#e]) > 0) ==> (M[Net#e][0] == 0);
  assume C[Net#m] == 1;
  assume (R[Net#f] + C[Net#f]) == M[Net#m][R[Net#m]];
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#d]) ==> (M[Net#d][i] < M[Net#m][R[Net#m]])
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#e][i] < M[Net#m][R[Net#m]])
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#f] + C[Net#f])) ==> (M[Net#f][i] == i)
  );
  assume (R[Net#n] + C[Net#n]) == ((R[Net#f] + C[Net#f]) + 1);
  assume R[Net#n] == R[Net#a];
  assume true;
  assume (!((1 <= C[Net#c]) && (1 <= C[Net#h]))) && (1 <= C[Net#c]);
  in#i := M[Net#c][R[Net#c]];
  R[Net#c] := R[Net#c] + 1;
  C[Net#c] := C[Net#c] - 1;
  M[Net#e][R[Net#e] + C[Net#e]] := in#i;
  C[Net#e] := C[Net#e] + 1;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) == C#init[Net#a];
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
  assume R[Net#f] == 0;
  assume 0 <= R[Net#g];
  assume 0 <= C[Net#g];
  assume 0 <= R[Net#h];
  assume 0 <= C[Net#h];
  assume 0 <= R[Net#m];
  assume 0 <= C[Net#m];
  assume 0 <= R[Net#n];
  assume 0 <= C[Net#n];
  assert {:msg "  Action at 2.3 ('n') for actor instance 'f2' might not preserve the channel invariant (#304)"} (M[Net#a][0] == 0) && (M[Net#a][1] == 1);
  assert {:msg "  35.3: Action at 2.3 ('n') for actor instance 'f2' might not preserve the channel invariant (#305)"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  36.3: Action at 2.3 ('n') for actor instance 'f2' might not preserve the channel invariant (#306)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  38.3: Action at 2.3 ('n') for actor instance 'f2' might not preserve the channel invariant (#307)"} (R[Net#a] + C[Net#a]) == 2;
  assert {:msg "  39.3: Action at 2.3 ('n') for actor instance 'f2' might not preserve the channel invariant (#308)"} R[Net#a] <= 2;
  assert {:msg "  40.3: Action at 2.3 ('n') for actor instance 'f2' might not preserve the channel invariant (#309)"} ((R[Net#g] + C[Net#g]) + (R[Net#h] + C[Net#h])) <= R[Net#a];
  assert {:msg "  41.3: Action at 2.3 ('n') for actor instance 'f2' might not preserve the channel invariant (#310)"} (C[Net#g] + C[Net#h]) <= 1;
  assert {:msg "  42.3: Action at 2.3 ('n') for actor instance 'f2' might not preserve the channel invariant (#311)"} C[Net#b] >= C[Net#g];
  assert {:msg "  43.3: Action at 2.3 ('n') for actor instance 'f2' might not preserve the channel invariant (#312)"} C[Net#c] >= C[Net#h];
  assert {:msg "  45.3: Action at 2.3 ('n') for actor instance 'f2' might not preserve the channel invariant (#313)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == i)
  );
  assert {:msg "  46.3: Action at 2.3 ('n') for actor instance 'f2' might not preserve the channel invariant (#314)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#a]) ==> (M[Net#b][i] == M[Net#a][i]) && (M[Net#c][i] == M[Net#a][i])
  );
  assert {:msg "  48.3: Action at 2.3 ('n') for actor instance 'f2' might not preserve the channel invariant (#315)"} (R[Net#d] + C[Net#d]) <= R[Net#b];
  assert {:msg "  49.3: Action at 2.3 ('n') for actor instance 'f2' might not preserve the channel invariant (#316)"} (R[Net#e] + C[Net#e]) <= R[Net#c];
  assert {:msg "  50.3: Action at 2.3 ('n') for actor instance 'f2' might not preserve the channel invariant (#317)"} R[Net#b] == ((R[Net#d] + C[Net#d]) + R[Net#g]);
  assert {:msg "  51.3: Action at 2.3 ('n') for actor instance 'f2' might not preserve the channel invariant (#318)"} R[Net#c] == ((R[Net#e] + C[Net#e]) + R[Net#h]);
  assert {:msg "  53.3: Action at 2.3 ('n') for actor instance 'f2' might not preserve the channel invariant (#319)"} ((R[Net#b] + R[Net#c]) == 2) ==> (((R[Net#d] + C[Net#d]) + (R[Net#e] + C[Net#e])) >= 1);
  assert {:msg "  54.3: Action at 2.3 ('n') for actor instance 'f2' might not preserve the channel invariant (#320)"} ((R[Net#d] + C[Net#d]) > 0) ==> (M[Net#d][0] == 0);
  assert {:msg "  55.3: Action at 2.3 ('n') for actor instance 'f2' might not preserve the channel invariant (#321)"} ((R[Net#e] + C[Net#e]) > 0) ==> (M[Net#e][0] == 0);
  assert {:msg "  57.3: Action at 2.3 ('n') for actor instance 'f2' might not preserve the channel invariant (#322)"} C[Net#m] == 1;
  assert {:msg "  58.3: Action at 2.3 ('n') for actor instance 'f2' might not preserve the channel invariant (#323)"} (R[Net#f] + C[Net#f]) == M[Net#m][R[Net#m]];
  assert {:msg "  60.3: Action at 2.3 ('n') for actor instance 'f2' might not preserve the channel invariant (#324)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#d]) ==> (M[Net#d][i] < M[Net#m][R[Net#m]])
  );
  assert {:msg "  61.3: Action at 2.3 ('n') for actor instance 'f2' might not preserve the channel invariant (#325)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#e][i] < M[Net#m][R[Net#m]])
  );
  assert {:msg "  63.3: Action at 2.3 ('n') for actor instance 'f2' might not preserve the channel invariant (#326)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#f] + C[Net#f])) ==> (M[Net#f][i] == i)
  );
  assert {:msg "  65.3: Action at 2.3 ('n') for actor instance 'f2' might not preserve the channel invariant (#327)"} (R[Net#n] + C[Net#n]) == ((R[Net#f] + C[Net#f]) + 1);
  assert {:msg "  66.3: Action at 2.3 ('n') for actor instance 'f2' might not preserve the channel invariant (#328)"} R[Net#n] == R[Net#a];
}
procedure Net#anon$2#Merge#read1#16()
  modifies C, R, M, St;
{
  var ActionPH#y1: int;
  var ActionPH#y2: int;
  var St#next: State;
  var in1#i: int;
  var s_in#s: int;
  assume C#init[Net#a] == 2;
  assume C#init[Net#b] == 0;
  assume C#init[Net#c] == 0;
  assume C#init[Net#d] == 0;
  assume C#init[Net#e] == 0;
  assume C#init[Net#f] == 0;
  assume C#init[Net#g] == 0;
  assume C#init[Net#h] == 0;
  assume C#init[Net#m] == 0;
  assume C#init[Net#n] == 0;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) == C#init[Net#a];
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
  assume R[Net#f] == 0;
  assume 0 <= R[Net#g];
  assume 0 <= C[Net#g];
  assume 0 <= R[Net#h];
  assume 0 <= C[Net#h];
  assume 0 <= R[Net#m];
  assume 0 <= C[Net#m];
  assume 0 <= R[Net#n];
  assume 0 <= C[Net#n];
  assume (M[Net#a][0] == 0) && (M[Net#a][1] == 1);
  assume R[Net#a] == (R[Net#b] + C[Net#b]);
  assume R[Net#a] == (R[Net#c] + C[Net#c]);
  assume (R[Net#a] + C[Net#a]) == 2;
  assume R[Net#a] <= 2;
  assume ((R[Net#g] + C[Net#g]) + (R[Net#h] + C[Net#h])) <= R[Net#a];
  assume (C[Net#g] + C[Net#h]) <= 1;
  assume C[Net#b] >= C[Net#g];
  assume C[Net#c] >= C[Net#h];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#a]) ==> (M[Net#b][i] == M[Net#a][i]) && (M[Net#c][i] == M[Net#a][i])
  );
  assume (R[Net#d] + C[Net#d]) <= R[Net#b];
  assume (R[Net#e] + C[Net#e]) <= R[Net#c];
  assume R[Net#b] == ((R[Net#d] + C[Net#d]) + R[Net#g]);
  assume R[Net#c] == ((R[Net#e] + C[Net#e]) + R[Net#h]);
  assume ((R[Net#b] + R[Net#c]) == 2) ==> (((R[Net#d] + C[Net#d]) + (R[Net#e] + C[Net#e])) >= 1);
  assume ((R[Net#d] + C[Net#d]) > 0) ==> (M[Net#d][0] == 0);
  assume ((R[Net#e] + C[Net#e]) > 0) ==> (M[Net#e][0] == 0);
  assume C[Net#m] == 1;
  assume (R[Net#f] + C[Net#f]) == M[Net#m][R[Net#m]];
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#d]) ==> (M[Net#d][i] < M[Net#m][R[Net#m]])
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#e][i] < M[Net#m][R[Net#m]])
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#f] + C[Net#f])) ==> (M[Net#f][i] == i)
  );
  assume (R[Net#n] + C[Net#n]) == ((R[Net#f] + C[Net#f]) + 1);
  assume R[Net#n] == R[Net#a];
  assume M[Net#m][R[Net#m] - 0] == M[Net#d][R[Net#d] - 0];
  assume true;
  assume (1 <= C[Net#d]) && (1 <= C[Net#m]) && (M[Net#m][R[Net#m] - 0] == M[Net#d][R[Net#d] - 0]);
  in1#i := M[Net#d][R[Net#d]];
  R[Net#d] := R[Net#d] + 1;
  C[Net#d] := C[Net#d] - 1;
  s_in#s := M[Net#m][R[Net#m]];
  R[Net#m] := R[Net#m] + 1;
  C[Net#m] := C[Net#m] - 1;
  M[Net#f][R[Net#f] + C[Net#f]] := in1#i;
  C[Net#f] := C[Net#f] + 1;
  M[Net#m][R[Net#m] + C[Net#m]] := s_in#s + 1;
  C[Net#m] := C[Net#m] + 1;
  M[Net#n][R[Net#n] + C[Net#n]] := 1;
  C[Net#n] := C[Net#n] + 1;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) == C#init[Net#a];
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
  assume R[Net#f] == 0;
  assume 0 <= R[Net#g];
  assume 0 <= C[Net#g];
  assume 0 <= R[Net#h];
  assume 0 <= C[Net#h];
  assume 0 <= R[Net#m];
  assume 0 <= C[Net#m];
  assume 0 <= R[Net#n];
  assume 0 <= C[Net#n];
  assert {:msg "  Action at 14.3 ('read1') for actor instance 'mrg' might not preserve the channel invariant (#351)"} (M[Net#a][0] == 0) && (M[Net#a][1] == 1);
  assert {:msg "  35.3: Action at 14.3 ('read1') for actor instance 'mrg' might not preserve the channel invariant (#352)"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  36.3: Action at 14.3 ('read1') for actor instance 'mrg' might not preserve the channel invariant (#353)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  38.3: Action at 14.3 ('read1') for actor instance 'mrg' might not preserve the channel invariant (#354)"} (R[Net#a] + C[Net#a]) == 2;
  assert {:msg "  39.3: Action at 14.3 ('read1') for actor instance 'mrg' might not preserve the channel invariant (#355)"} R[Net#a] <= 2;
  assert {:msg "  40.3: Action at 14.3 ('read1') for actor instance 'mrg' might not preserve the channel invariant (#356)"} ((R[Net#g] + C[Net#g]) + (R[Net#h] + C[Net#h])) <= R[Net#a];
  assert {:msg "  41.3: Action at 14.3 ('read1') for actor instance 'mrg' might not preserve the channel invariant (#357)"} (C[Net#g] + C[Net#h]) <= 1;
  assert {:msg "  42.3: Action at 14.3 ('read1') for actor instance 'mrg' might not preserve the channel invariant (#358)"} C[Net#b] >= C[Net#g];
  assert {:msg "  43.3: Action at 14.3 ('read1') for actor instance 'mrg' might not preserve the channel invariant (#359)"} C[Net#c] >= C[Net#h];
  assert {:msg "  45.3: Action at 14.3 ('read1') for actor instance 'mrg' might not preserve the channel invariant (#360)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == i)
  );
  assert {:msg "  46.3: Action at 14.3 ('read1') for actor instance 'mrg' might not preserve the channel invariant (#361)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#a]) ==> (M[Net#b][i] == M[Net#a][i]) && (M[Net#c][i] == M[Net#a][i])
  );
  assert {:msg "  48.3: Action at 14.3 ('read1') for actor instance 'mrg' might not preserve the channel invariant (#362)"} (R[Net#d] + C[Net#d]) <= R[Net#b];
  assert {:msg "  49.3: Action at 14.3 ('read1') for actor instance 'mrg' might not preserve the channel invariant (#363)"} (R[Net#e] + C[Net#e]) <= R[Net#c];
  assert {:msg "  50.3: Action at 14.3 ('read1') for actor instance 'mrg' might not preserve the channel invariant (#364)"} R[Net#b] == ((R[Net#d] + C[Net#d]) + R[Net#g]);
  assert {:msg "  51.3: Action at 14.3 ('read1') for actor instance 'mrg' might not preserve the channel invariant (#365)"} R[Net#c] == ((R[Net#e] + C[Net#e]) + R[Net#h]);
  assert {:msg "  53.3: Action at 14.3 ('read1') for actor instance 'mrg' might not preserve the channel invariant (#366)"} ((R[Net#b] + R[Net#c]) == 2) ==> (((R[Net#d] + C[Net#d]) + (R[Net#e] + C[Net#e])) >= 1);
  assert {:msg "  54.3: Action at 14.3 ('read1') for actor instance 'mrg' might not preserve the channel invariant (#367)"} ((R[Net#d] + C[Net#d]) > 0) ==> (M[Net#d][0] == 0);
  assert {:msg "  55.3: Action at 14.3 ('read1') for actor instance 'mrg' might not preserve the channel invariant (#368)"} ((R[Net#e] + C[Net#e]) > 0) ==> (M[Net#e][0] == 0);
  assert {:msg "  57.3: Action at 14.3 ('read1') for actor instance 'mrg' might not preserve the channel invariant (#369)"} C[Net#m] == 1;
  assert {:msg "  58.3: Action at 14.3 ('read1') for actor instance 'mrg' might not preserve the channel invariant (#370)"} (R[Net#f] + C[Net#f]) == M[Net#m][R[Net#m]];
  assert {:msg "  60.3: Action at 14.3 ('read1') for actor instance 'mrg' might not preserve the channel invariant (#371)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#d]) ==> (M[Net#d][i] < M[Net#m][R[Net#m]])
  );
  assert {:msg "  61.3: Action at 14.3 ('read1') for actor instance 'mrg' might not preserve the channel invariant (#372)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#e][i] < M[Net#m][R[Net#m]])
  );
  assert {:msg "  63.3: Action at 14.3 ('read1') for actor instance 'mrg' might not preserve the channel invariant (#373)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#f] + C[Net#f])) ==> (M[Net#f][i] == i)
  );
  assert {:msg "  65.3: Action at 14.3 ('read1') for actor instance 'mrg' might not preserve the channel invariant (#374)"} (R[Net#n] + C[Net#n]) == ((R[Net#f] + C[Net#f]) + 1);
  assert {:msg "  66.3: Action at 14.3 ('read1') for actor instance 'mrg' might not preserve the channel invariant (#375)"} R[Net#n] == R[Net#a];
}
procedure Net#anon$2#Merge#read2#17()
  modifies C, R, M, St;
{
  var ActionPH#y1: int;
  var ActionPH#y2: int;
  var St#next: State;
  var in2#i: int;
  var s_in#s: int;
  assume C#init[Net#a] == 2;
  assume C#init[Net#b] == 0;
  assume C#init[Net#c] == 0;
  assume C#init[Net#d] == 0;
  assume C#init[Net#e] == 0;
  assume C#init[Net#f] == 0;
  assume C#init[Net#g] == 0;
  assume C#init[Net#h] == 0;
  assume C#init[Net#m] == 0;
  assume C#init[Net#n] == 0;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) == C#init[Net#a];
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
  assume R[Net#f] == 0;
  assume 0 <= R[Net#g];
  assume 0 <= C[Net#g];
  assume 0 <= R[Net#h];
  assume 0 <= C[Net#h];
  assume 0 <= R[Net#m];
  assume 0 <= C[Net#m];
  assume 0 <= R[Net#n];
  assume 0 <= C[Net#n];
  assume (M[Net#a][0] == 0) && (M[Net#a][1] == 1);
  assume R[Net#a] == (R[Net#b] + C[Net#b]);
  assume R[Net#a] == (R[Net#c] + C[Net#c]);
  assume (R[Net#a] + C[Net#a]) == 2;
  assume R[Net#a] <= 2;
  assume ((R[Net#g] + C[Net#g]) + (R[Net#h] + C[Net#h])) <= R[Net#a];
  assume (C[Net#g] + C[Net#h]) <= 1;
  assume C[Net#b] >= C[Net#g];
  assume C[Net#c] >= C[Net#h];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#a]) ==> (M[Net#b][i] == M[Net#a][i]) && (M[Net#c][i] == M[Net#a][i])
  );
  assume (R[Net#d] + C[Net#d]) <= R[Net#b];
  assume (R[Net#e] + C[Net#e]) <= R[Net#c];
  assume R[Net#b] == ((R[Net#d] + C[Net#d]) + R[Net#g]);
  assume R[Net#c] == ((R[Net#e] + C[Net#e]) + R[Net#h]);
  assume ((R[Net#b] + R[Net#c]) == 2) ==> (((R[Net#d] + C[Net#d]) + (R[Net#e] + C[Net#e])) >= 1);
  assume ((R[Net#d] + C[Net#d]) > 0) ==> (M[Net#d][0] == 0);
  assume ((R[Net#e] + C[Net#e]) > 0) ==> (M[Net#e][0] == 0);
  assume C[Net#m] == 1;
  assume (R[Net#f] + C[Net#f]) == M[Net#m][R[Net#m]];
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#d]) ==> (M[Net#d][i] < M[Net#m][R[Net#m]])
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#e][i] < M[Net#m][R[Net#m]])
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#f] + C[Net#f])) ==> (M[Net#f][i] == i)
  );
  assume (R[Net#n] + C[Net#n]) == ((R[Net#f] + C[Net#f]) + 1);
  assume R[Net#n] == R[Net#a];
  assume M[Net#m][R[Net#m] - 0] == M[Net#e][R[Net#e] - 0];
  assume true;
  assume (1 <= C[Net#e]) && (1 <= C[Net#m]) && (M[Net#m][R[Net#m] - 0] == M[Net#e][R[Net#e] - 0]);
  in2#i := M[Net#e][R[Net#e]];
  R[Net#e] := R[Net#e] + 1;
  C[Net#e] := C[Net#e] - 1;
  s_in#s := M[Net#m][R[Net#m]];
  R[Net#m] := R[Net#m] + 1;
  C[Net#m] := C[Net#m] - 1;
  M[Net#f][R[Net#f] + C[Net#f]] := in2#i;
  C[Net#f] := C[Net#f] + 1;
  M[Net#m][R[Net#m] + C[Net#m]] := s_in#s + 1;
  C[Net#m] := C[Net#m] + 1;
  M[Net#n][R[Net#n] + C[Net#n]] := 1;
  C[Net#n] := C[Net#n] + 1;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) == C#init[Net#a];
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
  assume R[Net#f] == 0;
  assume 0 <= R[Net#g];
  assume 0 <= C[Net#g];
  assume 0 <= R[Net#h];
  assume 0 <= C[Net#h];
  assume 0 <= R[Net#m];
  assume 0 <= C[Net#m];
  assume 0 <= R[Net#n];
  assume 0 <= C[Net#n];
  assert {:msg "  Action at 17.3 ('read2') for actor instance 'mrg' might not preserve the channel invariant (#398)"} (M[Net#a][0] == 0) && (M[Net#a][1] == 1);
  assert {:msg "  35.3: Action at 17.3 ('read2') for actor instance 'mrg' might not preserve the channel invariant (#399)"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  36.3: Action at 17.3 ('read2') for actor instance 'mrg' might not preserve the channel invariant (#400)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  38.3: Action at 17.3 ('read2') for actor instance 'mrg' might not preserve the channel invariant (#401)"} (R[Net#a] + C[Net#a]) == 2;
  assert {:msg "  39.3: Action at 17.3 ('read2') for actor instance 'mrg' might not preserve the channel invariant (#402)"} R[Net#a] <= 2;
  assert {:msg "  40.3: Action at 17.3 ('read2') for actor instance 'mrg' might not preserve the channel invariant (#403)"} ((R[Net#g] + C[Net#g]) + (R[Net#h] + C[Net#h])) <= R[Net#a];
  assert {:msg "  41.3: Action at 17.3 ('read2') for actor instance 'mrg' might not preserve the channel invariant (#404)"} (C[Net#g] + C[Net#h]) <= 1;
  assert {:msg "  42.3: Action at 17.3 ('read2') for actor instance 'mrg' might not preserve the channel invariant (#405)"} C[Net#b] >= C[Net#g];
  assert {:msg "  43.3: Action at 17.3 ('read2') for actor instance 'mrg' might not preserve the channel invariant (#406)"} C[Net#c] >= C[Net#h];
  assert {:msg "  45.3: Action at 17.3 ('read2') for actor instance 'mrg' might not preserve the channel invariant (#407)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == i)
  );
  assert {:msg "  46.3: Action at 17.3 ('read2') for actor instance 'mrg' might not preserve the channel invariant (#408)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#a]) ==> (M[Net#b][i] == M[Net#a][i]) && (M[Net#c][i] == M[Net#a][i])
  );
  assert {:msg "  48.3: Action at 17.3 ('read2') for actor instance 'mrg' might not preserve the channel invariant (#409)"} (R[Net#d] + C[Net#d]) <= R[Net#b];
  assert {:msg "  49.3: Action at 17.3 ('read2') for actor instance 'mrg' might not preserve the channel invariant (#410)"} (R[Net#e] + C[Net#e]) <= R[Net#c];
  assert {:msg "  50.3: Action at 17.3 ('read2') for actor instance 'mrg' might not preserve the channel invariant (#411)"} R[Net#b] == ((R[Net#d] + C[Net#d]) + R[Net#g]);
  assert {:msg "  51.3: Action at 17.3 ('read2') for actor instance 'mrg' might not preserve the channel invariant (#412)"} R[Net#c] == ((R[Net#e] + C[Net#e]) + R[Net#h]);
  assert {:msg "  53.3: Action at 17.3 ('read2') for actor instance 'mrg' might not preserve the channel invariant (#413)"} ((R[Net#b] + R[Net#c]) == 2) ==> (((R[Net#d] + C[Net#d]) + (R[Net#e] + C[Net#e])) >= 1);
  assert {:msg "  54.3: Action at 17.3 ('read2') for actor instance 'mrg' might not preserve the channel invariant (#414)"} ((R[Net#d] + C[Net#d]) > 0) ==> (M[Net#d][0] == 0);
  assert {:msg "  55.3: Action at 17.3 ('read2') for actor instance 'mrg' might not preserve the channel invariant (#415)"} ((R[Net#e] + C[Net#e]) > 0) ==> (M[Net#e][0] == 0);
  assert {:msg "  57.3: Action at 17.3 ('read2') for actor instance 'mrg' might not preserve the channel invariant (#416)"} C[Net#m] == 1;
  assert {:msg "  58.3: Action at 17.3 ('read2') for actor instance 'mrg' might not preserve the channel invariant (#417)"} (R[Net#f] + C[Net#f]) == M[Net#m][R[Net#m]];
  assert {:msg "  60.3: Action at 17.3 ('read2') for actor instance 'mrg' might not preserve the channel invariant (#418)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#d]) ==> (M[Net#d][i] < M[Net#m][R[Net#m]])
  );
  assert {:msg "  61.3: Action at 17.3 ('read2') for actor instance 'mrg' might not preserve the channel invariant (#419)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#e][i] < M[Net#m][R[Net#m]])
  );
  assert {:msg "  63.3: Action at 17.3 ('read2') for actor instance 'mrg' might not preserve the channel invariant (#420)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#f] + C[Net#f])) ==> (M[Net#f][i] == i)
  );
  assert {:msg "  65.3: Action at 17.3 ('read2') for actor instance 'mrg' might not preserve the channel invariant (#421)"} (R[Net#n] + C[Net#n]) == ((R[Net#f] + C[Net#f]) + 1);
  assert {:msg "  66.3: Action at 17.3 ('read2') for actor instance 'mrg' might not preserve the channel invariant (#422)"} R[Net#n] == R[Net#a];
}
procedure Net#anon$2#Merge#discard1#18()
  modifies C, R, M, St;
{
  var ActionPH#y1: int;
  var ActionPH#y2: int;
  var St#next: State;
  var in1#i: int;
  var s_in#s: int;
  assume C#init[Net#a] == 2;
  assume C#init[Net#b] == 0;
  assume C#init[Net#c] == 0;
  assume C#init[Net#d] == 0;
  assume C#init[Net#e] == 0;
  assume C#init[Net#f] == 0;
  assume C#init[Net#g] == 0;
  assume C#init[Net#h] == 0;
  assume C#init[Net#m] == 0;
  assume C#init[Net#n] == 0;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) == C#init[Net#a];
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
  assume R[Net#f] == 0;
  assume 0 <= R[Net#g];
  assume 0 <= C[Net#g];
  assume 0 <= R[Net#h];
  assume 0 <= C[Net#h];
  assume 0 <= R[Net#m];
  assume 0 <= C[Net#m];
  assume 0 <= R[Net#n];
  assume 0 <= C[Net#n];
  assume (M[Net#a][0] == 0) && (M[Net#a][1] == 1);
  assume R[Net#a] == (R[Net#b] + C[Net#b]);
  assume R[Net#a] == (R[Net#c] + C[Net#c]);
  assume (R[Net#a] + C[Net#a]) == 2;
  assume R[Net#a] <= 2;
  assume ((R[Net#g] + C[Net#g]) + (R[Net#h] + C[Net#h])) <= R[Net#a];
  assume (C[Net#g] + C[Net#h]) <= 1;
  assume C[Net#b] >= C[Net#g];
  assume C[Net#c] >= C[Net#h];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#a]) ==> (M[Net#b][i] == M[Net#a][i]) && (M[Net#c][i] == M[Net#a][i])
  );
  assume (R[Net#d] + C[Net#d]) <= R[Net#b];
  assume (R[Net#e] + C[Net#e]) <= R[Net#c];
  assume R[Net#b] == ((R[Net#d] + C[Net#d]) + R[Net#g]);
  assume R[Net#c] == ((R[Net#e] + C[Net#e]) + R[Net#h]);
  assume ((R[Net#b] + R[Net#c]) == 2) ==> (((R[Net#d] + C[Net#d]) + (R[Net#e] + C[Net#e])) >= 1);
  assume ((R[Net#d] + C[Net#d]) > 0) ==> (M[Net#d][0] == 0);
  assume ((R[Net#e] + C[Net#e]) > 0) ==> (M[Net#e][0] == 0);
  assume C[Net#m] == 1;
  assume (R[Net#f] + C[Net#f]) == M[Net#m][R[Net#m]];
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#d]) ==> (M[Net#d][i] < M[Net#m][R[Net#m]])
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#e][i] < M[Net#m][R[Net#m]])
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#f] + C[Net#f])) ==> (M[Net#f][i] == i)
  );
  assume (R[Net#n] + C[Net#n]) == ((R[Net#f] + C[Net#f]) + 1);
  assume R[Net#n] == R[Net#a];
  assume M[Net#m][R[Net#m] - 0] > M[Net#d][R[Net#d] - 0];
  assume true;
  assume (1 <= C[Net#d]) && (1 <= C[Net#m]) && (M[Net#m][R[Net#m] - 0] > M[Net#d][R[Net#d] - 0]);
  in1#i := M[Net#d][R[Net#d]];
  R[Net#d] := R[Net#d] + 1;
  C[Net#d] := C[Net#d] - 1;
  s_in#s := M[Net#m][R[Net#m]];
  R[Net#m] := R[Net#m] + 1;
  C[Net#m] := C[Net#m] - 1;
  M[Net#m][R[Net#m] + C[Net#m]] := s_in#s;
  C[Net#m] := C[Net#m] + 1;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) == C#init[Net#a];
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
  assume R[Net#f] == 0;
  assume 0 <= R[Net#g];
  assume 0 <= C[Net#g];
  assume 0 <= R[Net#h];
  assume 0 <= C[Net#h];
  assume 0 <= R[Net#m];
  assume 0 <= C[Net#m];
  assume 0 <= R[Net#n];
  assume 0 <= C[Net#n];
  assert {:msg "  Action at 20.3 ('discard1') for actor instance 'mrg' might not preserve the channel invariant (#445)"} (M[Net#a][0] == 0) && (M[Net#a][1] == 1);
  assert {:msg "  35.3: Action at 20.3 ('discard1') for actor instance 'mrg' might not preserve the channel invariant (#446)"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  36.3: Action at 20.3 ('discard1') for actor instance 'mrg' might not preserve the channel invariant (#447)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  38.3: Action at 20.3 ('discard1') for actor instance 'mrg' might not preserve the channel invariant (#448)"} (R[Net#a] + C[Net#a]) == 2;
  assert {:msg "  39.3: Action at 20.3 ('discard1') for actor instance 'mrg' might not preserve the channel invariant (#449)"} R[Net#a] <= 2;
  assert {:msg "  40.3: Action at 20.3 ('discard1') for actor instance 'mrg' might not preserve the channel invariant (#450)"} ((R[Net#g] + C[Net#g]) + (R[Net#h] + C[Net#h])) <= R[Net#a];
  assert {:msg "  41.3: Action at 20.3 ('discard1') for actor instance 'mrg' might not preserve the channel invariant (#451)"} (C[Net#g] + C[Net#h]) <= 1;
  assert {:msg "  42.3: Action at 20.3 ('discard1') for actor instance 'mrg' might not preserve the channel invariant (#452)"} C[Net#b] >= C[Net#g];
  assert {:msg "  43.3: Action at 20.3 ('discard1') for actor instance 'mrg' might not preserve the channel invariant (#453)"} C[Net#c] >= C[Net#h];
  assert {:msg "  45.3: Action at 20.3 ('discard1') for actor instance 'mrg' might not preserve the channel invariant (#454)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == i)
  );
  assert {:msg "  46.3: Action at 20.3 ('discard1') for actor instance 'mrg' might not preserve the channel invariant (#455)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#a]) ==> (M[Net#b][i] == M[Net#a][i]) && (M[Net#c][i] == M[Net#a][i])
  );
  assert {:msg "  48.3: Action at 20.3 ('discard1') for actor instance 'mrg' might not preserve the channel invariant (#456)"} (R[Net#d] + C[Net#d]) <= R[Net#b];
  assert {:msg "  49.3: Action at 20.3 ('discard1') for actor instance 'mrg' might not preserve the channel invariant (#457)"} (R[Net#e] + C[Net#e]) <= R[Net#c];
  assert {:msg "  50.3: Action at 20.3 ('discard1') for actor instance 'mrg' might not preserve the channel invariant (#458)"} R[Net#b] == ((R[Net#d] + C[Net#d]) + R[Net#g]);
  assert {:msg "  51.3: Action at 20.3 ('discard1') for actor instance 'mrg' might not preserve the channel invariant (#459)"} R[Net#c] == ((R[Net#e] + C[Net#e]) + R[Net#h]);
  assert {:msg "  53.3: Action at 20.3 ('discard1') for actor instance 'mrg' might not preserve the channel invariant (#460)"} ((R[Net#b] + R[Net#c]) == 2) ==> (((R[Net#d] + C[Net#d]) + (R[Net#e] + C[Net#e])) >= 1);
  assert {:msg "  54.3: Action at 20.3 ('discard1') for actor instance 'mrg' might not preserve the channel invariant (#461)"} ((R[Net#d] + C[Net#d]) > 0) ==> (M[Net#d][0] == 0);
  assert {:msg "  55.3: Action at 20.3 ('discard1') for actor instance 'mrg' might not preserve the channel invariant (#462)"} ((R[Net#e] + C[Net#e]) > 0) ==> (M[Net#e][0] == 0);
  assert {:msg "  57.3: Action at 20.3 ('discard1') for actor instance 'mrg' might not preserve the channel invariant (#463)"} C[Net#m] == 1;
  assert {:msg "  58.3: Action at 20.3 ('discard1') for actor instance 'mrg' might not preserve the channel invariant (#464)"} (R[Net#f] + C[Net#f]) == M[Net#m][R[Net#m]];
  assert {:msg "  60.3: Action at 20.3 ('discard1') for actor instance 'mrg' might not preserve the channel invariant (#465)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#d]) ==> (M[Net#d][i] < M[Net#m][R[Net#m]])
  );
  assert {:msg "  61.3: Action at 20.3 ('discard1') for actor instance 'mrg' might not preserve the channel invariant (#466)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#e][i] < M[Net#m][R[Net#m]])
  );
  assert {:msg "  63.3: Action at 20.3 ('discard1') for actor instance 'mrg' might not preserve the channel invariant (#467)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#f] + C[Net#f])) ==> (M[Net#f][i] == i)
  );
  assert {:msg "  65.3: Action at 20.3 ('discard1') for actor instance 'mrg' might not preserve the channel invariant (#468)"} (R[Net#n] + C[Net#n]) == ((R[Net#f] + C[Net#f]) + 1);
  assert {:msg "  66.3: Action at 20.3 ('discard1') for actor instance 'mrg' might not preserve the channel invariant (#469)"} R[Net#n] == R[Net#a];
}
procedure Net#anon$2#Merge#discard2#19()
  modifies C, R, M, St;
{
  var ActionPH#y1: int;
  var ActionPH#y2: int;
  var St#next: State;
  var in2#i: int;
  var s_in#s: int;
  assume C#init[Net#a] == 2;
  assume C#init[Net#b] == 0;
  assume C#init[Net#c] == 0;
  assume C#init[Net#d] == 0;
  assume C#init[Net#e] == 0;
  assume C#init[Net#f] == 0;
  assume C#init[Net#g] == 0;
  assume C#init[Net#h] == 0;
  assume C#init[Net#m] == 0;
  assume C#init[Net#n] == 0;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) == C#init[Net#a];
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
  assume R[Net#f] == 0;
  assume 0 <= R[Net#g];
  assume 0 <= C[Net#g];
  assume 0 <= R[Net#h];
  assume 0 <= C[Net#h];
  assume 0 <= R[Net#m];
  assume 0 <= C[Net#m];
  assume 0 <= R[Net#n];
  assume 0 <= C[Net#n];
  assume (M[Net#a][0] == 0) && (M[Net#a][1] == 1);
  assume R[Net#a] == (R[Net#b] + C[Net#b]);
  assume R[Net#a] == (R[Net#c] + C[Net#c]);
  assume (R[Net#a] + C[Net#a]) == 2;
  assume R[Net#a] <= 2;
  assume ((R[Net#g] + C[Net#g]) + (R[Net#h] + C[Net#h])) <= R[Net#a];
  assume (C[Net#g] + C[Net#h]) <= 1;
  assume C[Net#b] >= C[Net#g];
  assume C[Net#c] >= C[Net#h];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#a]) ==> (M[Net#b][i] == M[Net#a][i]) && (M[Net#c][i] == M[Net#a][i])
  );
  assume (R[Net#d] + C[Net#d]) <= R[Net#b];
  assume (R[Net#e] + C[Net#e]) <= R[Net#c];
  assume R[Net#b] == ((R[Net#d] + C[Net#d]) + R[Net#g]);
  assume R[Net#c] == ((R[Net#e] + C[Net#e]) + R[Net#h]);
  assume ((R[Net#b] + R[Net#c]) == 2) ==> (((R[Net#d] + C[Net#d]) + (R[Net#e] + C[Net#e])) >= 1);
  assume ((R[Net#d] + C[Net#d]) > 0) ==> (M[Net#d][0] == 0);
  assume ((R[Net#e] + C[Net#e]) > 0) ==> (M[Net#e][0] == 0);
  assume C[Net#m] == 1;
  assume (R[Net#f] + C[Net#f]) == M[Net#m][R[Net#m]];
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#d]) ==> (M[Net#d][i] < M[Net#m][R[Net#m]])
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#e][i] < M[Net#m][R[Net#m]])
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#f] + C[Net#f])) ==> (M[Net#f][i] == i)
  );
  assume (R[Net#n] + C[Net#n]) == ((R[Net#f] + C[Net#f]) + 1);
  assume R[Net#n] == R[Net#a];
  assume M[Net#m][R[Net#m] - 0] > M[Net#e][R[Net#e] - 0];
  assume true;
  assume (1 <= C[Net#e]) && (1 <= C[Net#m]) && (M[Net#m][R[Net#m] - 0] > M[Net#e][R[Net#e] - 0]);
  in2#i := M[Net#e][R[Net#e]];
  R[Net#e] := R[Net#e] + 1;
  C[Net#e] := C[Net#e] - 1;
  s_in#s := M[Net#m][R[Net#m]];
  R[Net#m] := R[Net#m] + 1;
  C[Net#m] := C[Net#m] - 1;
  M[Net#m][R[Net#m] + C[Net#m]] := s_in#s;
  C[Net#m] := C[Net#m] + 1;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) == C#init[Net#a];
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
  assume R[Net#f] == 0;
  assume 0 <= R[Net#g];
  assume 0 <= C[Net#g];
  assume 0 <= R[Net#h];
  assume 0 <= C[Net#h];
  assume 0 <= R[Net#m];
  assume 0 <= C[Net#m];
  assume 0 <= R[Net#n];
  assume 0 <= C[Net#n];
  assert {:msg "  Action at 23.3 ('discard2') for actor instance 'mrg' might not preserve the channel invariant (#492)"} (M[Net#a][0] == 0) && (M[Net#a][1] == 1);
  assert {:msg "  35.3: Action at 23.3 ('discard2') for actor instance 'mrg' might not preserve the channel invariant (#493)"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  36.3: Action at 23.3 ('discard2') for actor instance 'mrg' might not preserve the channel invariant (#494)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  38.3: Action at 23.3 ('discard2') for actor instance 'mrg' might not preserve the channel invariant (#495)"} (R[Net#a] + C[Net#a]) == 2;
  assert {:msg "  39.3: Action at 23.3 ('discard2') for actor instance 'mrg' might not preserve the channel invariant (#496)"} R[Net#a] <= 2;
  assert {:msg "  40.3: Action at 23.3 ('discard2') for actor instance 'mrg' might not preserve the channel invariant (#497)"} ((R[Net#g] + C[Net#g]) + (R[Net#h] + C[Net#h])) <= R[Net#a];
  assert {:msg "  41.3: Action at 23.3 ('discard2') for actor instance 'mrg' might not preserve the channel invariant (#498)"} (C[Net#g] + C[Net#h]) <= 1;
  assert {:msg "  42.3: Action at 23.3 ('discard2') for actor instance 'mrg' might not preserve the channel invariant (#499)"} C[Net#b] >= C[Net#g];
  assert {:msg "  43.3: Action at 23.3 ('discard2') for actor instance 'mrg' might not preserve the channel invariant (#500)"} C[Net#c] >= C[Net#h];
  assert {:msg "  45.3: Action at 23.3 ('discard2') for actor instance 'mrg' might not preserve the channel invariant (#501)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == i)
  );
  assert {:msg "  46.3: Action at 23.3 ('discard2') for actor instance 'mrg' might not preserve the channel invariant (#502)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#a]) ==> (M[Net#b][i] == M[Net#a][i]) && (M[Net#c][i] == M[Net#a][i])
  );
  assert {:msg "  48.3: Action at 23.3 ('discard2') for actor instance 'mrg' might not preserve the channel invariant (#503)"} (R[Net#d] + C[Net#d]) <= R[Net#b];
  assert {:msg "  49.3: Action at 23.3 ('discard2') for actor instance 'mrg' might not preserve the channel invariant (#504)"} (R[Net#e] + C[Net#e]) <= R[Net#c];
  assert {:msg "  50.3: Action at 23.3 ('discard2') for actor instance 'mrg' might not preserve the channel invariant (#505)"} R[Net#b] == ((R[Net#d] + C[Net#d]) + R[Net#g]);
  assert {:msg "  51.3: Action at 23.3 ('discard2') for actor instance 'mrg' might not preserve the channel invariant (#506)"} R[Net#c] == ((R[Net#e] + C[Net#e]) + R[Net#h]);
  assert {:msg "  53.3: Action at 23.3 ('discard2') for actor instance 'mrg' might not preserve the channel invariant (#507)"} ((R[Net#b] + R[Net#c]) == 2) ==> (((R[Net#d] + C[Net#d]) + (R[Net#e] + C[Net#e])) >= 1);
  assert {:msg "  54.3: Action at 23.3 ('discard2') for actor instance 'mrg' might not preserve the channel invariant (#508)"} ((R[Net#d] + C[Net#d]) > 0) ==> (M[Net#d][0] == 0);
  assert {:msg "  55.3: Action at 23.3 ('discard2') for actor instance 'mrg' might not preserve the channel invariant (#509)"} ((R[Net#e] + C[Net#e]) > 0) ==> (M[Net#e][0] == 0);
  assert {:msg "  57.3: Action at 23.3 ('discard2') for actor instance 'mrg' might not preserve the channel invariant (#510)"} C[Net#m] == 1;
  assert {:msg "  58.3: Action at 23.3 ('discard2') for actor instance 'mrg' might not preserve the channel invariant (#511)"} (R[Net#f] + C[Net#f]) == M[Net#m][R[Net#m]];
  assert {:msg "  60.3: Action at 23.3 ('discard2') for actor instance 'mrg' might not preserve the channel invariant (#512)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#d]) ==> (M[Net#d][i] < M[Net#m][R[Net#m]])
  );
  assert {:msg "  61.3: Action at 23.3 ('discard2') for actor instance 'mrg' might not preserve the channel invariant (#513)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#e][i] < M[Net#m][R[Net#m]])
  );
  assert {:msg "  63.3: Action at 23.3 ('discard2') for actor instance 'mrg' might not preserve the channel invariant (#514)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#f] + C[Net#f])) ==> (M[Net#f][i] == i)
  );
  assert {:msg "  65.3: Action at 23.3 ('discard2') for actor instance 'mrg' might not preserve the channel invariant (#515)"} (R[Net#n] + C[Net#n]) == ((R[Net#f] + C[Net#f]) + 1);
  assert {:msg "  66.3: Action at 23.3 ('discard2') for actor instance 'mrg' might not preserve the channel invariant (#516)"} R[Net#n] == R[Net#a];
}
procedure Net#anon$2#exit#20()
  modifies C, R, M, St;
{
  var ActionPH#y1: int;
  var ActionPH#y2: int;
  assume C#init[Net#a] == 2;
  assume C#init[Net#b] == 0;
  assume C#init[Net#c] == 0;
  assume C#init[Net#d] == 0;
  assume C#init[Net#e] == 0;
  assume C#init[Net#f] == 0;
  assume C#init[Net#g] == 0;
  assume C#init[Net#h] == 0;
  assume C#init[Net#m] == 0;
  assume C#init[Net#n] == 0;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) == C#init[Net#a];
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
  assume R[Net#f] == 0;
  assume 0 <= R[Net#g];
  assume 0 <= C[Net#g];
  assume 0 <= R[Net#h];
  assume 0 <= C[Net#h];
  assume 0 <= R[Net#m];
  assume 0 <= C[Net#m];
  assume 0 <= R[Net#n];
  assume 0 <= C[Net#n];
  assume (M[Net#a][0] == 0) && (M[Net#a][1] == 1);
  assume R[Net#a] == (R[Net#b] + C[Net#b]);
  assume R[Net#a] == (R[Net#c] + C[Net#c]);
  assume (R[Net#a] + C[Net#a]) == 2;
  assume R[Net#a] <= 2;
  assume ((R[Net#g] + C[Net#g]) + (R[Net#h] + C[Net#h])) <= R[Net#a];
  assume (C[Net#g] + C[Net#h]) <= 1;
  assume C[Net#b] >= C[Net#g];
  assume C[Net#c] >= C[Net#h];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#a]) ==> (M[Net#b][i] == M[Net#a][i]) && (M[Net#c][i] == M[Net#a][i])
  );
  assume (R[Net#d] + C[Net#d]) <= R[Net#b];
  assume (R[Net#e] + C[Net#e]) <= R[Net#c];
  assume R[Net#b] == ((R[Net#d] + C[Net#d]) + R[Net#g]);
  assume R[Net#c] == ((R[Net#e] + C[Net#e]) + R[Net#h]);
  assume ((R[Net#b] + R[Net#c]) == 2) ==> (((R[Net#d] + C[Net#d]) + (R[Net#e] + C[Net#e])) >= 1);
  assume ((R[Net#d] + C[Net#d]) > 0) ==> (M[Net#d][0] == 0);
  assume ((R[Net#e] + C[Net#e]) > 0) ==> (M[Net#e][0] == 0);
  assume C[Net#m] == 1;
  assume (R[Net#f] + C[Net#f]) == M[Net#m][R[Net#m]];
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#d]) ==> (M[Net#d][i] < M[Net#m][R[Net#m]])
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#e][i] < M[Net#m][R[Net#m]])
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#f] + C[Net#f])) ==> (M[Net#f][i] == i)
  );
  assume (R[Net#n] + C[Net#n]) == ((R[Net#f] + C[Net#f]) + 1);
  assume R[Net#n] == R[Net#a];
  assume !((1 <= C[Net#a]) && (1 <= C[Net#n]));
  assume !((1 <= C[Net#a]) && (1 <= C[Net#n]));
  assume !((!((1 <= C[Net#b]) && (1 <= C[Net#g]))) && (1 <= C[Net#b]));
  assume !((1 <= C[Net#b]) && (1 <= C[Net#g]));
  assume !((!((1 <= C[Net#c]) && (1 <= C[Net#h]))) && (1 <= C[Net#c]));
  assume !((1 <= C[Net#c]) && (1 <= C[Net#h]));
  assume !((1 <= C[Net#e]) && (1 <= C[Net#m]) && (M[Net#m][R[Net#m] - 0] == M[Net#e][R[Net#e] - 0]));
  assume !((1 <= C[Net#e]) && (1 <= C[Net#m]) && (M[Net#m][R[Net#m] - 0] > M[Net#e][R[Net#e] - 0]));
  assume !((1 <= C[Net#d]) && (1 <= C[Net#m]) && (M[Net#m][R[Net#m] - 0] == M[Net#d][R[Net#d] - 0]));
  assume !((1 <= C[Net#d]) && (1 <= C[Net#m]) && (M[Net#m][R[Net#m] - 0] > M[Net#d][R[Net#d] - 0]));
  ActionPH#y1 := M[Net#f][0];
  ActionPH#y2 := M[Net#f][1];
  assert {:msg "  70.13: Network action postcondition might not hold"} (ActionPH#y1 == 0) && (ActionPH#y2 == 1);
  R[Net#f] := R[Net#f] + C[Net#f];
  C[Net#f] := C[Net#f] - 2;
  C[Net#m] := C[Net#m] - 1;
  assume M[Net#m][R[Net#m]] == 0;
  C[Net#n] := C[Net#n] - 1;
  assert {:msg "  68.3: The network might leave unread tokens on channel a"} C[Net#a] == 0;
  assert {:msg "  68.3: The network might leave unread tokens on channel b"} C[Net#b] == 0;
  assert {:msg "  68.3: The network might leave unread tokens on channel c"} C[Net#c] == 0;
  assert {:msg "  68.3: The network might leave unread tokens on channel d"} C[Net#d] == 0;
  assert {:msg "  68.3: The network might leave unread tokens on channel e"} C[Net#e] == 0;
  assert {:msg "  68.3: The network might not produce the specified number of tokens on output out"} C[Net#f] == 0;
  assert {:msg "  68.3: The network might leave unread tokens on channel g"} C[Net#g] == 0;
  assert {:msg "  68.3: The network might leave unread tokens on channel h"} C[Net#h] == 0;
  assert {:msg "  68.3: The network might leave unread tokens on channel m"} C[Net#m] == 0;
  assert {:msg "  68.3: The network might leave unread tokens on channel n"} C[Net#n] == 0;
}

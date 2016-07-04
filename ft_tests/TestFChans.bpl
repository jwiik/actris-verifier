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
  assume true;
}
procedure Split#anon$1#3()
  modifies C, R, M, St;
{
  var IV#in#i: int;
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
  C[Net#m] := C[Net#m] - 1;
  assume M[Net#m][R[Net#m]] == 0;
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
procedure Net#anon$2#entry#9()
  modifies C, R, M, St;
{
  var ActionPH#y1: int;
  var ActionPH#y2: int;
  var ActionPH#y3: int;
  assume C#init[Net#a] == 3;
  assume C#init[Net#b] == 0;
  assume C#init[Net#c] == 0;
  assume C#init[Net#d] == 0;
  assume C#init[Net#e] == 0;
  assume C#init[Net#f] == 0;
  assume C#init[Net#g] == 0;
  assume C#init[Net#h] == 0;
  assume C#init[Net#m] == 0;
  assume R[Net#a] == 0;
  assume R[Net#b] == 0;
  assume R[Net#c] == 0;
  assume R[Net#d] == 0;
  assume R[Net#e] == 0;
  assume R[Net#f] == 0;
  assume R[Net#g] == 0;
  assume R[Net#h] == 0;
  assume R[Net#m] == 0;
  assume C#init == C;
  C[Net#m] := C[Net#m] + 1;
  assume M[Net#m][R[Net#m]] == 0;
  assume (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
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
  assert {:msg "  Channel invariant might not hold on action entry (#20)"} (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
  assert {:msg "  33.3: Channel invariant might not hold on action entry (#21)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == i)
  );
  assert {:msg "  35.3: Channel invariant might not hold on action entry (#22)"} C[Net#m] == 1;
  assert {:msg "  36.3: Channel invariant might not hold on action entry (#23)"} (0 <= M[Net#m][R[Net#m]]) && (M[Net#m][R[Net#m]] <= 3);
  assert {:msg "  38.3: Channel invariant might not hold on action entry (#24)"} ((R[Net#g] + C[Net#g]) + (R[Net#h] + C[Net#h])) <= R[Net#a];
  assert {:msg "  40.3: Channel invariant might not hold on action entry (#25)"} (R[Net#b] + C[Net#b]) == R[Net#a];
  assert {:msg "  41.3: Channel invariant might not hold on action entry (#26)"} (R[Net#c] + C[Net#c]) == R[Net#a];
  assert {:msg "  42.3: Channel invariant might not hold on action entry (#27)"} C[Net#b] >= C[Net#g];
  assert {:msg "  43.3: Channel invariant might not hold on action entry (#28)"} C[Net#c] >= C[Net#h];
  assert {:msg "  45.3: Channel invariant might not hold on action entry (#29)"} (R[Net#d] + C[Net#d]) <= R[Net#b];
  assert {:msg "  46.3: Channel invariant might not hold on action entry (#30)"} (R[Net#e] + C[Net#e]) <= R[Net#c];
  assert {:msg "  49.3: Channel invariant might not hold on action entry (#31)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == M[Net#a][i]) && (M[Net#c][i] == M[Net#a][i])
  );
  assert {:msg "  52.3: Channel invariant might not hold on action entry (#32)"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == (M[Net#a][i - 1] + 1))
  );
  assert {:msg "  53.3: Channel invariant might not hold on action entry (#33)"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == (M[Net#b][i - 1] + 1))
  );
  assert {:msg "  54.3: Channel invariant might not hold on action entry (#34)"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (M[Net#c][i] == (M[Net#c][i - 1] + 1))
  );
  assert {:msg "  57.3: Channel invariant might not hold on action entry (#35)"} ((R[Net#d] + C[Net#d]) > 0) ==> (M[Net#d][(R[Net#d] + C[Net#d]) - 1] <= M[Net#b][R[Net#b] - 1]);
  assert {:msg "  58.3: Channel invariant might not hold on action entry (#36)"} ((R[Net#e] + C[Net#e]) > 0) ==> (M[Net#e][(R[Net#e] + C[Net#e]) - 1] <= M[Net#c][R[Net#c] - 1]);
  assert {:msg "  61.3: Channel invariant might not hold on action entry (#37)"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (M[Net#d][i] > M[Net#d][i - 1])
  );
  assert {:msg "  62.3: Channel invariant might not hold on action entry (#38)"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (M[Net#e][i] > M[Net#e][i - 1])
  );
  assume (forall i: int :: 
    (0 <= i) && (i <= AT#Min(R[Net#a], R[Net#b])) ==> (exists  j: int :: 
      ((0 <= j) && (j < (R[Net#d] + C[Net#d])) && (M[Net#d][j] == i)) || ((0 <= j) && (j < (R[Net#e] + C[Net#e])) && (M[Net#e][j] == i))
    )
  );
  assert {:msg "  79.3: Channel invariant might not hold on action entry (#40)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#d]) ==> (M[Net#d][i] < M[Net#m][R[Net#m]])
  );
  assert {:msg "  80.3: Channel invariant might not hold on action entry (#41)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#e][i] < M[Net#m][R[Net#m]])
  );
  assume ((C[Net#d] > 0) || (C[Net#e] > 0)) ==> ((M[Net#d][R[Net#d]] == M[Net#m][R[Net#m]]) || (M[Net#e][R[Net#e]] == M[Net#m][R[Net#m]]));
  assert {:msg "  84.3: Channel invariant might not hold on action entry (#43)"} (R[Net#f] + C[Net#f]) == M[Net#m][R[Net#m]];
  assert {:msg "  85.3: Channel invariant might not hold on action entry (#44)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#f] + C[Net#f])) ==> (M[Net#f][i] == i)
  );
}
procedure Net#anon$2#Split#anon$0#10()
  modifies C, R, M, St;
{
  var ActionPH#y1: int;
  var ActionPH#y2: int;
  var ActionPH#y3: int;
  var St#next: State;
  var in#i: int;
  assume C#init[Net#a] == 3;
  assume C#init[Net#b] == 0;
  assume C#init[Net#c] == 0;
  assume C#init[Net#d] == 0;
  assume C#init[Net#e] == 0;
  assume C#init[Net#f] == 0;
  assume C#init[Net#g] == 0;
  assume C#init[Net#h] == 0;
  assume C#init[Net#m] == 0;
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
  assume (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == i)
  );
  assume C[Net#m] == 1;
  assume (0 <= M[Net#m][R[Net#m]]) && (M[Net#m][R[Net#m]] <= 3);
  assume ((R[Net#g] + C[Net#g]) + (R[Net#h] + C[Net#h])) <= R[Net#a];
  assume (R[Net#b] + C[Net#b]) == R[Net#a];
  assume (R[Net#c] + C[Net#c]) == R[Net#a];
  assume C[Net#b] >= C[Net#g];
  assume C[Net#c] >= C[Net#h];
  assume (R[Net#d] + C[Net#d]) <= R[Net#b];
  assume (R[Net#e] + C[Net#e]) <= R[Net#c];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == M[Net#a][i]) && (M[Net#c][i] == M[Net#a][i])
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == (M[Net#a][i - 1] + 1))
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == (M[Net#b][i - 1] + 1))
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (M[Net#c][i] == (M[Net#c][i - 1] + 1))
  );
  assume ((R[Net#d] + C[Net#d]) > 0) ==> (M[Net#d][(R[Net#d] + C[Net#d]) - 1] <= M[Net#b][R[Net#b] - 1]);
  assume ((R[Net#e] + C[Net#e]) > 0) ==> (M[Net#e][(R[Net#e] + C[Net#e]) - 1] <= M[Net#c][R[Net#c] - 1]);
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (M[Net#d][i] > M[Net#d][i - 1])
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (M[Net#e][i] > M[Net#e][i - 1])
  );
  assume (forall i: int :: 
    (0 <= i) && (i <= AT#Min(R[Net#a], R[Net#b])) ==> (exists  j: int :: 
      ((0 <= j) && (j < (R[Net#d] + C[Net#d])) && (M[Net#d][j] == i)) || ((0 <= j) && (j < (R[Net#e] + C[Net#e])) && (M[Net#e][j] == i))
    )
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#d]) ==> (M[Net#d][i] < M[Net#m][R[Net#m]])
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#e][i] < M[Net#m][R[Net#m]])
  );
  assume ((C[Net#d] > 0) || (C[Net#e] > 0)) ==> ((M[Net#d][R[Net#d]] == M[Net#m][R[Net#m]]) || (M[Net#e][R[Net#e]] == M[Net#m][R[Net#m]]));
  assume (R[Net#f] + C[Net#f]) == M[Net#m][R[Net#m]];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#f] + C[Net#f])) ==> (M[Net#f][i] == i)
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
  assert {:msg "  Action at 8.3 ('anon$0') for actor instance 'spl' might not preserve the channel invariant (#65)"} (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
  assert {:msg "  33.3: Action at 8.3 ('anon$0') for actor instance 'spl' might not preserve the channel invariant (#66)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == i)
  );
  assert {:msg "  35.3: Action at 8.3 ('anon$0') for actor instance 'spl' might not preserve the channel invariant (#67)"} C[Net#m] == 1;
  assert {:msg "  36.3: Action at 8.3 ('anon$0') for actor instance 'spl' might not preserve the channel invariant (#68)"} (0 <= M[Net#m][R[Net#m]]) && (M[Net#m][R[Net#m]] <= 3);
  assert {:msg "  38.3: Action at 8.3 ('anon$0') for actor instance 'spl' might not preserve the channel invariant (#69)"} ((R[Net#g] + C[Net#g]) + (R[Net#h] + C[Net#h])) <= R[Net#a];
  assert {:msg "  40.3: Action at 8.3 ('anon$0') for actor instance 'spl' might not preserve the channel invariant (#70)"} (R[Net#b] + C[Net#b]) == R[Net#a];
  assert {:msg "  41.3: Action at 8.3 ('anon$0') for actor instance 'spl' might not preserve the channel invariant (#71)"} (R[Net#c] + C[Net#c]) == R[Net#a];
  assert {:msg "  42.3: Action at 8.3 ('anon$0') for actor instance 'spl' might not preserve the channel invariant (#72)"} C[Net#b] >= C[Net#g];
  assert {:msg "  43.3: Action at 8.3 ('anon$0') for actor instance 'spl' might not preserve the channel invariant (#73)"} C[Net#c] >= C[Net#h];
  assert {:msg "  45.3: Action at 8.3 ('anon$0') for actor instance 'spl' might not preserve the channel invariant (#74)"} (R[Net#d] + C[Net#d]) <= R[Net#b];
  assert {:msg "  46.3: Action at 8.3 ('anon$0') for actor instance 'spl' might not preserve the channel invariant (#75)"} (R[Net#e] + C[Net#e]) <= R[Net#c];
  assert {:msg "  49.3: Action at 8.3 ('anon$0') for actor instance 'spl' might not preserve the channel invariant (#76)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == M[Net#a][i]) && (M[Net#c][i] == M[Net#a][i])
  );
  assert {:msg "  52.3: Action at 8.3 ('anon$0') for actor instance 'spl' might not preserve the channel invariant (#77)"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == (M[Net#a][i - 1] + 1))
  );
  assert {:msg "  53.3: Action at 8.3 ('anon$0') for actor instance 'spl' might not preserve the channel invariant (#78)"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == (M[Net#b][i - 1] + 1))
  );
  assert {:msg "  54.3: Action at 8.3 ('anon$0') for actor instance 'spl' might not preserve the channel invariant (#79)"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (M[Net#c][i] == (M[Net#c][i - 1] + 1))
  );
  assert {:msg "  57.3: Action at 8.3 ('anon$0') for actor instance 'spl' might not preserve the channel invariant (#80)"} ((R[Net#d] + C[Net#d]) > 0) ==> (M[Net#d][(R[Net#d] + C[Net#d]) - 1] <= M[Net#b][R[Net#b] - 1]);
  assert {:msg "  58.3: Action at 8.3 ('anon$0') for actor instance 'spl' might not preserve the channel invariant (#81)"} ((R[Net#e] + C[Net#e]) > 0) ==> (M[Net#e][(R[Net#e] + C[Net#e]) - 1] <= M[Net#c][R[Net#c] - 1]);
  assert {:msg "  61.3: Action at 8.3 ('anon$0') for actor instance 'spl' might not preserve the channel invariant (#82)"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (M[Net#d][i] > M[Net#d][i - 1])
  );
  assert {:msg "  62.3: Action at 8.3 ('anon$0') for actor instance 'spl' might not preserve the channel invariant (#83)"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (M[Net#e][i] > M[Net#e][i - 1])
  );
  assume (forall i: int :: 
    (0 <= i) && (i <= AT#Min(R[Net#a], R[Net#b])) ==> (exists  j: int :: 
      ((0 <= j) && (j < (R[Net#d] + C[Net#d])) && (M[Net#d][j] == i)) || ((0 <= j) && (j < (R[Net#e] + C[Net#e])) && (M[Net#e][j] == i))
    )
  );
  assert {:msg "  79.3: Action at 8.3 ('anon$0') for actor instance 'spl' might not preserve the channel invariant (#85)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#d]) ==> (M[Net#d][i] < M[Net#m][R[Net#m]])
  );
  assert {:msg "  80.3: Action at 8.3 ('anon$0') for actor instance 'spl' might not preserve the channel invariant (#86)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#e][i] < M[Net#m][R[Net#m]])
  );
  assume ((C[Net#d] > 0) || (C[Net#e] > 0)) ==> ((M[Net#d][R[Net#d]] == M[Net#m][R[Net#m]]) || (M[Net#e][R[Net#e]] == M[Net#m][R[Net#m]]));
  assert {:msg "  84.3: Action at 8.3 ('anon$0') for actor instance 'spl' might not preserve the channel invariant (#88)"} (R[Net#f] + C[Net#f]) == M[Net#m][R[Net#m]];
  assert {:msg "  85.3: Action at 8.3 ('anon$0') for actor instance 'spl' might not preserve the channel invariant (#89)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#f] + C[Net#f])) ==> (M[Net#f][i] == i)
  );
}
procedure Net#anon$2#Split#anon$1#11()
  modifies C, R, M, St;
{
  var ActionPH#y1: int;
  var ActionPH#y2: int;
  var ActionPH#y3: int;
  var St#next: State;
  var in#i: int;
  assume C#init[Net#a] == 3;
  assume C#init[Net#b] == 0;
  assume C#init[Net#c] == 0;
  assume C#init[Net#d] == 0;
  assume C#init[Net#e] == 0;
  assume C#init[Net#f] == 0;
  assume C#init[Net#g] == 0;
  assume C#init[Net#h] == 0;
  assume C#init[Net#m] == 0;
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
  assume (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == i)
  );
  assume C[Net#m] == 1;
  assume (0 <= M[Net#m][R[Net#m]]) && (M[Net#m][R[Net#m]] <= 3);
  assume ((R[Net#g] + C[Net#g]) + (R[Net#h] + C[Net#h])) <= R[Net#a];
  assume (R[Net#b] + C[Net#b]) == R[Net#a];
  assume (R[Net#c] + C[Net#c]) == R[Net#a];
  assume C[Net#b] >= C[Net#g];
  assume C[Net#c] >= C[Net#h];
  assume (R[Net#d] + C[Net#d]) <= R[Net#b];
  assume (R[Net#e] + C[Net#e]) <= R[Net#c];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == M[Net#a][i]) && (M[Net#c][i] == M[Net#a][i])
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == (M[Net#a][i - 1] + 1))
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == (M[Net#b][i - 1] + 1))
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (M[Net#c][i] == (M[Net#c][i - 1] + 1))
  );
  assume ((R[Net#d] + C[Net#d]) > 0) ==> (M[Net#d][(R[Net#d] + C[Net#d]) - 1] <= M[Net#b][R[Net#b] - 1]);
  assume ((R[Net#e] + C[Net#e]) > 0) ==> (M[Net#e][(R[Net#e] + C[Net#e]) - 1] <= M[Net#c][R[Net#c] - 1]);
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (M[Net#d][i] > M[Net#d][i - 1])
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (M[Net#e][i] > M[Net#e][i - 1])
  );
  assume (forall i: int :: 
    (0 <= i) && (i <= AT#Min(R[Net#a], R[Net#b])) ==> (exists  j: int :: 
      ((0 <= j) && (j < (R[Net#d] + C[Net#d])) && (M[Net#d][j] == i)) || ((0 <= j) && (j < (R[Net#e] + C[Net#e])) && (M[Net#e][j] == i))
    )
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#d]) ==> (M[Net#d][i] < M[Net#m][R[Net#m]])
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#e][i] < M[Net#m][R[Net#m]])
  );
  assume ((C[Net#d] > 0) || (C[Net#e] > 0)) ==> ((M[Net#d][R[Net#d]] == M[Net#m][R[Net#m]]) || (M[Net#e][R[Net#e]] == M[Net#m][R[Net#m]]));
  assume (R[Net#f] + C[Net#f]) == M[Net#m][R[Net#m]];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#f] + C[Net#f])) ==> (M[Net#f][i] == i)
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
  assert {:msg "  Action at 9.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#110)"} (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
  assert {:msg "  33.3: Action at 9.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#111)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == i)
  );
  assert {:msg "  35.3: Action at 9.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#112)"} C[Net#m] == 1;
  assert {:msg "  36.3: Action at 9.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#113)"} (0 <= M[Net#m][R[Net#m]]) && (M[Net#m][R[Net#m]] <= 3);
  assert {:msg "  38.3: Action at 9.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#114)"} ((R[Net#g] + C[Net#g]) + (R[Net#h] + C[Net#h])) <= R[Net#a];
  assert {:msg "  40.3: Action at 9.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#115)"} (R[Net#b] + C[Net#b]) == R[Net#a];
  assert {:msg "  41.3: Action at 9.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#116)"} (R[Net#c] + C[Net#c]) == R[Net#a];
  assert {:msg "  42.3: Action at 9.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#117)"} C[Net#b] >= C[Net#g];
  assert {:msg "  43.3: Action at 9.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#118)"} C[Net#c] >= C[Net#h];
  assert {:msg "  45.3: Action at 9.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#119)"} (R[Net#d] + C[Net#d]) <= R[Net#b];
  assert {:msg "  46.3: Action at 9.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#120)"} (R[Net#e] + C[Net#e]) <= R[Net#c];
  assert {:msg "  49.3: Action at 9.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#121)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == M[Net#a][i]) && (M[Net#c][i] == M[Net#a][i])
  );
  assert {:msg "  52.3: Action at 9.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#122)"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == (M[Net#a][i - 1] + 1))
  );
  assert {:msg "  53.3: Action at 9.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#123)"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == (M[Net#b][i - 1] + 1))
  );
  assert {:msg "  54.3: Action at 9.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#124)"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (M[Net#c][i] == (M[Net#c][i - 1] + 1))
  );
  assert {:msg "  57.3: Action at 9.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#125)"} ((R[Net#d] + C[Net#d]) > 0) ==> (M[Net#d][(R[Net#d] + C[Net#d]) - 1] <= M[Net#b][R[Net#b] - 1]);
  assert {:msg "  58.3: Action at 9.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#126)"} ((R[Net#e] + C[Net#e]) > 0) ==> (M[Net#e][(R[Net#e] + C[Net#e]) - 1] <= M[Net#c][R[Net#c] - 1]);
  assert {:msg "  61.3: Action at 9.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#127)"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (M[Net#d][i] > M[Net#d][i - 1])
  );
  assert {:msg "  62.3: Action at 9.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#128)"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (M[Net#e][i] > M[Net#e][i - 1])
  );
  assume (forall i: int :: 
    (0 <= i) && (i <= AT#Min(R[Net#a], R[Net#b])) ==> (exists  j: int :: 
      ((0 <= j) && (j < (R[Net#d] + C[Net#d])) && (M[Net#d][j] == i)) || ((0 <= j) && (j < (R[Net#e] + C[Net#e])) && (M[Net#e][j] == i))
    )
  );
  assert {:msg "  79.3: Action at 9.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#130)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#d]) ==> (M[Net#d][i] < M[Net#m][R[Net#m]])
  );
  assert {:msg "  80.3: Action at 9.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#131)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#e][i] < M[Net#m][R[Net#m]])
  );
  assume ((C[Net#d] > 0) || (C[Net#e] > 0)) ==> ((M[Net#d][R[Net#d]] == M[Net#m][R[Net#m]]) || (M[Net#e][R[Net#e]] == M[Net#m][R[Net#m]]));
  assert {:msg "  84.3: Action at 9.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#133)"} (R[Net#f] + C[Net#f]) == M[Net#m][R[Net#m]];
  assert {:msg "  85.3: Action at 9.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#134)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#f] + C[Net#f])) ==> (M[Net#f][i] == i)
  );
}
procedure Net#anon$2#F#fail1#12()
  modifies C, R, M, St;
{
  var ActionPH#y1: int;
  var ActionPH#y2: int;
  var ActionPH#y3: int;
  var St#next: State;
  var in#i: int;
  var f#t: bool;
  assume C#init[Net#a] == 3;
  assume C#init[Net#b] == 0;
  assume C#init[Net#c] == 0;
  assume C#init[Net#d] == 0;
  assume C#init[Net#e] == 0;
  assume C#init[Net#f] == 0;
  assume C#init[Net#g] == 0;
  assume C#init[Net#h] == 0;
  assume C#init[Net#m] == 0;
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
  assume (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == i)
  );
  assume C[Net#m] == 1;
  assume (0 <= M[Net#m][R[Net#m]]) && (M[Net#m][R[Net#m]] <= 3);
  assume ((R[Net#g] + C[Net#g]) + (R[Net#h] + C[Net#h])) <= R[Net#a];
  assume (R[Net#b] + C[Net#b]) == R[Net#a];
  assume (R[Net#c] + C[Net#c]) == R[Net#a];
  assume C[Net#b] >= C[Net#g];
  assume C[Net#c] >= C[Net#h];
  assume (R[Net#d] + C[Net#d]) <= R[Net#b];
  assume (R[Net#e] + C[Net#e]) <= R[Net#c];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == M[Net#a][i]) && (M[Net#c][i] == M[Net#a][i])
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == (M[Net#a][i - 1] + 1))
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == (M[Net#b][i - 1] + 1))
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (M[Net#c][i] == (M[Net#c][i - 1] + 1))
  );
  assume ((R[Net#d] + C[Net#d]) > 0) ==> (M[Net#d][(R[Net#d] + C[Net#d]) - 1] <= M[Net#b][R[Net#b] - 1]);
  assume ((R[Net#e] + C[Net#e]) > 0) ==> (M[Net#e][(R[Net#e] + C[Net#e]) - 1] <= M[Net#c][R[Net#c] - 1]);
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (M[Net#d][i] > M[Net#d][i - 1])
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (M[Net#e][i] > M[Net#e][i - 1])
  );
  assume (forall i: int :: 
    (0 <= i) && (i <= AT#Min(R[Net#a], R[Net#b])) ==> (exists  j: int :: 
      ((0 <= j) && (j < (R[Net#d] + C[Net#d])) && (M[Net#d][j] == i)) || ((0 <= j) && (j < (R[Net#e] + C[Net#e])) && (M[Net#e][j] == i))
    )
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#d]) ==> (M[Net#d][i] < M[Net#m][R[Net#m]])
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#e][i] < M[Net#m][R[Net#m]])
  );
  assume ((C[Net#d] > 0) || (C[Net#e] > 0)) ==> ((M[Net#d][R[Net#d]] == M[Net#m][R[Net#m]]) || (M[Net#e][R[Net#e]] == M[Net#m][R[Net#m]]));
  assume (R[Net#f] + C[Net#f]) == M[Net#m][R[Net#m]];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#f] + C[Net#f])) ==> (M[Net#f][i] == i)
  );
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
  assert {:msg "  Action at 3.3 ('fail1') for actor instance 'f1' might not preserve the channel invariant (#155)"} (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
  assert {:msg "  33.3: Action at 3.3 ('fail1') for actor instance 'f1' might not preserve the channel invariant (#156)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == i)
  );
  assert {:msg "  35.3: Action at 3.3 ('fail1') for actor instance 'f1' might not preserve the channel invariant (#157)"} C[Net#m] == 1;
  assert {:msg "  36.3: Action at 3.3 ('fail1') for actor instance 'f1' might not preserve the channel invariant (#158)"} (0 <= M[Net#m][R[Net#m]]) && (M[Net#m][R[Net#m]] <= 3);
  assert {:msg "  38.3: Action at 3.3 ('fail1') for actor instance 'f1' might not preserve the channel invariant (#159)"} ((R[Net#g] + C[Net#g]) + (R[Net#h] + C[Net#h])) <= R[Net#a];
  assert {:msg "  40.3: Action at 3.3 ('fail1') for actor instance 'f1' might not preserve the channel invariant (#160)"} (R[Net#b] + C[Net#b]) == R[Net#a];
  assert {:msg "  41.3: Action at 3.3 ('fail1') for actor instance 'f1' might not preserve the channel invariant (#161)"} (R[Net#c] + C[Net#c]) == R[Net#a];
  assert {:msg "  42.3: Action at 3.3 ('fail1') for actor instance 'f1' might not preserve the channel invariant (#162)"} C[Net#b] >= C[Net#g];
  assert {:msg "  43.3: Action at 3.3 ('fail1') for actor instance 'f1' might not preserve the channel invariant (#163)"} C[Net#c] >= C[Net#h];
  assert {:msg "  45.3: Action at 3.3 ('fail1') for actor instance 'f1' might not preserve the channel invariant (#164)"} (R[Net#d] + C[Net#d]) <= R[Net#b];
  assert {:msg "  46.3: Action at 3.3 ('fail1') for actor instance 'f1' might not preserve the channel invariant (#165)"} (R[Net#e] + C[Net#e]) <= R[Net#c];
  assert {:msg "  49.3: Action at 3.3 ('fail1') for actor instance 'f1' might not preserve the channel invariant (#166)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == M[Net#a][i]) && (M[Net#c][i] == M[Net#a][i])
  );
  assert {:msg "  52.3: Action at 3.3 ('fail1') for actor instance 'f1' might not preserve the channel invariant (#167)"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == (M[Net#a][i - 1] + 1))
  );
  assert {:msg "  53.3: Action at 3.3 ('fail1') for actor instance 'f1' might not preserve the channel invariant (#168)"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == (M[Net#b][i - 1] + 1))
  );
  assert {:msg "  54.3: Action at 3.3 ('fail1') for actor instance 'f1' might not preserve the channel invariant (#169)"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (M[Net#c][i] == (M[Net#c][i - 1] + 1))
  );
  assert {:msg "  57.3: Action at 3.3 ('fail1') for actor instance 'f1' might not preserve the channel invariant (#170)"} ((R[Net#d] + C[Net#d]) > 0) ==> (M[Net#d][(R[Net#d] + C[Net#d]) - 1] <= M[Net#b][R[Net#b] - 1]);
  assert {:msg "  58.3: Action at 3.3 ('fail1') for actor instance 'f1' might not preserve the channel invariant (#171)"} ((R[Net#e] + C[Net#e]) > 0) ==> (M[Net#e][(R[Net#e] + C[Net#e]) - 1] <= M[Net#c][R[Net#c] - 1]);
  assert {:msg "  61.3: Action at 3.3 ('fail1') for actor instance 'f1' might not preserve the channel invariant (#172)"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (M[Net#d][i] > M[Net#d][i - 1])
  );
  assert {:msg "  62.3: Action at 3.3 ('fail1') for actor instance 'f1' might not preserve the channel invariant (#173)"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (M[Net#e][i] > M[Net#e][i - 1])
  );
  assume (forall i: int :: 
    (0 <= i) && (i <= AT#Min(R[Net#a], R[Net#b])) ==> (exists  j: int :: 
      ((0 <= j) && (j < (R[Net#d] + C[Net#d])) && (M[Net#d][j] == i)) || ((0 <= j) && (j < (R[Net#e] + C[Net#e])) && (M[Net#e][j] == i))
    )
  );
  assert {:msg "  79.3: Action at 3.3 ('fail1') for actor instance 'f1' might not preserve the channel invariant (#175)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#d]) ==> (M[Net#d][i] < M[Net#m][R[Net#m]])
  );
  assert {:msg "  80.3: Action at 3.3 ('fail1') for actor instance 'f1' might not preserve the channel invariant (#176)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#e][i] < M[Net#m][R[Net#m]])
  );
  assume ((C[Net#d] > 0) || (C[Net#e] > 0)) ==> ((M[Net#d][R[Net#d]] == M[Net#m][R[Net#m]]) || (M[Net#e][R[Net#e]] == M[Net#m][R[Net#m]]));
  assert {:msg "  84.3: Action at 3.3 ('fail1') for actor instance 'f1' might not preserve the channel invariant (#178)"} (R[Net#f] + C[Net#f]) == M[Net#m][R[Net#m]];
  assert {:msg "  85.3: Action at 3.3 ('fail1') for actor instance 'f1' might not preserve the channel invariant (#179)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#f] + C[Net#f])) ==> (M[Net#f][i] == i)
  );
}
procedure Net#anon$2#F#n#13()
  modifies C, R, M, St;
{
  var ActionPH#y1: int;
  var ActionPH#y2: int;
  var ActionPH#y3: int;
  var St#next: State;
  var in#i: int;
  assume C#init[Net#a] == 3;
  assume C#init[Net#b] == 0;
  assume C#init[Net#c] == 0;
  assume C#init[Net#d] == 0;
  assume C#init[Net#e] == 0;
  assume C#init[Net#f] == 0;
  assume C#init[Net#g] == 0;
  assume C#init[Net#h] == 0;
  assume C#init[Net#m] == 0;
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
  assume (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == i)
  );
  assume C[Net#m] == 1;
  assume (0 <= M[Net#m][R[Net#m]]) && (M[Net#m][R[Net#m]] <= 3);
  assume ((R[Net#g] + C[Net#g]) + (R[Net#h] + C[Net#h])) <= R[Net#a];
  assume (R[Net#b] + C[Net#b]) == R[Net#a];
  assume (R[Net#c] + C[Net#c]) == R[Net#a];
  assume C[Net#b] >= C[Net#g];
  assume C[Net#c] >= C[Net#h];
  assume (R[Net#d] + C[Net#d]) <= R[Net#b];
  assume (R[Net#e] + C[Net#e]) <= R[Net#c];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == M[Net#a][i]) && (M[Net#c][i] == M[Net#a][i])
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == (M[Net#a][i - 1] + 1))
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == (M[Net#b][i - 1] + 1))
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (M[Net#c][i] == (M[Net#c][i - 1] + 1))
  );
  assume ((R[Net#d] + C[Net#d]) > 0) ==> (M[Net#d][(R[Net#d] + C[Net#d]) - 1] <= M[Net#b][R[Net#b] - 1]);
  assume ((R[Net#e] + C[Net#e]) > 0) ==> (M[Net#e][(R[Net#e] + C[Net#e]) - 1] <= M[Net#c][R[Net#c] - 1]);
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (M[Net#d][i] > M[Net#d][i - 1])
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (M[Net#e][i] > M[Net#e][i - 1])
  );
  assume (forall i: int :: 
    (0 <= i) && (i <= AT#Min(R[Net#a], R[Net#b])) ==> (exists  j: int :: 
      ((0 <= j) && (j < (R[Net#d] + C[Net#d])) && (M[Net#d][j] == i)) || ((0 <= j) && (j < (R[Net#e] + C[Net#e])) && (M[Net#e][j] == i))
    )
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#d]) ==> (M[Net#d][i] < M[Net#m][R[Net#m]])
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#e][i] < M[Net#m][R[Net#m]])
  );
  assume ((C[Net#d] > 0) || (C[Net#e] > 0)) ==> ((M[Net#d][R[Net#d]] == M[Net#m][R[Net#m]]) || (M[Net#e][R[Net#e]] == M[Net#m][R[Net#m]]));
  assume (R[Net#f] + C[Net#f]) == M[Net#m][R[Net#m]];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#f] + C[Net#f])) ==> (M[Net#f][i] == i)
  );
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
  assert {:msg "  Action at 2.3 ('n') for actor instance 'f1' might not preserve the channel invariant (#200)"} (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
  assert {:msg "  33.3: Action at 2.3 ('n') for actor instance 'f1' might not preserve the channel invariant (#201)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == i)
  );
  assert {:msg "  35.3: Action at 2.3 ('n') for actor instance 'f1' might not preserve the channel invariant (#202)"} C[Net#m] == 1;
  assert {:msg "  36.3: Action at 2.3 ('n') for actor instance 'f1' might not preserve the channel invariant (#203)"} (0 <= M[Net#m][R[Net#m]]) && (M[Net#m][R[Net#m]] <= 3);
  assert {:msg "  38.3: Action at 2.3 ('n') for actor instance 'f1' might not preserve the channel invariant (#204)"} ((R[Net#g] + C[Net#g]) + (R[Net#h] + C[Net#h])) <= R[Net#a];
  assert {:msg "  40.3: Action at 2.3 ('n') for actor instance 'f1' might not preserve the channel invariant (#205)"} (R[Net#b] + C[Net#b]) == R[Net#a];
  assert {:msg "  41.3: Action at 2.3 ('n') for actor instance 'f1' might not preserve the channel invariant (#206)"} (R[Net#c] + C[Net#c]) == R[Net#a];
  assert {:msg "  42.3: Action at 2.3 ('n') for actor instance 'f1' might not preserve the channel invariant (#207)"} C[Net#b] >= C[Net#g];
  assert {:msg "  43.3: Action at 2.3 ('n') for actor instance 'f1' might not preserve the channel invariant (#208)"} C[Net#c] >= C[Net#h];
  assert {:msg "  45.3: Action at 2.3 ('n') for actor instance 'f1' might not preserve the channel invariant (#209)"} (R[Net#d] + C[Net#d]) <= R[Net#b];
  assert {:msg "  46.3: Action at 2.3 ('n') for actor instance 'f1' might not preserve the channel invariant (#210)"} (R[Net#e] + C[Net#e]) <= R[Net#c];
  assert {:msg "  49.3: Action at 2.3 ('n') for actor instance 'f1' might not preserve the channel invariant (#211)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == M[Net#a][i]) && (M[Net#c][i] == M[Net#a][i])
  );
  assert {:msg "  52.3: Action at 2.3 ('n') for actor instance 'f1' might not preserve the channel invariant (#212)"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == (M[Net#a][i - 1] + 1))
  );
  assert {:msg "  53.3: Action at 2.3 ('n') for actor instance 'f1' might not preserve the channel invariant (#213)"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == (M[Net#b][i - 1] + 1))
  );
  assert {:msg "  54.3: Action at 2.3 ('n') for actor instance 'f1' might not preserve the channel invariant (#214)"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (M[Net#c][i] == (M[Net#c][i - 1] + 1))
  );
  assert {:msg "  57.3: Action at 2.3 ('n') for actor instance 'f1' might not preserve the channel invariant (#215)"} ((R[Net#d] + C[Net#d]) > 0) ==> (M[Net#d][(R[Net#d] + C[Net#d]) - 1] <= M[Net#b][R[Net#b] - 1]);
  assert {:msg "  58.3: Action at 2.3 ('n') for actor instance 'f1' might not preserve the channel invariant (#216)"} ((R[Net#e] + C[Net#e]) > 0) ==> (M[Net#e][(R[Net#e] + C[Net#e]) - 1] <= M[Net#c][R[Net#c] - 1]);
  assert {:msg "  61.3: Action at 2.3 ('n') for actor instance 'f1' might not preserve the channel invariant (#217)"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (M[Net#d][i] > M[Net#d][i - 1])
  );
  assert {:msg "  62.3: Action at 2.3 ('n') for actor instance 'f1' might not preserve the channel invariant (#218)"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (M[Net#e][i] > M[Net#e][i - 1])
  );
  assume (forall i: int :: 
    (0 <= i) && (i <= AT#Min(R[Net#a], R[Net#b])) ==> (exists  j: int :: 
      ((0 <= j) && (j < (R[Net#d] + C[Net#d])) && (M[Net#d][j] == i)) || ((0 <= j) && (j < (R[Net#e] + C[Net#e])) && (M[Net#e][j] == i))
    )
  );
  assert {:msg "  79.3: Action at 2.3 ('n') for actor instance 'f1' might not preserve the channel invariant (#220)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#d]) ==> (M[Net#d][i] < M[Net#m][R[Net#m]])
  );
  assert {:msg "  80.3: Action at 2.3 ('n') for actor instance 'f1' might not preserve the channel invariant (#221)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#e][i] < M[Net#m][R[Net#m]])
  );
  assume ((C[Net#d] > 0) || (C[Net#e] > 0)) ==> ((M[Net#d][R[Net#d]] == M[Net#m][R[Net#m]]) || (M[Net#e][R[Net#e]] == M[Net#m][R[Net#m]]));
  assert {:msg "  84.3: Action at 2.3 ('n') for actor instance 'f1' might not preserve the channel invariant (#223)"} (R[Net#f] + C[Net#f]) == M[Net#m][R[Net#m]];
  assert {:msg "  85.3: Action at 2.3 ('n') for actor instance 'f1' might not preserve the channel invariant (#224)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#f] + C[Net#f])) ==> (M[Net#f][i] == i)
  );
}
procedure Net#anon$2#F#fail1#14()
  modifies C, R, M, St;
{
  var ActionPH#y1: int;
  var ActionPH#y2: int;
  var ActionPH#y3: int;
  var St#next: State;
  var in#i: int;
  var f#t: bool;
  assume C#init[Net#a] == 3;
  assume C#init[Net#b] == 0;
  assume C#init[Net#c] == 0;
  assume C#init[Net#d] == 0;
  assume C#init[Net#e] == 0;
  assume C#init[Net#f] == 0;
  assume C#init[Net#g] == 0;
  assume C#init[Net#h] == 0;
  assume C#init[Net#m] == 0;
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
  assume (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == i)
  );
  assume C[Net#m] == 1;
  assume (0 <= M[Net#m][R[Net#m]]) && (M[Net#m][R[Net#m]] <= 3);
  assume ((R[Net#g] + C[Net#g]) + (R[Net#h] + C[Net#h])) <= R[Net#a];
  assume (R[Net#b] + C[Net#b]) == R[Net#a];
  assume (R[Net#c] + C[Net#c]) == R[Net#a];
  assume C[Net#b] >= C[Net#g];
  assume C[Net#c] >= C[Net#h];
  assume (R[Net#d] + C[Net#d]) <= R[Net#b];
  assume (R[Net#e] + C[Net#e]) <= R[Net#c];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == M[Net#a][i]) && (M[Net#c][i] == M[Net#a][i])
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == (M[Net#a][i - 1] + 1))
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == (M[Net#b][i - 1] + 1))
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (M[Net#c][i] == (M[Net#c][i - 1] + 1))
  );
  assume ((R[Net#d] + C[Net#d]) > 0) ==> (M[Net#d][(R[Net#d] + C[Net#d]) - 1] <= M[Net#b][R[Net#b] - 1]);
  assume ((R[Net#e] + C[Net#e]) > 0) ==> (M[Net#e][(R[Net#e] + C[Net#e]) - 1] <= M[Net#c][R[Net#c] - 1]);
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (M[Net#d][i] > M[Net#d][i - 1])
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (M[Net#e][i] > M[Net#e][i - 1])
  );
  assume (forall i: int :: 
    (0 <= i) && (i <= AT#Min(R[Net#a], R[Net#b])) ==> (exists  j: int :: 
      ((0 <= j) && (j < (R[Net#d] + C[Net#d])) && (M[Net#d][j] == i)) || ((0 <= j) && (j < (R[Net#e] + C[Net#e])) && (M[Net#e][j] == i))
    )
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#d]) ==> (M[Net#d][i] < M[Net#m][R[Net#m]])
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#e][i] < M[Net#m][R[Net#m]])
  );
  assume ((C[Net#d] > 0) || (C[Net#e] > 0)) ==> ((M[Net#d][R[Net#d]] == M[Net#m][R[Net#m]]) || (M[Net#e][R[Net#e]] == M[Net#m][R[Net#m]]));
  assume (R[Net#f] + C[Net#f]) == M[Net#m][R[Net#m]];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#f] + C[Net#f])) ==> (M[Net#f][i] == i)
  );
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
  assert {:msg "  Action at 3.3 ('fail1') for actor instance 'f2' might not preserve the channel invariant (#245)"} (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
  assert {:msg "  33.3: Action at 3.3 ('fail1') for actor instance 'f2' might not preserve the channel invariant (#246)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == i)
  );
  assert {:msg "  35.3: Action at 3.3 ('fail1') for actor instance 'f2' might not preserve the channel invariant (#247)"} C[Net#m] == 1;
  assert {:msg "  36.3: Action at 3.3 ('fail1') for actor instance 'f2' might not preserve the channel invariant (#248)"} (0 <= M[Net#m][R[Net#m]]) && (M[Net#m][R[Net#m]] <= 3);
  assert {:msg "  38.3: Action at 3.3 ('fail1') for actor instance 'f2' might not preserve the channel invariant (#249)"} ((R[Net#g] + C[Net#g]) + (R[Net#h] + C[Net#h])) <= R[Net#a];
  assert {:msg "  40.3: Action at 3.3 ('fail1') for actor instance 'f2' might not preserve the channel invariant (#250)"} (R[Net#b] + C[Net#b]) == R[Net#a];
  assert {:msg "  41.3: Action at 3.3 ('fail1') for actor instance 'f2' might not preserve the channel invariant (#251)"} (R[Net#c] + C[Net#c]) == R[Net#a];
  assert {:msg "  42.3: Action at 3.3 ('fail1') for actor instance 'f2' might not preserve the channel invariant (#252)"} C[Net#b] >= C[Net#g];
  assert {:msg "  43.3: Action at 3.3 ('fail1') for actor instance 'f2' might not preserve the channel invariant (#253)"} C[Net#c] >= C[Net#h];
  assert {:msg "  45.3: Action at 3.3 ('fail1') for actor instance 'f2' might not preserve the channel invariant (#254)"} (R[Net#d] + C[Net#d]) <= R[Net#b];
  assert {:msg "  46.3: Action at 3.3 ('fail1') for actor instance 'f2' might not preserve the channel invariant (#255)"} (R[Net#e] + C[Net#e]) <= R[Net#c];
  assert {:msg "  49.3: Action at 3.3 ('fail1') for actor instance 'f2' might not preserve the channel invariant (#256)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == M[Net#a][i]) && (M[Net#c][i] == M[Net#a][i])
  );
  assert {:msg "  52.3: Action at 3.3 ('fail1') for actor instance 'f2' might not preserve the channel invariant (#257)"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == (M[Net#a][i - 1] + 1))
  );
  assert {:msg "  53.3: Action at 3.3 ('fail1') for actor instance 'f2' might not preserve the channel invariant (#258)"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == (M[Net#b][i - 1] + 1))
  );
  assert {:msg "  54.3: Action at 3.3 ('fail1') for actor instance 'f2' might not preserve the channel invariant (#259)"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (M[Net#c][i] == (M[Net#c][i - 1] + 1))
  );
  assert {:msg "  57.3: Action at 3.3 ('fail1') for actor instance 'f2' might not preserve the channel invariant (#260)"} ((R[Net#d] + C[Net#d]) > 0) ==> (M[Net#d][(R[Net#d] + C[Net#d]) - 1] <= M[Net#b][R[Net#b] - 1]);
  assert {:msg "  58.3: Action at 3.3 ('fail1') for actor instance 'f2' might not preserve the channel invariant (#261)"} ((R[Net#e] + C[Net#e]) > 0) ==> (M[Net#e][(R[Net#e] + C[Net#e]) - 1] <= M[Net#c][R[Net#c] - 1]);
  assert {:msg "  61.3: Action at 3.3 ('fail1') for actor instance 'f2' might not preserve the channel invariant (#262)"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (M[Net#d][i] > M[Net#d][i - 1])
  );
  assert {:msg "  62.3: Action at 3.3 ('fail1') for actor instance 'f2' might not preserve the channel invariant (#263)"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (M[Net#e][i] > M[Net#e][i - 1])
  );
  assume (forall i: int :: 
    (0 <= i) && (i <= AT#Min(R[Net#a], R[Net#b])) ==> (exists  j: int :: 
      ((0 <= j) && (j < (R[Net#d] + C[Net#d])) && (M[Net#d][j] == i)) || ((0 <= j) && (j < (R[Net#e] + C[Net#e])) && (M[Net#e][j] == i))
    )
  );
  assert {:msg "  79.3: Action at 3.3 ('fail1') for actor instance 'f2' might not preserve the channel invariant (#265)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#d]) ==> (M[Net#d][i] < M[Net#m][R[Net#m]])
  );
  assert {:msg "  80.3: Action at 3.3 ('fail1') for actor instance 'f2' might not preserve the channel invariant (#266)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#e][i] < M[Net#m][R[Net#m]])
  );
  assume ((C[Net#d] > 0) || (C[Net#e] > 0)) ==> ((M[Net#d][R[Net#d]] == M[Net#m][R[Net#m]]) || (M[Net#e][R[Net#e]] == M[Net#m][R[Net#m]]));
  assert {:msg "  84.3: Action at 3.3 ('fail1') for actor instance 'f2' might not preserve the channel invariant (#268)"} (R[Net#f] + C[Net#f]) == M[Net#m][R[Net#m]];
  assert {:msg "  85.3: Action at 3.3 ('fail1') for actor instance 'f2' might not preserve the channel invariant (#269)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#f] + C[Net#f])) ==> (M[Net#f][i] == i)
  );
}
procedure Net#anon$2#F#n#15()
  modifies C, R, M, St;
{
  var ActionPH#y1: int;
  var ActionPH#y2: int;
  var ActionPH#y3: int;
  var St#next: State;
  var in#i: int;
  assume C#init[Net#a] == 3;
  assume C#init[Net#b] == 0;
  assume C#init[Net#c] == 0;
  assume C#init[Net#d] == 0;
  assume C#init[Net#e] == 0;
  assume C#init[Net#f] == 0;
  assume C#init[Net#g] == 0;
  assume C#init[Net#h] == 0;
  assume C#init[Net#m] == 0;
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
  assume (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == i)
  );
  assume C[Net#m] == 1;
  assume (0 <= M[Net#m][R[Net#m]]) && (M[Net#m][R[Net#m]] <= 3);
  assume ((R[Net#g] + C[Net#g]) + (R[Net#h] + C[Net#h])) <= R[Net#a];
  assume (R[Net#b] + C[Net#b]) == R[Net#a];
  assume (R[Net#c] + C[Net#c]) == R[Net#a];
  assume C[Net#b] >= C[Net#g];
  assume C[Net#c] >= C[Net#h];
  assume (R[Net#d] + C[Net#d]) <= R[Net#b];
  assume (R[Net#e] + C[Net#e]) <= R[Net#c];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == M[Net#a][i]) && (M[Net#c][i] == M[Net#a][i])
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == (M[Net#a][i - 1] + 1))
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == (M[Net#b][i - 1] + 1))
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (M[Net#c][i] == (M[Net#c][i - 1] + 1))
  );
  assume ((R[Net#d] + C[Net#d]) > 0) ==> (M[Net#d][(R[Net#d] + C[Net#d]) - 1] <= M[Net#b][R[Net#b] - 1]);
  assume ((R[Net#e] + C[Net#e]) > 0) ==> (M[Net#e][(R[Net#e] + C[Net#e]) - 1] <= M[Net#c][R[Net#c] - 1]);
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (M[Net#d][i] > M[Net#d][i - 1])
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (M[Net#e][i] > M[Net#e][i - 1])
  );
  assume (forall i: int :: 
    (0 <= i) && (i <= AT#Min(R[Net#a], R[Net#b])) ==> (exists  j: int :: 
      ((0 <= j) && (j < (R[Net#d] + C[Net#d])) && (M[Net#d][j] == i)) || ((0 <= j) && (j < (R[Net#e] + C[Net#e])) && (M[Net#e][j] == i))
    )
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#d]) ==> (M[Net#d][i] < M[Net#m][R[Net#m]])
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#e][i] < M[Net#m][R[Net#m]])
  );
  assume ((C[Net#d] > 0) || (C[Net#e] > 0)) ==> ((M[Net#d][R[Net#d]] == M[Net#m][R[Net#m]]) || (M[Net#e][R[Net#e]] == M[Net#m][R[Net#m]]));
  assume (R[Net#f] + C[Net#f]) == M[Net#m][R[Net#m]];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#f] + C[Net#f])) ==> (M[Net#f][i] == i)
  );
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
  assert {:msg "  Action at 2.3 ('n') for actor instance 'f2' might not preserve the channel invariant (#290)"} (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
  assert {:msg "  33.3: Action at 2.3 ('n') for actor instance 'f2' might not preserve the channel invariant (#291)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == i)
  );
  assert {:msg "  35.3: Action at 2.3 ('n') for actor instance 'f2' might not preserve the channel invariant (#292)"} C[Net#m] == 1;
  assert {:msg "  36.3: Action at 2.3 ('n') for actor instance 'f2' might not preserve the channel invariant (#293)"} (0 <= M[Net#m][R[Net#m]]) && (M[Net#m][R[Net#m]] <= 3);
  assert {:msg "  38.3: Action at 2.3 ('n') for actor instance 'f2' might not preserve the channel invariant (#294)"} ((R[Net#g] + C[Net#g]) + (R[Net#h] + C[Net#h])) <= R[Net#a];
  assert {:msg "  40.3: Action at 2.3 ('n') for actor instance 'f2' might not preserve the channel invariant (#295)"} (R[Net#b] + C[Net#b]) == R[Net#a];
  assert {:msg "  41.3: Action at 2.3 ('n') for actor instance 'f2' might not preserve the channel invariant (#296)"} (R[Net#c] + C[Net#c]) == R[Net#a];
  assert {:msg "  42.3: Action at 2.3 ('n') for actor instance 'f2' might not preserve the channel invariant (#297)"} C[Net#b] >= C[Net#g];
  assert {:msg "  43.3: Action at 2.3 ('n') for actor instance 'f2' might not preserve the channel invariant (#298)"} C[Net#c] >= C[Net#h];
  assert {:msg "  45.3: Action at 2.3 ('n') for actor instance 'f2' might not preserve the channel invariant (#299)"} (R[Net#d] + C[Net#d]) <= R[Net#b];
  assert {:msg "  46.3: Action at 2.3 ('n') for actor instance 'f2' might not preserve the channel invariant (#300)"} (R[Net#e] + C[Net#e]) <= R[Net#c];
  assert {:msg "  49.3: Action at 2.3 ('n') for actor instance 'f2' might not preserve the channel invariant (#301)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == M[Net#a][i]) && (M[Net#c][i] == M[Net#a][i])
  );
  assert {:msg "  52.3: Action at 2.3 ('n') for actor instance 'f2' might not preserve the channel invariant (#302)"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == (M[Net#a][i - 1] + 1))
  );
  assert {:msg "  53.3: Action at 2.3 ('n') for actor instance 'f2' might not preserve the channel invariant (#303)"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == (M[Net#b][i - 1] + 1))
  );
  assert {:msg "  54.3: Action at 2.3 ('n') for actor instance 'f2' might not preserve the channel invariant (#304)"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (M[Net#c][i] == (M[Net#c][i - 1] + 1))
  );
  assert {:msg "  57.3: Action at 2.3 ('n') for actor instance 'f2' might not preserve the channel invariant (#305)"} ((R[Net#d] + C[Net#d]) > 0) ==> (M[Net#d][(R[Net#d] + C[Net#d]) - 1] <= M[Net#b][R[Net#b] - 1]);
  assert {:msg "  58.3: Action at 2.3 ('n') for actor instance 'f2' might not preserve the channel invariant (#306)"} ((R[Net#e] + C[Net#e]) > 0) ==> (M[Net#e][(R[Net#e] + C[Net#e]) - 1] <= M[Net#c][R[Net#c] - 1]);
  assert {:msg "  61.3: Action at 2.3 ('n') for actor instance 'f2' might not preserve the channel invariant (#307)"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (M[Net#d][i] > M[Net#d][i - 1])
  );
  assert {:msg "  62.3: Action at 2.3 ('n') for actor instance 'f2' might not preserve the channel invariant (#308)"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (M[Net#e][i] > M[Net#e][i - 1])
  );
  assume (forall i: int :: 
    (0 <= i) && (i <= AT#Min(R[Net#a], R[Net#b])) ==> (exists  j: int :: 
      ((0 <= j) && (j < (R[Net#d] + C[Net#d])) && (M[Net#d][j] == i)) || ((0 <= j) && (j < (R[Net#e] + C[Net#e])) && (M[Net#e][j] == i))
    )
  );
  assert {:msg "  79.3: Action at 2.3 ('n') for actor instance 'f2' might not preserve the channel invariant (#310)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#d]) ==> (M[Net#d][i] < M[Net#m][R[Net#m]])
  );
  assert {:msg "  80.3: Action at 2.3 ('n') for actor instance 'f2' might not preserve the channel invariant (#311)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#e][i] < M[Net#m][R[Net#m]])
  );
  assume ((C[Net#d] > 0) || (C[Net#e] > 0)) ==> ((M[Net#d][R[Net#d]] == M[Net#m][R[Net#m]]) || (M[Net#e][R[Net#e]] == M[Net#m][R[Net#m]]));
  assert {:msg "  84.3: Action at 2.3 ('n') for actor instance 'f2' might not preserve the channel invariant (#313)"} (R[Net#f] + C[Net#f]) == M[Net#m][R[Net#m]];
  assert {:msg "  85.3: Action at 2.3 ('n') for actor instance 'f2' might not preserve the channel invariant (#314)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#f] + C[Net#f])) ==> (M[Net#f][i] == i)
  );
}
procedure Net#anon$2#Merge#read1#16()
  modifies C, R, M, St;
{
  var ActionPH#y1: int;
  var ActionPH#y2: int;
  var ActionPH#y3: int;
  var St#next: State;
  var in1#i: int;
  var s_in#s: int;
  assume C#init[Net#a] == 3;
  assume C#init[Net#b] == 0;
  assume C#init[Net#c] == 0;
  assume C#init[Net#d] == 0;
  assume C#init[Net#e] == 0;
  assume C#init[Net#f] == 0;
  assume C#init[Net#g] == 0;
  assume C#init[Net#h] == 0;
  assume C#init[Net#m] == 0;
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
  assume (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == i)
  );
  assume C[Net#m] == 1;
  assume (0 <= M[Net#m][R[Net#m]]) && (M[Net#m][R[Net#m]] <= 3);
  assume ((R[Net#g] + C[Net#g]) + (R[Net#h] + C[Net#h])) <= R[Net#a];
  assume (R[Net#b] + C[Net#b]) == R[Net#a];
  assume (R[Net#c] + C[Net#c]) == R[Net#a];
  assume C[Net#b] >= C[Net#g];
  assume C[Net#c] >= C[Net#h];
  assume (R[Net#d] + C[Net#d]) <= R[Net#b];
  assume (R[Net#e] + C[Net#e]) <= R[Net#c];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == M[Net#a][i]) && (M[Net#c][i] == M[Net#a][i])
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == (M[Net#a][i - 1] + 1))
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == (M[Net#b][i - 1] + 1))
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (M[Net#c][i] == (M[Net#c][i - 1] + 1))
  );
  assume ((R[Net#d] + C[Net#d]) > 0) ==> (M[Net#d][(R[Net#d] + C[Net#d]) - 1] <= M[Net#b][R[Net#b] - 1]);
  assume ((R[Net#e] + C[Net#e]) > 0) ==> (M[Net#e][(R[Net#e] + C[Net#e]) - 1] <= M[Net#c][R[Net#c] - 1]);
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (M[Net#d][i] > M[Net#d][i - 1])
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (M[Net#e][i] > M[Net#e][i - 1])
  );
  assume (forall i: int :: 
    (0 <= i) && (i <= AT#Min(R[Net#a], R[Net#b])) ==> (exists  j: int :: 
      ((0 <= j) && (j < (R[Net#d] + C[Net#d])) && (M[Net#d][j] == i)) || ((0 <= j) && (j < (R[Net#e] + C[Net#e])) && (M[Net#e][j] == i))
    )
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#d]) ==> (M[Net#d][i] < M[Net#m][R[Net#m]])
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#e][i] < M[Net#m][R[Net#m]])
  );
  assume ((C[Net#d] > 0) || (C[Net#e] > 0)) ==> ((M[Net#d][R[Net#d]] == M[Net#m][R[Net#m]]) || (M[Net#e][R[Net#e]] == M[Net#m][R[Net#m]]));
  assume (R[Net#f] + C[Net#f]) == M[Net#m][R[Net#m]];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#f] + C[Net#f])) ==> (M[Net#f][i] == i)
  );
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
  assert {:msg "  Action at 14.3 ('read1') for actor instance 'mrg' might not preserve the channel invariant (#335)"} (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
  assert {:msg "  33.3: Action at 14.3 ('read1') for actor instance 'mrg' might not preserve the channel invariant (#336)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == i)
  );
  assert {:msg "  35.3: Action at 14.3 ('read1') for actor instance 'mrg' might not preserve the channel invariant (#337)"} C[Net#m] == 1;
  assert {:msg "  36.3: Action at 14.3 ('read1') for actor instance 'mrg' might not preserve the channel invariant (#338)"} (0 <= M[Net#m][R[Net#m]]) && (M[Net#m][R[Net#m]] <= 3);
  assert {:msg "  38.3: Action at 14.3 ('read1') for actor instance 'mrg' might not preserve the channel invariant (#339)"} ((R[Net#g] + C[Net#g]) + (R[Net#h] + C[Net#h])) <= R[Net#a];
  assert {:msg "  40.3: Action at 14.3 ('read1') for actor instance 'mrg' might not preserve the channel invariant (#340)"} (R[Net#b] + C[Net#b]) == R[Net#a];
  assert {:msg "  41.3: Action at 14.3 ('read1') for actor instance 'mrg' might not preserve the channel invariant (#341)"} (R[Net#c] + C[Net#c]) == R[Net#a];
  assert {:msg "  42.3: Action at 14.3 ('read1') for actor instance 'mrg' might not preserve the channel invariant (#342)"} C[Net#b] >= C[Net#g];
  assert {:msg "  43.3: Action at 14.3 ('read1') for actor instance 'mrg' might not preserve the channel invariant (#343)"} C[Net#c] >= C[Net#h];
  assert {:msg "  45.3: Action at 14.3 ('read1') for actor instance 'mrg' might not preserve the channel invariant (#344)"} (R[Net#d] + C[Net#d]) <= R[Net#b];
  assert {:msg "  46.3: Action at 14.3 ('read1') for actor instance 'mrg' might not preserve the channel invariant (#345)"} (R[Net#e] + C[Net#e]) <= R[Net#c];
  assert {:msg "  49.3: Action at 14.3 ('read1') for actor instance 'mrg' might not preserve the channel invariant (#346)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == M[Net#a][i]) && (M[Net#c][i] == M[Net#a][i])
  );
  assert {:msg "  52.3: Action at 14.3 ('read1') for actor instance 'mrg' might not preserve the channel invariant (#347)"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == (M[Net#a][i - 1] + 1))
  );
  assert {:msg "  53.3: Action at 14.3 ('read1') for actor instance 'mrg' might not preserve the channel invariant (#348)"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == (M[Net#b][i - 1] + 1))
  );
  assert {:msg "  54.3: Action at 14.3 ('read1') for actor instance 'mrg' might not preserve the channel invariant (#349)"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (M[Net#c][i] == (M[Net#c][i - 1] + 1))
  );
  assert {:msg "  57.3: Action at 14.3 ('read1') for actor instance 'mrg' might not preserve the channel invariant (#350)"} ((R[Net#d] + C[Net#d]) > 0) ==> (M[Net#d][(R[Net#d] + C[Net#d]) - 1] <= M[Net#b][R[Net#b] - 1]);
  assert {:msg "  58.3: Action at 14.3 ('read1') for actor instance 'mrg' might not preserve the channel invariant (#351)"} ((R[Net#e] + C[Net#e]) > 0) ==> (M[Net#e][(R[Net#e] + C[Net#e]) - 1] <= M[Net#c][R[Net#c] - 1]);
  assert {:msg "  61.3: Action at 14.3 ('read1') for actor instance 'mrg' might not preserve the channel invariant (#352)"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (M[Net#d][i] > M[Net#d][i - 1])
  );
  assert {:msg "  62.3: Action at 14.3 ('read1') for actor instance 'mrg' might not preserve the channel invariant (#353)"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (M[Net#e][i] > M[Net#e][i - 1])
  );
  assume (forall i: int :: 
    (0 <= i) && (i <= AT#Min(R[Net#a], R[Net#b])) ==> (exists  j: int :: 
      ((0 <= j) && (j < (R[Net#d] + C[Net#d])) && (M[Net#d][j] == i)) || ((0 <= j) && (j < (R[Net#e] + C[Net#e])) && (M[Net#e][j] == i))
    )
  );
  assert {:msg "  79.3: Action at 14.3 ('read1') for actor instance 'mrg' might not preserve the channel invariant (#355)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#d]) ==> (M[Net#d][i] < M[Net#m][R[Net#m]])
  );
  assert {:msg "  80.3: Action at 14.3 ('read1') for actor instance 'mrg' might not preserve the channel invariant (#356)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#e][i] < M[Net#m][R[Net#m]])
  );
  assume ((C[Net#d] > 0) || (C[Net#e] > 0)) ==> ((M[Net#d][R[Net#d]] == M[Net#m][R[Net#m]]) || (M[Net#e][R[Net#e]] == M[Net#m][R[Net#m]]));
  assert {:msg "  84.3: Action at 14.3 ('read1') for actor instance 'mrg' might not preserve the channel invariant (#358)"} (R[Net#f] + C[Net#f]) == M[Net#m][R[Net#m]];
  assert {:msg "  85.3: Action at 14.3 ('read1') for actor instance 'mrg' might not preserve the channel invariant (#359)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#f] + C[Net#f])) ==> (M[Net#f][i] == i)
  );
}
procedure Net#anon$2#Merge#read2#17()
  modifies C, R, M, St;
{
  var ActionPH#y1: int;
  var ActionPH#y2: int;
  var ActionPH#y3: int;
  var St#next: State;
  var in2#i: int;
  var s_in#s: int;
  assume C#init[Net#a] == 3;
  assume C#init[Net#b] == 0;
  assume C#init[Net#c] == 0;
  assume C#init[Net#d] == 0;
  assume C#init[Net#e] == 0;
  assume C#init[Net#f] == 0;
  assume C#init[Net#g] == 0;
  assume C#init[Net#h] == 0;
  assume C#init[Net#m] == 0;
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
  assume (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == i)
  );
  assume C[Net#m] == 1;
  assume (0 <= M[Net#m][R[Net#m]]) && (M[Net#m][R[Net#m]] <= 3);
  assume ((R[Net#g] + C[Net#g]) + (R[Net#h] + C[Net#h])) <= R[Net#a];
  assume (R[Net#b] + C[Net#b]) == R[Net#a];
  assume (R[Net#c] + C[Net#c]) == R[Net#a];
  assume C[Net#b] >= C[Net#g];
  assume C[Net#c] >= C[Net#h];
  assume (R[Net#d] + C[Net#d]) <= R[Net#b];
  assume (R[Net#e] + C[Net#e]) <= R[Net#c];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == M[Net#a][i]) && (M[Net#c][i] == M[Net#a][i])
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == (M[Net#a][i - 1] + 1))
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == (M[Net#b][i - 1] + 1))
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (M[Net#c][i] == (M[Net#c][i - 1] + 1))
  );
  assume ((R[Net#d] + C[Net#d]) > 0) ==> (M[Net#d][(R[Net#d] + C[Net#d]) - 1] <= M[Net#b][R[Net#b] - 1]);
  assume ((R[Net#e] + C[Net#e]) > 0) ==> (M[Net#e][(R[Net#e] + C[Net#e]) - 1] <= M[Net#c][R[Net#c] - 1]);
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (M[Net#d][i] > M[Net#d][i - 1])
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (M[Net#e][i] > M[Net#e][i - 1])
  );
  assume (forall i: int :: 
    (0 <= i) && (i <= AT#Min(R[Net#a], R[Net#b])) ==> (exists  j: int :: 
      ((0 <= j) && (j < (R[Net#d] + C[Net#d])) && (M[Net#d][j] == i)) || ((0 <= j) && (j < (R[Net#e] + C[Net#e])) && (M[Net#e][j] == i))
    )
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#d]) ==> (M[Net#d][i] < M[Net#m][R[Net#m]])
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#e][i] < M[Net#m][R[Net#m]])
  );
  assume ((C[Net#d] > 0) || (C[Net#e] > 0)) ==> ((M[Net#d][R[Net#d]] == M[Net#m][R[Net#m]]) || (M[Net#e][R[Net#e]] == M[Net#m][R[Net#m]]));
  assume (R[Net#f] + C[Net#f]) == M[Net#m][R[Net#m]];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#f] + C[Net#f])) ==> (M[Net#f][i] == i)
  );
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
  assert {:msg "  Action at 17.3 ('read2') for actor instance 'mrg' might not preserve the channel invariant (#380)"} (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
  assert {:msg "  33.3: Action at 17.3 ('read2') for actor instance 'mrg' might not preserve the channel invariant (#381)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == i)
  );
  assert {:msg "  35.3: Action at 17.3 ('read2') for actor instance 'mrg' might not preserve the channel invariant (#382)"} C[Net#m] == 1;
  assert {:msg "  36.3: Action at 17.3 ('read2') for actor instance 'mrg' might not preserve the channel invariant (#383)"} (0 <= M[Net#m][R[Net#m]]) && (M[Net#m][R[Net#m]] <= 3);
  assert {:msg "  38.3: Action at 17.3 ('read2') for actor instance 'mrg' might not preserve the channel invariant (#384)"} ((R[Net#g] + C[Net#g]) + (R[Net#h] + C[Net#h])) <= R[Net#a];
  assert {:msg "  40.3: Action at 17.3 ('read2') for actor instance 'mrg' might not preserve the channel invariant (#385)"} (R[Net#b] + C[Net#b]) == R[Net#a];
  assert {:msg "  41.3: Action at 17.3 ('read2') for actor instance 'mrg' might not preserve the channel invariant (#386)"} (R[Net#c] + C[Net#c]) == R[Net#a];
  assert {:msg "  42.3: Action at 17.3 ('read2') for actor instance 'mrg' might not preserve the channel invariant (#387)"} C[Net#b] >= C[Net#g];
  assert {:msg "  43.3: Action at 17.3 ('read2') for actor instance 'mrg' might not preserve the channel invariant (#388)"} C[Net#c] >= C[Net#h];
  assert {:msg "  45.3: Action at 17.3 ('read2') for actor instance 'mrg' might not preserve the channel invariant (#389)"} (R[Net#d] + C[Net#d]) <= R[Net#b];
  assert {:msg "  46.3: Action at 17.3 ('read2') for actor instance 'mrg' might not preserve the channel invariant (#390)"} (R[Net#e] + C[Net#e]) <= R[Net#c];
  assert {:msg "  49.3: Action at 17.3 ('read2') for actor instance 'mrg' might not preserve the channel invariant (#391)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == M[Net#a][i]) && (M[Net#c][i] == M[Net#a][i])
  );
  assert {:msg "  52.3: Action at 17.3 ('read2') for actor instance 'mrg' might not preserve the channel invariant (#392)"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == (M[Net#a][i - 1] + 1))
  );
  assert {:msg "  53.3: Action at 17.3 ('read2') for actor instance 'mrg' might not preserve the channel invariant (#393)"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == (M[Net#b][i - 1] + 1))
  );
  assert {:msg "  54.3: Action at 17.3 ('read2') for actor instance 'mrg' might not preserve the channel invariant (#394)"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (M[Net#c][i] == (M[Net#c][i - 1] + 1))
  );
  assert {:msg "  57.3: Action at 17.3 ('read2') for actor instance 'mrg' might not preserve the channel invariant (#395)"} ((R[Net#d] + C[Net#d]) > 0) ==> (M[Net#d][(R[Net#d] + C[Net#d]) - 1] <= M[Net#b][R[Net#b] - 1]);
  assert {:msg "  58.3: Action at 17.3 ('read2') for actor instance 'mrg' might not preserve the channel invariant (#396)"} ((R[Net#e] + C[Net#e]) > 0) ==> (M[Net#e][(R[Net#e] + C[Net#e]) - 1] <= M[Net#c][R[Net#c] - 1]);
  assert {:msg "  61.3: Action at 17.3 ('read2') for actor instance 'mrg' might not preserve the channel invariant (#397)"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (M[Net#d][i] > M[Net#d][i - 1])
  );
  assert {:msg "  62.3: Action at 17.3 ('read2') for actor instance 'mrg' might not preserve the channel invariant (#398)"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (M[Net#e][i] > M[Net#e][i - 1])
  );
  assume (forall i: int :: 
    (0 <= i) && (i <= AT#Min(R[Net#a], R[Net#b])) ==> (exists  j: int :: 
      ((0 <= j) && (j < (R[Net#d] + C[Net#d])) && (M[Net#d][j] == i)) || ((0 <= j) && (j < (R[Net#e] + C[Net#e])) && (M[Net#e][j] == i))
    )
  );
  assert {:msg "  79.3: Action at 17.3 ('read2') for actor instance 'mrg' might not preserve the channel invariant (#400)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#d]) ==> (M[Net#d][i] < M[Net#m][R[Net#m]])
  );
  assert {:msg "  80.3: Action at 17.3 ('read2') for actor instance 'mrg' might not preserve the channel invariant (#401)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#e][i] < M[Net#m][R[Net#m]])
  );
  assume ((C[Net#d] > 0) || (C[Net#e] > 0)) ==> ((M[Net#d][R[Net#d]] == M[Net#m][R[Net#m]]) || (M[Net#e][R[Net#e]] == M[Net#m][R[Net#m]]));
  assert {:msg "  84.3: Action at 17.3 ('read2') for actor instance 'mrg' might not preserve the channel invariant (#403)"} (R[Net#f] + C[Net#f]) == M[Net#m][R[Net#m]];
  assert {:msg "  85.3: Action at 17.3 ('read2') for actor instance 'mrg' might not preserve the channel invariant (#404)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#f] + C[Net#f])) ==> (M[Net#f][i] == i)
  );
}
procedure Net#anon$2#Merge#discard1#18()
  modifies C, R, M, St;
{
  var ActionPH#y1: int;
  var ActionPH#y2: int;
  var ActionPH#y3: int;
  var St#next: State;
  var in1#i: int;
  var s_in#s: int;
  assume C#init[Net#a] == 3;
  assume C#init[Net#b] == 0;
  assume C#init[Net#c] == 0;
  assume C#init[Net#d] == 0;
  assume C#init[Net#e] == 0;
  assume C#init[Net#f] == 0;
  assume C#init[Net#g] == 0;
  assume C#init[Net#h] == 0;
  assume C#init[Net#m] == 0;
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
  assume (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == i)
  );
  assume C[Net#m] == 1;
  assume (0 <= M[Net#m][R[Net#m]]) && (M[Net#m][R[Net#m]] <= 3);
  assume ((R[Net#g] + C[Net#g]) + (R[Net#h] + C[Net#h])) <= R[Net#a];
  assume (R[Net#b] + C[Net#b]) == R[Net#a];
  assume (R[Net#c] + C[Net#c]) == R[Net#a];
  assume C[Net#b] >= C[Net#g];
  assume C[Net#c] >= C[Net#h];
  assume (R[Net#d] + C[Net#d]) <= R[Net#b];
  assume (R[Net#e] + C[Net#e]) <= R[Net#c];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == M[Net#a][i]) && (M[Net#c][i] == M[Net#a][i])
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == (M[Net#a][i - 1] + 1))
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == (M[Net#b][i - 1] + 1))
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (M[Net#c][i] == (M[Net#c][i - 1] + 1))
  );
  assume ((R[Net#d] + C[Net#d]) > 0) ==> (M[Net#d][(R[Net#d] + C[Net#d]) - 1] <= M[Net#b][R[Net#b] - 1]);
  assume ((R[Net#e] + C[Net#e]) > 0) ==> (M[Net#e][(R[Net#e] + C[Net#e]) - 1] <= M[Net#c][R[Net#c] - 1]);
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (M[Net#d][i] > M[Net#d][i - 1])
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (M[Net#e][i] > M[Net#e][i - 1])
  );
  assume (forall i: int :: 
    (0 <= i) && (i <= AT#Min(R[Net#a], R[Net#b])) ==> (exists  j: int :: 
      ((0 <= j) && (j < (R[Net#d] + C[Net#d])) && (M[Net#d][j] == i)) || ((0 <= j) && (j < (R[Net#e] + C[Net#e])) && (M[Net#e][j] == i))
    )
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#d]) ==> (M[Net#d][i] < M[Net#m][R[Net#m]])
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#e][i] < M[Net#m][R[Net#m]])
  );
  assume ((C[Net#d] > 0) || (C[Net#e] > 0)) ==> ((M[Net#d][R[Net#d]] == M[Net#m][R[Net#m]]) || (M[Net#e][R[Net#e]] == M[Net#m][R[Net#m]]));
  assume (R[Net#f] + C[Net#f]) == M[Net#m][R[Net#m]];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#f] + C[Net#f])) ==> (M[Net#f][i] == i)
  );
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
  assert {:msg "  Action at 20.3 ('discard1') for actor instance 'mrg' might not preserve the channel invariant (#425)"} (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
  assert {:msg "  33.3: Action at 20.3 ('discard1') for actor instance 'mrg' might not preserve the channel invariant (#426)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == i)
  );
  assert {:msg "  35.3: Action at 20.3 ('discard1') for actor instance 'mrg' might not preserve the channel invariant (#427)"} C[Net#m] == 1;
  assert {:msg "  36.3: Action at 20.3 ('discard1') for actor instance 'mrg' might not preserve the channel invariant (#428)"} (0 <= M[Net#m][R[Net#m]]) && (M[Net#m][R[Net#m]] <= 3);
  assert {:msg "  38.3: Action at 20.3 ('discard1') for actor instance 'mrg' might not preserve the channel invariant (#429)"} ((R[Net#g] + C[Net#g]) + (R[Net#h] + C[Net#h])) <= R[Net#a];
  assert {:msg "  40.3: Action at 20.3 ('discard1') for actor instance 'mrg' might not preserve the channel invariant (#430)"} (R[Net#b] + C[Net#b]) == R[Net#a];
  assert {:msg "  41.3: Action at 20.3 ('discard1') for actor instance 'mrg' might not preserve the channel invariant (#431)"} (R[Net#c] + C[Net#c]) == R[Net#a];
  assert {:msg "  42.3: Action at 20.3 ('discard1') for actor instance 'mrg' might not preserve the channel invariant (#432)"} C[Net#b] >= C[Net#g];
  assert {:msg "  43.3: Action at 20.3 ('discard1') for actor instance 'mrg' might not preserve the channel invariant (#433)"} C[Net#c] >= C[Net#h];
  assert {:msg "  45.3: Action at 20.3 ('discard1') for actor instance 'mrg' might not preserve the channel invariant (#434)"} (R[Net#d] + C[Net#d]) <= R[Net#b];
  assert {:msg "  46.3: Action at 20.3 ('discard1') for actor instance 'mrg' might not preserve the channel invariant (#435)"} (R[Net#e] + C[Net#e]) <= R[Net#c];
  assert {:msg "  49.3: Action at 20.3 ('discard1') for actor instance 'mrg' might not preserve the channel invariant (#436)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == M[Net#a][i]) && (M[Net#c][i] == M[Net#a][i])
  );
  assert {:msg "  52.3: Action at 20.3 ('discard1') for actor instance 'mrg' might not preserve the channel invariant (#437)"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == (M[Net#a][i - 1] + 1))
  );
  assert {:msg "  53.3: Action at 20.3 ('discard1') for actor instance 'mrg' might not preserve the channel invariant (#438)"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == (M[Net#b][i - 1] + 1))
  );
  assert {:msg "  54.3: Action at 20.3 ('discard1') for actor instance 'mrg' might not preserve the channel invariant (#439)"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (M[Net#c][i] == (M[Net#c][i - 1] + 1))
  );
  assert {:msg "  57.3: Action at 20.3 ('discard1') for actor instance 'mrg' might not preserve the channel invariant (#440)"} ((R[Net#d] + C[Net#d]) > 0) ==> (M[Net#d][(R[Net#d] + C[Net#d]) - 1] <= M[Net#b][R[Net#b] - 1]);
  assert {:msg "  58.3: Action at 20.3 ('discard1') for actor instance 'mrg' might not preserve the channel invariant (#441)"} ((R[Net#e] + C[Net#e]) > 0) ==> (M[Net#e][(R[Net#e] + C[Net#e]) - 1] <= M[Net#c][R[Net#c] - 1]);
  assert {:msg "  61.3: Action at 20.3 ('discard1') for actor instance 'mrg' might not preserve the channel invariant (#442)"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (M[Net#d][i] > M[Net#d][i - 1])
  );
  assert {:msg "  62.3: Action at 20.3 ('discard1') for actor instance 'mrg' might not preserve the channel invariant (#443)"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (M[Net#e][i] > M[Net#e][i - 1])
  );
  assume (forall i: int :: 
    (0 <= i) && (i <= AT#Min(R[Net#a], R[Net#b])) ==> (exists  j: int :: 
      ((0 <= j) && (j < (R[Net#d] + C[Net#d])) && (M[Net#d][j] == i)) || ((0 <= j) && (j < (R[Net#e] + C[Net#e])) && (M[Net#e][j] == i))
    )
  );
  assert {:msg "  79.3: Action at 20.3 ('discard1') for actor instance 'mrg' might not preserve the channel invariant (#445)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#d]) ==> (M[Net#d][i] < M[Net#m][R[Net#m]])
  );
  assert {:msg "  80.3: Action at 20.3 ('discard1') for actor instance 'mrg' might not preserve the channel invariant (#446)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#e][i] < M[Net#m][R[Net#m]])
  );
  assume ((C[Net#d] > 0) || (C[Net#e] > 0)) ==> ((M[Net#d][R[Net#d]] == M[Net#m][R[Net#m]]) || (M[Net#e][R[Net#e]] == M[Net#m][R[Net#m]]));
  assert {:msg "  84.3: Action at 20.3 ('discard1') for actor instance 'mrg' might not preserve the channel invariant (#448)"} (R[Net#f] + C[Net#f]) == M[Net#m][R[Net#m]];
  assert {:msg "  85.3: Action at 20.3 ('discard1') for actor instance 'mrg' might not preserve the channel invariant (#449)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#f] + C[Net#f])) ==> (M[Net#f][i] == i)
  );
}
procedure Net#anon$2#Merge#discard2#19()
  modifies C, R, M, St;
{
  var ActionPH#y1: int;
  var ActionPH#y2: int;
  var ActionPH#y3: int;
  var St#next: State;
  var in2#i: int;
  var s_in#s: int;
  assume C#init[Net#a] == 3;
  assume C#init[Net#b] == 0;
  assume C#init[Net#c] == 0;
  assume C#init[Net#d] == 0;
  assume C#init[Net#e] == 0;
  assume C#init[Net#f] == 0;
  assume C#init[Net#g] == 0;
  assume C#init[Net#h] == 0;
  assume C#init[Net#m] == 0;
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
  assume (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == i)
  );
  assume C[Net#m] == 1;
  assume (0 <= M[Net#m][R[Net#m]]) && (M[Net#m][R[Net#m]] <= 3);
  assume ((R[Net#g] + C[Net#g]) + (R[Net#h] + C[Net#h])) <= R[Net#a];
  assume (R[Net#b] + C[Net#b]) == R[Net#a];
  assume (R[Net#c] + C[Net#c]) == R[Net#a];
  assume C[Net#b] >= C[Net#g];
  assume C[Net#c] >= C[Net#h];
  assume (R[Net#d] + C[Net#d]) <= R[Net#b];
  assume (R[Net#e] + C[Net#e]) <= R[Net#c];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == M[Net#a][i]) && (M[Net#c][i] == M[Net#a][i])
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == (M[Net#a][i - 1] + 1))
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == (M[Net#b][i - 1] + 1))
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (M[Net#c][i] == (M[Net#c][i - 1] + 1))
  );
  assume ((R[Net#d] + C[Net#d]) > 0) ==> (M[Net#d][(R[Net#d] + C[Net#d]) - 1] <= M[Net#b][R[Net#b] - 1]);
  assume ((R[Net#e] + C[Net#e]) > 0) ==> (M[Net#e][(R[Net#e] + C[Net#e]) - 1] <= M[Net#c][R[Net#c] - 1]);
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (M[Net#d][i] > M[Net#d][i - 1])
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (M[Net#e][i] > M[Net#e][i - 1])
  );
  assume (forall i: int :: 
    (0 <= i) && (i <= AT#Min(R[Net#a], R[Net#b])) ==> (exists  j: int :: 
      ((0 <= j) && (j < (R[Net#d] + C[Net#d])) && (M[Net#d][j] == i)) || ((0 <= j) && (j < (R[Net#e] + C[Net#e])) && (M[Net#e][j] == i))
    )
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#d]) ==> (M[Net#d][i] < M[Net#m][R[Net#m]])
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#e][i] < M[Net#m][R[Net#m]])
  );
  assume ((C[Net#d] > 0) || (C[Net#e] > 0)) ==> ((M[Net#d][R[Net#d]] == M[Net#m][R[Net#m]]) || (M[Net#e][R[Net#e]] == M[Net#m][R[Net#m]]));
  assume (R[Net#f] + C[Net#f]) == M[Net#m][R[Net#m]];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#f] + C[Net#f])) ==> (M[Net#f][i] == i)
  );
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
  assert {:msg "  Action at 23.3 ('discard2') for actor instance 'mrg' might not preserve the channel invariant (#470)"} (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
  assert {:msg "  33.3: Action at 23.3 ('discard2') for actor instance 'mrg' might not preserve the channel invariant (#471)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == i)
  );
  assert {:msg "  35.3: Action at 23.3 ('discard2') for actor instance 'mrg' might not preserve the channel invariant (#472)"} C[Net#m] == 1;
  assert {:msg "  36.3: Action at 23.3 ('discard2') for actor instance 'mrg' might not preserve the channel invariant (#473)"} (0 <= M[Net#m][R[Net#m]]) && (M[Net#m][R[Net#m]] <= 3);
  assert {:msg "  38.3: Action at 23.3 ('discard2') for actor instance 'mrg' might not preserve the channel invariant (#474)"} ((R[Net#g] + C[Net#g]) + (R[Net#h] + C[Net#h])) <= R[Net#a];
  assert {:msg "  40.3: Action at 23.3 ('discard2') for actor instance 'mrg' might not preserve the channel invariant (#475)"} (R[Net#b] + C[Net#b]) == R[Net#a];
  assert {:msg "  41.3: Action at 23.3 ('discard2') for actor instance 'mrg' might not preserve the channel invariant (#476)"} (R[Net#c] + C[Net#c]) == R[Net#a];
  assert {:msg "  42.3: Action at 23.3 ('discard2') for actor instance 'mrg' might not preserve the channel invariant (#477)"} C[Net#b] >= C[Net#g];
  assert {:msg "  43.3: Action at 23.3 ('discard2') for actor instance 'mrg' might not preserve the channel invariant (#478)"} C[Net#c] >= C[Net#h];
  assert {:msg "  45.3: Action at 23.3 ('discard2') for actor instance 'mrg' might not preserve the channel invariant (#479)"} (R[Net#d] + C[Net#d]) <= R[Net#b];
  assert {:msg "  46.3: Action at 23.3 ('discard2') for actor instance 'mrg' might not preserve the channel invariant (#480)"} (R[Net#e] + C[Net#e]) <= R[Net#c];
  assert {:msg "  49.3: Action at 23.3 ('discard2') for actor instance 'mrg' might not preserve the channel invariant (#481)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == M[Net#a][i]) && (M[Net#c][i] == M[Net#a][i])
  );
  assert {:msg "  52.3: Action at 23.3 ('discard2') for actor instance 'mrg' might not preserve the channel invariant (#482)"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == (M[Net#a][i - 1] + 1))
  );
  assert {:msg "  53.3: Action at 23.3 ('discard2') for actor instance 'mrg' might not preserve the channel invariant (#483)"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == (M[Net#b][i - 1] + 1))
  );
  assert {:msg "  54.3: Action at 23.3 ('discard2') for actor instance 'mrg' might not preserve the channel invariant (#484)"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (M[Net#c][i] == (M[Net#c][i - 1] + 1))
  );
  assert {:msg "  57.3: Action at 23.3 ('discard2') for actor instance 'mrg' might not preserve the channel invariant (#485)"} ((R[Net#d] + C[Net#d]) > 0) ==> (M[Net#d][(R[Net#d] + C[Net#d]) - 1] <= M[Net#b][R[Net#b] - 1]);
  assert {:msg "  58.3: Action at 23.3 ('discard2') for actor instance 'mrg' might not preserve the channel invariant (#486)"} ((R[Net#e] + C[Net#e]) > 0) ==> (M[Net#e][(R[Net#e] + C[Net#e]) - 1] <= M[Net#c][R[Net#c] - 1]);
  assert {:msg "  61.3: Action at 23.3 ('discard2') for actor instance 'mrg' might not preserve the channel invariant (#487)"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (M[Net#d][i] > M[Net#d][i - 1])
  );
  assert {:msg "  62.3: Action at 23.3 ('discard2') for actor instance 'mrg' might not preserve the channel invariant (#488)"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (M[Net#e][i] > M[Net#e][i - 1])
  );
  assume (forall i: int :: 
    (0 <= i) && (i <= AT#Min(R[Net#a], R[Net#b])) ==> (exists  j: int :: 
      ((0 <= j) && (j < (R[Net#d] + C[Net#d])) && (M[Net#d][j] == i)) || ((0 <= j) && (j < (R[Net#e] + C[Net#e])) && (M[Net#e][j] == i))
    )
  );
  assert {:msg "  79.3: Action at 23.3 ('discard2') for actor instance 'mrg' might not preserve the channel invariant (#490)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#d]) ==> (M[Net#d][i] < M[Net#m][R[Net#m]])
  );
  assert {:msg "  80.3: Action at 23.3 ('discard2') for actor instance 'mrg' might not preserve the channel invariant (#491)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#e][i] < M[Net#m][R[Net#m]])
  );
  assume ((C[Net#d] > 0) || (C[Net#e] > 0)) ==> ((M[Net#d][R[Net#d]] == M[Net#m][R[Net#m]]) || (M[Net#e][R[Net#e]] == M[Net#m][R[Net#m]]));
  assert {:msg "  84.3: Action at 23.3 ('discard2') for actor instance 'mrg' might not preserve the channel invariant (#493)"} (R[Net#f] + C[Net#f]) == M[Net#m][R[Net#m]];
  assert {:msg "  85.3: Action at 23.3 ('discard2') for actor instance 'mrg' might not preserve the channel invariant (#494)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#f] + C[Net#f])) ==> (M[Net#f][i] == i)
  );
}
procedure Net#anon$2#exit#20()
  modifies C, R, M, St;
{
  var ActionPH#y1: int;
  var ActionPH#y2: int;
  var ActionPH#y3: int;
  assume C#init[Net#a] == 3;
  assume C#init[Net#b] == 0;
  assume C#init[Net#c] == 0;
  assume C#init[Net#d] == 0;
  assume C#init[Net#e] == 0;
  assume C#init[Net#f] == 0;
  assume C#init[Net#g] == 0;
  assume C#init[Net#h] == 0;
  assume C#init[Net#m] == 0;
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
  assume (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == i)
  );
  assume C[Net#m] == 1;
  assume (0 <= M[Net#m][R[Net#m]]) && (M[Net#m][R[Net#m]] <= 3);
  assume ((R[Net#g] + C[Net#g]) + (R[Net#h] + C[Net#h])) <= R[Net#a];
  assume (R[Net#b] + C[Net#b]) == R[Net#a];
  assume (R[Net#c] + C[Net#c]) == R[Net#a];
  assume C[Net#b] >= C[Net#g];
  assume C[Net#c] >= C[Net#h];
  assume (R[Net#d] + C[Net#d]) <= R[Net#b];
  assume (R[Net#e] + C[Net#e]) <= R[Net#c];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == M[Net#a][i]) && (M[Net#c][i] == M[Net#a][i])
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == (M[Net#a][i - 1] + 1))
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == (M[Net#b][i - 1] + 1))
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (M[Net#c][i] == (M[Net#c][i - 1] + 1))
  );
  assume ((R[Net#d] + C[Net#d]) > 0) ==> (M[Net#d][(R[Net#d] + C[Net#d]) - 1] <= M[Net#b][R[Net#b] - 1]);
  assume ((R[Net#e] + C[Net#e]) > 0) ==> (M[Net#e][(R[Net#e] + C[Net#e]) - 1] <= M[Net#c][R[Net#c] - 1]);
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (M[Net#d][i] > M[Net#d][i - 1])
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (M[Net#e][i] > M[Net#e][i - 1])
  );
  assume (forall i: int :: 
    (0 <= i) && (i <= AT#Min(R[Net#a], R[Net#b])) ==> (exists  j: int :: 
      ((0 <= j) && (j < (R[Net#d] + C[Net#d])) && (M[Net#d][j] == i)) || ((0 <= j) && (j < (R[Net#e] + C[Net#e])) && (M[Net#e][j] == i))
    )
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#d]) ==> (M[Net#d][i] < M[Net#m][R[Net#m]])
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (M[Net#e][i] < M[Net#m][R[Net#m]])
  );
  assume ((C[Net#d] > 0) || (C[Net#e] > 0)) ==> ((M[Net#d][R[Net#d]] == M[Net#m][R[Net#m]]) || (M[Net#e][R[Net#e]] == M[Net#m][R[Net#m]]));
  assume (R[Net#f] + C[Net#f]) == M[Net#m][R[Net#m]];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#f] + C[Net#f])) ==> (M[Net#f][i] == i)
  );
  assume !(1 <= C[Net#a]);
  assume !(1 <= C[Net#a]);
  assume !((!((1 <= C[Net#b]) && (1 <= C[Net#g]))) && (1 <= C[Net#b]));
  assume !((1 <= C[Net#b]) && (1 <= C[Net#g]));
  assume !((!((1 <= C[Net#c]) && (1 <= C[Net#h]))) && (1 <= C[Net#c]));
  assume !((1 <= C[Net#c]) && (1 <= C[Net#h]));
  assume !((1 <= C[Net#e]) && (1 <= C[Net#m]) && (M[Net#m][R[Net#m] - 0] == M[Net#e][R[Net#e] - 0]));
  assume !((1 <= C[Net#d]) && (1 <= C[Net#m]) && (M[Net#m][R[Net#m] - 0] == M[Net#d][R[Net#d] - 0]));
  assume !((1 <= C[Net#e]) && (1 <= C[Net#m]) && (M[Net#m][R[Net#m] - 0] > M[Net#e][R[Net#e] - 0]));
  assume !((1 <= C[Net#d]) && (1 <= C[Net#m]) && (M[Net#m][R[Net#m] - 0] > M[Net#d][R[Net#d] - 0]));
  ActionPH#y1 := M[Net#f][0];
  ActionPH#y2 := M[Net#f][1];
  ActionPH#y3 := M[Net#f][2];
  assert {:msg "  89.13: Network action postcondition might not hold"} 0 <= (R[Net#f] + C[Net#f]);
  assert {:msg "  90.13: Network action postcondition might not hold"} (R[Net#f] + C[Net#f]) <= 3;
  R[Net#f] := R[Net#f] + C[Net#f];
  C[Net#f] := C[Net#f] - 3;
  C[Net#m] := C[Net#m] - 1;
  assume M[Net#m][R[Net#m]] == 0;
  assert {:msg "  87.3: The network might leave unread tokens on channel a"} C[Net#a] == 0;
  assert {:msg "  87.3: The network might leave unread tokens on channel b"} C[Net#b] == 0;
  assert {:msg "  87.3: The network might leave unread tokens on channel c"} C[Net#c] == 0;
  assert {:msg "  87.3: The network might leave unread tokens on channel d"} C[Net#d] == 0;
  assert {:msg "  87.3: The network might leave unread tokens on channel e"} C[Net#e] == 0;
  assert {:msg "  87.3: The network might not produce the specified number of tokens on output out"} C[Net#f] == 0;
  assert {:msg "  87.3: The network might leave unread tokens on channel g"} C[Net#g] == 0;
  assert {:msg "  87.3: The network might leave unread tokens on channel h"} C[Net#h] == 0;
  assert {:msg "  87.3: The network might leave unread tokens on channel m"} C[Net#m] == 0;
}

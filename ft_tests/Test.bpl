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


// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

procedure Rep#anon$0#0()
  modifies C, R, M, St;
{
  var IV#in#i: int;
  assume true;
}
procedure Jetson#anon$1#1()
  modifies C, R, M, St;
{
  var IV#in#i: int;
  assume true;
}
procedure Jetson#anon$2#2()
  modifies C, R, M, St;
{
  var IV#in#i: int;
  assume true;
}
procedure Split#anon$3#3()
  modifies C, R, M, St;
{
  var IV#in#i: int;
  assume true;
}
procedure Merge#primary#4()
  modifies C, R, M, St;
{
  var IV#in1#i: int;
  var IV#in2#j: int;
  assume IV#in1#i == IV#in2#j;
  assume true;
}
procedure Merge#backup#5()
  modifies C, R, M, St;
{
  var IV#in1#i: int;
  assume true;
}
procedure Merge#discard#6()
  modifies C, R, M, St;
{
  var IV#in2#i: int;
  assume true;
}
procedure Net#init#7()
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
}
const unique Net#spl: Actor;
const unique Net#rep: Actor;
const unique Net#jet: Actor;
const unique Net#mrg: Actor;
const unique Net#a: Chan (int);
const unique Net#b: Chan (int);
const unique Net#c: Chan (int);
const unique Net#d: Chan (int);
const unique Net#e: Chan (int);
const unique Net#f: Chan (int);
procedure Net#anon$4#entry#8()
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
  assume R[Net#a] == 0;
  assume R[Net#b] == 0;
  assume R[Net#c] == 0;
  assume R[Net#d] == 0;
  assume R[Net#e] == 0;
  assume R[Net#f] == 0;
  assume C#init == C;
  assume (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
  assert {:msg "  Channel invariant might not hold on action entry (generated #0)"} 0 <= R[Net#a];
  assert {:msg "  Channel invariant might not hold on action entry (generated #1)"} 0 <= C[Net#a];
  assert {:msg "  Channel invariant might not hold on action entry (generated #2)"} (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assert {:msg "  Channel invariant might not hold on action entry (generated #3)"} 0 <= R[Net#b];
  assert {:msg "  Channel invariant might not hold on action entry (generated #4)"} 0 <= C[Net#b];
  assert {:msg "  Channel invariant might not hold on action entry (generated #5)"} 0 <= R[Net#c];
  assert {:msg "  Channel invariant might not hold on action entry (generated #6)"} 0 <= C[Net#c];
  assert {:msg "  Channel invariant might not hold on action entry (generated #7)"} 0 <= R[Net#d];
  assert {:msg "  Channel invariant might not hold on action entry (generated #8)"} 0 <= C[Net#d];
  assert {:msg "  Channel invariant might not hold on action entry (generated #9)"} 0 <= R[Net#e];
  assert {:msg "  Channel invariant might not hold on action entry (generated #10)"} 0 <= C[Net#e];
  assert {:msg "  Channel invariant might not hold on action entry (generated #11)"} 0 <= R[Net#f];
  assert {:msg "  Channel invariant might not hold on action entry (generated #12)"} 0 <= C[Net#f];
  assert {:msg "  Channel invariant might not hold on action entry (generated #13)"} R[Net#f] == 0;
  assert {:msg "  Channel invariant might not hold on action entry (generated #14)"} (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
  assert {:msg "  Channel invariant might not hold on action entry (generated #15)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Channel invariant might not hold on action entry (generated #16)"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  Channel invariant might not hold on action entry (generated #17)"} R[Net#c] == (R[Net#d] + C[Net#d]);
  assert {:msg "  Channel invariant might not hold on action entry (generated #18)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Channel invariant might not hold on action entry (generated #19)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Channel invariant might not hold on action entry (generated #20)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#c][idx$])
  );
  assert {:msg "  31.3: Channel invariant might not hold on action entry"} (R[Net#b] + C[Net#b]) == R[Net#a];
  assert {:msg "  32.3: Channel invariant might not hold on action entry"} (R[Net#c] + C[Net#c]) == R[Net#a];
  assert {:msg "  33.3: Channel invariant might not hold on action entry"} (R[Net#d] + C[Net#d]) == R[Net#c];
  assert {:msg "  35.3: Channel invariant might not hold on action entry"} (R[Net#e] + C[Net#e]) <= R[Net#b];
  assert {:msg "  37.3: Channel invariant might not hold on action entry"} (R[Net#f] + C[Net#f]) == R[Net#d];
  assert {:msg "  39.3: Channel invariant might not hold on action entry"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == (M[Net#a][i - 1] + 1))
  );
  assert {:msg "  40.3: Channel invariant might not hold on action entry"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == (M[Net#b][i - 1] + 1))
  );
  assert {:msg "  41.3: Channel invariant might not hold on action entry"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (M[Net#c][i] == (M[Net#c][i - 1] + 1))
  );
  assert {:msg "  42.3: Channel invariant might not hold on action entry"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (M[Net#d][i] == (M[Net#d][i - 1] + 1))
  );
  assert {:msg "  44.3: Channel invariant might not hold on action entry"} (R[Net#e] + C[Net#e]) <= R[Net#b];
  assert {:msg "  45.3: Channel invariant might not hold on action entry"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (exists  j: int :: 
      (0 <= j) && (j < R[Net#b]) && (M[Net#e][i] == M[Net#b][j])
    )
  );
  assert {:msg "  47.3: Channel invariant might not hold on action entry"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (M[Net#e][i] > (M[Net#e][i - 1] + 1))
  );
}
procedure Net#anon$4#Split#anon$3#9()
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
  assume (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
  assume R[Net#a] == (R[Net#c] + C[Net#c]);
  assume R[Net#a] == (R[Net#b] + C[Net#b]);
  assume R[Net#c] == (R[Net#d] + C[Net#d]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#c][idx$])
  );
  assume (R[Net#b] + C[Net#b]) == R[Net#a];
  assume (R[Net#c] + C[Net#c]) == R[Net#a];
  assume (R[Net#d] + C[Net#d]) == R[Net#c];
  assume (R[Net#e] + C[Net#e]) <= R[Net#b];
  assume (R[Net#f] + C[Net#f]) == R[Net#d];
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == (M[Net#a][i - 1] + 1))
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == (M[Net#b][i - 1] + 1))
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (M[Net#c][i] == (M[Net#c][i - 1] + 1))
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (M[Net#d][i] == (M[Net#d][i - 1] + 1))
  );
  assume (R[Net#e] + C[Net#e]) <= R[Net#b];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (exists  j: int :: 
      (0 <= j) && (j < R[Net#b]) && (M[Net#e][i] == M[Net#b][j])
    )
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (M[Net#e][i] > (M[Net#e][i - 1] + 1))
  );
  assume true;
  assume 1 <= C[Net#a];
  in#i := M[Net#a][R[Net#a]];
  R[Net#a] := R[Net#a] + 1;
  C[Net#a] := C[Net#a] - 1;
  M[Net#c][R[Net#c] + C[Net#c]] := in#i;
  C[Net#c] := C[Net#c] + 1;
  M[Net#b][R[Net#b] + C[Net#b]] := in#i;
  C[Net#b] := C[Net#b] + 1;
  assert {:msg "  Sub-actor action at 13.3 might not preserve the channel invariant (generated #21)"} 0 <= R[Net#a];
  assert {:msg "  Sub-actor action at 13.3 might not preserve the channel invariant (generated #22)"} 0 <= C[Net#a];
  assert {:msg "  Sub-actor action at 13.3 might not preserve the channel invariant (generated #23)"} (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assert {:msg "  Sub-actor action at 13.3 might not preserve the channel invariant (generated #24)"} 0 <= R[Net#b];
  assert {:msg "  Sub-actor action at 13.3 might not preserve the channel invariant (generated #25)"} 0 <= C[Net#b];
  assert {:msg "  Sub-actor action at 13.3 might not preserve the channel invariant (generated #26)"} 0 <= R[Net#c];
  assert {:msg "  Sub-actor action at 13.3 might not preserve the channel invariant (generated #27)"} 0 <= C[Net#c];
  assert {:msg "  Sub-actor action at 13.3 might not preserve the channel invariant (generated #28)"} 0 <= R[Net#d];
  assert {:msg "  Sub-actor action at 13.3 might not preserve the channel invariant (generated #29)"} 0 <= C[Net#d];
  assert {:msg "  Sub-actor action at 13.3 might not preserve the channel invariant (generated #30)"} 0 <= R[Net#e];
  assert {:msg "  Sub-actor action at 13.3 might not preserve the channel invariant (generated #31)"} 0 <= C[Net#e];
  assert {:msg "  Sub-actor action at 13.3 might not preserve the channel invariant (generated #32)"} 0 <= R[Net#f];
  assert {:msg "  Sub-actor action at 13.3 might not preserve the channel invariant (generated #33)"} 0 <= C[Net#f];
  assert {:msg "  Sub-actor action at 13.3 might not preserve the channel invariant (generated #34)"} R[Net#f] == 0;
  assert {:msg "  Sub-actor action at 13.3 might not preserve the channel invariant (generated #35)"} (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
  assert {:msg "  Sub-actor action at 13.3 might not preserve the channel invariant (generated #36)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Sub-actor action at 13.3 might not preserve the channel invariant (generated #37)"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  Sub-actor action at 13.3 might not preserve the channel invariant (generated #38)"} R[Net#c] == (R[Net#d] + C[Net#d]);
  assert {:msg "  Sub-actor action at 13.3 might not preserve the channel invariant (generated #39)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Sub-actor action at 13.3 might not preserve the channel invariant (generated #40)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Sub-actor action at 13.3 might not preserve the channel invariant (generated #41)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#c][idx$])
  );
  assert {:msg "  31.3: Sub-actor action at 13.3 might not preserve the channel invariant"} (R[Net#b] + C[Net#b]) == R[Net#a];
  assert {:msg "  32.3: Sub-actor action at 13.3 might not preserve the channel invariant"} (R[Net#c] + C[Net#c]) == R[Net#a];
  assert {:msg "  33.3: Sub-actor action at 13.3 might not preserve the channel invariant"} (R[Net#d] + C[Net#d]) == R[Net#c];
  assert {:msg "  35.3: Sub-actor action at 13.3 might not preserve the channel invariant"} (R[Net#e] + C[Net#e]) <= R[Net#b];
  assert {:msg "  37.3: Sub-actor action at 13.3 might not preserve the channel invariant"} (R[Net#f] + C[Net#f]) == R[Net#d];
  assert {:msg "  39.3: Sub-actor action at 13.3 might not preserve the channel invariant"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == (M[Net#a][i - 1] + 1))
  );
  assert {:msg "  40.3: Sub-actor action at 13.3 might not preserve the channel invariant"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == (M[Net#b][i - 1] + 1))
  );
  assert {:msg "  41.3: Sub-actor action at 13.3 might not preserve the channel invariant"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (M[Net#c][i] == (M[Net#c][i - 1] + 1))
  );
  assert {:msg "  42.3: Sub-actor action at 13.3 might not preserve the channel invariant"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (M[Net#d][i] == (M[Net#d][i - 1] + 1))
  );
  assert {:msg "  44.3: Sub-actor action at 13.3 might not preserve the channel invariant"} (R[Net#e] + C[Net#e]) <= R[Net#b];
  assert {:msg "  45.3: Sub-actor action at 13.3 might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (exists  j: int :: 
      (0 <= j) && (j < R[Net#b]) && (M[Net#e][i] == M[Net#b][j])
    )
  );
  assert {:msg "  47.3: Sub-actor action at 13.3 might not preserve the channel invariant"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (M[Net#e][i] > (M[Net#e][i - 1] + 1))
  );
}
procedure Net#anon$4#Rep#anon$0#10()
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
  assume (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
  assume R[Net#a] == (R[Net#c] + C[Net#c]);
  assume R[Net#a] == (R[Net#b] + C[Net#b]);
  assume R[Net#c] == (R[Net#d] + C[Net#d]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#c][idx$])
  );
  assume (R[Net#b] + C[Net#b]) == R[Net#a];
  assume (R[Net#c] + C[Net#c]) == R[Net#a];
  assume (R[Net#d] + C[Net#d]) == R[Net#c];
  assume (R[Net#e] + C[Net#e]) <= R[Net#b];
  assume (R[Net#f] + C[Net#f]) == R[Net#d];
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == (M[Net#a][i - 1] + 1))
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == (M[Net#b][i - 1] + 1))
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (M[Net#c][i] == (M[Net#c][i - 1] + 1))
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (M[Net#d][i] == (M[Net#d][i - 1] + 1))
  );
  assume (R[Net#e] + C[Net#e]) <= R[Net#b];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (exists  j: int :: 
      (0 <= j) && (j < R[Net#b]) && (M[Net#e][i] == M[Net#b][j])
    )
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (M[Net#e][i] > (M[Net#e][i - 1] + 1))
  );
  assume true;
  assume 1 <= C[Net#c];
  in#i := M[Net#c][R[Net#c]];
  R[Net#c] := R[Net#c] + 1;
  C[Net#c] := C[Net#c] - 1;
  M[Net#d][R[Net#d] + C[Net#d]] := in#i;
  C[Net#d] := C[Net#d] + 1;
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #42)"} 0 <= R[Net#a];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #43)"} 0 <= C[Net#a];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #44)"} (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #45)"} 0 <= R[Net#b];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #46)"} 0 <= C[Net#b];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #47)"} 0 <= R[Net#c];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #48)"} 0 <= C[Net#c];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #49)"} 0 <= R[Net#d];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #50)"} 0 <= C[Net#d];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #51)"} 0 <= R[Net#e];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #52)"} 0 <= C[Net#e];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #53)"} 0 <= R[Net#f];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #54)"} 0 <= C[Net#f];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #55)"} R[Net#f] == 0;
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #56)"} (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #57)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #58)"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #59)"} R[Net#c] == (R[Net#d] + C[Net#d]);
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #60)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #61)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #62)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#c][idx$])
  );
  assert {:msg "  31.3: Sub-actor action at 3.3 might not preserve the channel invariant"} (R[Net#b] + C[Net#b]) == R[Net#a];
  assert {:msg "  32.3: Sub-actor action at 3.3 might not preserve the channel invariant"} (R[Net#c] + C[Net#c]) == R[Net#a];
  assert {:msg "  33.3: Sub-actor action at 3.3 might not preserve the channel invariant"} (R[Net#d] + C[Net#d]) == R[Net#c];
  assert {:msg "  35.3: Sub-actor action at 3.3 might not preserve the channel invariant"} (R[Net#e] + C[Net#e]) <= R[Net#b];
  assert {:msg "  37.3: Sub-actor action at 3.3 might not preserve the channel invariant"} (R[Net#f] + C[Net#f]) == R[Net#d];
  assert {:msg "  39.3: Sub-actor action at 3.3 might not preserve the channel invariant"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == (M[Net#a][i - 1] + 1))
  );
  assert {:msg "  40.3: Sub-actor action at 3.3 might not preserve the channel invariant"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == (M[Net#b][i - 1] + 1))
  );
  assert {:msg "  41.3: Sub-actor action at 3.3 might not preserve the channel invariant"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (M[Net#c][i] == (M[Net#c][i - 1] + 1))
  );
  assert {:msg "  42.3: Sub-actor action at 3.3 might not preserve the channel invariant"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (M[Net#d][i] == (M[Net#d][i - 1] + 1))
  );
  assert {:msg "  44.3: Sub-actor action at 3.3 might not preserve the channel invariant"} (R[Net#e] + C[Net#e]) <= R[Net#b];
  assert {:msg "  45.3: Sub-actor action at 3.3 might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (exists  j: int :: 
      (0 <= j) && (j < R[Net#b]) && (M[Net#e][i] == M[Net#b][j])
    )
  );
  assert {:msg "  47.3: Sub-actor action at 3.3 might not preserve the channel invariant"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (M[Net#e][i] > (M[Net#e][i - 1] + 1))
  );
}
procedure Net#anon$4#Jetson#anon$1#11()
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
  assume (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
  assume R[Net#a] == (R[Net#c] + C[Net#c]);
  assume R[Net#a] == (R[Net#b] + C[Net#b]);
  assume R[Net#c] == (R[Net#d] + C[Net#d]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#c][idx$])
  );
  assume (R[Net#b] + C[Net#b]) == R[Net#a];
  assume (R[Net#c] + C[Net#c]) == R[Net#a];
  assume (R[Net#d] + C[Net#d]) == R[Net#c];
  assume (R[Net#e] + C[Net#e]) <= R[Net#b];
  assume (R[Net#f] + C[Net#f]) == R[Net#d];
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == (M[Net#a][i - 1] + 1))
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == (M[Net#b][i - 1] + 1))
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (M[Net#c][i] == (M[Net#c][i - 1] + 1))
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (M[Net#d][i] == (M[Net#d][i - 1] + 1))
  );
  assume (R[Net#e] + C[Net#e]) <= R[Net#b];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (exists  j: int :: 
      (0 <= j) && (j < R[Net#b]) && (M[Net#e][i] == M[Net#b][j])
    )
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (M[Net#e][i] > (M[Net#e][i - 1] + 1))
  );
  assume true;
  assume 1 <= C[Net#b];
  in#i := M[Net#b][R[Net#b]];
  R[Net#b] := R[Net#b] + 1;
  C[Net#b] := C[Net#b] - 1;
  M[Net#e][R[Net#e] + C[Net#e]] := in#i;
  C[Net#e] := C[Net#e] + 1;
  assert {:msg "  Sub-actor action at 7.3 might not preserve the channel invariant (generated #63)"} 0 <= R[Net#a];
  assert {:msg "  Sub-actor action at 7.3 might not preserve the channel invariant (generated #64)"} 0 <= C[Net#a];
  assert {:msg "  Sub-actor action at 7.3 might not preserve the channel invariant (generated #65)"} (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assert {:msg "  Sub-actor action at 7.3 might not preserve the channel invariant (generated #66)"} 0 <= R[Net#b];
  assert {:msg "  Sub-actor action at 7.3 might not preserve the channel invariant (generated #67)"} 0 <= C[Net#b];
  assert {:msg "  Sub-actor action at 7.3 might not preserve the channel invariant (generated #68)"} 0 <= R[Net#c];
  assert {:msg "  Sub-actor action at 7.3 might not preserve the channel invariant (generated #69)"} 0 <= C[Net#c];
  assert {:msg "  Sub-actor action at 7.3 might not preserve the channel invariant (generated #70)"} 0 <= R[Net#d];
  assert {:msg "  Sub-actor action at 7.3 might not preserve the channel invariant (generated #71)"} 0 <= C[Net#d];
  assert {:msg "  Sub-actor action at 7.3 might not preserve the channel invariant (generated #72)"} 0 <= R[Net#e];
  assert {:msg "  Sub-actor action at 7.3 might not preserve the channel invariant (generated #73)"} 0 <= C[Net#e];
  assert {:msg "  Sub-actor action at 7.3 might not preserve the channel invariant (generated #74)"} 0 <= R[Net#f];
  assert {:msg "  Sub-actor action at 7.3 might not preserve the channel invariant (generated #75)"} 0 <= C[Net#f];
  assert {:msg "  Sub-actor action at 7.3 might not preserve the channel invariant (generated #76)"} R[Net#f] == 0;
  assert {:msg "  Sub-actor action at 7.3 might not preserve the channel invariant (generated #77)"} (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
  assert {:msg "  Sub-actor action at 7.3 might not preserve the channel invariant (generated #78)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Sub-actor action at 7.3 might not preserve the channel invariant (generated #79)"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  Sub-actor action at 7.3 might not preserve the channel invariant (generated #80)"} R[Net#c] == (R[Net#d] + C[Net#d]);
  assert {:msg "  Sub-actor action at 7.3 might not preserve the channel invariant (generated #81)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Sub-actor action at 7.3 might not preserve the channel invariant (generated #82)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Sub-actor action at 7.3 might not preserve the channel invariant (generated #83)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#c][idx$])
  );
  assert {:msg "  31.3: Sub-actor action at 7.3 might not preserve the channel invariant"} (R[Net#b] + C[Net#b]) == R[Net#a];
  assert {:msg "  32.3: Sub-actor action at 7.3 might not preserve the channel invariant"} (R[Net#c] + C[Net#c]) == R[Net#a];
  assert {:msg "  33.3: Sub-actor action at 7.3 might not preserve the channel invariant"} (R[Net#d] + C[Net#d]) == R[Net#c];
  assert {:msg "  35.3: Sub-actor action at 7.3 might not preserve the channel invariant"} (R[Net#e] + C[Net#e]) <= R[Net#b];
  assert {:msg "  37.3: Sub-actor action at 7.3 might not preserve the channel invariant"} (R[Net#f] + C[Net#f]) == R[Net#d];
  assert {:msg "  39.3: Sub-actor action at 7.3 might not preserve the channel invariant"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == (M[Net#a][i - 1] + 1))
  );
  assert {:msg "  40.3: Sub-actor action at 7.3 might not preserve the channel invariant"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == (M[Net#b][i - 1] + 1))
  );
  assert {:msg "  41.3: Sub-actor action at 7.3 might not preserve the channel invariant"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (M[Net#c][i] == (M[Net#c][i - 1] + 1))
  );
  assert {:msg "  42.3: Sub-actor action at 7.3 might not preserve the channel invariant"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (M[Net#d][i] == (M[Net#d][i - 1] + 1))
  );
  assert {:msg "  44.3: Sub-actor action at 7.3 might not preserve the channel invariant"} (R[Net#e] + C[Net#e]) <= R[Net#b];
  assert {:msg "  45.3: Sub-actor action at 7.3 might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (exists  j: int :: 
      (0 <= j) && (j < R[Net#b]) && (M[Net#e][i] == M[Net#b][j])
    )
  );
  assert {:msg "  47.3: Sub-actor action at 7.3 might not preserve the channel invariant"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (M[Net#e][i] > (M[Net#e][i - 1] + 1))
  );
}
procedure Net#anon$4#Jetson#anon$2#12()
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
  assume (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
  assume R[Net#a] == (R[Net#c] + C[Net#c]);
  assume R[Net#a] == (R[Net#b] + C[Net#b]);
  assume R[Net#c] == (R[Net#d] + C[Net#d]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#c][idx$])
  );
  assume (R[Net#b] + C[Net#b]) == R[Net#a];
  assume (R[Net#c] + C[Net#c]) == R[Net#a];
  assume (R[Net#d] + C[Net#d]) == R[Net#c];
  assume (R[Net#e] + C[Net#e]) <= R[Net#b];
  assume (R[Net#f] + C[Net#f]) == R[Net#d];
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == (M[Net#a][i - 1] + 1))
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == (M[Net#b][i - 1] + 1))
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (M[Net#c][i] == (M[Net#c][i - 1] + 1))
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (M[Net#d][i] == (M[Net#d][i - 1] + 1))
  );
  assume (R[Net#e] + C[Net#e]) <= R[Net#b];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (exists  j: int :: 
      (0 <= j) && (j < R[Net#b]) && (M[Net#e][i] == M[Net#b][j])
    )
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (M[Net#e][i] > (M[Net#e][i - 1] + 1))
  );
  assume true;
  assume 1 <= C[Net#b];
  in#i := M[Net#b][R[Net#b]];
  R[Net#b] := R[Net#b] + 1;
  C[Net#b] := C[Net#b] - 1;
  assert {:msg "  Sub-actor action at 8.3 might not preserve the channel invariant (generated #84)"} 0 <= R[Net#a];
  assert {:msg "  Sub-actor action at 8.3 might not preserve the channel invariant (generated #85)"} 0 <= C[Net#a];
  assert {:msg "  Sub-actor action at 8.3 might not preserve the channel invariant (generated #86)"} (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assert {:msg "  Sub-actor action at 8.3 might not preserve the channel invariant (generated #87)"} 0 <= R[Net#b];
  assert {:msg "  Sub-actor action at 8.3 might not preserve the channel invariant (generated #88)"} 0 <= C[Net#b];
  assert {:msg "  Sub-actor action at 8.3 might not preserve the channel invariant (generated #89)"} 0 <= R[Net#c];
  assert {:msg "  Sub-actor action at 8.3 might not preserve the channel invariant (generated #90)"} 0 <= C[Net#c];
  assert {:msg "  Sub-actor action at 8.3 might not preserve the channel invariant (generated #91)"} 0 <= R[Net#d];
  assert {:msg "  Sub-actor action at 8.3 might not preserve the channel invariant (generated #92)"} 0 <= C[Net#d];
  assert {:msg "  Sub-actor action at 8.3 might not preserve the channel invariant (generated #93)"} 0 <= R[Net#e];
  assert {:msg "  Sub-actor action at 8.3 might not preserve the channel invariant (generated #94)"} 0 <= C[Net#e];
  assert {:msg "  Sub-actor action at 8.3 might not preserve the channel invariant (generated #95)"} 0 <= R[Net#f];
  assert {:msg "  Sub-actor action at 8.3 might not preserve the channel invariant (generated #96)"} 0 <= C[Net#f];
  assert {:msg "  Sub-actor action at 8.3 might not preserve the channel invariant (generated #97)"} R[Net#f] == 0;
  assert {:msg "  Sub-actor action at 8.3 might not preserve the channel invariant (generated #98)"} (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
  assert {:msg "  Sub-actor action at 8.3 might not preserve the channel invariant (generated #99)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Sub-actor action at 8.3 might not preserve the channel invariant (generated #100)"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  Sub-actor action at 8.3 might not preserve the channel invariant (generated #101)"} R[Net#c] == (R[Net#d] + C[Net#d]);
  assert {:msg "  Sub-actor action at 8.3 might not preserve the channel invariant (generated #102)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Sub-actor action at 8.3 might not preserve the channel invariant (generated #103)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Sub-actor action at 8.3 might not preserve the channel invariant (generated #104)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#c][idx$])
  );
  assert {:msg "  31.3: Sub-actor action at 8.3 might not preserve the channel invariant"} (R[Net#b] + C[Net#b]) == R[Net#a];
  assert {:msg "  32.3: Sub-actor action at 8.3 might not preserve the channel invariant"} (R[Net#c] + C[Net#c]) == R[Net#a];
  assert {:msg "  33.3: Sub-actor action at 8.3 might not preserve the channel invariant"} (R[Net#d] + C[Net#d]) == R[Net#c];
  assert {:msg "  35.3: Sub-actor action at 8.3 might not preserve the channel invariant"} (R[Net#e] + C[Net#e]) <= R[Net#b];
  assert {:msg "  37.3: Sub-actor action at 8.3 might not preserve the channel invariant"} (R[Net#f] + C[Net#f]) == R[Net#d];
  assert {:msg "  39.3: Sub-actor action at 8.3 might not preserve the channel invariant"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == (M[Net#a][i - 1] + 1))
  );
  assert {:msg "  40.3: Sub-actor action at 8.3 might not preserve the channel invariant"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == (M[Net#b][i - 1] + 1))
  );
  assert {:msg "  41.3: Sub-actor action at 8.3 might not preserve the channel invariant"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (M[Net#c][i] == (M[Net#c][i - 1] + 1))
  );
  assert {:msg "  42.3: Sub-actor action at 8.3 might not preserve the channel invariant"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (M[Net#d][i] == (M[Net#d][i - 1] + 1))
  );
  assert {:msg "  44.3: Sub-actor action at 8.3 might not preserve the channel invariant"} (R[Net#e] + C[Net#e]) <= R[Net#b];
  assert {:msg "  45.3: Sub-actor action at 8.3 might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (exists  j: int :: 
      (0 <= j) && (j < R[Net#b]) && (M[Net#e][i] == M[Net#b][j])
    )
  );
  assert {:msg "  47.3: Sub-actor action at 8.3 might not preserve the channel invariant"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (M[Net#e][i] > (M[Net#e][i - 1] + 1))
  );
}
procedure Net#anon$4#Merge#primary#13()
  modifies C, R, M, St;
{
  var ActionPH#y1: int;
  var ActionPH#y2: int;
  var ActionPH#y3: int;
  var St#next: State;
  var in1#i: int;
  var in2#j: int;
  assume C#init[Net#a] == 3;
  assume C#init[Net#b] == 0;
  assume C#init[Net#c] == 0;
  assume C#init[Net#d] == 0;
  assume C#init[Net#e] == 0;
  assume C#init[Net#f] == 0;
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
  assume (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
  assume R[Net#a] == (R[Net#c] + C[Net#c]);
  assume R[Net#a] == (R[Net#b] + C[Net#b]);
  assume R[Net#c] == (R[Net#d] + C[Net#d]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#c][idx$])
  );
  assume (R[Net#b] + C[Net#b]) == R[Net#a];
  assume (R[Net#c] + C[Net#c]) == R[Net#a];
  assume (R[Net#d] + C[Net#d]) == R[Net#c];
  assume (R[Net#e] + C[Net#e]) <= R[Net#b];
  assume (R[Net#f] + C[Net#f]) == R[Net#d];
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == (M[Net#a][i - 1] + 1))
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == (M[Net#b][i - 1] + 1))
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (M[Net#c][i] == (M[Net#c][i - 1] + 1))
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (M[Net#d][i] == (M[Net#d][i - 1] + 1))
  );
  assume (R[Net#e] + C[Net#e]) <= R[Net#b];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (exists  j: int :: 
      (0 <= j) && (j < R[Net#b]) && (M[Net#e][i] == M[Net#b][j])
    )
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (M[Net#e][i] > (M[Net#e][i - 1] + 1))
  );
  assume M[Net#d][R[Net#d] - 0] == M[Net#e][R[Net#e] - 0];
  assume true;
  assume (1 <= C[Net#d]) && (1 <= C[Net#e]) && (M[Net#d][R[Net#d] - 0] == M[Net#e][R[Net#e] - 0]);
  in1#i := M[Net#d][R[Net#d]];
  R[Net#d] := R[Net#d] + 1;
  C[Net#d] := C[Net#d] - 1;
  in2#j := M[Net#e][R[Net#e]];
  R[Net#e] := R[Net#e] + 1;
  C[Net#e] := C[Net#e] - 1;
  M[Net#f][R[Net#f] + C[Net#f]] := in2#j;
  C[Net#f] := C[Net#f] + 1;
  assert {:msg "  Sub-actor action at 17.3 might not preserve the channel invariant (generated #105)"} 0 <= R[Net#a];
  assert {:msg "  Sub-actor action at 17.3 might not preserve the channel invariant (generated #106)"} 0 <= C[Net#a];
  assert {:msg "  Sub-actor action at 17.3 might not preserve the channel invariant (generated #107)"} (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assert {:msg "  Sub-actor action at 17.3 might not preserve the channel invariant (generated #108)"} 0 <= R[Net#b];
  assert {:msg "  Sub-actor action at 17.3 might not preserve the channel invariant (generated #109)"} 0 <= C[Net#b];
  assert {:msg "  Sub-actor action at 17.3 might not preserve the channel invariant (generated #110)"} 0 <= R[Net#c];
  assert {:msg "  Sub-actor action at 17.3 might not preserve the channel invariant (generated #111)"} 0 <= C[Net#c];
  assert {:msg "  Sub-actor action at 17.3 might not preserve the channel invariant (generated #112)"} 0 <= R[Net#d];
  assert {:msg "  Sub-actor action at 17.3 might not preserve the channel invariant (generated #113)"} 0 <= C[Net#d];
  assert {:msg "  Sub-actor action at 17.3 might not preserve the channel invariant (generated #114)"} 0 <= R[Net#e];
  assert {:msg "  Sub-actor action at 17.3 might not preserve the channel invariant (generated #115)"} 0 <= C[Net#e];
  assert {:msg "  Sub-actor action at 17.3 might not preserve the channel invariant (generated #116)"} 0 <= R[Net#f];
  assert {:msg "  Sub-actor action at 17.3 might not preserve the channel invariant (generated #117)"} 0 <= C[Net#f];
  assert {:msg "  Sub-actor action at 17.3 might not preserve the channel invariant (generated #118)"} R[Net#f] == 0;
  assert {:msg "  Sub-actor action at 17.3 might not preserve the channel invariant (generated #119)"} (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
  assert {:msg "  Sub-actor action at 17.3 might not preserve the channel invariant (generated #120)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Sub-actor action at 17.3 might not preserve the channel invariant (generated #121)"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  Sub-actor action at 17.3 might not preserve the channel invariant (generated #122)"} R[Net#c] == (R[Net#d] + C[Net#d]);
  assert {:msg "  Sub-actor action at 17.3 might not preserve the channel invariant (generated #123)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Sub-actor action at 17.3 might not preserve the channel invariant (generated #124)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Sub-actor action at 17.3 might not preserve the channel invariant (generated #125)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#c][idx$])
  );
  assert {:msg "  31.3: Sub-actor action at 17.3 might not preserve the channel invariant"} (R[Net#b] + C[Net#b]) == R[Net#a];
  assert {:msg "  32.3: Sub-actor action at 17.3 might not preserve the channel invariant"} (R[Net#c] + C[Net#c]) == R[Net#a];
  assert {:msg "  33.3: Sub-actor action at 17.3 might not preserve the channel invariant"} (R[Net#d] + C[Net#d]) == R[Net#c];
  assert {:msg "  35.3: Sub-actor action at 17.3 might not preserve the channel invariant"} (R[Net#e] + C[Net#e]) <= R[Net#b];
  assert {:msg "  37.3: Sub-actor action at 17.3 might not preserve the channel invariant"} (R[Net#f] + C[Net#f]) == R[Net#d];
  assert {:msg "  39.3: Sub-actor action at 17.3 might not preserve the channel invariant"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == (M[Net#a][i - 1] + 1))
  );
  assert {:msg "  40.3: Sub-actor action at 17.3 might not preserve the channel invariant"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == (M[Net#b][i - 1] + 1))
  );
  assert {:msg "  41.3: Sub-actor action at 17.3 might not preserve the channel invariant"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (M[Net#c][i] == (M[Net#c][i - 1] + 1))
  );
  assert {:msg "  42.3: Sub-actor action at 17.3 might not preserve the channel invariant"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (M[Net#d][i] == (M[Net#d][i - 1] + 1))
  );
  assert {:msg "  44.3: Sub-actor action at 17.3 might not preserve the channel invariant"} (R[Net#e] + C[Net#e]) <= R[Net#b];
  assert {:msg "  45.3: Sub-actor action at 17.3 might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (exists  j: int :: 
      (0 <= j) && (j < R[Net#b]) && (M[Net#e][i] == M[Net#b][j])
    )
  );
  assert {:msg "  47.3: Sub-actor action at 17.3 might not preserve the channel invariant"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (M[Net#e][i] > (M[Net#e][i - 1] + 1))
  );
}
procedure Net#anon$4#Merge#backup#14()
  modifies C, R, M, St;
{
  var ActionPH#y1: int;
  var ActionPH#y2: int;
  var ActionPH#y3: int;
  var St#next: State;
  var in1#i: int;
  assume C#init[Net#a] == 3;
  assume C#init[Net#b] == 0;
  assume C#init[Net#c] == 0;
  assume C#init[Net#d] == 0;
  assume C#init[Net#e] == 0;
  assume C#init[Net#f] == 0;
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
  assume (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
  assume R[Net#a] == (R[Net#c] + C[Net#c]);
  assume R[Net#a] == (R[Net#b] + C[Net#b]);
  assume R[Net#c] == (R[Net#d] + C[Net#d]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#c][idx$])
  );
  assume (R[Net#b] + C[Net#b]) == R[Net#a];
  assume (R[Net#c] + C[Net#c]) == R[Net#a];
  assume (R[Net#d] + C[Net#d]) == R[Net#c];
  assume (R[Net#e] + C[Net#e]) <= R[Net#b];
  assume (R[Net#f] + C[Net#f]) == R[Net#d];
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == (M[Net#a][i - 1] + 1))
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == (M[Net#b][i - 1] + 1))
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (M[Net#c][i] == (M[Net#c][i - 1] + 1))
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (M[Net#d][i] == (M[Net#d][i - 1] + 1))
  );
  assume (R[Net#e] + C[Net#e]) <= R[Net#b];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (exists  j: int :: 
      (0 <= j) && (j < R[Net#b]) && (M[Net#e][i] == M[Net#b][j])
    )
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (M[Net#e][i] > (M[Net#e][i - 1] + 1))
  );
  assume true;
  assume (!((1 <= C[Net#d]) && (1 <= C[Net#e]) && (M[Net#d][R[Net#d] - 0] == M[Net#e][R[Net#e] - 0]))) && (1 <= C[Net#d]);
  in1#i := M[Net#d][R[Net#d]];
  R[Net#d] := R[Net#d] + 1;
  C[Net#d] := C[Net#d] - 1;
  M[Net#f][R[Net#f] + C[Net#f]] := in1#i;
  C[Net#f] := C[Net#f] + 1;
  assert {:msg "  Sub-actor action at 20.3 might not preserve the channel invariant (generated #126)"} 0 <= R[Net#a];
  assert {:msg "  Sub-actor action at 20.3 might not preserve the channel invariant (generated #127)"} 0 <= C[Net#a];
  assert {:msg "  Sub-actor action at 20.3 might not preserve the channel invariant (generated #128)"} (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assert {:msg "  Sub-actor action at 20.3 might not preserve the channel invariant (generated #129)"} 0 <= R[Net#b];
  assert {:msg "  Sub-actor action at 20.3 might not preserve the channel invariant (generated #130)"} 0 <= C[Net#b];
  assert {:msg "  Sub-actor action at 20.3 might not preserve the channel invariant (generated #131)"} 0 <= R[Net#c];
  assert {:msg "  Sub-actor action at 20.3 might not preserve the channel invariant (generated #132)"} 0 <= C[Net#c];
  assert {:msg "  Sub-actor action at 20.3 might not preserve the channel invariant (generated #133)"} 0 <= R[Net#d];
  assert {:msg "  Sub-actor action at 20.3 might not preserve the channel invariant (generated #134)"} 0 <= C[Net#d];
  assert {:msg "  Sub-actor action at 20.3 might not preserve the channel invariant (generated #135)"} 0 <= R[Net#e];
  assert {:msg "  Sub-actor action at 20.3 might not preserve the channel invariant (generated #136)"} 0 <= C[Net#e];
  assert {:msg "  Sub-actor action at 20.3 might not preserve the channel invariant (generated #137)"} 0 <= R[Net#f];
  assert {:msg "  Sub-actor action at 20.3 might not preserve the channel invariant (generated #138)"} 0 <= C[Net#f];
  assert {:msg "  Sub-actor action at 20.3 might not preserve the channel invariant (generated #139)"} R[Net#f] == 0;
  assert {:msg "  Sub-actor action at 20.3 might not preserve the channel invariant (generated #140)"} (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
  assert {:msg "  Sub-actor action at 20.3 might not preserve the channel invariant (generated #141)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Sub-actor action at 20.3 might not preserve the channel invariant (generated #142)"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  Sub-actor action at 20.3 might not preserve the channel invariant (generated #143)"} R[Net#c] == (R[Net#d] + C[Net#d]);
  assert {:msg "  Sub-actor action at 20.3 might not preserve the channel invariant (generated #144)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Sub-actor action at 20.3 might not preserve the channel invariant (generated #145)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Sub-actor action at 20.3 might not preserve the channel invariant (generated #146)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#c][idx$])
  );
  assert {:msg "  31.3: Sub-actor action at 20.3 might not preserve the channel invariant"} (R[Net#b] + C[Net#b]) == R[Net#a];
  assert {:msg "  32.3: Sub-actor action at 20.3 might not preserve the channel invariant"} (R[Net#c] + C[Net#c]) == R[Net#a];
  assert {:msg "  33.3: Sub-actor action at 20.3 might not preserve the channel invariant"} (R[Net#d] + C[Net#d]) == R[Net#c];
  assert {:msg "  35.3: Sub-actor action at 20.3 might not preserve the channel invariant"} (R[Net#e] + C[Net#e]) <= R[Net#b];
  assert {:msg "  37.3: Sub-actor action at 20.3 might not preserve the channel invariant"} (R[Net#f] + C[Net#f]) == R[Net#d];
  assert {:msg "  39.3: Sub-actor action at 20.3 might not preserve the channel invariant"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == (M[Net#a][i - 1] + 1))
  );
  assert {:msg "  40.3: Sub-actor action at 20.3 might not preserve the channel invariant"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == (M[Net#b][i - 1] + 1))
  );
  assert {:msg "  41.3: Sub-actor action at 20.3 might not preserve the channel invariant"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (M[Net#c][i] == (M[Net#c][i - 1] + 1))
  );
  assert {:msg "  42.3: Sub-actor action at 20.3 might not preserve the channel invariant"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (M[Net#d][i] == (M[Net#d][i - 1] + 1))
  );
  assert {:msg "  44.3: Sub-actor action at 20.3 might not preserve the channel invariant"} (R[Net#e] + C[Net#e]) <= R[Net#b];
  assert {:msg "  45.3: Sub-actor action at 20.3 might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (exists  j: int :: 
      (0 <= j) && (j < R[Net#b]) && (M[Net#e][i] == M[Net#b][j])
    )
  );
  assert {:msg "  47.3: Sub-actor action at 20.3 might not preserve the channel invariant"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (M[Net#e][i] > (M[Net#e][i - 1] + 1))
  );
}
procedure Net#anon$4#Merge#discard#15()
  modifies C, R, M, St;
{
  var ActionPH#y1: int;
  var ActionPH#y2: int;
  var ActionPH#y3: int;
  var St#next: State;
  var in2#i: int;
  assume C#init[Net#a] == 3;
  assume C#init[Net#b] == 0;
  assume C#init[Net#c] == 0;
  assume C#init[Net#d] == 0;
  assume C#init[Net#e] == 0;
  assume C#init[Net#f] == 0;
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
  assume (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
  assume R[Net#a] == (R[Net#c] + C[Net#c]);
  assume R[Net#a] == (R[Net#b] + C[Net#b]);
  assume R[Net#c] == (R[Net#d] + C[Net#d]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#c][idx$])
  );
  assume (R[Net#b] + C[Net#b]) == R[Net#a];
  assume (R[Net#c] + C[Net#c]) == R[Net#a];
  assume (R[Net#d] + C[Net#d]) == R[Net#c];
  assume (R[Net#e] + C[Net#e]) <= R[Net#b];
  assume (R[Net#f] + C[Net#f]) == R[Net#d];
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == (M[Net#a][i - 1] + 1))
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == (M[Net#b][i - 1] + 1))
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (M[Net#c][i] == (M[Net#c][i - 1] + 1))
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (M[Net#d][i] == (M[Net#d][i - 1] + 1))
  );
  assume (R[Net#e] + C[Net#e]) <= R[Net#b];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (exists  j: int :: 
      (0 <= j) && (j < R[Net#b]) && (M[Net#e][i] == M[Net#b][j])
    )
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (M[Net#e][i] > (M[Net#e][i - 1] + 1))
  );
  assume true;
  assume (!((1 <= C[Net#d]) && (1 <= C[Net#e]) && (M[Net#d][R[Net#d] - 0] == M[Net#e][R[Net#e] - 0]))) && (!(1 <= C[Net#d])) && (1 <= C[Net#e]);
  in2#i := M[Net#e][R[Net#e]];
  R[Net#e] := R[Net#e] + 1;
  C[Net#e] := C[Net#e] - 1;
  assert {:msg "  Sub-actor action at 21.3 might not preserve the channel invariant (generated #147)"} 0 <= R[Net#a];
  assert {:msg "  Sub-actor action at 21.3 might not preserve the channel invariant (generated #148)"} 0 <= C[Net#a];
  assert {:msg "  Sub-actor action at 21.3 might not preserve the channel invariant (generated #149)"} (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assert {:msg "  Sub-actor action at 21.3 might not preserve the channel invariant (generated #150)"} 0 <= R[Net#b];
  assert {:msg "  Sub-actor action at 21.3 might not preserve the channel invariant (generated #151)"} 0 <= C[Net#b];
  assert {:msg "  Sub-actor action at 21.3 might not preserve the channel invariant (generated #152)"} 0 <= R[Net#c];
  assert {:msg "  Sub-actor action at 21.3 might not preserve the channel invariant (generated #153)"} 0 <= C[Net#c];
  assert {:msg "  Sub-actor action at 21.3 might not preserve the channel invariant (generated #154)"} 0 <= R[Net#d];
  assert {:msg "  Sub-actor action at 21.3 might not preserve the channel invariant (generated #155)"} 0 <= C[Net#d];
  assert {:msg "  Sub-actor action at 21.3 might not preserve the channel invariant (generated #156)"} 0 <= R[Net#e];
  assert {:msg "  Sub-actor action at 21.3 might not preserve the channel invariant (generated #157)"} 0 <= C[Net#e];
  assert {:msg "  Sub-actor action at 21.3 might not preserve the channel invariant (generated #158)"} 0 <= R[Net#f];
  assert {:msg "  Sub-actor action at 21.3 might not preserve the channel invariant (generated #159)"} 0 <= C[Net#f];
  assert {:msg "  Sub-actor action at 21.3 might not preserve the channel invariant (generated #160)"} R[Net#f] == 0;
  assert {:msg "  Sub-actor action at 21.3 might not preserve the channel invariant (generated #161)"} (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
  assert {:msg "  Sub-actor action at 21.3 might not preserve the channel invariant (generated #162)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Sub-actor action at 21.3 might not preserve the channel invariant (generated #163)"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  Sub-actor action at 21.3 might not preserve the channel invariant (generated #164)"} R[Net#c] == (R[Net#d] + C[Net#d]);
  assert {:msg "  Sub-actor action at 21.3 might not preserve the channel invariant (generated #165)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Sub-actor action at 21.3 might not preserve the channel invariant (generated #166)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  Sub-actor action at 21.3 might not preserve the channel invariant (generated #167)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#c][idx$])
  );
  assert {:msg "  31.3: Sub-actor action at 21.3 might not preserve the channel invariant"} (R[Net#b] + C[Net#b]) == R[Net#a];
  assert {:msg "  32.3: Sub-actor action at 21.3 might not preserve the channel invariant"} (R[Net#c] + C[Net#c]) == R[Net#a];
  assert {:msg "  33.3: Sub-actor action at 21.3 might not preserve the channel invariant"} (R[Net#d] + C[Net#d]) == R[Net#c];
  assert {:msg "  35.3: Sub-actor action at 21.3 might not preserve the channel invariant"} (R[Net#e] + C[Net#e]) <= R[Net#b];
  assert {:msg "  37.3: Sub-actor action at 21.3 might not preserve the channel invariant"} (R[Net#f] + C[Net#f]) == R[Net#d];
  assert {:msg "  39.3: Sub-actor action at 21.3 might not preserve the channel invariant"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == (M[Net#a][i - 1] + 1))
  );
  assert {:msg "  40.3: Sub-actor action at 21.3 might not preserve the channel invariant"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == (M[Net#b][i - 1] + 1))
  );
  assert {:msg "  41.3: Sub-actor action at 21.3 might not preserve the channel invariant"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (M[Net#c][i] == (M[Net#c][i - 1] + 1))
  );
  assert {:msg "  42.3: Sub-actor action at 21.3 might not preserve the channel invariant"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (M[Net#d][i] == (M[Net#d][i - 1] + 1))
  );
  assert {:msg "  44.3: Sub-actor action at 21.3 might not preserve the channel invariant"} (R[Net#e] + C[Net#e]) <= R[Net#b];
  assert {:msg "  45.3: Sub-actor action at 21.3 might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (exists  j: int :: 
      (0 <= j) && (j < R[Net#b]) && (M[Net#e][i] == M[Net#b][j])
    )
  );
  assert {:msg "  47.3: Sub-actor action at 21.3 might not preserve the channel invariant"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (M[Net#e][i] > (M[Net#e][i - 1] + 1))
  );
}
procedure Net#anon$4#exit#16()
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
  assume (M[Net#a][0] == 0) && (M[Net#a][1] == 1) && (M[Net#a][2] == 2);
  assume R[Net#a] == (R[Net#c] + C[Net#c]);
  assume R[Net#a] == (R[Net#b] + C[Net#b]);
  assume R[Net#c] == (R[Net#d] + C[Net#d]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == M[Net#c][idx$])
  );
  assume (R[Net#b] + C[Net#b]) == R[Net#a];
  assume (R[Net#c] + C[Net#c]) == R[Net#a];
  assume (R[Net#d] + C[Net#d]) == R[Net#c];
  assume (R[Net#e] + C[Net#e]) <= R[Net#b];
  assume (R[Net#f] + C[Net#f]) == R[Net#d];
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (M[Net#a][i] == (M[Net#a][i - 1] + 1))
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == (M[Net#b][i - 1] + 1))
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (M[Net#c][i] == (M[Net#c][i - 1] + 1))
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (M[Net#d][i] == (M[Net#d][i - 1] + 1))
  );
  assume (R[Net#e] + C[Net#e]) <= R[Net#b];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (exists  j: int :: 
      (0 <= j) && (j < R[Net#b]) && (M[Net#e][i] == M[Net#b][j])
    )
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#e] + C[Net#e])) ==> (M[Net#e][i] > (M[Net#e][i - 1] + 1))
  );
  assume !(1 <= C[Net#a]);
  assume !(1 <= C[Net#c]);
  assume !(1 <= C[Net#b]);
  assume !(1 <= C[Net#b]);
  assume !((1 <= C[Net#d]) && (1 <= C[Net#e]) && (M[Net#d][R[Net#d] - 0] == M[Net#e][R[Net#e] - 0]));
  assume !((!((1 <= C[Net#d]) && (1 <= C[Net#e]) && (M[Net#d][R[Net#d] - 0] == M[Net#e][R[Net#e] - 0]))) && (!(1 <= C[Net#d])) && (1 <= C[Net#e]));
  assume !((!((1 <= C[Net#d]) && (1 <= C[Net#e]) && (M[Net#d][R[Net#d] - 0] == M[Net#e][R[Net#e] - 0]))) && (1 <= C[Net#d]));
  ActionPH#y1 := M[Net#f][0];
  ActionPH#y2 := M[Net#f][1];
  ActionPH#y3 := M[Net#f][2];
  R[Net#f] := R[Net#f] + C[Net#f];
  C[Net#f] := C[Net#f] - 3;
  assert {:msg "  27.3: The network might leave unread tokens on channel a"} C[Net#a] == 0;
  assert {:msg "  27.3: The network might leave unread tokens on channel b"} C[Net#b] == 0;
  assert {:msg "  27.3: The network might leave unread tokens on channel c"} C[Net#c] == 0;
  assert {:msg "  27.3: The network might leave unread tokens on channel d"} C[Net#d] == 0;
  assert {:msg "  27.3: The network might leave unread tokens on channel e"} C[Net#e] == 0;
  assert {:msg "  27.3: The network might not produce the specified number of tokens on output out"} C[Net#f] == 0;
}

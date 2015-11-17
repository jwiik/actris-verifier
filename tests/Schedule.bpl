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

// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

const unique FairMerge#s1: State;
const unique FairMerge#s2: State;
procedure FairMerge#a1#0()
  modifies C, R, M, St;
{
  var this#: Actor;
  var i: int;
  assume (St[this#] == FairMerge#s1) || (St[this#] == FairMerge#s2);
  assume St[this#] == FairMerge#s1;
  assume true;
  St[this#] := FairMerge#s2;
  assert {:msg "  1.1: Action might not preserve invariant"} (St[this#] == FairMerge#s1) || (St[this#] == FairMerge#s2);
}
procedure FairMerge#a2#1()
  modifies C, R, M, St;
{
  var this#: Actor;
  var i: int;
  assume (St[this#] == FairMerge#s1) || (St[this#] == FairMerge#s2);
  assume St[this#] == FairMerge#s2;
  assume true;
  St[this#] := FairMerge#s1;
  assert {:msg "  1.1: Action might not preserve invariant"} (St[this#] == FairMerge#s1) || (St[this#] == FairMerge#s2);
}
const unique Top#fm: Actor;
const unique Top#a: Chan (int);
const unique Top#b: Chan (int);
const unique Top#c: Chan (int);
procedure Top#anon$0#entry#2()
  modifies C, R, M, St;
{
  assume C#init[Top#a] == 1;
  assume C#init[Top#b] == 1;
  assume C#init[Top#c] == 0;
  assume R[Top#a] == 0;
  assume R[Top#b] == 0;
  assume R[Top#c] == 0;
  assume C#init == C;
  assume St[Top#fm] == FairMerge#s1;
  assert {:msg "  Channel invariant might not hold on action entry (generated #0 )"} 0 <= R[Top#a];
  assert {:msg "  Channel invariant might not hold on action entry (generated #1 )"} 0 <= C[Top#a];
  assert {:msg "  Channel invariant might not hold on action entry (generated #2 )"} (R[Top#a] + C[Top#a]) == C#init[Top#a];
  assert {:msg "  Channel invariant might not hold on action entry (generated #3 )"} 0 <= R[Top#b];
  assert {:msg "  Channel invariant might not hold on action entry (generated #4 )"} 0 <= C[Top#b];
  assert {:msg "  Channel invariant might not hold on action entry (generated #5 )"} (R[Top#b] + C[Top#b]) == C#init[Top#b];
  assert {:msg "  Channel invariant might not hold on action entry (generated #6 )"} 0 <= R[Top#c];
  assert {:msg "  Channel invariant might not hold on action entry (generated #7 )"} 0 <= C[Top#c];
  assert {:msg "  Channel invariant might not hold on action entry (generated #8 )"} R[Top#c] == 0;
  assert {:msg "  16.3: Channel invariant might not hold on action entry"} (R[Top#c] + C[Top#c]) == (R[Top#a] + R[Top#b]);
  assert {:msg "  17.3: Channel invariant might not hold on action entry"} ((R[Top#c] + C[Top#c]) >= 1) ==> (C[Top#a] == 0);
  assert {:msg "  18.3: Channel invariant might not hold on action entry"} ((R[Top#c] + C[Top#c]) >= 2) ==> (C[Top#b] == 0);
  assert {:msg "  19.3: Channel invariant might not hold on action entry"} (R[Top#a] == 0) && (R[Top#b] == 0) ==> (St[Top#fm] == FairMerge#s1);
  assert {:msg "  20.3: Channel invariant might not hold on action entry"} (R[Top#a] == 1) && (R[Top#b] == 0) ==> (St[Top#fm] == FairMerge#s2);
  assert {:msg "  21.3: Channel invariant might not hold on action entry"} (R[Top#a] == 1) && (R[Top#b] == 1) ==> (St[Top#fm] == FairMerge#s1);
  assert {:msg "  23.3: Channel invariant might not hold on action entry"} ((R[Top#c] + C[Top#c]) >= 1) ==> (M[Top#c][0] == M[Top#a][0]);
  assert {:msg "  24.3: Channel invariant might not hold on action entry"} ((R[Top#c] + C[Top#c]) >= 2) ==> (M[Top#c][1] == M[Top#b][0]);
}
procedure Top#anon$0#FairMerge#a1#3()
  modifies C, R, M, St;
{
  var St#next: State;
  var x1#i: int;
  assume C#init[Top#a] == 1;
  assume C#init[Top#b] == 1;
  assume C#init[Top#c] == 0;
  assume 0 <= R[Top#a];
  assume 0 <= C[Top#a];
  assume (R[Top#a] + C[Top#a]) == C#init[Top#a];
  assume 0 <= R[Top#b];
  assume 0 <= C[Top#b];
  assume (R[Top#b] + C[Top#b]) == C#init[Top#b];
  assume 0 <= R[Top#c];
  assume 0 <= C[Top#c];
  assume R[Top#c] == 0;
  assume (R[Top#c] + C[Top#c]) == (R[Top#a] + R[Top#b]);
  assume ((R[Top#c] + C[Top#c]) >= 1) ==> (C[Top#a] == 0);
  assume ((R[Top#c] + C[Top#c]) >= 2) ==> (C[Top#b] == 0);
  assume (R[Top#a] == 0) && (R[Top#b] == 0) ==> (St[Top#fm] == FairMerge#s1);
  assume (R[Top#a] == 1) && (R[Top#b] == 0) ==> (St[Top#fm] == FairMerge#s2);
  assume (R[Top#a] == 1) && (R[Top#b] == 1) ==> (St[Top#fm] == FairMerge#s1);
  assume ((R[Top#c] + C[Top#c]) >= 1) ==> (M[Top#c][0] == M[Top#a][0]);
  assume ((R[Top#c] + C[Top#c]) >= 2) ==> (M[Top#c][1] == M[Top#b][0]);
  assume St[Top#fm] == FairMerge#s1;
  assume (1 <= C[Top#a]) && (St[Top#fm] == FairMerge#s1);
  x1#i := M[Top#a][R[Top#a]];
  R[Top#a] := R[Top#a] + 1;
  C[Top#a] := C[Top#a] - 1;
  M[Top#c][R[Top#c] + C[Top#c]] := x1#i;
  C[Top#c] := C[Top#c] + 1;
  assume St#next == FairMerge#s2;
  St[Top#fm] := St#next;
  assert {:msg "  Sub-actor action at 2.3 might not preserve the channel invariant (generated #9)"} 0 <= R[Top#a];
  assert {:msg "  Sub-actor action at 2.3 might not preserve the channel invariant (generated #10)"} 0 <= C[Top#a];
  assert {:msg "  Sub-actor action at 2.3 might not preserve the channel invariant (generated #11)"} (R[Top#a] + C[Top#a]) == C#init[Top#a];
  assert {:msg "  Sub-actor action at 2.3 might not preserve the channel invariant (generated #12)"} 0 <= R[Top#b];
  assert {:msg "  Sub-actor action at 2.3 might not preserve the channel invariant (generated #13)"} 0 <= C[Top#b];
  assert {:msg "  Sub-actor action at 2.3 might not preserve the channel invariant (generated #14)"} (R[Top#b] + C[Top#b]) == C#init[Top#b];
  assert {:msg "  Sub-actor action at 2.3 might not preserve the channel invariant (generated #15)"} 0 <= R[Top#c];
  assert {:msg "  Sub-actor action at 2.3 might not preserve the channel invariant (generated #16)"} 0 <= C[Top#c];
  assert {:msg "  Sub-actor action at 2.3 might not preserve the channel invariant (generated #17)"} R[Top#c] == 0;
  assert {:msg "  16.3: Sub-actor action at 2.3 might not preserve the channel invariant"} (R[Top#c] + C[Top#c]) == (R[Top#a] + R[Top#b]);
  assert {:msg "  17.3: Sub-actor action at 2.3 might not preserve the channel invariant"} ((R[Top#c] + C[Top#c]) >= 1) ==> (C[Top#a] == 0);
  assert {:msg "  18.3: Sub-actor action at 2.3 might not preserve the channel invariant"} ((R[Top#c] + C[Top#c]) >= 2) ==> (C[Top#b] == 0);
  assert {:msg "  19.3: Sub-actor action at 2.3 might not preserve the channel invariant"} (R[Top#a] == 0) && (R[Top#b] == 0) ==> (St[Top#fm] == FairMerge#s1);
  assert {:msg "  20.3: Sub-actor action at 2.3 might not preserve the channel invariant"} (R[Top#a] == 1) && (R[Top#b] == 0) ==> (St[Top#fm] == FairMerge#s2);
  assert {:msg "  21.3: Sub-actor action at 2.3 might not preserve the channel invariant"} (R[Top#a] == 1) && (R[Top#b] == 1) ==> (St[Top#fm] == FairMerge#s1);
  assert {:msg "  23.3: Sub-actor action at 2.3 might not preserve the channel invariant"} ((R[Top#c] + C[Top#c]) >= 1) ==> (M[Top#c][0] == M[Top#a][0]);
  assert {:msg "  24.3: Sub-actor action at 2.3 might not preserve the channel invariant"} ((R[Top#c] + C[Top#c]) >= 2) ==> (M[Top#c][1] == M[Top#b][0]);
}
procedure Top#anon$0#FairMerge#a2#4()
  modifies C, R, M, St;
{
  var St#next: State;
  var x2#i: int;
  assume C#init[Top#a] == 1;
  assume C#init[Top#b] == 1;
  assume C#init[Top#c] == 0;
  assume 0 <= R[Top#a];
  assume 0 <= C[Top#a];
  assume (R[Top#a] + C[Top#a]) == C#init[Top#a];
  assume 0 <= R[Top#b];
  assume 0 <= C[Top#b];
  assume (R[Top#b] + C[Top#b]) == C#init[Top#b];
  assume 0 <= R[Top#c];
  assume 0 <= C[Top#c];
  assume R[Top#c] == 0;
  assume (R[Top#c] + C[Top#c]) == (R[Top#a] + R[Top#b]);
  assume ((R[Top#c] + C[Top#c]) >= 1) ==> (C[Top#a] == 0);
  assume ((R[Top#c] + C[Top#c]) >= 2) ==> (C[Top#b] == 0);
  assume (R[Top#a] == 0) && (R[Top#b] == 0) ==> (St[Top#fm] == FairMerge#s1);
  assume (R[Top#a] == 1) && (R[Top#b] == 0) ==> (St[Top#fm] == FairMerge#s2);
  assume (R[Top#a] == 1) && (R[Top#b] == 1) ==> (St[Top#fm] == FairMerge#s1);
  assume ((R[Top#c] + C[Top#c]) >= 1) ==> (M[Top#c][0] == M[Top#a][0]);
  assume ((R[Top#c] + C[Top#c]) >= 2) ==> (M[Top#c][1] == M[Top#b][0]);
  assume St[Top#fm] == FairMerge#s2;
  assume (1 <= C[Top#b]) && (St[Top#fm] == FairMerge#s2);
  x2#i := M[Top#b][R[Top#b]];
  R[Top#b] := R[Top#b] + 1;
  C[Top#b] := C[Top#b] - 1;
  M[Top#c][R[Top#c] + C[Top#c]] := x2#i;
  C[Top#c] := C[Top#c] + 1;
  assume St#next == FairMerge#s1;
  St[Top#fm] := St#next;
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #18)"} 0 <= R[Top#a];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #19)"} 0 <= C[Top#a];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #20)"} (R[Top#a] + C[Top#a]) == C#init[Top#a];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #21)"} 0 <= R[Top#b];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #22)"} 0 <= C[Top#b];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #23)"} (R[Top#b] + C[Top#b]) == C#init[Top#b];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #24)"} 0 <= R[Top#c];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #25)"} 0 <= C[Top#c];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #26)"} R[Top#c] == 0;
  assert {:msg "  16.3: Sub-actor action at 3.3 might not preserve the channel invariant"} (R[Top#c] + C[Top#c]) == (R[Top#a] + R[Top#b]);
  assert {:msg "  17.3: Sub-actor action at 3.3 might not preserve the channel invariant"} ((R[Top#c] + C[Top#c]) >= 1) ==> (C[Top#a] == 0);
  assert {:msg "  18.3: Sub-actor action at 3.3 might not preserve the channel invariant"} ((R[Top#c] + C[Top#c]) >= 2) ==> (C[Top#b] == 0);
  assert {:msg "  19.3: Sub-actor action at 3.3 might not preserve the channel invariant"} (R[Top#a] == 0) && (R[Top#b] == 0) ==> (St[Top#fm] == FairMerge#s1);
  assert {:msg "  20.3: Sub-actor action at 3.3 might not preserve the channel invariant"} (R[Top#a] == 1) && (R[Top#b] == 0) ==> (St[Top#fm] == FairMerge#s2);
  assert {:msg "  21.3: Sub-actor action at 3.3 might not preserve the channel invariant"} (R[Top#a] == 1) && (R[Top#b] == 1) ==> (St[Top#fm] == FairMerge#s1);
  assert {:msg "  23.3: Sub-actor action at 3.3 might not preserve the channel invariant"} ((R[Top#c] + C[Top#c]) >= 1) ==> (M[Top#c][0] == M[Top#a][0]);
  assert {:msg "  24.3: Sub-actor action at 3.3 might not preserve the channel invariant"} ((R[Top#c] + C[Top#c]) >= 2) ==> (M[Top#c][1] == M[Top#b][0]);
}
procedure Top#anon$0#exit#5()
  modifies C, R, M, St;
{
  assume C#init[Top#a] == 1;
  assume C#init[Top#b] == 1;
  assume C#init[Top#c] == 0;
  assume 0 <= R[Top#a];
  assume 0 <= C[Top#a];
  assume (R[Top#a] + C[Top#a]) == C#init[Top#a];
  assume 0 <= R[Top#b];
  assume 0 <= C[Top#b];
  assume (R[Top#b] + C[Top#b]) == C#init[Top#b];
  assume 0 <= R[Top#c];
  assume 0 <= C[Top#c];
  assume R[Top#c] == 0;
  assume (R[Top#c] + C[Top#c]) == (R[Top#a] + R[Top#b]);
  assume ((R[Top#c] + C[Top#c]) >= 1) ==> (C[Top#a] == 0);
  assume ((R[Top#c] + C[Top#c]) >= 2) ==> (C[Top#b] == 0);
  assume (R[Top#a] == 0) && (R[Top#b] == 0) ==> (St[Top#fm] == FairMerge#s1);
  assume (R[Top#a] == 1) && (R[Top#b] == 0) ==> (St[Top#fm] == FairMerge#s2);
  assume (R[Top#a] == 1) && (R[Top#b] == 1) ==> (St[Top#fm] == FairMerge#s1);
  assume ((R[Top#c] + C[Top#c]) >= 1) ==> (M[Top#c][0] == M[Top#a][0]);
  assume ((R[Top#c] + C[Top#c]) >= 2) ==> (M[Top#c][1] == M[Top#b][0]);
  assume !(((1 <= C[Top#a]) && (St[Top#fm] == FairMerge#s1)) || ((1 <= C[Top#b]) && (St[Top#fm] == FairMerge#s2)));
  assert {:msg "  12.3: The network might leave unread tokens on channel a"} C[Top#a] == 0;
  assert {:msg "  12.3: The network might leave unread tokens on channel b"} C[Top#b] == 0;
  assert {:msg "  12.3: The network might not produce the specified number of tokens on output out"} C[Top#c] == 2;
  assert {:msg "  12.36: Network output might not conform to specified action output"} M[Top#c][0] == M[Top#a][0];
  assert {:msg "  12.38: Network output might not conform to specified action output"} M[Top#c][1] == M[Top#b][0];
  R[Top#c] := R[Top#c] + C[Top#c];
  C[Top#c] := 0;
  assert {:msg "  14.3: The network might not preserve the network invariant"} St[Top#fm] == FairMerge#s1;
}

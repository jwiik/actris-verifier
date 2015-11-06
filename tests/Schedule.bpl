
// ---------------------------------------------------------------
// -- Types and global variables ---------------------------------
// ---------------------------------------------------------------
type Chan a;
type CType = <a>[Chan a]int;
type MType = <a>[Chan a][int]a;
type State;
var M: MType;
var C: CType;
var R: CType; 
var C#init: CType;

// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

const unique FairMerge#s1: State;
const unique FairMerge#s2: State;
procedure FairMerge#a1()
{
  var A#State: State;
  var i: int;
  assume (A#State == FairMerge#s1) || (A#State == FairMerge#s2);
  assume A#State == FairMerge#s1;
  assume true;
  A#State := FairMerge#s2;
  assert {:msg "  1.1: Action might not preserve invariant"} (A#State == FairMerge#s1) || (A#State == FairMerge#s2);
}
procedure FairMerge#a2()
{
  var A#State: State;
  var i: int;
  assume (A#State == FairMerge#s1) || (A#State == FairMerge#s2);
  assume A#State == FairMerge#s2;
  assume true;
  A#State := FairMerge#s1;
  assert {:msg "  1.1: Action might not preserve invariant"} (A#State == FairMerge#s1) || (A#State == FairMerge#s2);
}
const unique Top#a: Chan (int);
const unique Top#b: Chan (int);
const unique Top#c: Chan (int);
procedure Top#anon$0#entry()
  modifies C, R, M;
{
  assume C#init[Top#a] == 2;
  assume C#init[Top#b] == 0;
  assume C#init[Top#c] == 0;
  assume R[Top#a] == 0;
  assume R[Top#b] == 0;
  assume R[Top#c] == 0;
  assume C#init == C;
  assert {:msg "  Channel invariant might not hold on action entry"} R[Top#c] == 0;
  assert {:msg "  Channel invariant might not hold on action entry"} 0 <= C[Top#c];
  assert {:msg "  Channel invariant might not hold on action entry"} 0 <= R[Top#c];
  assert {:msg "  Channel invariant might not hold on action entry"} (R[Top#b] + C[Top#b]) == C#init[Top#b];
  assert {:msg "  Channel invariant might not hold on action entry"} 0 <= C[Top#b];
  assert {:msg "  Channel invariant might not hold on action entry"} 0 <= R[Top#b];
  assert {:msg "  Channel invariant might not hold on action entry"} (R[Top#a] + C[Top#a]) == C#init[Top#a];
  assert {:msg "  Channel invariant might not hold on action entry"} 0 <= C[Top#a];
  assert {:msg "  Channel invariant might not hold on action entry"} 0 <= R[Top#a];
  assert {:msg "  14.15: Channel invariant might not hold on action entry"} (R[Top#c] + C[Top#c]) == (R[Top#a] + R[Top#b]);
}
procedure Top#anon$0#FairMerge#a1()
  modifies C, R, M;
{
  var x1#i: int;
  assume C#init[Top#a] == 2;
  assume C#init[Top#b] == 0;
  assume C#init[Top#c] == 0;
  assume R[Top#c] == 0;
  assume 0 <= C[Top#c];
  assume 0 <= R[Top#c];
  assume (R[Top#b] + C[Top#b]) == C#init[Top#b];
  assume 0 <= C[Top#b];
  assume 0 <= R[Top#b];
  assume (R[Top#a] + C[Top#a]) == C#init[Top#a];
  assume 0 <= C[Top#a];
  assume 0 <= R[Top#a];
  assume (R[Top#c] + C[Top#c]) == (R[Top#a] + R[Top#b]);
  assume 1 <= C[Top#a];
  x1#i := M[Top#a][R[Top#a]];
  R[Top#a] := R[Top#a] + 1;
  C[Top#a] := C[Top#a] - 1;
  M[Top#c][R[Top#c] + C[Top#c]] := x1#i;
  C[Top#c] := C[Top#c] + 1;
  assert {:msg "  Sub-actor action at 2.3 might not preserve the channel invariant"} R[Top#c] == 0;
  assert {:msg "  Sub-actor action at 2.3 might not preserve the channel invariant"} 0 <= C[Top#c];
  assert {:msg "  Sub-actor action at 2.3 might not preserve the channel invariant"} 0 <= R[Top#c];
  assert {:msg "  Sub-actor action at 2.3 might not preserve the channel invariant"} (R[Top#b] + C[Top#b]) == C#init[Top#b];
  assert {:msg "  Sub-actor action at 2.3 might not preserve the channel invariant"} 0 <= C[Top#b];
  assert {:msg "  Sub-actor action at 2.3 might not preserve the channel invariant"} 0 <= R[Top#b];
  assert {:msg "  Sub-actor action at 2.3 might not preserve the channel invariant"} (R[Top#a] + C[Top#a]) == C#init[Top#a];
  assert {:msg "  Sub-actor action at 2.3 might not preserve the channel invariant"} 0 <= C[Top#a];
  assert {:msg "  Sub-actor action at 2.3 might not preserve the channel invariant"} 0 <= R[Top#a];
  assert {:msg "  14.15: Sub-actor action at 2.3 might not preserve the channel invariant"} (R[Top#c] + C[Top#c]) == (R[Top#a] + R[Top#b]);
}
procedure Top#anon$0#FairMerge#a2()
  modifies C, R, M;
{
  var x2#i: int;
  assume C#init[Top#a] == 2;
  assume C#init[Top#b] == 0;
  assume C#init[Top#c] == 0;
  assume R[Top#c] == 0;
  assume 0 <= C[Top#c];
  assume 0 <= R[Top#c];
  assume (R[Top#b] + C[Top#b]) == C#init[Top#b];
  assume 0 <= C[Top#b];
  assume 0 <= R[Top#b];
  assume (R[Top#a] + C[Top#a]) == C#init[Top#a];
  assume 0 <= C[Top#a];
  assume 0 <= R[Top#a];
  assume (R[Top#c] + C[Top#c]) == (R[Top#a] + R[Top#b]);
  assume 1 <= C[Top#b];
  x2#i := M[Top#b][R[Top#b]];
  R[Top#b] := R[Top#b] + 1;
  C[Top#b] := C[Top#b] - 1;
  M[Top#c][R[Top#c] + C[Top#c]] := x2#i;
  C[Top#c] := C[Top#c] + 1;
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant"} R[Top#c] == 0;
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant"} 0 <= C[Top#c];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant"} 0 <= R[Top#c];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant"} (R[Top#b] + C[Top#b]) == C#init[Top#b];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant"} 0 <= C[Top#b];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant"} 0 <= R[Top#b];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant"} (R[Top#a] + C[Top#a]) == C#init[Top#a];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant"} 0 <= C[Top#a];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant"} 0 <= R[Top#a];
  assert {:msg "  14.15: Sub-actor action at 3.3 might not preserve the channel invariant"} (R[Top#c] + C[Top#c]) == (R[Top#a] + R[Top#b]);
}
procedure Top#anon$0#exit()
  modifies C, R, M;
{
  assume C#init[Top#a] == 2;
  assume C#init[Top#b] == 0;
  assume C#init[Top#c] == 0;
  assume R[Top#c] == 0;
  assume 0 <= C[Top#c];
  assume 0 <= R[Top#c];
  assume (R[Top#b] + C[Top#b]) == C#init[Top#b];
  assume 0 <= C[Top#b];
  assume 0 <= R[Top#b];
  assume (R[Top#a] + C[Top#a]) == C#init[Top#a];
  assume 0 <= C[Top#a];
  assume 0 <= R[Top#a];
  assume (R[Top#c] + C[Top#c]) == (R[Top#a] + R[Top#b]);
  assume !((1 <= C[Top#a]) || (1 <= C[Top#b]));
  assert {:msg "  12.3: The network might leave unread tokens on channel a"} C[Top#a] == 0;
  assert {:msg "  12.3: The network might leave unread tokens on channel b"} C[Top#b] == 0;
  assert {:msg "  12.3: The network might not produce the specified number of tokens on output out"} C[Top#c] == 2;
  assert {:msg "  12.29: Network output might not conform to specified action output"} M[Top#c][0] == M[Top#a][0];
  assert {:msg "  12.31: Network output might not conform to specified action output"} M[Top#c][1] == M[Top#a][1];
  R[Top#c] := R[Top#c] + C[Top#c];
  C[Top#c] := 0;
}


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

const unique Top#x: Chan (int);
const unique Top#y: Chan (int);
procedure Top#anon$0#entry()
  modifies C, R, M;
{
  assume C#init[Top#x] == 1;
  assume C#init[Top#y] == 0;
  assume R[Top#x] == 0;
  assume R[Top#y] == 0;
  assume C#init == C;
  assert {:msg "  Channel invariant might not hold on action entry"} R[Top#y] == 0;
  assert {:msg "  Channel invariant might not hold on action entry"} 0 <= C[Top#y];
  assert {:msg "  Channel invariant might not hold on action entry"} 0 <= R[Top#y];
  assert {:msg "  Channel invariant might not hold on action entry"} (R[Top#x] + C[Top#x]) == C#init[Top#x];
  assert {:msg "  Channel invariant might not hold on action entry"} 0 <= C[Top#x];
  assert {:msg "  Channel invariant might not hold on action entry"} 0 <= R[Top#x];
  assert {:msg "  4.15: Channel invariant might not hold on action entry"} (R[Top#y] + C[Top#y]) == R[Top#x];
  assert {:msg "  5.16: Channel invariant might not hold on action entry"} (forall i: int :: 
    (0 <= i) && (i < (R[Top#y] + C[Top#y])) ==> (M[Top#x][i] == M[Top#y][i])
  );
}
procedure Top#anon$0#Nested#anon$1()
  modifies C, R, M;
{
  var x#i: int;
  assume C#init[Top#x] == 1;
  assume C#init[Top#y] == 0;
  assume R[Top#y] == 0;
  assume 0 <= C[Top#y];
  assume 0 <= R[Top#y];
  assume (R[Top#x] + C[Top#x]) == C#init[Top#x];
  assume 0 <= C[Top#x];
  assume 0 <= R[Top#x];
  assume (R[Top#y] + C[Top#y]) == R[Top#x];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Top#y] + C[Top#y])) ==> (M[Top#x][i] == M[Top#y][i])
  );
  assume 1 <= C[Top#x];
  x#i := M[Top#x][R[Top#x]];
  R[Top#x] := R[Top#x] + 1;
  C[Top#x] := C[Top#x] - 1;
  M[Top#y][R[Top#y] + C[Top#y]] := x#i;
  C[Top#y] := C[Top#y] + 1;
  assert {:msg "  Sub-actor action at 17.3 might not preserve the channel invariant"} R[Top#y] == 0;
  assert {:msg "  Sub-actor action at 17.3 might not preserve the channel invariant"} 0 <= C[Top#y];
  assert {:msg "  Sub-actor action at 17.3 might not preserve the channel invariant"} 0 <= R[Top#y];
  assert {:msg "  Sub-actor action at 17.3 might not preserve the channel invariant"} (R[Top#x] + C[Top#x]) == C#init[Top#x];
  assert {:msg "  Sub-actor action at 17.3 might not preserve the channel invariant"} 0 <= C[Top#x];
  assert {:msg "  Sub-actor action at 17.3 might not preserve the channel invariant"} 0 <= R[Top#x];
  assert {:msg "  4.15: Sub-actor action at 17.3 might not preserve the channel invariant"} (R[Top#y] + C[Top#y]) == R[Top#x];
  assert {:msg "  5.16: Sub-actor action at 17.3 might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[Top#y] + C[Top#y])) ==> (M[Top#x][i] == M[Top#y][i])
  );
}
procedure Top#anon$0#exit()
  modifies C, R, M;
{
  assume C#init[Top#x] == 1;
  assume C#init[Top#y] == 0;
  assume R[Top#y] == 0;
  assume 0 <= C[Top#y];
  assume 0 <= R[Top#y];
  assume (R[Top#x] + C[Top#x]) == C#init[Top#x];
  assume 0 <= C[Top#x];
  assume 0 <= R[Top#x];
  assume (R[Top#y] + C[Top#y]) == R[Top#x];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Top#y] + C[Top#y])) ==> (M[Top#x][i] == M[Top#y][i])
  );
  assume !(1 <= C[Top#x]);
  assert {:msg "  2.3: The network might leave unread tokens on channel x"} C[Top#x] == 0;
  assert {:msg "  2.3: The network might not produce the specified number of tokens on output out"} C[Top#y] == 1;
  assert {:msg "  2.26: Network output might not conform to specified action output"} M[Top#y][0] == M[Top#x][0];
  R[Top#y] := R[Top#y] + C[Top#y];
  C[Top#y] := 0;
}
const unique Nested#x: Chan (int);
const unique Nested#y: Chan (int);
procedure Nested#anon$1#entry()
  modifies C, R, M;
{
  assume C#init[Nested#x] == 1;
  assume C#init[Nested#y] == 0;
  assume R[Nested#x] == 0;
  assume R[Nested#y] == 0;
  assume C#init == C;
  assert {:msg "  Channel invariant might not hold on action entry"} R[Nested#y] == 0;
  assert {:msg "  Channel invariant might not hold on action entry"} 0 <= C[Nested#y];
  assert {:msg "  Channel invariant might not hold on action entry"} 0 <= R[Nested#y];
  assert {:msg "  Channel invariant might not hold on action entry"} (R[Nested#x] + C[Nested#x]) == C#init[Nested#x];
  assert {:msg "  Channel invariant might not hold on action entry"} 0 <= C[Nested#x];
  assert {:msg "  Channel invariant might not hold on action entry"} 0 <= R[Nested#x];
  assert {:msg "  19.15: Channel invariant might not hold on action entry"} (R[Nested#y] + C[Nested#y]) == R[Nested#x];
  assert {:msg "  20.16: Channel invariant might not hold on action entry"} (forall i: int :: 
    (0 <= i) && (i < (R[Nested#y] + C[Nested#y])) ==> (M[Nested#x][i] == M[Nested#y][i])
  );
}
procedure Nested#anon$1#Repeater#anon$2()
  modifies C, R, M;
{
  var in#i: int;
  assume C#init[Nested#x] == 1;
  assume C#init[Nested#y] == 0;
  assume R[Nested#y] == 0;
  assume 0 <= C[Nested#y];
  assume 0 <= R[Nested#y];
  assume (R[Nested#x] + C[Nested#x]) == C#init[Nested#x];
  assume 0 <= C[Nested#x];
  assume 0 <= R[Nested#x];
  assume (R[Nested#y] + C[Nested#y]) == R[Nested#x];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Nested#y] + C[Nested#y])) ==> (M[Nested#x][i] == M[Nested#y][i])
  );
  assume 1 <= C[Nested#x];
  in#i := M[Nested#x][R[Nested#x]];
  R[Nested#x] := R[Nested#x] + 1;
  C[Nested#x] := C[Nested#x] - 1;
  M[Nested#y][R[Nested#y] + C[Nested#y]] := in#i;
  C[Nested#y] := C[Nested#y] + 1;
  assert {:msg "  Sub-actor action at 33.3 might not preserve the channel invariant"} R[Nested#y] == 0;
  assert {:msg "  Sub-actor action at 33.3 might not preserve the channel invariant"} 0 <= C[Nested#y];
  assert {:msg "  Sub-actor action at 33.3 might not preserve the channel invariant"} 0 <= R[Nested#y];
  assert {:msg "  Sub-actor action at 33.3 might not preserve the channel invariant"} (R[Nested#x] + C[Nested#x]) == C#init[Nested#x];
  assert {:msg "  Sub-actor action at 33.3 might not preserve the channel invariant"} 0 <= C[Nested#x];
  assert {:msg "  Sub-actor action at 33.3 might not preserve the channel invariant"} 0 <= R[Nested#x];
  assert {:msg "  19.15: Sub-actor action at 33.3 might not preserve the channel invariant"} (R[Nested#y] + C[Nested#y]) == R[Nested#x];
  assert {:msg "  20.16: Sub-actor action at 33.3 might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[Nested#y] + C[Nested#y])) ==> (M[Nested#x][i] == M[Nested#y][i])
  );
}
procedure Nested#anon$1#exit()
  modifies C, R, M;
{
  assume C#init[Nested#x] == 1;
  assume C#init[Nested#y] == 0;
  assume R[Nested#y] == 0;
  assume 0 <= C[Nested#y];
  assume 0 <= R[Nested#y];
  assume (R[Nested#x] + C[Nested#x]) == C#init[Nested#x];
  assume 0 <= C[Nested#x];
  assume 0 <= R[Nested#x];
  assume (R[Nested#y] + C[Nested#y]) == R[Nested#x];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Nested#y] + C[Nested#y])) ==> (M[Nested#x][i] == M[Nested#y][i])
  );
  assume !(1 <= C[Nested#x]);
  assert {:msg "  17.3: The network might leave unread tokens on channel x"} C[Nested#x] == 0;
  assert {:msg "  17.3: The network might not produce the specified number of tokens on output y"} C[Nested#y] == 1;
  assert {:msg "  17.23: Network output might not conform to specified action output"} M[Nested#y][0] == M[Nested#x][0];
  R[Nested#y] := R[Nested#y] + C[Nested#y];
  C[Nested#y] := 0;
}
procedure Repeater#anon$2()
{
  var i: int;
  assume true;
}

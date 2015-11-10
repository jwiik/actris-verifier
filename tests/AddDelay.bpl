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

procedure Add#anon$0()
  modifies C, R, M, St;
{
  var i: int;
  var j: int;
  assume true;
}
procedure Delay#anon$1()
  modifies C, R, M, St;
{
  assume true;
}
procedure Delay#anon$2()
  modifies C, R, M, St;
{
  var i: int;
  assume true;
}
const unique Net#add: Actor;
const unique Net#del: Actor;
const unique Net#a: Chan (int);
const unique Net#b: Chan (int);
const unique Net#c: Chan (int);
const unique Net#d: Chan (int);
procedure Net#anon$3#entry()
  modifies C, R, M, St;
{
  assume C#init[Net#a] == 1;
  assume C#init[Net#c] == 0;
  assume C#init[Net#d] == 0;
  assume R[Net#a] == 0;
  assume R[Net#b] == 0;
  assume R[Net#c] == 0;
  assume R[Net#d] == 0;
  assume C#init == C;
  assume C[Net#b] == 1;
  assume M[Net#b][R[Net#b]] == M[Net#c][R[Net#c] - 1];
  assert {:msg "  Channel invariant might not hold on action entry"} 0 <= C[Net#d];
  assert {:msg "  Channel invariant might not hold on action entry"} 0 <= R[Net#d];
  assert {:msg "  Channel invariant might not hold on action entry"} R[Net#c] == 0;
  assert {:msg "  Channel invariant might not hold on action entry"} 0 <= C[Net#c];
  assert {:msg "  Channel invariant might not hold on action entry"} 0 <= R[Net#c];
  assert {:msg "  Channel invariant might not hold on action entry"} 0 <= C[Net#b];
  assert {:msg "  Channel invariant might not hold on action entry"} 0 <= R[Net#b];
  assert {:msg "  Channel invariant might not hold on action entry"} (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assert {:msg "  Channel invariant might not hold on action entry"} 0 <= C[Net#a];
  assert {:msg "  Channel invariant might not hold on action entry"} 0 <= R[Net#a];
  assert {:msg "  16.15: Channel invariant might not hold on action entry"} (R[Net#c] + C[Net#c]) == R[Net#a];
  assert {:msg "  17.15: Channel invariant might not hold on action entry"} (R[Net#c] + C[Net#c]) == R[Net#b];
  assert {:msg "  18.15: Channel invariant might not hold on action entry"} (R[Net#d] + C[Net#d]) == R[Net#a];
  assert {:msg "  19.15: Channel invariant might not hold on action entry"} (R[Net#d] + C[Net#d]) == R[Net#b];
  assert {:msg "  20.15: Channel invariant might not hold on action entry"} (R[Net#b] + C[Net#b]) == (R[Net#d] + 1);
  assert {:msg "  21.16: Channel invariant might not hold on action entry"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (M[Net#c][i] == (M[Net#a][i] + M[Net#b][i]))
  );
  assert {:msg "  22.16: Channel invariant might not hold on action entry"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (M[Net#d][i] == (M[Net#a][i] + M[Net#b][i]))
  );
  assert {:msg "  23.16: Channel invariant might not hold on action entry"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == M[Net#d][i - 1])
  );
  assert {:msg "  24.15: Channel invariant might not hold on action entry"} M[Net#b][0] == M[Net#c][-1];
}
procedure Net#anon$3#Add#anon$0()
  modifies C, R, M, St;
{
  var St#next: State;
  var in1#i: int;
  var in2#j: int;
  assume C#init[Net#a] == 1;
  assume C#init[Net#c] == 0;
  assume C#init[Net#d] == 0;
  assume 0 <= C[Net#d];
  assume 0 <= R[Net#d];
  assume R[Net#c] == 0;
  assume 0 <= C[Net#c];
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#b];
  assume 0 <= R[Net#b];
  assume (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assume 0 <= C[Net#a];
  assume 0 <= R[Net#a];
  assume (R[Net#c] + C[Net#c]) == R[Net#a];
  assume (R[Net#c] + C[Net#c]) == R[Net#b];
  assume (R[Net#d] + C[Net#d]) == R[Net#a];
  assume (R[Net#d] + C[Net#d]) == R[Net#b];
  assume (R[Net#b] + C[Net#b]) == (R[Net#d] + 1);
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (M[Net#c][i] == (M[Net#a][i] + M[Net#b][i]))
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (M[Net#d][i] == (M[Net#a][i] + M[Net#b][i]))
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == M[Net#d][i - 1])
  );
  assume M[Net#b][0] == M[Net#c][-1];
  assume true;
  assume (1 <= C[Net#a]) && (1 <= C[Net#b]);
  in1#i := M[Net#a][R[Net#a]];
  R[Net#a] := R[Net#a] + 1;
  C[Net#a] := C[Net#a] - 1;
  in2#j := M[Net#b][R[Net#b]];
  R[Net#b] := R[Net#b] + 1;
  C[Net#b] := C[Net#b] - 1;
  M[Net#c][R[Net#c] + C[Net#c]] := in1#i + in2#j;
  C[Net#c] := C[Net#c] + 1;
  M[Net#d][R[Net#d] + C[Net#d]] := in1#i + in2#j;
  C[Net#d] := C[Net#d] + 1;
  assert {:msg "  Sub-actor action at 2.3 might not preserve the channel invariant"} 0 <= C[Net#d];
  assert {:msg "  Sub-actor action at 2.3 might not preserve the channel invariant"} 0 <= R[Net#d];
  assert {:msg "  Sub-actor action at 2.3 might not preserve the channel invariant"} R[Net#c] == 0;
  assert {:msg "  Sub-actor action at 2.3 might not preserve the channel invariant"} 0 <= C[Net#c];
  assert {:msg "  Sub-actor action at 2.3 might not preserve the channel invariant"} 0 <= R[Net#c];
  assert {:msg "  Sub-actor action at 2.3 might not preserve the channel invariant"} 0 <= C[Net#b];
  assert {:msg "  Sub-actor action at 2.3 might not preserve the channel invariant"} 0 <= R[Net#b];
  assert {:msg "  Sub-actor action at 2.3 might not preserve the channel invariant"} (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assert {:msg "  Sub-actor action at 2.3 might not preserve the channel invariant"} 0 <= C[Net#a];
  assert {:msg "  Sub-actor action at 2.3 might not preserve the channel invariant"} 0 <= R[Net#a];
  assert {:msg "  16.15: Sub-actor action at 2.3 might not preserve the channel invariant"} (R[Net#c] + C[Net#c]) == R[Net#a];
  assert {:msg "  17.15: Sub-actor action at 2.3 might not preserve the channel invariant"} (R[Net#c] + C[Net#c]) == R[Net#b];
  assert {:msg "  18.15: Sub-actor action at 2.3 might not preserve the channel invariant"} (R[Net#d] + C[Net#d]) == R[Net#a];
  assert {:msg "  19.15: Sub-actor action at 2.3 might not preserve the channel invariant"} (R[Net#d] + C[Net#d]) == R[Net#b];
  assert {:msg "  20.15: Sub-actor action at 2.3 might not preserve the channel invariant"} (R[Net#b] + C[Net#b]) == (R[Net#d] + 1);
  assert {:msg "  21.16: Sub-actor action at 2.3 might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (M[Net#c][i] == (M[Net#a][i] + M[Net#b][i]))
  );
  assert {:msg "  22.16: Sub-actor action at 2.3 might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (M[Net#d][i] == (M[Net#a][i] + M[Net#b][i]))
  );
  assert {:msg "  23.16: Sub-actor action at 2.3 might not preserve the channel invariant"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == M[Net#d][i - 1])
  );
  assert {:msg "  24.15: Sub-actor action at 2.3 might not preserve the channel invariant"} M[Net#b][0] == M[Net#c][-1];
}
procedure Net#anon$3#Delay#anon$2()
  modifies C, R, M, St;
{
  var St#next: State;
  var in#i: int;
  assume C#init[Net#a] == 1;
  assume C#init[Net#c] == 0;
  assume C#init[Net#d] == 0;
  assume 0 <= C[Net#d];
  assume 0 <= R[Net#d];
  assume R[Net#c] == 0;
  assume 0 <= C[Net#c];
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#b];
  assume 0 <= R[Net#b];
  assume (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assume 0 <= C[Net#a];
  assume 0 <= R[Net#a];
  assume (R[Net#c] + C[Net#c]) == R[Net#a];
  assume (R[Net#c] + C[Net#c]) == R[Net#b];
  assume (R[Net#d] + C[Net#d]) == R[Net#a];
  assume (R[Net#d] + C[Net#d]) == R[Net#b];
  assume (R[Net#b] + C[Net#b]) == (R[Net#d] + 1);
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (M[Net#c][i] == (M[Net#a][i] + M[Net#b][i]))
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (M[Net#d][i] == (M[Net#a][i] + M[Net#b][i]))
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == M[Net#d][i - 1])
  );
  assume M[Net#b][0] == M[Net#c][-1];
  assume true;
  assume 1 <= C[Net#d];
  in#i := M[Net#d][R[Net#d]];
  R[Net#d] := R[Net#d] + 1;
  C[Net#d] := C[Net#d] - 1;
  M[Net#b][R[Net#b] + C[Net#b]] := in#i;
  C[Net#b] := C[Net#b] + 1;
  assert {:msg "  Sub-actor action at 7.3 might not preserve the channel invariant"} 0 <= C[Net#d];
  assert {:msg "  Sub-actor action at 7.3 might not preserve the channel invariant"} 0 <= R[Net#d];
  assert {:msg "  Sub-actor action at 7.3 might not preserve the channel invariant"} R[Net#c] == 0;
  assert {:msg "  Sub-actor action at 7.3 might not preserve the channel invariant"} 0 <= C[Net#c];
  assert {:msg "  Sub-actor action at 7.3 might not preserve the channel invariant"} 0 <= R[Net#c];
  assert {:msg "  Sub-actor action at 7.3 might not preserve the channel invariant"} 0 <= C[Net#b];
  assert {:msg "  Sub-actor action at 7.3 might not preserve the channel invariant"} 0 <= R[Net#b];
  assert {:msg "  Sub-actor action at 7.3 might not preserve the channel invariant"} (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assert {:msg "  Sub-actor action at 7.3 might not preserve the channel invariant"} 0 <= C[Net#a];
  assert {:msg "  Sub-actor action at 7.3 might not preserve the channel invariant"} 0 <= R[Net#a];
  assert {:msg "  16.15: Sub-actor action at 7.3 might not preserve the channel invariant"} (R[Net#c] + C[Net#c]) == R[Net#a];
  assert {:msg "  17.15: Sub-actor action at 7.3 might not preserve the channel invariant"} (R[Net#c] + C[Net#c]) == R[Net#b];
  assert {:msg "  18.15: Sub-actor action at 7.3 might not preserve the channel invariant"} (R[Net#d] + C[Net#d]) == R[Net#a];
  assert {:msg "  19.15: Sub-actor action at 7.3 might not preserve the channel invariant"} (R[Net#d] + C[Net#d]) == R[Net#b];
  assert {:msg "  20.15: Sub-actor action at 7.3 might not preserve the channel invariant"} (R[Net#b] + C[Net#b]) == (R[Net#d] + 1);
  assert {:msg "  21.16: Sub-actor action at 7.3 might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (M[Net#c][i] == (M[Net#a][i] + M[Net#b][i]))
  );
  assert {:msg "  22.16: Sub-actor action at 7.3 might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (M[Net#d][i] == (M[Net#a][i] + M[Net#b][i]))
  );
  assert {:msg "  23.16: Sub-actor action at 7.3 might not preserve the channel invariant"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == M[Net#d][i - 1])
  );
  assert {:msg "  24.15: Sub-actor action at 7.3 might not preserve the channel invariant"} M[Net#b][0] == M[Net#c][-1];
}
procedure Net#anon$3#exit()
  modifies C, R, M, St;
{
  assume C#init[Net#a] == 1;
  assume C#init[Net#c] == 0;
  assume C#init[Net#d] == 0;
  assume 0 <= C[Net#d];
  assume 0 <= R[Net#d];
  assume R[Net#c] == 0;
  assume 0 <= C[Net#c];
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#b];
  assume 0 <= R[Net#b];
  assume (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assume 0 <= C[Net#a];
  assume 0 <= R[Net#a];
  assume (R[Net#c] + C[Net#c]) == R[Net#a];
  assume (R[Net#c] + C[Net#c]) == R[Net#b];
  assume (R[Net#d] + C[Net#d]) == R[Net#a];
  assume (R[Net#d] + C[Net#d]) == R[Net#b];
  assume (R[Net#b] + C[Net#b]) == (R[Net#d] + 1);
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (M[Net#c][i] == (M[Net#a][i] + M[Net#b][i]))
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#d] + C[Net#d])) ==> (M[Net#d][i] == (M[Net#a][i] + M[Net#b][i]))
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == M[Net#d][i - 1])
  );
  assume M[Net#b][0] == M[Net#c][-1];
  assume !(((1 <= C[Net#a]) && (1 <= C[Net#b])) || (1 <= C[Net#d]));
  assert {:msg "  11.3: The network might leave unread tokens on channel a"} C[Net#a] == 0;
  assert {:msg "  11.3: The network might not produce the specified number of tokens on output out"} C[Net#c] == 1;
  assert {:msg "  11.3: The network might leave unread tokens on channel d"} C[Net#d] == 0;
  assert {:msg "  11.26: Network output might not conform to specified action output"} M[Net#c][0] == (M[Net#c][R[Net#c] - 1] + M[Net#a][0]);
  R[Net#c] := R[Net#c] + C[Net#c];
  C[Net#c] := 0;
  assert {:msg "  13.13: The network might not preserve the network invariant"} C[Net#b] == 1;
  assert {:msg "  14.13: The network might not preserve the network invariant"} M[Net#b][R[Net#b]] == M[Net#c][R[Net#c] - 1];
}

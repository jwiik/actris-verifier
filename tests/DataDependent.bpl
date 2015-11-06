
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

function at$abs(x: int): int { if 0 <= x then x else -x }
function at$div(int, int): int;
function at$mod(int, int): int;
axiom (forall a,b: int :: at$div(a,b)*b + at$mod(a,b) == a);
axiom (forall a,b: int :: 0 <= at$mod(a,b) && at$mod(a,b) < at$abs(b));

// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

procedure Repeater#anon$0()
{
  var i: int;
  assume true;
}
procedure Split#anon$1()
{
  var i: int;
  assume 0 <= i;
  assume true;
}
procedure Split#anon$2()
{
  var i: int;
  assume i < 0;
  assume true;
}
const unique Net#a: Chan (int);
const unique Net#b: Chan (int);
const unique Net#c: Chan (int);
const unique Net#d: Chan (int);
procedure Net#anon$3#entry()
  modifies C, R, M;
{
  assume C#init[Net#a] == 2;
  assume C#init[Net#b] == 0;
  assume C#init[Net#c] == 0;
  assume C#init[Net#d] == 0;
  assume R[Net#a] == 0;
  assume R[Net#b] == 0;
  assume R[Net#c] == 0;
  assume R[Net#d] == 0;
  assume (M[Net#a][0] < 0) && (M[Net#a][1] > 0);
  assume C#init == C;
  assert {:msg "  Channel invariant might not hold on action entry"} R[Net#d] == 0;
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
  assert {:msg "  19.15: Channel invariant might not hold on action entry"} (M[Net#a][0] < 0) && (M[Net#a][1] > 0);
  assert {:msg "  20.15: Channel invariant might not hold on action entry"} (R[Net#b] + C[Net#b]) == R[Net#a];
  assert {:msg "  21.15: Channel invariant might not hold on action entry"} (R[Net#d] + C[Net#d]) == at$div(R[Net#b] + 1, 2);
  assert {:msg "  22.15: Channel invariant might not hold on action entry"} (R[Net#c] + C[Net#c]) == at$div(R[Net#b], 2);
  assert {:msg "  23.16: Channel invariant might not hold on action entry"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == M[Net#a][i])
  );
  assert {:msg "  24.16: Channel invariant might not hold on action entry"} (forall i: int :: 
    (0 <= i) && (i < R[Net#b]) && (at$mod(i, 2) == 0) ==> (M[Net#b][i] == M[Net#d][at$div(i, 2)])
  );
  assert {:msg "  25.16: Channel invariant might not hold on action entry"} (forall i: int :: 
    (0 <= i) && (i < R[Net#b]) && (at$mod(i, 2) == 1) ==> (M[Net#b][i] == M[Net#c][at$div(i, 2)])
  );
}
procedure Net#anon$3#Repeater#anon$0()
  modifies C, R, M;
{
  var in#i: int;
  assume C#init[Net#a] == 2;
  assume C#init[Net#b] == 0;
  assume C#init[Net#c] == 0;
  assume C#init[Net#d] == 0;
  assume R[Net#d] == 0;
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
  assume (M[Net#a][0] < 0) && (M[Net#a][1] > 0);
  assume (R[Net#b] + C[Net#b]) == R[Net#a];
  assume (R[Net#d] + C[Net#d]) == at$div(R[Net#b] + 1, 2);
  assume (R[Net#c] + C[Net#c]) == at$div(R[Net#b], 2);
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == M[Net#a][i])
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#b]) && (at$mod(i, 2) == 0) ==> (M[Net#b][i] == M[Net#d][at$div(i, 2)])
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#b]) && (at$mod(i, 2) == 1) ==> (M[Net#b][i] == M[Net#c][at$div(i, 2)])
  );
  assume 1 <= C[Net#a];
  in#i := M[Net#a][R[Net#a]];
  R[Net#a] := R[Net#a] + 1;
  C[Net#a] := C[Net#a] - 1;
  M[Net#b][R[Net#b] + C[Net#b]] := in#i;
  C[Net#b] := C[Net#b] + 1;
  assert {:msg "  Sub-actor action at 2.3 might not preserve the channel invariant"} R[Net#d] == 0;
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
  assert {:msg "  19.15: Sub-actor action at 2.3 might not preserve the channel invariant"} (M[Net#a][0] < 0) && (M[Net#a][1] > 0);
  assert {:msg "  20.15: Sub-actor action at 2.3 might not preserve the channel invariant"} (R[Net#b] + C[Net#b]) == R[Net#a];
  assert {:msg "  21.15: Sub-actor action at 2.3 might not preserve the channel invariant"} (R[Net#d] + C[Net#d]) == at$div(R[Net#b] + 1, 2);
  assert {:msg "  22.15: Sub-actor action at 2.3 might not preserve the channel invariant"} (R[Net#c] + C[Net#c]) == at$div(R[Net#b], 2);
  assert {:msg "  23.16: Sub-actor action at 2.3 might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == M[Net#a][i])
  );
  assert {:msg "  24.16: Sub-actor action at 2.3 might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < R[Net#b]) && (at$mod(i, 2) == 0) ==> (M[Net#b][i] == M[Net#d][at$div(i, 2)])
  );
  assert {:msg "  25.16: Sub-actor action at 2.3 might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < R[Net#b]) && (at$mod(i, 2) == 1) ==> (M[Net#b][i] == M[Net#c][at$div(i, 2)])
  );
}
procedure Net#anon$3#Split#anon$1()
  modifies C, R, M;
{
  var in#i: int;
  assume C#init[Net#a] == 2;
  assume C#init[Net#b] == 0;
  assume C#init[Net#c] == 0;
  assume C#init[Net#d] == 0;
  assume R[Net#d] == 0;
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
  assume (M[Net#a][0] < 0) && (M[Net#a][1] > 0);
  assume (R[Net#b] + C[Net#b]) == R[Net#a];
  assume (R[Net#d] + C[Net#d]) == at$div(R[Net#b] + 1, 2);
  assume (R[Net#c] + C[Net#c]) == at$div(R[Net#b], 2);
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == M[Net#a][i])
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#b]) && (at$mod(i, 2) == 0) ==> (M[Net#b][i] == M[Net#d][at$div(i, 2)])
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#b]) && (at$mod(i, 2) == 1) ==> (M[Net#b][i] == M[Net#c][at$div(i, 2)])
  );
  assume 0 <= M[Net#b][R[Net#b] - 0];
  assume (1 <= C[Net#b]) && (0 <= M[Net#b][R[Net#b] - 0]);
  in#i := M[Net#b][R[Net#b]];
  R[Net#b] := R[Net#b] + 1;
  C[Net#b] := C[Net#b] - 1;
  M[Net#c][R[Net#c] + C[Net#c]] := in#i;
  C[Net#c] := C[Net#c] + 1;
  assert {:msg "  Sub-actor action at 6.3 might not preserve the channel invariant"} R[Net#d] == 0;
  assert {:msg "  Sub-actor action at 6.3 might not preserve the channel invariant"} 0 <= C[Net#d];
  assert {:msg "  Sub-actor action at 6.3 might not preserve the channel invariant"} 0 <= R[Net#d];
  assert {:msg "  Sub-actor action at 6.3 might not preserve the channel invariant"} R[Net#c] == 0;
  assert {:msg "  Sub-actor action at 6.3 might not preserve the channel invariant"} 0 <= C[Net#c];
  assert {:msg "  Sub-actor action at 6.3 might not preserve the channel invariant"} 0 <= R[Net#c];
  assert {:msg "  Sub-actor action at 6.3 might not preserve the channel invariant"} 0 <= C[Net#b];
  assert {:msg "  Sub-actor action at 6.3 might not preserve the channel invariant"} 0 <= R[Net#b];
  assert {:msg "  Sub-actor action at 6.3 might not preserve the channel invariant"} (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assert {:msg "  Sub-actor action at 6.3 might not preserve the channel invariant"} 0 <= C[Net#a];
  assert {:msg "  Sub-actor action at 6.3 might not preserve the channel invariant"} 0 <= R[Net#a];
  assert {:msg "  19.15: Sub-actor action at 6.3 might not preserve the channel invariant"} (M[Net#a][0] < 0) && (M[Net#a][1] > 0);
  assert {:msg "  20.15: Sub-actor action at 6.3 might not preserve the channel invariant"} (R[Net#b] + C[Net#b]) == R[Net#a];
  assert {:msg "  21.15: Sub-actor action at 6.3 might not preserve the channel invariant"} (R[Net#d] + C[Net#d]) == at$div(R[Net#b] + 1, 2);
  assert {:msg "  22.15: Sub-actor action at 6.3 might not preserve the channel invariant"} (R[Net#c] + C[Net#c]) == at$div(R[Net#b], 2);
  assert {:msg "  23.16: Sub-actor action at 6.3 might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == M[Net#a][i])
  );
  assert {:msg "  24.16: Sub-actor action at 6.3 might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < R[Net#b]) && (at$mod(i, 2) == 0) ==> (M[Net#b][i] == M[Net#d][at$div(i, 2)])
  );
  assert {:msg "  25.16: Sub-actor action at 6.3 might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < R[Net#b]) && (at$mod(i, 2) == 1) ==> (M[Net#b][i] == M[Net#c][at$div(i, 2)])
  );
}
procedure Net#anon$3#Split#anon$2()
  modifies C, R, M;
{
  var in#i: int;
  assume C#init[Net#a] == 2;
  assume C#init[Net#b] == 0;
  assume C#init[Net#c] == 0;
  assume C#init[Net#d] == 0;
  assume R[Net#d] == 0;
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
  assume (M[Net#a][0] < 0) && (M[Net#a][1] > 0);
  assume (R[Net#b] + C[Net#b]) == R[Net#a];
  assume (R[Net#d] + C[Net#d]) == at$div(R[Net#b] + 1, 2);
  assume (R[Net#c] + C[Net#c]) == at$div(R[Net#b], 2);
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == M[Net#a][i])
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#b]) && (at$mod(i, 2) == 0) ==> (M[Net#b][i] == M[Net#d][at$div(i, 2)])
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#b]) && (at$mod(i, 2) == 1) ==> (M[Net#b][i] == M[Net#c][at$div(i, 2)])
  );
  assume M[Net#b][R[Net#b] - 0] < 0;
  assume (1 <= C[Net#b]) && (M[Net#b][R[Net#b] - 0] < 0);
  in#i := M[Net#b][R[Net#b]];
  R[Net#b] := R[Net#b] + 1;
  C[Net#b] := C[Net#b] - 1;
  M[Net#d][R[Net#d] + C[Net#d]] := in#i;
  C[Net#d] := C[Net#d] + 1;
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant"} R[Net#d] == 0;
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant"} 0 <= C[Net#d];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant"} 0 <= R[Net#d];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant"} R[Net#c] == 0;
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant"} 0 <= C[Net#c];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant"} 0 <= R[Net#c];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant"} 0 <= C[Net#b];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant"} 0 <= R[Net#b];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant"} (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant"} 0 <= C[Net#a];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant"} 0 <= R[Net#a];
  assert {:msg "  19.15: Sub-actor action at 9.3 might not preserve the channel invariant"} (M[Net#a][0] < 0) && (M[Net#a][1] > 0);
  assert {:msg "  20.15: Sub-actor action at 9.3 might not preserve the channel invariant"} (R[Net#b] + C[Net#b]) == R[Net#a];
  assert {:msg "  21.15: Sub-actor action at 9.3 might not preserve the channel invariant"} (R[Net#d] + C[Net#d]) == at$div(R[Net#b] + 1, 2);
  assert {:msg "  22.15: Sub-actor action at 9.3 might not preserve the channel invariant"} (R[Net#c] + C[Net#c]) == at$div(R[Net#b], 2);
  assert {:msg "  23.16: Sub-actor action at 9.3 might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == M[Net#a][i])
  );
  assert {:msg "  24.16: Sub-actor action at 9.3 might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < R[Net#b]) && (at$mod(i, 2) == 0) ==> (M[Net#b][i] == M[Net#d][at$div(i, 2)])
  );
  assert {:msg "  25.16: Sub-actor action at 9.3 might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < R[Net#b]) && (at$mod(i, 2) == 1) ==> (M[Net#b][i] == M[Net#c][at$div(i, 2)])
  );
}
procedure Net#anon$3#exit()
  modifies C, R, M;
{
  assume C#init[Net#a] == 2;
  assume C#init[Net#b] == 0;
  assume C#init[Net#c] == 0;
  assume C#init[Net#d] == 0;
  assume R[Net#d] == 0;
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
  assume (M[Net#a][0] < 0) && (M[Net#a][1] > 0);
  assume (R[Net#b] + C[Net#b]) == R[Net#a];
  assume (R[Net#d] + C[Net#d]) == at$div(R[Net#b] + 1, 2);
  assume (R[Net#c] + C[Net#c]) == at$div(R[Net#b], 2);
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == M[Net#a][i])
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#b]) && (at$mod(i, 2) == 0) ==> (M[Net#b][i] == M[Net#d][at$div(i, 2)])
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#b]) && (at$mod(i, 2) == 1) ==> (M[Net#b][i] == M[Net#c][at$div(i, 2)])
  );
  assume !(((1 <= C[Net#a]) || ((1 <= C[Net#b]) && (0 <= M[Net#b][R[Net#b] - 0]))) || ((1 <= C[Net#b]) && (M[Net#b][R[Net#b] - 0] < 0)));
  assert {:msg "  15.3: The network might leave unread tokens on channel a"} C[Net#a] == 0;
  assert {:msg "  15.3: The network might leave unread tokens on channel b"} C[Net#b] == 0;
  assert {:msg "  15.3: The network might not produce the specified number of tokens on output out1"} C[Net#c] == 1;
  assert {:msg "  15.3: The network might not produce the specified number of tokens on output out2"} C[Net#d] == 1;
  assert {:msg "  15.31: Network output might not conform to specified action output"} M[Net#c][0] == M[Net#a][1];
  assert {:msg "  15.42: Network output might not conform to specified action output"} M[Net#d][0] == M[Net#a][0];
  R[Net#c] := R[Net#c] + C[Net#c];
  C[Net#c] := 0;
  R[Net#d] := R[Net#d] + C[Net#d];
  C[Net#d] := 0;
}

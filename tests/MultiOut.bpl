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

function AT#Abs(x: int): int { if 0 <= x then x else -x }
function AT#Div(int, int): int;
function AT#Mod(int, int): int;
axiom (forall a,b: int :: AT#Div(a,b)*b + AT#Mod(a,b) == a);
axiom (forall a,b: int :: 0 <= AT#Mod(a,b) && AT#Mod(a,b) < AT#Abs(b));

// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

procedure Add2#anon$0#0()
  modifies C, R, M, St;
{
  var i: int;
  assume true;
}
const unique Net#add: Actor;
const unique Net#a: Chan (int);
const unique Net#b: Chan (int);
procedure Net#anon$1#entry#1()
  modifies C, R, M, St;
{
  assume C#init[Net#a] == 1;
  assume C#init[Net#b] == 0;
  assume R[Net#a] == 0;
  assume R[Net#b] == 0;
  assume C#init == C;
  assert {:msg "  Channel invariant might not hold on action entry (generated #0 )"} 0 <= R[Net#a];
  assert {:msg "  Channel invariant might not hold on action entry (generated #1 )"} 0 <= C[Net#a];
  assert {:msg "  Channel invariant might not hold on action entry (generated #2 )"} (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assert {:msg "  Channel invariant might not hold on action entry (generated #3 )"} 0 <= R[Net#b];
  assert {:msg "  Channel invariant might not hold on action entry (generated #4 )"} 0 <= C[Net#b];
  assert {:msg "  Channel invariant might not hold on action entry (generated #5 )"} R[Net#b] == 0;
  assert {:msg "  9.3: Channel invariant might not hold on action entry"} (R[Net#b] + C[Net#b]) == (2 * R[Net#a]);
  assert {:msg "  10.3: Channel invariant might not hold on action entry"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) && (AT#Mod(i, 2) == 0) ==> (M[Net#b][i] == M[Net#a][AT#Div(i, 2)])
  );
  assert {:msg "  11.3: Channel invariant might not hold on action entry"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) && (AT#Mod(i, 2) == 1) ==> (M[Net#b][i] == (M[Net#a][AT#Div(i, 2)] + M[Net#a][AT#Div(i, 2)]))
  );
}
procedure Net#anon$1#Add2#anon$0#2()
  modifies C, R, M, St;
{
  var St#next: State;
  var in#i: int;
  assume C#init[Net#a] == 1;
  assume C#init[Net#b] == 0;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume R[Net#b] == 0;
  assume (R[Net#b] + C[Net#b]) == (2 * R[Net#a]);
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) && (AT#Mod(i, 2) == 0) ==> (M[Net#b][i] == M[Net#a][AT#Div(i, 2)])
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) && (AT#Mod(i, 2) == 1) ==> (M[Net#b][i] == (M[Net#a][AT#Div(i, 2)] + M[Net#a][AT#Div(i, 2)]))
  );
  assume true;
  assume 1 <= C[Net#a];
  in#i := M[Net#a][R[Net#a]];
  R[Net#a] := R[Net#a] + 1;
  C[Net#a] := C[Net#a] - 1;
  M[Net#b][R[Net#b] + C[Net#b]] := in#i;
  C[Net#b] := C[Net#b] + 1;
  M[Net#b][R[Net#b] + C[Net#b]] := in#i + in#i;
  C[Net#b] := C[Net#b] + 1;
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #6)"} 0 <= R[Net#a];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #7)"} 0 <= C[Net#a];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #8)"} (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #9)"} 0 <= R[Net#b];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #10)"} 0 <= C[Net#b];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #11)"} R[Net#b] == 0;
  assert {:msg "  9.3: Sub-actor action at 3.3 might not preserve the channel invariant"} (R[Net#b] + C[Net#b]) == (2 * R[Net#a]);
  assert {:msg "  10.3: Sub-actor action at 3.3 might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) && (AT#Mod(i, 2) == 0) ==> (M[Net#b][i] == M[Net#a][AT#Div(i, 2)])
  );
  assert {:msg "  11.3: Sub-actor action at 3.3 might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) && (AT#Mod(i, 2) == 1) ==> (M[Net#b][i] == (M[Net#a][AT#Div(i, 2)] + M[Net#a][AT#Div(i, 2)]))
  );
}
procedure Net#anon$1#exit#3()
  modifies C, R, M, St;
{
  assume C#init[Net#a] == 1;
  assume C#init[Net#b] == 0;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume R[Net#b] == 0;
  assume (R[Net#b] + C[Net#b]) == (2 * R[Net#a]);
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) && (AT#Mod(i, 2) == 0) ==> (M[Net#b][i] == M[Net#a][AT#Div(i, 2)])
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) && (AT#Mod(i, 2) == 1) ==> (M[Net#b][i] == (M[Net#a][AT#Div(i, 2)] + M[Net#a][AT#Div(i, 2)]))
  );
  assume !(1 <= C[Net#a]);
  assert {:msg "  7.3: The network might leave unread tokens on channel a"} C[Net#a] == 0;
  assert {:msg "  7.3: The network might not produce the specified number of tokens on output out"} C[Net#b] == 2;
  assert {:msg "  7.26: Network output might not conform to specified action output"} M[Net#b][0] == M[Net#a][0];
  assert {:msg "  7.28: Network output might not conform to specified action output"} M[Net#b][1] == (M[Net#a][0] + M[Net#a][0]);
  R[Net#b] := R[Net#b] + C[Net#b];
  C[Net#b] := 0;
}

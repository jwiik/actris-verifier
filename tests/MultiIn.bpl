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
var N: CType;
var C#init: CType;
var St: [Actor]State;

const unique this#: Actor;

type List a = [int]a;
var AT#intlst: List int;


// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

procedure Add2#anon$0#0()
  modifies C, R, M, St;
{
  var IV#in#i: int;
  var IV#in#j: int;
  assume true;
}
procedure Net#init#1()
  modifies C, R, M, St;
{
  assume C[Net#a] == 0;
  assume R[Net#a] == 0;
  assume C[Net#b] == 0;
  assume R[Net#b] == 0;
}
const unique Net#add: Actor;
const unique Net#a: Chan (int);
const unique Net#b: Chan (int);
procedure Net#anon$1#entry#2()
  modifies C, R, M, St;
{
  var Net#out#0: int;
  assume C#init[Net#a] == 2;
  assume C#init[Net#b] == 0;
  assume R[Net#a] == 0;
  assume R[Net#b] == 0;
  assume C#init == C;
  assert {:msg "  Channel invariant might not hold on action entry (generated #0)"} 0 <= R[Net#a];
  assert {:msg "  Channel invariant might not hold on action entry (generated #1)"} 0 <= C[Net#a];
  assert {:msg "  Channel invariant might not hold on action entry (generated #2)"} (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assert {:msg "  Channel invariant might not hold on action entry (generated #3)"} 0 <= R[Net#b];
  assert {:msg "  Channel invariant might not hold on action entry (generated #4)"} 0 <= C[Net#b];
  assert {:msg "  Channel invariant might not hold on action entry (generated #5)"} R[Net#b] == 0;
  assert {:msg "  8.3: Channel invariant might not hold on action entry"} R[Net#a] == (2 * (R[Net#b] + C[Net#b]));
  assert {:msg "  9.3: Channel invariant might not hold on action entry"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == (M[Net#a][2 * i] + M[Net#a][(2 * i) + 1]))
  );
}
procedure Net#anon$1#Add2#anon$0#3()
  modifies C, R, M, St;
{
  var St#next: State;
  var in#i: int;
  var in#j: int;
  assume C#init[Net#a] == 2;
  assume C#init[Net#b] == 0;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume R[Net#b] == 0;
  assume R[Net#a] == (2 * (R[Net#b] + C[Net#b]));
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == (M[Net#a][2 * i] + M[Net#a][(2 * i) + 1]))
  );
  assume true;
  assume 2 <= C[Net#a];
  in#i := M[Net#a][R[Net#a]];
  R[Net#a] := R[Net#a] + 1;
  C[Net#a] := C[Net#a] - 1;
  in#j := M[Net#a][R[Net#a]];
  R[Net#a] := R[Net#a] + 1;
  C[Net#a] := C[Net#a] - 1;
  M[Net#b][R[Net#b] + C[Net#b]] := in#i + in#j;
  C[Net#b] := C[Net#b] + 1;
  assert {:msg "  Sub-actor action at 2.3 might not preserve the channel invariant (generated #6)"} 0 <= R[Net#a];
  assert {:msg "  Sub-actor action at 2.3 might not preserve the channel invariant (generated #7)"} 0 <= C[Net#a];
  assert {:msg "  Sub-actor action at 2.3 might not preserve the channel invariant (generated #8)"} (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assert {:msg "  Sub-actor action at 2.3 might not preserve the channel invariant (generated #9)"} 0 <= R[Net#b];
  assert {:msg "  Sub-actor action at 2.3 might not preserve the channel invariant (generated #10)"} 0 <= C[Net#b];
  assert {:msg "  Sub-actor action at 2.3 might not preserve the channel invariant (generated #11)"} R[Net#b] == 0;
  assert {:msg "  8.3: Sub-actor action at 2.3 might not preserve the channel invariant"} R[Net#a] == (2 * (R[Net#b] + C[Net#b]));
  assert {:msg "  9.3: Sub-actor action at 2.3 might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == (M[Net#a][2 * i] + M[Net#a][(2 * i) + 1]))
  );
}
procedure Net#anon$1#exit#4()
  modifies C, R, M, St;
{
  var Net#out#0: int;
  assume C#init[Net#a] == 2;
  assume C#init[Net#b] == 0;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume R[Net#b] == 0;
  assume R[Net#a] == (2 * (R[Net#b] + C[Net#b]));
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (M[Net#b][i] == (M[Net#a][2 * i] + M[Net#a][(2 * i) + 1]))
  );
  assume !(2 <= C[Net#a]);
  assert {:msg "  6.3: The network might leave unread tokens on channel a"} C[Net#a] == 0;
  assert {:msg "  6.3: The network might not produce the specified number of tokens on output out"} C[Net#b] == 1;
  Net#out#0 := M[Net#b][0];
  assert {:msg "  6.28: Network output might not conform to the specified action output"} Net#out#0 == (M[Net#a][0] + M[Net#a][1]);
  R[Net#b] := R[Net#b] + C[Net#b];
  C[Net#b] := 0;
}

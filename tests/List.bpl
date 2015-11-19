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

procedure ListTest#anon$0#0()
  modifies C, R, M, St;
{
  var X: List (int);
  var IV#in#i: int;
  var ActionVar#o: int;
  assume (X[0] == 10) && (X[1] == 11) && (X[2] == 12);
  assume (0 <= IV#in#i) && (IV#in#i < 3);
  ActionVar#o := X[IV#in#i];
  assert {:msg "  3.13: Action might not preserve invariant"} (X[0] == 10) && (X[1] == 11) && (X[2] == 12);
}
const unique Net#l: Actor;
const unique Net#a: Chan (int);
const unique Net#b: Chan (int);
procedure Net#anon$1#entry#1()
  modifies C, R, M, St;
{
  var ActionVar#y: int;
  assume C#init[Net#a] == 1;
  assume C#init[Net#b] == 0;
  assume R[Net#a] == 0;
  assume R[Net#b] == 0;
  assume (0 <= M[Net#a][0]) && (M[Net#a][0] < 3);
  assume C#init == C;
  assert {:msg "  Channel invariant might not hold on action entry (generated #0)"} 0 <= R[Net#a];
  assert {:msg "  Channel invariant might not hold on action entry (generated #1)"} 0 <= C[Net#a];
  assert {:msg "  Channel invariant might not hold on action entry (generated #2)"} (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assert {:msg "  Channel invariant might not hold on action entry (generated #3)"} 0 <= R[Net#b];
  assert {:msg "  Channel invariant might not hold on action entry (generated #4)"} 0 <= C[Net#b];
  assert {:msg "  Channel invariant might not hold on action entry (generated #5)"} R[Net#b] == 0;
  assert {:msg "  22.3: Channel invariant might not hold on action entry"} (0 <= M[Net#a][0]) && (M[Net#a][0] < 3);
  assert {:msg "  23.3: Channel invariant might not hold on action entry"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  24.3: Channel invariant might not hold on action entry"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (10 <= M[Net#b][i]) && (M[Net#b][i] <= 12)
  );
  assert {:msg "  25.3: Channel invariant might not hold on action entry"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> ((M[Net#a][i] == 0) ==> (M[Net#b][i] == 10))
  );
}
procedure Net#anon$1#ListTest#anon$0#2()
  modifies C, R, M, St;
{
  var ActorVar#X: List (int);
  var ActionVar#o: int;
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
  assume (0 <= M[Net#a][0]) && (M[Net#a][0] < 3);
  assume R[Net#a] == (R[Net#b] + C[Net#b]);
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (10 <= M[Net#b][i]) && (M[Net#b][i] <= 12)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> ((M[Net#a][i] == 0) ==> (M[Net#b][i] == 10))
  );
  assume (0 <= M[Net#a][R[Net#a] - 0]) && (M[Net#a][R[Net#a] - 0] < 3);
  assume true;
  assume (1 <= C[Net#a]) && (0 <= M[Net#a][R[Net#a] - 0]) && (M[Net#a][R[Net#a] - 0] < 3);
  assume (ActorVar#X[0] == 10) && (ActorVar#X[1] == 11) && (ActorVar#X[2] == 12);
  in#i := M[Net#a][R[Net#a]];
  R[Net#a] := R[Net#a] + 1;
  C[Net#a] := C[Net#a] - 1;
  M[Net#b][R[Net#b] + C[Net#b]] := ActorVar#X[in#i];
  C[Net#b] := C[Net#b] + 1;
  assert {:msg "  Sub-actor action at 7.3 might not preserve the channel invariant (generated #6)"} 0 <= R[Net#a];
  assert {:msg "  Sub-actor action at 7.3 might not preserve the channel invariant (generated #7)"} 0 <= C[Net#a];
  assert {:msg "  Sub-actor action at 7.3 might not preserve the channel invariant (generated #8)"} (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assert {:msg "  Sub-actor action at 7.3 might not preserve the channel invariant (generated #9)"} 0 <= R[Net#b];
  assert {:msg "  Sub-actor action at 7.3 might not preserve the channel invariant (generated #10)"} 0 <= C[Net#b];
  assert {:msg "  Sub-actor action at 7.3 might not preserve the channel invariant (generated #11)"} R[Net#b] == 0;
  assert {:msg "  22.3: Sub-actor action at 7.3 might not preserve the channel invariant"} (0 <= M[Net#a][0]) && (M[Net#a][0] < 3);
  assert {:msg "  23.3: Sub-actor action at 7.3 might not preserve the channel invariant"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  24.3: Sub-actor action at 7.3 might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (10 <= M[Net#b][i]) && (M[Net#b][i] <= 12)
  );
  assert {:msg "  25.3: Sub-actor action at 7.3 might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> ((M[Net#a][i] == 0) ==> (M[Net#b][i] == 10))
  );
}
procedure Net#anon$1#exit#3()
  modifies C, R, M, St;
{
  var ActionVar#y: int;
  assume C#init[Net#a] == 1;
  assume C#init[Net#b] == 0;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume R[Net#b] == 0;
  assume (0 <= M[Net#a][0]) && (M[Net#a][0] < 3);
  assume R[Net#a] == (R[Net#b] + C[Net#b]);
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (10 <= M[Net#b][i]) && (M[Net#b][i] <= 12)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> ((M[Net#a][i] == 0) ==> (M[Net#b][i] == 10))
  );
  assume !((1 <= C[Net#a]) && (0 <= M[Net#a][R[Net#a] - 0]) && (M[Net#a][R[Net#a] - 0] < 3));
  assert {:msg "  16.3: The network might leave unread tokens on channel a"} C[Net#a] == 0;
  assert {:msg "  16.3: The network might not produce the specified number of tokens on output out"} C[Net#b] == 1;
  ActionVar#y := M[Net#b][0];
  assert {:msg "  19.14: Postcondition might not hold"} (M[Net#a][0] == 0) ==> (ActionVar#y == 10);
  R[Net#b] := R[Net#b] + C[Net#b];
  C[Net#b] := 0;
}

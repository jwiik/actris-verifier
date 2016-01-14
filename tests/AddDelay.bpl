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

procedure Add#anon$0#0()
  modifies C, R, M, St;
{
  var IV#in1#i: int;
  var IV#in2#j: int;
  assume true;
}
procedure Delay#anon$1#1()
  modifies C, R, M, St;
{
  assume true;
}
procedure Delay#anon$2#2()
  modifies C, R, M, St;
{
  var IV#in#i: int;
  assume true;
}
procedure Net#init#3()
  modifies C, R, M, St;
{
  var ActorParam#del#k: int;
  assume C[Net#a] == 0;
  assume R[Net#a] == 0;
  assume C[Net#b] == 0;
  assume R[Net#b] == 0;
  assume C[Net#c] == 0;
  assume R[Net#c] == 0;
  assume C[Net#d] == 0;
  assume R[Net#d] == 0;
  assume ActorParam#del#k == 0;
  M[Net#b][R[Net#b] + C[Net#b]] := ActorParam#del#k;
  C[Net#b] := C[Net#b] + 1;
  C[Net#b] := C[Net#b] - 1;
  assert {:msg "  19.13: Network initialization might not establish the network invariant"} (M[Net#b][R[Net#b]] == M[Net#c][R[Net#c] - 1]) || (M[Net#b][R[Net#b]] == 0);
}
const unique Net#add: Actor;
const unique Net#del: Actor;
const unique Net#a: Chan (int);
const unique Net#b: Chan (int);
const unique Net#c: Chan (int);
const unique Net#d: Chan (int);
procedure Net#anon$3#entry#4()
  modifies C, R, M, St;
{
  var ActionPH#y: int;
  assume C#init[Net#a] == 1;
  assume C#init[Net#b] == 0;
  assume C#init[Net#c] == 0;
  assume C#init[Net#d] == 0;
  assume R[Net#a] == 0;
  assume R[Net#b] == 0;
  assume R[Net#c] == 0;
  assume R[Net#d] == 0;
  assume C#init == C;
  C[Net#b] := C[Net#b] + 1;
  assume (M[Net#b][R[Net#b]] == M[Net#c][R[Net#c] - 1]) || (M[Net#b][R[Net#b]] == 0);
  assert {:msg "  Channel invariant might not hold on action entry (generated #0)"} 0 <= R[Net#a];
  assert {:msg "  Channel invariant might not hold on action entry (generated #1)"} 0 <= C[Net#a];
  assert {:msg "  Channel invariant might not hold on action entry (generated #2)"} (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assert {:msg "  Channel invariant might not hold on action entry (generated #3)"} 0 <= R[Net#b];
  assert {:msg "  Channel invariant might not hold on action entry (generated #4)"} 0 <= C[Net#b];
  assert {:msg "  Channel invariant might not hold on action entry (generated #5)"} 0 <= R[Net#c];
  assert {:msg "  Channel invariant might not hold on action entry (generated #6)"} 0 <= C[Net#c];
  assert {:msg "  Channel invariant might not hold on action entry (generated #7)"} R[Net#c] == 0;
  assert {:msg "  Channel invariant might not hold on action entry (generated #8)"} 0 <= R[Net#d];
  assert {:msg "  Channel invariant might not hold on action entry (generated #9)"} 0 <= C[Net#d];
  assert {:msg "  Channel invariant might not hold on action entry (generated #10)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Channel invariant might not hold on action entry (generated #11)"} R[Net#b] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Channel invariant might not hold on action entry (generated #12)"} R[Net#a] == (R[Net#d] + C[Net#d]);
  assert {:msg "  Channel invariant might not hold on action entry (generated #13)"} R[Net#b] == (R[Net#d] + C[Net#d]);
  assert {:msg "  Channel invariant might not hold on action entry (generated #14)"} R[Net#d] == ((R[Net#b] + C[Net#b]) - 1);
  assert {:msg "  Channel invariant might not hold on action entry (generated #15)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assert {:msg "  Channel invariant might not hold on action entry (generated #16)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assert {:msg "  Channel invariant might not hold on action entry (generated #17)"} (forall idx$: int :: 
    (1 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#d][idx$ - 1])
  );
  assert {:msg "  21.3: Channel invariant might not hold on action entry"} (M[Net#b][0] == M[Net#c][-1]) || (M[Net#b][0] == 0);
}
procedure Net#anon$3#Add#anon$0#5()
  modifies C, R, M, St;
{
  var ActionPH#y: int;
  var St#next: State;
  var in1#i: int;
  var in2#j: int;
  assume C#init[Net#a] == 1;
  assume C#init[Net#b] == 0;
  assume C#init[Net#c] == 0;
  assume C#init[Net#d] == 0;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume R[Net#c] == 0;
  assume 0 <= R[Net#d];
  assume 0 <= C[Net#d];
  assume R[Net#a] == (R[Net#c] + C[Net#c]);
  assume R[Net#b] == (R[Net#c] + C[Net#c]);
  assume R[Net#a] == (R[Net#d] + C[Net#d]);
  assume R[Net#b] == (R[Net#d] + C[Net#d]);
  assume R[Net#d] == ((R[Net#b] + C[Net#b]) - 1);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#d][idx$ - 1])
  );
  assume (M[Net#b][0] == M[Net#c][-1]) || (M[Net#b][0] == 0);
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
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #18)"} 0 <= R[Net#a];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #19)"} 0 <= C[Net#a];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #20)"} (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #21)"} 0 <= R[Net#b];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #22)"} 0 <= C[Net#b];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #23)"} 0 <= R[Net#c];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #24)"} 0 <= C[Net#c];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #25)"} R[Net#c] == 0;
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #26)"} 0 <= R[Net#d];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #27)"} 0 <= C[Net#d];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #28)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #29)"} R[Net#b] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #30)"} R[Net#a] == (R[Net#d] + C[Net#d]);
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #31)"} R[Net#b] == (R[Net#d] + C[Net#d]);
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #32)"} R[Net#d] == ((R[Net#b] + C[Net#b]) - 1);
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #33)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #34)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #35)"} (forall idx$: int :: 
    (1 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#d][idx$ - 1])
  );
  assert {:msg "  21.3: Sub-actor action at 3.3 might not preserve the channel invariant"} (M[Net#b][0] == M[Net#c][-1]) || (M[Net#b][0] == 0);
}
procedure Net#anon$3#Delay#anon$2#6()
  modifies C, R, M, St;
{
  var ActionPH#y: int;
  var ActorParam#k: int;
  var St#next: State;
  var in#i: int;
  assume ActorParam#k == 0;
  assume C#init[Net#a] == 1;
  assume C#init[Net#b] == 0;
  assume C#init[Net#c] == 0;
  assume C#init[Net#d] == 0;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume R[Net#c] == 0;
  assume 0 <= R[Net#d];
  assume 0 <= C[Net#d];
  assume R[Net#a] == (R[Net#c] + C[Net#c]);
  assume R[Net#b] == (R[Net#c] + C[Net#c]);
  assume R[Net#a] == (R[Net#d] + C[Net#d]);
  assume R[Net#b] == (R[Net#d] + C[Net#d]);
  assume R[Net#d] == ((R[Net#b] + C[Net#b]) - 1);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#d][idx$ - 1])
  );
  assume (M[Net#b][0] == M[Net#c][-1]) || (M[Net#b][0] == 0);
  assume true;
  assume 1 <= C[Net#d];
  in#i := M[Net#d][R[Net#d]];
  R[Net#d] := R[Net#d] + 1;
  C[Net#d] := C[Net#d] - 1;
  M[Net#b][R[Net#b] + C[Net#b]] := in#i;
  C[Net#b] := C[Net#b] + 1;
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #36)"} 0 <= R[Net#a];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #37)"} 0 <= C[Net#a];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #38)"} (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #39)"} 0 <= R[Net#b];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #40)"} 0 <= C[Net#b];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #41)"} 0 <= R[Net#c];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #42)"} 0 <= C[Net#c];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #43)"} R[Net#c] == 0;
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #44)"} 0 <= R[Net#d];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #45)"} 0 <= C[Net#d];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #46)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #47)"} R[Net#b] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #48)"} R[Net#a] == (R[Net#d] + C[Net#d]);
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #49)"} R[Net#b] == (R[Net#d] + C[Net#d]);
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #50)"} R[Net#d] == ((R[Net#b] + C[Net#b]) - 1);
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #51)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #52)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #53)"} (forall idx$: int :: 
    (1 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#d][idx$ - 1])
  );
  assert {:msg "  21.3: Sub-actor action at 9.3 might not preserve the channel invariant"} (M[Net#b][0] == M[Net#c][-1]) || (M[Net#b][0] == 0);
}
procedure Net#anon$3#exit#7()
  modifies C, R, M, St;
{
  var ActionPH#y: int;
  assume C#init[Net#a] == 1;
  assume C#init[Net#b] == 0;
  assume C#init[Net#c] == 0;
  assume C#init[Net#d] == 0;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume R[Net#c] == 0;
  assume 0 <= R[Net#d];
  assume 0 <= C[Net#d];
  assume R[Net#a] == (R[Net#c] + C[Net#c]);
  assume R[Net#b] == (R[Net#c] + C[Net#c]);
  assume R[Net#a] == (R[Net#d] + C[Net#d]);
  assume R[Net#b] == (R[Net#d] + C[Net#d]);
  assume R[Net#d] == ((R[Net#b] + C[Net#b]) - 1);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#d][idx$ - 1])
  );
  assume (M[Net#b][0] == M[Net#c][-1]) || (M[Net#b][0] == 0);
  assume !(((1 <= C[Net#a]) && (1 <= C[Net#b])) || (1 <= C[Net#d]));
  ActionPH#y := M[Net#c][0];
  assert {:msg "  15.13: Network action postcondition might not hold"} (ActionPH#y == (M[Net#c][R[Net#c] - 1] + M[Net#a][0])) || (ActionPH#y == M[Net#a][0]);
  R[Net#c] := R[Net#c] + C[Net#c];
  C[Net#c] := C[Net#c] - 1;
  C[Net#b] := C[Net#b] - 1;
  assert {:msg "  19.13: The network might not preserve the network invariant"} (M[Net#b][R[Net#b]] == M[Net#c][R[Net#c] - 1]) || (M[Net#b][R[Net#b]] == 0);
  assert {:msg "  14.3: The network might leave unread tokens on channel a"} C[Net#a] == 0;
  assert {:msg "  14.3: The network might leave unread tokens on channel b"} C[Net#b] == 0;
  assert {:msg "  14.3: The network might not produce the specified number of tokens on output out"} C[Net#c] == 0;
  assert {:msg "  14.3: The network might leave unread tokens on channel d"} C[Net#d] == 0;
}

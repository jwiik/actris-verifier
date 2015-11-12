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

procedure Add#anon$0#0()
  modifies C, R, M, St;
{
  var i: int;
  var j: int;
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
  var i: int;
  assume true;
}
const unique Net#add: Actor;
const unique Net#del: Actor;
const unique Net#a: Chan (int);
const unique Net#b: Chan (int);
const unique Net#c: Chan (int);
const unique Net#d: Chan (int);
procedure Net#anon$3#entry#3()
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
  assert {:msg "  Channel invariant might not hold on action entry (generated #0 )"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < ((R[Net#b] + C[Net#b]) - 1)) ==> (M[Net#b][(idx$ + 1) - 0] == M[Net#d][idx$ - 0])
  );
  assert {:msg "  Channel invariant might not hold on action entry (generated #1 )"} R[Net#d] == ((R[Net#b] + C[Net#b]) - 1);
  assert {:msg "  Channel invariant might not hold on action entry (generated #2 )"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$ - 0] == (M[Net#a][idx$ - 0] + M[Net#b][idx$ - 0]))
  );
  assert {:msg "  Channel invariant might not hold on action entry (generated #3 )"} R[Net#b] == (R[Net#d] + C[Net#d]);
  assert {:msg "  Channel invariant might not hold on action entry (generated #4 )"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$ - 0] == (M[Net#a][idx$ - 0] + M[Net#b][idx$ - 0]))
  );
  assert {:msg "  Channel invariant might not hold on action entry (generated #5 )"} R[Net#b] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Channel invariant might not hold on action entry (generated #6 )"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$ - 0] == (M[Net#a][idx$ - 0] + M[Net#b][idx$ - 0]))
  );
  assert {:msg "  Channel invariant might not hold on action entry (generated #7 )"} R[Net#a] == (R[Net#d] + C[Net#d]);
  assert {:msg "  Channel invariant might not hold on action entry (generated #8 )"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$ - 0] == (M[Net#a][idx$ - 0] + M[Net#b][idx$ - 0]))
  );
  assert {:msg "  Channel invariant might not hold on action entry (generated #9 )"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Channel invariant might not hold on action entry (generated #10 )"} 0 <= C[Net#d];
  assert {:msg "  Channel invariant might not hold on action entry (generated #11 )"} 0 <= R[Net#d];
  assert {:msg "  Channel invariant might not hold on action entry (generated #12 )"} R[Net#c] == 0;
  assert {:msg "  Channel invariant might not hold on action entry (generated #13 )"} 0 <= C[Net#c];
  assert {:msg "  Channel invariant might not hold on action entry (generated #14 )"} 0 <= R[Net#c];
  assert {:msg "  Channel invariant might not hold on action entry (generated #15 )"} 0 <= C[Net#b];
  assert {:msg "  Channel invariant might not hold on action entry (generated #16 )"} 0 <= R[Net#b];
  assert {:msg "  Channel invariant might not hold on action entry (generated #17 )"} (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assert {:msg "  Channel invariant might not hold on action entry (generated #18 )"} 0 <= C[Net#a];
  assert {:msg "  Channel invariant might not hold on action entry (generated #19 )"} 0 <= R[Net#a];
  assert {:msg "  18.3: Channel invariant might not hold on action entry"} M[Net#b][0] == M[Net#c][-1];
}
procedure Net#anon$3#Add#anon$0#4()
  modifies C, R, M, St;
{
  var St#next: State;
  var in1#i: int;
  var in2#j: int;
  assume C#init[Net#a] == 1;
  assume C#init[Net#c] == 0;
  assume C#init[Net#d] == 0;
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < ((R[Net#b] + C[Net#b]) - 1)) ==> (M[Net#b][(idx$ + 1) - 0] == M[Net#d][idx$ - 0])
  );
  assume R[Net#d] == ((R[Net#b] + C[Net#b]) - 1);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$ - 0] == (M[Net#a][idx$ - 0] + M[Net#b][idx$ - 0]))
  );
  assume R[Net#b] == (R[Net#d] + C[Net#d]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$ - 0] == (M[Net#a][idx$ - 0] + M[Net#b][idx$ - 0]))
  );
  assume R[Net#b] == (R[Net#c] + C[Net#c]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$ - 0] == (M[Net#a][idx$ - 0] + M[Net#b][idx$ - 0]))
  );
  assume R[Net#a] == (R[Net#d] + C[Net#d]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$ - 0] == (M[Net#a][idx$ - 0] + M[Net#b][idx$ - 0]))
  );
  assume R[Net#a] == (R[Net#c] + C[Net#c]);
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
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #20)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < ((R[Net#b] + C[Net#b]) - 1)) ==> (M[Net#b][(idx$ + 1) - 0] == M[Net#d][idx$ - 0])
  );
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #21)"} R[Net#d] == ((R[Net#b] + C[Net#b]) - 1);
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #22)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$ - 0] == (M[Net#a][idx$ - 0] + M[Net#b][idx$ - 0]))
  );
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #23)"} R[Net#b] == (R[Net#d] + C[Net#d]);
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #24)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$ - 0] == (M[Net#a][idx$ - 0] + M[Net#b][idx$ - 0]))
  );
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #25)"} R[Net#b] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #26)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$ - 0] == (M[Net#a][idx$ - 0] + M[Net#b][idx$ - 0]))
  );
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #27)"} R[Net#a] == (R[Net#d] + C[Net#d]);
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #28)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$ - 0] == (M[Net#a][idx$ - 0] + M[Net#b][idx$ - 0]))
  );
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #29)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #30)"} 0 <= C[Net#d];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #31)"} 0 <= R[Net#d];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #32)"} R[Net#c] == 0;
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #33)"} 0 <= C[Net#c];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #34)"} 0 <= R[Net#c];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #35)"} 0 <= C[Net#b];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #36)"} 0 <= R[Net#b];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #37)"} (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #38)"} 0 <= C[Net#a];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #39)"} 0 <= R[Net#a];
  assert {:msg "  18.3: Sub-actor action at 3.3 might not preserve the channel invariant"} M[Net#b][0] == M[Net#c][-1];
}
procedure Net#anon$3#Delay#anon$2#5()
  modifies C, R, M, St;
{
  var ActorParam#k: int;
  var St#next: State;
  var in#i: int;
  assume ActorParam#k == 0;
  assume C#init[Net#a] == 1;
  assume C#init[Net#c] == 0;
  assume C#init[Net#d] == 0;
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < ((R[Net#b] + C[Net#b]) - 1)) ==> (M[Net#b][(idx$ + 1) - 0] == M[Net#d][idx$ - 0])
  );
  assume R[Net#d] == ((R[Net#b] + C[Net#b]) - 1);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$ - 0] == (M[Net#a][idx$ - 0] + M[Net#b][idx$ - 0]))
  );
  assume R[Net#b] == (R[Net#d] + C[Net#d]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$ - 0] == (M[Net#a][idx$ - 0] + M[Net#b][idx$ - 0]))
  );
  assume R[Net#b] == (R[Net#c] + C[Net#c]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$ - 0] == (M[Net#a][idx$ - 0] + M[Net#b][idx$ - 0]))
  );
  assume R[Net#a] == (R[Net#d] + C[Net#d]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$ - 0] == (M[Net#a][idx$ - 0] + M[Net#b][idx$ - 0]))
  );
  assume R[Net#a] == (R[Net#c] + C[Net#c]);
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
  assume M[Net#b][0] == M[Net#c][-1];
  assume true;
  assume 1 <= C[Net#d];
  in#i := M[Net#d][R[Net#d]];
  R[Net#d] := R[Net#d] + 1;
  C[Net#d] := C[Net#d] - 1;
  M[Net#b][R[Net#b] + C[Net#b]] := in#i;
  C[Net#b] := C[Net#b] + 1;
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #40)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < ((R[Net#b] + C[Net#b]) - 1)) ==> (M[Net#b][(idx$ + 1) - 0] == M[Net#d][idx$ - 0])
  );
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #41)"} R[Net#d] == ((R[Net#b] + C[Net#b]) - 1);
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #42)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$ - 0] == (M[Net#a][idx$ - 0] + M[Net#b][idx$ - 0]))
  );
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #43)"} R[Net#b] == (R[Net#d] + C[Net#d]);
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #44)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$ - 0] == (M[Net#a][idx$ - 0] + M[Net#b][idx$ - 0]))
  );
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #45)"} R[Net#b] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #46)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$ - 0] == (M[Net#a][idx$ - 0] + M[Net#b][idx$ - 0]))
  );
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #47)"} R[Net#a] == (R[Net#d] + C[Net#d]);
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #48)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$ - 0] == (M[Net#a][idx$ - 0] + M[Net#b][idx$ - 0]))
  );
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #49)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #50)"} 0 <= C[Net#d];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #51)"} 0 <= R[Net#d];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #52)"} R[Net#c] == 0;
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #53)"} 0 <= C[Net#c];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #54)"} 0 <= R[Net#c];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #55)"} 0 <= C[Net#b];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #56)"} 0 <= R[Net#b];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #57)"} (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #58)"} 0 <= C[Net#a];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #59)"} 0 <= R[Net#a];
  assert {:msg "  18.3: Sub-actor action at 9.3 might not preserve the channel invariant"} M[Net#b][0] == M[Net#c][-1];
}
procedure Net#anon$3#exit#6()
  modifies C, R, M, St;
{
  assume C#init[Net#a] == 1;
  assume C#init[Net#c] == 0;
  assume C#init[Net#d] == 0;
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < ((R[Net#b] + C[Net#b]) - 1)) ==> (M[Net#b][(idx$ + 1) - 0] == M[Net#d][idx$ - 0])
  );
  assume R[Net#d] == ((R[Net#b] + C[Net#b]) - 1);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$ - 0] == (M[Net#a][idx$ - 0] + M[Net#b][idx$ - 0]))
  );
  assume R[Net#b] == (R[Net#d] + C[Net#d]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$ - 0] == (M[Net#a][idx$ - 0] + M[Net#b][idx$ - 0]))
  );
  assume R[Net#b] == (R[Net#c] + C[Net#c]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$ - 0] == (M[Net#a][idx$ - 0] + M[Net#b][idx$ - 0]))
  );
  assume R[Net#a] == (R[Net#d] + C[Net#d]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$ - 0] == (M[Net#a][idx$ - 0] + M[Net#b][idx$ - 0]))
  );
  assume R[Net#a] == (R[Net#c] + C[Net#c]);
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
  assume M[Net#b][0] == M[Net#c][-1];
  assume !(((1 <= C[Net#a]) && (1 <= C[Net#b])) || (1 <= C[Net#d]));
  assert {:msg "  13.3: The network might leave unread tokens on channel a"} C[Net#a] == 0;
  assert {:msg "  13.3: The network might not produce the specified number of tokens on output out"} C[Net#c] == 1;
  assert {:msg "  13.3: The network might leave unread tokens on channel d"} C[Net#d] == 0;
  assert {:msg "  13.26: Network output might not conform to specified action output"} M[Net#c][0] == (M[Net#c][R[Net#c] - 1] + M[Net#a][0]);
  R[Net#c] := R[Net#c] + C[Net#c];
  C[Net#c] := 0;
  assert {:msg "  15.3: The network might not preserve the network invariant"} C[Net#b] == 1;
  assert {:msg "  16.3: The network might not preserve the network invariant"} M[Net#b][R[Net#b]] == M[Net#c][R[Net#c] - 1];
}

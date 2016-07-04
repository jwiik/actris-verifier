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

procedure Split#anon$0#0()
  modifies C, R, M, St;
{
  var IV#in#i: int;
  assume true;
}
procedure Split#anon$1#1()
  modifies C, R, M, St;
{
  var IV#in#i: int;
  assume true;
}
procedure Delay#anon$2#2()
  modifies C, R, M, St;
{
  assume true;
}
procedure Delay#anon$3#3()
  modifies C, R, M, St;
{
  var IV#in#i: int;
  assume true;
}
procedure Repeater#anon$4#4()
  modifies C, R, M, St;
{
  var IV#in1#i: int;
  assume true;
}
procedure Repeater#anon$5#5()
  modifies C, R, M, St;
{
  var IV#in2#i: int;
  assume true;
}
procedure Livelock#init#6()
  modifies C, R, M, St;
{
  var ActorParam#del#k: int;
  assume C[Livelock#a] == 0;
  assume R[Livelock#a] == 0;
  assume C[Livelock#b] == 0;
  assume R[Livelock#b] == 0;
  assume C[Livelock#c] == 0;
  assume R[Livelock#c] == 0;
  assume C[Livelock#d] == 0;
  assume R[Livelock#d] == 0;
  assume C[Livelock#e] == 0;
  assume R[Livelock#e] == 0;
  assume ActorParam#del#k == 0;
  M[Livelock#e][R[Livelock#e] + C[Livelock#e]] := ActorParam#del#k;
  C[Livelock#e] := C[Livelock#e] + 1;
}
const unique Livelock#spl: Actor;
const unique Livelock#rep: Actor;
const unique Livelock#del: Actor;
const unique Livelock#a: Chan (int);
const unique Livelock#b: Chan (int);
const unique Livelock#c: Chan (int);
const unique Livelock#d: Chan (int);
const unique Livelock#e: Chan (int);
procedure Livelock#anon$6#entry#7()
  modifies C, R, M, St;
{
  var ActionPH#y: int;
  assume C#init[Livelock#a] == 1;
  assume C#init[Livelock#b] == 0;
  assume C#init[Livelock#c] == 0;
  assume C#init[Livelock#d] == 0;
  assume C#init[Livelock#e] == 0;
  assume R[Livelock#a] == 0;
  assume R[Livelock#b] == 0;
  assume R[Livelock#c] == 0;
  assume R[Livelock#d] == 0;
  assume R[Livelock#e] == 0;
  assume C#init == C;
  assert {:msg "  Channel invariant might not hold on action entry (generated #0)"} 0 <= R[Livelock#a];
  assert {:msg "  Channel invariant might not hold on action entry (generated #1)"} 0 <= C[Livelock#a];
  assert {:msg "  Channel invariant might not hold on action entry (generated #2)"} (R[Livelock#a] + C[Livelock#a]) == C#init[Livelock#a];
  assert {:msg "  Channel invariant might not hold on action entry (generated #3)"} 0 <= R[Livelock#b];
  assert {:msg "  Channel invariant might not hold on action entry (generated #4)"} 0 <= C[Livelock#b];
  assert {:msg "  Channel invariant might not hold on action entry (generated #5)"} R[Livelock#b] == 0;
  assert {:msg "  Channel invariant might not hold on action entry (generated #6)"} 0 <= R[Livelock#c];
  assert {:msg "  Channel invariant might not hold on action entry (generated #7)"} 0 <= C[Livelock#c];
  assert {:msg "  Channel invariant might not hold on action entry (generated #8)"} 0 <= R[Livelock#d];
  assert {:msg "  Channel invariant might not hold on action entry (generated #9)"} 0 <= C[Livelock#d];
  assert {:msg "  Channel invariant might not hold on action entry (generated #10)"} 0 <= R[Livelock#e];
  assert {:msg "  Channel invariant might not hold on action entry (generated #11)"} 0 <= C[Livelock#e];
  assert {:msg "  Channel invariant might not hold on action entry (generated #12)"} R[Livelock#d] == (R[Livelock#e] + C[Livelock#e]);
  assert {:msg "  Channel invariant might not hold on action entry (generated #13)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Livelock#e] + C[Livelock#e])) ==> (M[Livelock#e][idx$] == M[Livelock#d][idx$])
  );
}
procedure Livelock#anon$6#Split#anon$0#8()
  modifies C, R, M, St;
{
  var ActionPH#y: int;
  var St#next: State;
  var in#i: int;
  assume C#init[Livelock#a] == 1;
  assume C#init[Livelock#b] == 0;
  assume C#init[Livelock#c] == 0;
  assume C#init[Livelock#d] == 0;
  assume C#init[Livelock#e] == 0;
  assume 0 <= R[Livelock#a];
  assume 0 <= C[Livelock#a];
  assume (R[Livelock#a] + C[Livelock#a]) == C#init[Livelock#a];
  assume 0 <= R[Livelock#b];
  assume 0 <= C[Livelock#b];
  assume R[Livelock#b] == 0;
  assume 0 <= R[Livelock#c];
  assume 0 <= C[Livelock#c];
  assume 0 <= R[Livelock#d];
  assume 0 <= C[Livelock#d];
  assume 0 <= R[Livelock#e];
  assume 0 <= C[Livelock#e];
  assume R[Livelock#d] == (R[Livelock#e] + C[Livelock#e]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Livelock#e] + C[Livelock#e])) ==> (M[Livelock#e][idx$] == M[Livelock#d][idx$])
  );
  assume true;
  assume 1 <= C[Livelock#a];
  in#i := M[Livelock#a][R[Livelock#a]];
  R[Livelock#a] := R[Livelock#a] + 1;
  C[Livelock#a] := C[Livelock#a] - 1;
  M[Livelock#b][R[Livelock#b] + C[Livelock#b]] := in#i;
  C[Livelock#b] := C[Livelock#b] + 1;
  M[Livelock#c][R[Livelock#c] + C[Livelock#c]] := in#i;
  C[Livelock#c] := C[Livelock#c] + 1;
  assert {:msg "  Sub-actor action at 2.3 might not preserve the channel invariant (generated #14)"} 0 <= R[Livelock#a];
  assert {:msg "  Sub-actor action at 2.3 might not preserve the channel invariant (generated #15)"} 0 <= C[Livelock#a];
  assert {:msg "  Sub-actor action at 2.3 might not preserve the channel invariant (generated #16)"} (R[Livelock#a] + C[Livelock#a]) == C#init[Livelock#a];
  assert {:msg "  Sub-actor action at 2.3 might not preserve the channel invariant (generated #17)"} 0 <= R[Livelock#b];
  assert {:msg "  Sub-actor action at 2.3 might not preserve the channel invariant (generated #18)"} 0 <= C[Livelock#b];
  assert {:msg "  Sub-actor action at 2.3 might not preserve the channel invariant (generated #19)"} R[Livelock#b] == 0;
  assert {:msg "  Sub-actor action at 2.3 might not preserve the channel invariant (generated #20)"} 0 <= R[Livelock#c];
  assert {:msg "  Sub-actor action at 2.3 might not preserve the channel invariant (generated #21)"} 0 <= C[Livelock#c];
  assert {:msg "  Sub-actor action at 2.3 might not preserve the channel invariant (generated #22)"} 0 <= R[Livelock#d];
  assert {:msg "  Sub-actor action at 2.3 might not preserve the channel invariant (generated #23)"} 0 <= C[Livelock#d];
  assert {:msg "  Sub-actor action at 2.3 might not preserve the channel invariant (generated #24)"} 0 <= R[Livelock#e];
  assert {:msg "  Sub-actor action at 2.3 might not preserve the channel invariant (generated #25)"} 0 <= C[Livelock#e];
  assert {:msg "  Sub-actor action at 2.3 might not preserve the channel invariant (generated #26)"} R[Livelock#d] == (R[Livelock#e] + C[Livelock#e]);
  assert {:msg "  Sub-actor action at 2.3 might not preserve the channel invariant (generated #27)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Livelock#e] + C[Livelock#e])) ==> (M[Livelock#e][idx$] == M[Livelock#d][idx$])
  );
}
procedure Livelock#anon$6#Split#anon$1#9()
  modifies C, R, M, St;
{
  var ActionPH#y: int;
  var St#next: State;
  var in#i: int;
  assume C#init[Livelock#a] == 1;
  assume C#init[Livelock#b] == 0;
  assume C#init[Livelock#c] == 0;
  assume C#init[Livelock#d] == 0;
  assume C#init[Livelock#e] == 0;
  assume 0 <= R[Livelock#a];
  assume 0 <= C[Livelock#a];
  assume (R[Livelock#a] + C[Livelock#a]) == C#init[Livelock#a];
  assume 0 <= R[Livelock#b];
  assume 0 <= C[Livelock#b];
  assume R[Livelock#b] == 0;
  assume 0 <= R[Livelock#c];
  assume 0 <= C[Livelock#c];
  assume 0 <= R[Livelock#d];
  assume 0 <= C[Livelock#d];
  assume 0 <= R[Livelock#e];
  assume 0 <= C[Livelock#e];
  assume R[Livelock#d] == (R[Livelock#e] + C[Livelock#e]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Livelock#e] + C[Livelock#e])) ==> (M[Livelock#e][idx$] == M[Livelock#d][idx$])
  );
  assume true;
  assume 1 <= C[Livelock#a];
  in#i := M[Livelock#a][R[Livelock#a]];
  R[Livelock#a] := R[Livelock#a] + 1;
  C[Livelock#a] := C[Livelock#a] - 1;
  M[Livelock#c][R[Livelock#c] + C[Livelock#c]] := in#i;
  C[Livelock#c] := C[Livelock#c] + 1;
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #28)"} 0 <= R[Livelock#a];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #29)"} 0 <= C[Livelock#a];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #30)"} (R[Livelock#a] + C[Livelock#a]) == C#init[Livelock#a];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #31)"} 0 <= R[Livelock#b];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #32)"} 0 <= C[Livelock#b];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #33)"} R[Livelock#b] == 0;
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #34)"} 0 <= R[Livelock#c];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #35)"} 0 <= C[Livelock#c];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #36)"} 0 <= R[Livelock#d];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #37)"} 0 <= C[Livelock#d];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #38)"} 0 <= R[Livelock#e];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #39)"} 0 <= C[Livelock#e];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #40)"} R[Livelock#d] == (R[Livelock#e] + C[Livelock#e]);
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #41)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Livelock#e] + C[Livelock#e])) ==> (M[Livelock#e][idx$] == M[Livelock#d][idx$])
  );
}
procedure Livelock#anon$6#Repeater#anon$4#10()
  modifies C, R, M, St;
{
  var ActionPH#y: int;
  var St#next: State;
  var in1#i: int;
  assume C#init[Livelock#a] == 1;
  assume C#init[Livelock#b] == 0;
  assume C#init[Livelock#c] == 0;
  assume C#init[Livelock#d] == 0;
  assume C#init[Livelock#e] == 0;
  assume 0 <= R[Livelock#a];
  assume 0 <= C[Livelock#a];
  assume (R[Livelock#a] + C[Livelock#a]) == C#init[Livelock#a];
  assume 0 <= R[Livelock#b];
  assume 0 <= C[Livelock#b];
  assume R[Livelock#b] == 0;
  assume 0 <= R[Livelock#c];
  assume 0 <= C[Livelock#c];
  assume 0 <= R[Livelock#d];
  assume 0 <= C[Livelock#d];
  assume 0 <= R[Livelock#e];
  assume 0 <= C[Livelock#e];
  assume R[Livelock#d] == (R[Livelock#e] + C[Livelock#e]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Livelock#e] + C[Livelock#e])) ==> (M[Livelock#e][idx$] == M[Livelock#d][idx$])
  );
  assume true;
  assume 1 <= C[Livelock#c];
  in1#i := M[Livelock#c][R[Livelock#c]];
  R[Livelock#c] := R[Livelock#c] + 1;
  C[Livelock#c] := C[Livelock#c] - 1;
  M[Livelock#d][R[Livelock#d] + C[Livelock#d]] := in1#i;
  C[Livelock#d] := C[Livelock#d] + 1;
  assert {:msg "  Sub-actor action at 13.3 might not preserve the channel invariant (generated #42)"} 0 <= R[Livelock#a];
  assert {:msg "  Sub-actor action at 13.3 might not preserve the channel invariant (generated #43)"} 0 <= C[Livelock#a];
  assert {:msg "  Sub-actor action at 13.3 might not preserve the channel invariant (generated #44)"} (R[Livelock#a] + C[Livelock#a]) == C#init[Livelock#a];
  assert {:msg "  Sub-actor action at 13.3 might not preserve the channel invariant (generated #45)"} 0 <= R[Livelock#b];
  assert {:msg "  Sub-actor action at 13.3 might not preserve the channel invariant (generated #46)"} 0 <= C[Livelock#b];
  assert {:msg "  Sub-actor action at 13.3 might not preserve the channel invariant (generated #47)"} R[Livelock#b] == 0;
  assert {:msg "  Sub-actor action at 13.3 might not preserve the channel invariant (generated #48)"} 0 <= R[Livelock#c];
  assert {:msg "  Sub-actor action at 13.3 might not preserve the channel invariant (generated #49)"} 0 <= C[Livelock#c];
  assert {:msg "  Sub-actor action at 13.3 might not preserve the channel invariant (generated #50)"} 0 <= R[Livelock#d];
  assert {:msg "  Sub-actor action at 13.3 might not preserve the channel invariant (generated #51)"} 0 <= C[Livelock#d];
  assert {:msg "  Sub-actor action at 13.3 might not preserve the channel invariant (generated #52)"} 0 <= R[Livelock#e];
  assert {:msg "  Sub-actor action at 13.3 might not preserve the channel invariant (generated #53)"} 0 <= C[Livelock#e];
  assert {:msg "  Sub-actor action at 13.3 might not preserve the channel invariant (generated #54)"} R[Livelock#d] == (R[Livelock#e] + C[Livelock#e]);
  assert {:msg "  Sub-actor action at 13.3 might not preserve the channel invariant (generated #55)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Livelock#e] + C[Livelock#e])) ==> (M[Livelock#e][idx$] == M[Livelock#d][idx$])
  );
}
procedure Livelock#anon$6#Repeater#anon$5#11()
  modifies C, R, M, St;
{
  var ActionPH#y: int;
  var St#next: State;
  var in2#i: int;
  assume C#init[Livelock#a] == 1;
  assume C#init[Livelock#b] == 0;
  assume C#init[Livelock#c] == 0;
  assume C#init[Livelock#d] == 0;
  assume C#init[Livelock#e] == 0;
  assume 0 <= R[Livelock#a];
  assume 0 <= C[Livelock#a];
  assume (R[Livelock#a] + C[Livelock#a]) == C#init[Livelock#a];
  assume 0 <= R[Livelock#b];
  assume 0 <= C[Livelock#b];
  assume R[Livelock#b] == 0;
  assume 0 <= R[Livelock#c];
  assume 0 <= C[Livelock#c];
  assume 0 <= R[Livelock#d];
  assume 0 <= C[Livelock#d];
  assume 0 <= R[Livelock#e];
  assume 0 <= C[Livelock#e];
  assume R[Livelock#d] == (R[Livelock#e] + C[Livelock#e]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Livelock#e] + C[Livelock#e])) ==> (M[Livelock#e][idx$] == M[Livelock#d][idx$])
  );
  assume true;
  assume 1 <= C[Livelock#e];
  in2#i := M[Livelock#e][R[Livelock#e]];
  R[Livelock#e] := R[Livelock#e] + 1;
  C[Livelock#e] := C[Livelock#e] - 1;
  M[Livelock#d][R[Livelock#d] + C[Livelock#d]] := in2#i;
  C[Livelock#d] := C[Livelock#d] + 1;
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #56)"} 0 <= R[Livelock#a];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #57)"} 0 <= C[Livelock#a];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #58)"} (R[Livelock#a] + C[Livelock#a]) == C#init[Livelock#a];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #59)"} 0 <= R[Livelock#b];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #60)"} 0 <= C[Livelock#b];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #61)"} R[Livelock#b] == 0;
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #62)"} 0 <= R[Livelock#c];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #63)"} 0 <= C[Livelock#c];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #64)"} 0 <= R[Livelock#d];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #65)"} 0 <= C[Livelock#d];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #66)"} 0 <= R[Livelock#e];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #67)"} 0 <= C[Livelock#e];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #68)"} R[Livelock#d] == (R[Livelock#e] + C[Livelock#e]);
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #69)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Livelock#e] + C[Livelock#e])) ==> (M[Livelock#e][idx$] == M[Livelock#d][idx$])
  );
}
procedure Livelock#anon$6#Delay#anon$3#12()
  modifies C, R, M, St;
{
  var ActionPH#y: int;
  var ActorParam#k: int;
  var St#next: State;
  var in#i: int;
  assume ActorParam#k == 0;
  assume C#init[Livelock#a] == 1;
  assume C#init[Livelock#b] == 0;
  assume C#init[Livelock#c] == 0;
  assume C#init[Livelock#d] == 0;
  assume C#init[Livelock#e] == 0;
  assume 0 <= R[Livelock#a];
  assume 0 <= C[Livelock#a];
  assume (R[Livelock#a] + C[Livelock#a]) == C#init[Livelock#a];
  assume 0 <= R[Livelock#b];
  assume 0 <= C[Livelock#b];
  assume R[Livelock#b] == 0;
  assume 0 <= R[Livelock#c];
  assume 0 <= C[Livelock#c];
  assume 0 <= R[Livelock#d];
  assume 0 <= C[Livelock#d];
  assume 0 <= R[Livelock#e];
  assume 0 <= C[Livelock#e];
  assume R[Livelock#d] == (R[Livelock#e] + C[Livelock#e]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Livelock#e] + C[Livelock#e])) ==> (M[Livelock#e][idx$] == M[Livelock#d][idx$])
  );
  assume true;
  assume 1 <= C[Livelock#d];
  in#i := M[Livelock#d][R[Livelock#d]];
  R[Livelock#d] := R[Livelock#d] + 1;
  C[Livelock#d] := C[Livelock#d] - 1;
  M[Livelock#e][R[Livelock#e] + C[Livelock#e]] := in#i;
  C[Livelock#e] := C[Livelock#e] + 1;
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #70)"} 0 <= R[Livelock#a];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #71)"} 0 <= C[Livelock#a];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #72)"} (R[Livelock#a] + C[Livelock#a]) == C#init[Livelock#a];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #73)"} 0 <= R[Livelock#b];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #74)"} 0 <= C[Livelock#b];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #75)"} R[Livelock#b] == 0;
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #76)"} 0 <= R[Livelock#c];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #77)"} 0 <= C[Livelock#c];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #78)"} 0 <= R[Livelock#d];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #79)"} 0 <= C[Livelock#d];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #80)"} 0 <= R[Livelock#e];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #81)"} 0 <= C[Livelock#e];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #82)"} R[Livelock#d] == (R[Livelock#e] + C[Livelock#e]);
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #83)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Livelock#e] + C[Livelock#e])) ==> (M[Livelock#e][idx$] == M[Livelock#d][idx$])
  );
}
procedure Livelock#anon$6#exit#13()
  modifies C, R, M, St;
{
  var ActionPH#y: int;
  assume C#init[Livelock#a] == 1;
  assume C#init[Livelock#b] == 0;
  assume C#init[Livelock#c] == 0;
  assume C#init[Livelock#d] == 0;
  assume C#init[Livelock#e] == 0;
  assume 0 <= R[Livelock#a];
  assume 0 <= C[Livelock#a];
  assume (R[Livelock#a] + C[Livelock#a]) == C#init[Livelock#a];
  assume 0 <= R[Livelock#b];
  assume 0 <= C[Livelock#b];
  assume R[Livelock#b] == 0;
  assume 0 <= R[Livelock#c];
  assume 0 <= C[Livelock#c];
  assume 0 <= R[Livelock#d];
  assume 0 <= C[Livelock#d];
  assume 0 <= R[Livelock#e];
  assume 0 <= C[Livelock#e];
  assume R[Livelock#d] == (R[Livelock#e] + C[Livelock#e]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Livelock#e] + C[Livelock#e])) ==> (M[Livelock#e][idx$] == M[Livelock#d][idx$])
  );
  assume !(((((1 <= C[Livelock#a]) || (1 <= C[Livelock#a])) || (1 <= C[Livelock#c])) || (1 <= C[Livelock#e])) || (1 <= C[Livelock#d]));
  ActionPH#y := M[Livelock#b][0];
  R[Livelock#b] := R[Livelock#b] + C[Livelock#b];
  C[Livelock#b] := C[Livelock#b] - 1;
  assert {:msg "  19.3: The network might leave unread tokens on channel a"} C[Livelock#a] == 0;
  assert {:msg "  19.3: The network might not produce the specified number of tokens on output out"} C[Livelock#b] == 0;
  assert {:msg "  19.3: The network might leave unread tokens on channel c"} C[Livelock#c] == 0;
  assert {:msg "  19.3: The network might leave unread tokens on channel d"} C[Livelock#d] == 0;
  assert {:msg "  19.3: The network might leave unread tokens on channel e"} C[Livelock#e] == 0;
}

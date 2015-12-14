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


function AT#Abs(x: int): int { if 0 <= x then x else -x }
function AT#Div(int, int): int;
function AT#Mod(int, int): int;
axiom (forall a,b: int :: AT#Div(a,b)*b + AT#Mod(a,b) == a);
axiom (forall a,b: int :: 0 <= AT#Mod(a,b) && AT#Mod(a,b) < AT#Abs(b));

function AT#RShift(int, int): int;
function AT#LShift(int, int): int;
axiom (forall a: int :: (
  AT#RShift(a,1) == AT#Div(a,2) &&
  AT#RShift(a,2) == AT#Div(a,4) &&
  AT#RShift(a,3) == AT#Div(a,8) &&
  AT#RShift(a,4) == AT#Div(a,16) &&
  AT#RShift(a,5) == AT#Div(a,32) &&
  AT#RShift(a,6) == AT#Div(a,64) &&
  AT#RShift(a,7) == AT#Div(a,128) &&
  AT#RShift(a,8) == AT#Div(a,256)
));

// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

procedure add#anon$0#0()
  modifies C, R, M, St;
{
  var IV#in1#i: int;
  var IV#in2#j: int;
  assume true;
}
procedure delay#anon$1#1()
  modifies C, R, M, St;
{
  assume true;
}
procedure delay#anon$2#2()
  modifies C, R, M, St;
{
  var IV#in#i: int;
  assume true;
}
procedure mulc#anon$3#3()
  modifies C, R, M, St;
{
  var IV#in#i: int;
  assume true;
}
procedure rshift#anon$4#4()
  modifies C, R, M, St;
{
  var IV#in#i: int;
  assume true;
}
procedure iir#init#5()
  modifies C, R, M, St;
{
  var ActorParam#del1#k: int;
  var ActorParam#mul1#c: int;
  var ActorParam#mul2#c: int;
  var ActorParam#rsh1#s: int;
  assume C[iir#a] == 0;
  assume R[iir#a] == 0;
  assume C[iir#b] == 0;
  assume R[iir#b] == 0;
  assume C[iir#c] == 0;
  assume R[iir#c] == 0;
  assume C[iir#d] == 0;
  assume R[iir#d] == 0;
  assume C[iir#e] == 0;
  assume R[iir#e] == 0;
  assume C[iir#f] == 0;
  assume R[iir#f] == 0;
  assume C[iir#g] == 0;
  assume R[iir#g] == 0;
  assume ActorParam#del1#k == 0;
  M[iir#f][R[iir#f] + C[iir#f]] := ActorParam#del1#k;
  C[iir#f] := C[iir#f] + 1;
  assume ActorParam#mul1#c == 85;
  assume ActorParam#mul2#c == 171;
  assume ActorParam#rsh1#s == 8;
  assert {:msg "  Network initialization might not establish the network invariant"} iir#f == 1;
  assert {:msg "  Network initialization might not establish the network invariant"} M[iir#f][R[iir#f]] == (171 * M[iir#g][R[iir#g] - 1]);
}
const unique iir#del1: Actor;
const unique iir#mul1: Actor;
const unique iir#mul2: Actor;
const unique iir#rsh1: Actor;
const unique iir#add1: Actor;
const unique iir#a: Chan (int);
const unique iir#b: Chan (int);
const unique iir#c: Chan (int);
const unique iir#d: Chan (int);
const unique iir#e: Chan (int);
const unique iir#f: Chan (int);
const unique iir#g: Chan (int);
procedure iir#anon$5#entry#6()
  modifies C, R, M, St;
{
  var iir#out#0: int;
  assume C#init[iir#a] == 1;
  assume C#init[iir#b] == 0;
  assume C#init[iir#c] == 0;
  assume C#init[iir#d] == 0;
  assume C#init[iir#e] == 0;
  assume C#init[iir#g] == 0;
  assume R[iir#a] == 0;
  assume R[iir#b] == 0;
  assume R[iir#c] == 0;
  assume R[iir#d] == 0;
  assume R[iir#e] == 0;
  assume R[iir#f] == 0;
  assume R[iir#g] == 0;
  assume C#init == C;
  assume iir#f == 1;
  assume M[iir#f][R[iir#f]] == (171 * M[iir#g][R[iir#g] - 1]);
  assert {:msg "  Channel invariant might not hold on action entry (generated #0)"} 0 <= R[iir#a];
  assert {:msg "  Channel invariant might not hold on action entry (generated #1)"} 0 <= C[iir#a];
  assert {:msg "  Channel invariant might not hold on action entry (generated #2)"} (R[iir#a] + C[iir#a]) == C#init[iir#a];
  assert {:msg "  Channel invariant might not hold on action entry (generated #3)"} 0 <= R[iir#b];
  assert {:msg "  Channel invariant might not hold on action entry (generated #4)"} 0 <= C[iir#b];
  assert {:msg "  Channel invariant might not hold on action entry (generated #5)"} 0 <= R[iir#c];
  assert {:msg "  Channel invariant might not hold on action entry (generated #6)"} 0 <= C[iir#c];
  assert {:msg "  Channel invariant might not hold on action entry (generated #7)"} 0 <= R[iir#d];
  assert {:msg "  Channel invariant might not hold on action entry (generated #8)"} 0 <= C[iir#d];
  assert {:msg "  Channel invariant might not hold on action entry (generated #9)"} 0 <= R[iir#e];
  assert {:msg "  Channel invariant might not hold on action entry (generated #10)"} 0 <= C[iir#e];
  assert {:msg "  Channel invariant might not hold on action entry (generated #11)"} 0 <= R[iir#f];
  assert {:msg "  Channel invariant might not hold on action entry (generated #12)"} 0 <= C[iir#f];
  assert {:msg "  Channel invariant might not hold on action entry (generated #13)"} 0 <= R[iir#g];
  assert {:msg "  Channel invariant might not hold on action entry (generated #14)"} 0 <= C[iir#g];
  assert {:msg "  Channel invariant might not hold on action entry (generated #15)"} R[iir#g] == 0;
  assert {:msg "  Channel invariant might not hold on action entry (generated #16)"} R[iir#e] == ((R[iir#f] + C[iir#f]) - 1);
  assert {:msg "  Channel invariant might not hold on action entry (generated #17)"} R[iir#a] == (R[iir#b] + C[iir#b]);
  assert {:msg "  Channel invariant might not hold on action entry (generated #18)"} R[iir#d] == (R[iir#e] + C[iir#e]);
  assert {:msg "  Channel invariant might not hold on action entry (generated #19)"} R[iir#c] == (R[iir#d] + C[iir#d]);
  assert {:msg "  Channel invariant might not hold on action entry (generated #20)"} R[iir#c] == (R[iir#g] + C[iir#g]);
  assert {:msg "  Channel invariant might not hold on action entry (generated #21)"} R[iir#b] == (R[iir#c] + C[iir#c]);
  assert {:msg "  Channel invariant might not hold on action entry (generated #22)"} R[iir#f] == (R[iir#c] + C[iir#c]);
  assert {:msg "  Channel invariant might not hold on action entry (generated #23)"} (forall idx$: int :: 
    (1 <= idx$) && (idx$ < (R[iir#f] + C[iir#f])) ==> (M[iir#f][idx$] == M[iir#e][idx$ - 1])
  );
  assert {:msg "  Channel invariant might not hold on action entry (generated #24)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#b] + C[iir#b])) ==> (M[iir#b][idx$] == (85 * M[iir#a][idx$]))
  );
  assert {:msg "  Channel invariant might not hold on action entry (generated #25)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#e] + C[iir#e])) ==> (M[iir#e][idx$] == (171 * M[iir#d][idx$]))
  );
  assert {:msg "  Channel invariant might not hold on action entry (generated #26)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#d] + C[iir#d])) ==> (M[iir#d][idx$] == AT#RShift(M[iir#c][idx$], 8))
  );
  assert {:msg "  Channel invariant might not hold on action entry (generated #27)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#g] + C[iir#g])) ==> (M[iir#g][idx$] == AT#RShift(M[iir#c][idx$], 8))
  );
  assert {:msg "  Channel invariant might not hold on action entry (generated #28)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#c] + C[iir#c])) ==> (M[iir#c][idx$] == (M[iir#b][idx$] + M[iir#f][idx$]))
  );
  assert {:msg "  28.3: Channel invariant might not hold on action entry"} (171 * M[iir#g][-1]) == M[iir#f][0];
}
procedure iir#anon$5#delay#anon$2#7()
  modifies C, R, M, St;
{
  var ActorParam#k: int;
  var St#next: State;
  var in#i: int;
  assume ActorParam#k == 0;
  assume C#init[iir#a] == 1;
  assume C#init[iir#b] == 0;
  assume C#init[iir#c] == 0;
  assume C#init[iir#d] == 0;
  assume C#init[iir#e] == 0;
  assume C#init[iir#g] == 0;
  assume 0 <= R[iir#a];
  assume 0 <= C[iir#a];
  assume (R[iir#a] + C[iir#a]) == C#init[iir#a];
  assume 0 <= R[iir#b];
  assume 0 <= C[iir#b];
  assume 0 <= R[iir#c];
  assume 0 <= C[iir#c];
  assume 0 <= R[iir#d];
  assume 0 <= C[iir#d];
  assume 0 <= R[iir#e];
  assume 0 <= C[iir#e];
  assume 0 <= R[iir#f];
  assume 0 <= C[iir#f];
  assume 0 <= R[iir#g];
  assume 0 <= C[iir#g];
  assume R[iir#g] == 0;
  assume R[iir#e] == ((R[iir#f] + C[iir#f]) - 1);
  assume R[iir#a] == (R[iir#b] + C[iir#b]);
  assume R[iir#d] == (R[iir#e] + C[iir#e]);
  assume R[iir#c] == (R[iir#d] + C[iir#d]);
  assume R[iir#c] == (R[iir#g] + C[iir#g]);
  assume R[iir#b] == (R[iir#c] + C[iir#c]);
  assume R[iir#f] == (R[iir#c] + C[iir#c]);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < (R[iir#f] + C[iir#f])) ==> (M[iir#f][idx$] == M[iir#e][idx$ - 1])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#b] + C[iir#b])) ==> (M[iir#b][idx$] == (85 * M[iir#a][idx$]))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#e] + C[iir#e])) ==> (M[iir#e][idx$] == (171 * M[iir#d][idx$]))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#d] + C[iir#d])) ==> (M[iir#d][idx$] == AT#RShift(M[iir#c][idx$], 8))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#g] + C[iir#g])) ==> (M[iir#g][idx$] == AT#RShift(M[iir#c][idx$], 8))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#c] + C[iir#c])) ==> (M[iir#c][idx$] == (M[iir#b][idx$] + M[iir#f][idx$]))
  );
  assume (171 * M[iir#g][-1]) == M[iir#f][0];
  assume true;
  assume 1 <= C[iir#e];
  in#i := M[iir#e][R[iir#e]];
  R[iir#e] := R[iir#e] + 1;
  C[iir#e] := C[iir#e] - 1;
  M[iir#f][R[iir#f] + C[iir#f]] := in#i;
  C[iir#f] := C[iir#f] + 1;
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #29)"} 0 <= R[iir#a];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #30)"} 0 <= C[iir#a];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #31)"} (R[iir#a] + C[iir#a]) == C#init[iir#a];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #32)"} 0 <= R[iir#b];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #33)"} 0 <= C[iir#b];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #34)"} 0 <= R[iir#c];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #35)"} 0 <= C[iir#c];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #36)"} 0 <= R[iir#d];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #37)"} 0 <= C[iir#d];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #38)"} 0 <= R[iir#e];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #39)"} 0 <= C[iir#e];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #40)"} 0 <= R[iir#f];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #41)"} 0 <= C[iir#f];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #42)"} 0 <= R[iir#g];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #43)"} 0 <= C[iir#g];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #44)"} R[iir#g] == 0;
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #45)"} R[iir#e] == ((R[iir#f] + C[iir#f]) - 1);
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #46)"} R[iir#a] == (R[iir#b] + C[iir#b]);
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #47)"} R[iir#d] == (R[iir#e] + C[iir#e]);
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #48)"} R[iir#c] == (R[iir#d] + C[iir#d]);
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #49)"} R[iir#c] == (R[iir#g] + C[iir#g]);
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #50)"} R[iir#b] == (R[iir#c] + C[iir#c]);
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #51)"} R[iir#f] == (R[iir#c] + C[iir#c]);
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #52)"} (forall idx$: int :: 
    (1 <= idx$) && (idx$ < (R[iir#f] + C[iir#f])) ==> (M[iir#f][idx$] == M[iir#e][idx$ - 1])
  );
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #53)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#b] + C[iir#b])) ==> (M[iir#b][idx$] == (85 * M[iir#a][idx$]))
  );
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #54)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#e] + C[iir#e])) ==> (M[iir#e][idx$] == (171 * M[iir#d][idx$]))
  );
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #55)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#d] + C[iir#d])) ==> (M[iir#d][idx$] == AT#RShift(M[iir#c][idx$], 8))
  );
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #56)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#g] + C[iir#g])) ==> (M[iir#g][idx$] == AT#RShift(M[iir#c][idx$], 8))
  );
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #57)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#c] + C[iir#c])) ==> (M[iir#c][idx$] == (M[iir#b][idx$] + M[iir#f][idx$]))
  );
  assert {:msg "  28.3: Sub-actor action at 9.3 might not preserve the channel invariant"} (171 * M[iir#g][-1]) == M[iir#f][0];
}
procedure iir#anon$5#mulc#anon$3#8()
  modifies C, R, M, St;
{
  var ActorParam#c: int;
  var St#next: State;
  var in#i: int;
  assume ActorParam#c == 85;
  assume C#init[iir#a] == 1;
  assume C#init[iir#b] == 0;
  assume C#init[iir#c] == 0;
  assume C#init[iir#d] == 0;
  assume C#init[iir#e] == 0;
  assume C#init[iir#g] == 0;
  assume 0 <= R[iir#a];
  assume 0 <= C[iir#a];
  assume (R[iir#a] + C[iir#a]) == C#init[iir#a];
  assume 0 <= R[iir#b];
  assume 0 <= C[iir#b];
  assume 0 <= R[iir#c];
  assume 0 <= C[iir#c];
  assume 0 <= R[iir#d];
  assume 0 <= C[iir#d];
  assume 0 <= R[iir#e];
  assume 0 <= C[iir#e];
  assume 0 <= R[iir#f];
  assume 0 <= C[iir#f];
  assume 0 <= R[iir#g];
  assume 0 <= C[iir#g];
  assume R[iir#g] == 0;
  assume R[iir#e] == ((R[iir#f] + C[iir#f]) - 1);
  assume R[iir#a] == (R[iir#b] + C[iir#b]);
  assume R[iir#d] == (R[iir#e] + C[iir#e]);
  assume R[iir#c] == (R[iir#d] + C[iir#d]);
  assume R[iir#c] == (R[iir#g] + C[iir#g]);
  assume R[iir#b] == (R[iir#c] + C[iir#c]);
  assume R[iir#f] == (R[iir#c] + C[iir#c]);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < (R[iir#f] + C[iir#f])) ==> (M[iir#f][idx$] == M[iir#e][idx$ - 1])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#b] + C[iir#b])) ==> (M[iir#b][idx$] == (85 * M[iir#a][idx$]))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#e] + C[iir#e])) ==> (M[iir#e][idx$] == (171 * M[iir#d][idx$]))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#d] + C[iir#d])) ==> (M[iir#d][idx$] == AT#RShift(M[iir#c][idx$], 8))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#g] + C[iir#g])) ==> (M[iir#g][idx$] == AT#RShift(M[iir#c][idx$], 8))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#c] + C[iir#c])) ==> (M[iir#c][idx$] == (M[iir#b][idx$] + M[iir#f][idx$]))
  );
  assume (171 * M[iir#g][-1]) == M[iir#f][0];
  assume true;
  assume 1 <= C[iir#a];
  in#i := M[iir#a][R[iir#a]];
  R[iir#a] := R[iir#a] + 1;
  C[iir#a] := C[iir#a] - 1;
  M[iir#b][R[iir#b] + C[iir#b]] := ActorParam#c * in#i;
  C[iir#b] := C[iir#b] + 1;
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #58)"} 0 <= R[iir#a];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #59)"} 0 <= C[iir#a];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #60)"} (R[iir#a] + C[iir#a]) == C#init[iir#a];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #61)"} 0 <= R[iir#b];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #62)"} 0 <= C[iir#b];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #63)"} 0 <= R[iir#c];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #64)"} 0 <= C[iir#c];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #65)"} 0 <= R[iir#d];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #66)"} 0 <= C[iir#d];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #67)"} 0 <= R[iir#e];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #68)"} 0 <= C[iir#e];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #69)"} 0 <= R[iir#f];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #70)"} 0 <= C[iir#f];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #71)"} 0 <= R[iir#g];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #72)"} 0 <= C[iir#g];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #73)"} R[iir#g] == 0;
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #74)"} R[iir#e] == ((R[iir#f] + C[iir#f]) - 1);
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #75)"} R[iir#a] == (R[iir#b] + C[iir#b]);
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #76)"} R[iir#d] == (R[iir#e] + C[iir#e]);
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #77)"} R[iir#c] == (R[iir#d] + C[iir#d]);
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #78)"} R[iir#c] == (R[iir#g] + C[iir#g]);
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #79)"} R[iir#b] == (R[iir#c] + C[iir#c]);
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #80)"} R[iir#f] == (R[iir#c] + C[iir#c]);
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #81)"} (forall idx$: int :: 
    (1 <= idx$) && (idx$ < (R[iir#f] + C[iir#f])) ==> (M[iir#f][idx$] == M[iir#e][idx$ - 1])
  );
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #82)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#b] + C[iir#b])) ==> (M[iir#b][idx$] == (85 * M[iir#a][idx$]))
  );
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #83)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#e] + C[iir#e])) ==> (M[iir#e][idx$] == (171 * M[iir#d][idx$]))
  );
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #84)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#d] + C[iir#d])) ==> (M[iir#d][idx$] == AT#RShift(M[iir#c][idx$], 8))
  );
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #85)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#g] + C[iir#g])) ==> (M[iir#g][idx$] == AT#RShift(M[iir#c][idx$], 8))
  );
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #86)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#c] + C[iir#c])) ==> (M[iir#c][idx$] == (M[iir#b][idx$] + M[iir#f][idx$]))
  );
  assert {:msg "  28.3: Sub-actor action at 14.3 might not preserve the channel invariant"} (171 * M[iir#g][-1]) == M[iir#f][0];
}
procedure iir#anon$5#mulc#anon$3#9()
  modifies C, R, M, St;
{
  var ActorParam#c: int;
  var St#next: State;
  var in#i: int;
  assume ActorParam#c == 171;
  assume C#init[iir#a] == 1;
  assume C#init[iir#b] == 0;
  assume C#init[iir#c] == 0;
  assume C#init[iir#d] == 0;
  assume C#init[iir#e] == 0;
  assume C#init[iir#g] == 0;
  assume 0 <= R[iir#a];
  assume 0 <= C[iir#a];
  assume (R[iir#a] + C[iir#a]) == C#init[iir#a];
  assume 0 <= R[iir#b];
  assume 0 <= C[iir#b];
  assume 0 <= R[iir#c];
  assume 0 <= C[iir#c];
  assume 0 <= R[iir#d];
  assume 0 <= C[iir#d];
  assume 0 <= R[iir#e];
  assume 0 <= C[iir#e];
  assume 0 <= R[iir#f];
  assume 0 <= C[iir#f];
  assume 0 <= R[iir#g];
  assume 0 <= C[iir#g];
  assume R[iir#g] == 0;
  assume R[iir#e] == ((R[iir#f] + C[iir#f]) - 1);
  assume R[iir#a] == (R[iir#b] + C[iir#b]);
  assume R[iir#d] == (R[iir#e] + C[iir#e]);
  assume R[iir#c] == (R[iir#d] + C[iir#d]);
  assume R[iir#c] == (R[iir#g] + C[iir#g]);
  assume R[iir#b] == (R[iir#c] + C[iir#c]);
  assume R[iir#f] == (R[iir#c] + C[iir#c]);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < (R[iir#f] + C[iir#f])) ==> (M[iir#f][idx$] == M[iir#e][idx$ - 1])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#b] + C[iir#b])) ==> (M[iir#b][idx$] == (85 * M[iir#a][idx$]))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#e] + C[iir#e])) ==> (M[iir#e][idx$] == (171 * M[iir#d][idx$]))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#d] + C[iir#d])) ==> (M[iir#d][idx$] == AT#RShift(M[iir#c][idx$], 8))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#g] + C[iir#g])) ==> (M[iir#g][idx$] == AT#RShift(M[iir#c][idx$], 8))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#c] + C[iir#c])) ==> (M[iir#c][idx$] == (M[iir#b][idx$] + M[iir#f][idx$]))
  );
  assume (171 * M[iir#g][-1]) == M[iir#f][0];
  assume true;
  assume 1 <= C[iir#d];
  in#i := M[iir#d][R[iir#d]];
  R[iir#d] := R[iir#d] + 1;
  C[iir#d] := C[iir#d] - 1;
  M[iir#e][R[iir#e] + C[iir#e]] := ActorParam#c * in#i;
  C[iir#e] := C[iir#e] + 1;
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #87)"} 0 <= R[iir#a];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #88)"} 0 <= C[iir#a];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #89)"} (R[iir#a] + C[iir#a]) == C#init[iir#a];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #90)"} 0 <= R[iir#b];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #91)"} 0 <= C[iir#b];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #92)"} 0 <= R[iir#c];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #93)"} 0 <= C[iir#c];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #94)"} 0 <= R[iir#d];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #95)"} 0 <= C[iir#d];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #96)"} 0 <= R[iir#e];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #97)"} 0 <= C[iir#e];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #98)"} 0 <= R[iir#f];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #99)"} 0 <= C[iir#f];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #100)"} 0 <= R[iir#g];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #101)"} 0 <= C[iir#g];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #102)"} R[iir#g] == 0;
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #103)"} R[iir#e] == ((R[iir#f] + C[iir#f]) - 1);
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #104)"} R[iir#a] == (R[iir#b] + C[iir#b]);
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #105)"} R[iir#d] == (R[iir#e] + C[iir#e]);
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #106)"} R[iir#c] == (R[iir#d] + C[iir#d]);
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #107)"} R[iir#c] == (R[iir#g] + C[iir#g]);
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #108)"} R[iir#b] == (R[iir#c] + C[iir#c]);
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #109)"} R[iir#f] == (R[iir#c] + C[iir#c]);
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #110)"} (forall idx$: int :: 
    (1 <= idx$) && (idx$ < (R[iir#f] + C[iir#f])) ==> (M[iir#f][idx$] == M[iir#e][idx$ - 1])
  );
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #111)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#b] + C[iir#b])) ==> (M[iir#b][idx$] == (85 * M[iir#a][idx$]))
  );
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #112)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#e] + C[iir#e])) ==> (M[iir#e][idx$] == (171 * M[iir#d][idx$]))
  );
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #113)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#d] + C[iir#d])) ==> (M[iir#d][idx$] == AT#RShift(M[iir#c][idx$], 8))
  );
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #114)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#g] + C[iir#g])) ==> (M[iir#g][idx$] == AT#RShift(M[iir#c][idx$], 8))
  );
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #115)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#c] + C[iir#c])) ==> (M[iir#c][idx$] == (M[iir#b][idx$] + M[iir#f][idx$]))
  );
  assert {:msg "  28.3: Sub-actor action at 14.3 might not preserve the channel invariant"} (171 * M[iir#g][-1]) == M[iir#f][0];
}
procedure iir#anon$5#rshift#anon$4#10()
  modifies C, R, M, St;
{
  var ActorParam#s: int;
  var St#next: State;
  var in#i: int;
  assume ActorParam#s == 8;
  assume C#init[iir#a] == 1;
  assume C#init[iir#b] == 0;
  assume C#init[iir#c] == 0;
  assume C#init[iir#d] == 0;
  assume C#init[iir#e] == 0;
  assume C#init[iir#g] == 0;
  assume 0 <= R[iir#a];
  assume 0 <= C[iir#a];
  assume (R[iir#a] + C[iir#a]) == C#init[iir#a];
  assume 0 <= R[iir#b];
  assume 0 <= C[iir#b];
  assume 0 <= R[iir#c];
  assume 0 <= C[iir#c];
  assume 0 <= R[iir#d];
  assume 0 <= C[iir#d];
  assume 0 <= R[iir#e];
  assume 0 <= C[iir#e];
  assume 0 <= R[iir#f];
  assume 0 <= C[iir#f];
  assume 0 <= R[iir#g];
  assume 0 <= C[iir#g];
  assume R[iir#g] == 0;
  assume R[iir#e] == ((R[iir#f] + C[iir#f]) - 1);
  assume R[iir#a] == (R[iir#b] + C[iir#b]);
  assume R[iir#d] == (R[iir#e] + C[iir#e]);
  assume R[iir#c] == (R[iir#d] + C[iir#d]);
  assume R[iir#c] == (R[iir#g] + C[iir#g]);
  assume R[iir#b] == (R[iir#c] + C[iir#c]);
  assume R[iir#f] == (R[iir#c] + C[iir#c]);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < (R[iir#f] + C[iir#f])) ==> (M[iir#f][idx$] == M[iir#e][idx$ - 1])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#b] + C[iir#b])) ==> (M[iir#b][idx$] == (85 * M[iir#a][idx$]))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#e] + C[iir#e])) ==> (M[iir#e][idx$] == (171 * M[iir#d][idx$]))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#d] + C[iir#d])) ==> (M[iir#d][idx$] == AT#RShift(M[iir#c][idx$], 8))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#g] + C[iir#g])) ==> (M[iir#g][idx$] == AT#RShift(M[iir#c][idx$], 8))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#c] + C[iir#c])) ==> (M[iir#c][idx$] == (M[iir#b][idx$] + M[iir#f][idx$]))
  );
  assume (171 * M[iir#g][-1]) == M[iir#f][0];
  assume true;
  assume 1 <= C[iir#c];
  in#i := M[iir#c][R[iir#c]];
  R[iir#c] := R[iir#c] + 1;
  C[iir#c] := C[iir#c] - 1;
  M[iir#d][R[iir#d] + C[iir#d]] := AT#RShift(in#i, ActorParam#s);
  C[iir#d] := C[iir#d] + 1;
  M[iir#g][R[iir#g] + C[iir#g]] := AT#RShift(in#i, ActorParam#s);
  C[iir#g] := C[iir#g] + 1;
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #116)"} 0 <= R[iir#a];
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #117)"} 0 <= C[iir#a];
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #118)"} (R[iir#a] + C[iir#a]) == C#init[iir#a];
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #119)"} 0 <= R[iir#b];
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #120)"} 0 <= C[iir#b];
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #121)"} 0 <= R[iir#c];
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #122)"} 0 <= C[iir#c];
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #123)"} 0 <= R[iir#d];
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #124)"} 0 <= C[iir#d];
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #125)"} 0 <= R[iir#e];
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #126)"} 0 <= C[iir#e];
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #127)"} 0 <= R[iir#f];
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #128)"} 0 <= C[iir#f];
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #129)"} 0 <= R[iir#g];
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #130)"} 0 <= C[iir#g];
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #131)"} R[iir#g] == 0;
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #132)"} R[iir#e] == ((R[iir#f] + C[iir#f]) - 1);
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #133)"} R[iir#a] == (R[iir#b] + C[iir#b]);
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #134)"} R[iir#d] == (R[iir#e] + C[iir#e]);
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #135)"} R[iir#c] == (R[iir#d] + C[iir#d]);
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #136)"} R[iir#c] == (R[iir#g] + C[iir#g]);
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #137)"} R[iir#b] == (R[iir#c] + C[iir#c]);
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #138)"} R[iir#f] == (R[iir#c] + C[iir#c]);
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #139)"} (forall idx$: int :: 
    (1 <= idx$) && (idx$ < (R[iir#f] + C[iir#f])) ==> (M[iir#f][idx$] == M[iir#e][idx$ - 1])
  );
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #140)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#b] + C[iir#b])) ==> (M[iir#b][idx$] == (85 * M[iir#a][idx$]))
  );
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #141)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#e] + C[iir#e])) ==> (M[iir#e][idx$] == (171 * M[iir#d][idx$]))
  );
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #142)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#d] + C[iir#d])) ==> (M[iir#d][idx$] == AT#RShift(M[iir#c][idx$], 8))
  );
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #143)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#g] + C[iir#g])) ==> (M[iir#g][idx$] == AT#RShift(M[iir#c][idx$], 8))
  );
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #144)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#c] + C[iir#c])) ==> (M[iir#c][idx$] == (M[iir#b][idx$] + M[iir#f][idx$]))
  );
  assert {:msg "  28.3: Sub-actor action at 19.3 might not preserve the channel invariant"} (171 * M[iir#g][-1]) == M[iir#f][0];
}
procedure iir#anon$5#add#anon$0#11()
  modifies C, R, M, St;
{
  var St#next: State;
  var in1#i: int;
  var in2#j: int;
  assume C#init[iir#a] == 1;
  assume C#init[iir#b] == 0;
  assume C#init[iir#c] == 0;
  assume C#init[iir#d] == 0;
  assume C#init[iir#e] == 0;
  assume C#init[iir#g] == 0;
  assume 0 <= R[iir#a];
  assume 0 <= C[iir#a];
  assume (R[iir#a] + C[iir#a]) == C#init[iir#a];
  assume 0 <= R[iir#b];
  assume 0 <= C[iir#b];
  assume 0 <= R[iir#c];
  assume 0 <= C[iir#c];
  assume 0 <= R[iir#d];
  assume 0 <= C[iir#d];
  assume 0 <= R[iir#e];
  assume 0 <= C[iir#e];
  assume 0 <= R[iir#f];
  assume 0 <= C[iir#f];
  assume 0 <= R[iir#g];
  assume 0 <= C[iir#g];
  assume R[iir#g] == 0;
  assume R[iir#e] == ((R[iir#f] + C[iir#f]) - 1);
  assume R[iir#a] == (R[iir#b] + C[iir#b]);
  assume R[iir#d] == (R[iir#e] + C[iir#e]);
  assume R[iir#c] == (R[iir#d] + C[iir#d]);
  assume R[iir#c] == (R[iir#g] + C[iir#g]);
  assume R[iir#b] == (R[iir#c] + C[iir#c]);
  assume R[iir#f] == (R[iir#c] + C[iir#c]);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < (R[iir#f] + C[iir#f])) ==> (M[iir#f][idx$] == M[iir#e][idx$ - 1])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#b] + C[iir#b])) ==> (M[iir#b][idx$] == (85 * M[iir#a][idx$]))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#e] + C[iir#e])) ==> (M[iir#e][idx$] == (171 * M[iir#d][idx$]))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#d] + C[iir#d])) ==> (M[iir#d][idx$] == AT#RShift(M[iir#c][idx$], 8))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#g] + C[iir#g])) ==> (M[iir#g][idx$] == AT#RShift(M[iir#c][idx$], 8))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#c] + C[iir#c])) ==> (M[iir#c][idx$] == (M[iir#b][idx$] + M[iir#f][idx$]))
  );
  assume (171 * M[iir#g][-1]) == M[iir#f][0];
  assume true;
  assume (1 <= C[iir#b]) && (1 <= C[iir#f]);
  in1#i := M[iir#b][R[iir#b]];
  R[iir#b] := R[iir#b] + 1;
  C[iir#b] := C[iir#b] - 1;
  in2#j := M[iir#f][R[iir#f]];
  R[iir#f] := R[iir#f] + 1;
  C[iir#f] := C[iir#f] - 1;
  M[iir#c][R[iir#c] + C[iir#c]] := in1#i + in2#j;
  C[iir#c] := C[iir#c] + 1;
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #145)"} 0 <= R[iir#a];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #146)"} 0 <= C[iir#a];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #147)"} (R[iir#a] + C[iir#a]) == C#init[iir#a];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #148)"} 0 <= R[iir#b];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #149)"} 0 <= C[iir#b];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #150)"} 0 <= R[iir#c];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #151)"} 0 <= C[iir#c];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #152)"} 0 <= R[iir#d];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #153)"} 0 <= C[iir#d];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #154)"} 0 <= R[iir#e];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #155)"} 0 <= C[iir#e];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #156)"} 0 <= R[iir#f];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #157)"} 0 <= C[iir#f];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #158)"} 0 <= R[iir#g];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #159)"} 0 <= C[iir#g];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #160)"} R[iir#g] == 0;
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #161)"} R[iir#e] == ((R[iir#f] + C[iir#f]) - 1);
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #162)"} R[iir#a] == (R[iir#b] + C[iir#b]);
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #163)"} R[iir#d] == (R[iir#e] + C[iir#e]);
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #164)"} R[iir#c] == (R[iir#d] + C[iir#d]);
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #165)"} R[iir#c] == (R[iir#g] + C[iir#g]);
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #166)"} R[iir#b] == (R[iir#c] + C[iir#c]);
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #167)"} R[iir#f] == (R[iir#c] + C[iir#c]);
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #168)"} (forall idx$: int :: 
    (1 <= idx$) && (idx$ < (R[iir#f] + C[iir#f])) ==> (M[iir#f][idx$] == M[iir#e][idx$ - 1])
  );
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #169)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#b] + C[iir#b])) ==> (M[iir#b][idx$] == (85 * M[iir#a][idx$]))
  );
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #170)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#e] + C[iir#e])) ==> (M[iir#e][idx$] == (171 * M[iir#d][idx$]))
  );
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #171)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#d] + C[iir#d])) ==> (M[iir#d][idx$] == AT#RShift(M[iir#c][idx$], 8))
  );
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #172)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#g] + C[iir#g])) ==> (M[iir#g][idx$] == AT#RShift(M[iir#c][idx$], 8))
  );
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #173)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#c] + C[iir#c])) ==> (M[iir#c][idx$] == (M[iir#b][idx$] + M[iir#f][idx$]))
  );
  assert {:msg "  28.3: Sub-actor action at 3.3 might not preserve the channel invariant"} (171 * M[iir#g][-1]) == M[iir#f][0];
}
procedure iir#anon$5#exit#12()
  modifies C, R, M, St;
{
  var iir#out#0: int;
  assume C#init[iir#a] == 1;
  assume C#init[iir#b] == 0;
  assume C#init[iir#c] == 0;
  assume C#init[iir#d] == 0;
  assume C#init[iir#e] == 0;
  assume C#init[iir#g] == 0;
  assume 0 <= R[iir#a];
  assume 0 <= C[iir#a];
  assume (R[iir#a] + C[iir#a]) == C#init[iir#a];
  assume 0 <= R[iir#b];
  assume 0 <= C[iir#b];
  assume 0 <= R[iir#c];
  assume 0 <= C[iir#c];
  assume 0 <= R[iir#d];
  assume 0 <= C[iir#d];
  assume 0 <= R[iir#e];
  assume 0 <= C[iir#e];
  assume 0 <= R[iir#f];
  assume 0 <= C[iir#f];
  assume 0 <= R[iir#g];
  assume 0 <= C[iir#g];
  assume R[iir#g] == 0;
  assume R[iir#e] == ((R[iir#f] + C[iir#f]) - 1);
  assume R[iir#a] == (R[iir#b] + C[iir#b]);
  assume R[iir#d] == (R[iir#e] + C[iir#e]);
  assume R[iir#c] == (R[iir#d] + C[iir#d]);
  assume R[iir#c] == (R[iir#g] + C[iir#g]);
  assume R[iir#b] == (R[iir#c] + C[iir#c]);
  assume R[iir#f] == (R[iir#c] + C[iir#c]);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < (R[iir#f] + C[iir#f])) ==> (M[iir#f][idx$] == M[iir#e][idx$ - 1])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#b] + C[iir#b])) ==> (M[iir#b][idx$] == (85 * M[iir#a][idx$]))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#e] + C[iir#e])) ==> (M[iir#e][idx$] == (171 * M[iir#d][idx$]))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#d] + C[iir#d])) ==> (M[iir#d][idx$] == AT#RShift(M[iir#c][idx$], 8))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#g] + C[iir#g])) ==> (M[iir#g][idx$] == AT#RShift(M[iir#c][idx$], 8))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#c] + C[iir#c])) ==> (M[iir#c][idx$] == (M[iir#b][idx$] + M[iir#f][idx$]))
  );
  assume (171 * M[iir#g][-1]) == M[iir#f][0];
  assume !(((((1 <= C[iir#e]) || (1 <= C[iir#a])) || (1 <= C[iir#d])) || (1 <= C[iir#c])) || ((1 <= C[iir#b]) && (1 <= C[iir#f])));
  assert {:msg "  23.3: The network might leave unread tokens on channel a"} C[iir#a] == 0;
  assert {:msg "  23.3: The network might leave unread tokens on channel b"} C[iir#b] == 0;
  assert {:msg "  23.3: The network might leave unread tokens on channel c"} C[iir#c] == 0;
  assert {:msg "  23.3: The network might leave unread tokens on channel d"} C[iir#d] == 0;
  assert {:msg "  23.3: The network might leave unread tokens on channel e"} C[iir#e] == 0;
  assert {:msg "  23.3: The network might not produce the specified number of tokens on output out"} C[iir#g] == 1;
  iir#out#0 := M[iir#g][0];
  assert {:msg "  23.26: Network output might not conform to the specified action output"} iir#out#0 == AT#RShift((171 * M[iir#g][R[iir#g] - 1]) + (85 * M[iir#a][0]), 8);
  R[iir#g] := R[iir#g] + C[iir#g];
  C[iir#g] := 0;
  assert {:msg "  The network might not preserve the network invariant"} iir#f == 1;
  assert {:msg "  The network might not preserve the network invariant"} M[iir#f][R[iir#f]] == (171 * M[iir#g][R[iir#g] - 1]);
}

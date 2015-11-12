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
  var i: int;
  var j: int;
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
  var i: int;
  assume true;
}
procedure mulc#anon$3#3()
  modifies C, R, M, St;
{
  var i: int;
  assume true;
}
procedure rshift#anon$4#4()
  modifies C, R, M, St;
{
  var i: int;
  assume true;
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
procedure iir#anon$5#entry#5()
  modifies C, R, M, St;
{
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
  assume C[iir#f] == 1;
  assume M[iir#f][R[iir#f]] == (171 * M[iir#g][R[iir#g] - 1]);
  assert {:msg "  Channel invariant might not hold on action entry (generated #0 )"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#c] + C[iir#c])) ==> (M[iir#c][idx$ - 0] == (M[iir#b][idx$ - 0] + M[iir#f][idx$ - 0]))
  );
  assert {:msg "  Channel invariant might not hold on action entry (generated #1 )"} R[iir#f] == (R[iir#c] + C[iir#c]);
  assert {:msg "  Channel invariant might not hold on action entry (generated #2 )"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#c] + C[iir#c])) ==> (M[iir#c][idx$ - 0] == (M[iir#b][idx$ - 0] + M[iir#f][idx$ - 0]))
  );
  assert {:msg "  Channel invariant might not hold on action entry (generated #3 )"} R[iir#b] == (R[iir#c] + C[iir#c]);
  assert {:msg "  Channel invariant might not hold on action entry (generated #4 )"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#g] + C[iir#g])) ==> (M[iir#g][idx$ - 0] == AT#RShift(M[iir#c][idx$ - 0], 8))
  );
  assert {:msg "  Channel invariant might not hold on action entry (generated #5 )"} R[iir#c] == (R[iir#g] + C[iir#g]);
  assert {:msg "  Channel invariant might not hold on action entry (generated #6 )"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#d] + C[iir#d])) ==> (M[iir#d][idx$ - 0] == AT#RShift(M[iir#c][idx$ - 0], 8))
  );
  assert {:msg "  Channel invariant might not hold on action entry (generated #7 )"} R[iir#c] == (R[iir#d] + C[iir#d]);
  assert {:msg "  Channel invariant might not hold on action entry (generated #8 )"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#e] + C[iir#e])) ==> (M[iir#e][idx$ - 0] == (171 * M[iir#d][idx$ - 0]))
  );
  assert {:msg "  Channel invariant might not hold on action entry (generated #9 )"} R[iir#d] == (R[iir#e] + C[iir#e]);
  assert {:msg "  Channel invariant might not hold on action entry (generated #10 )"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#b] + C[iir#b])) ==> (M[iir#b][idx$ - 0] == (85 * M[iir#a][idx$ - 0]))
  );
  assert {:msg "  Channel invariant might not hold on action entry (generated #11 )"} R[iir#a] == (R[iir#b] + C[iir#b]);
  assert {:msg "  Channel invariant might not hold on action entry (generated #12 )"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < ((R[iir#f] + C[iir#f]) - 1)) ==> (M[iir#f][(idx$ + 1) - 0] == M[iir#e][idx$ - 0])
  );
  assert {:msg "  Channel invariant might not hold on action entry (generated #13 )"} R[iir#e] == ((R[iir#f] + C[iir#f]) - 1);
  assert {:msg "  Channel invariant might not hold on action entry (generated #14 )"} R[iir#g] == 0;
  assert {:msg "  Channel invariant might not hold on action entry (generated #15 )"} 0 <= C[iir#g];
  assert {:msg "  Channel invariant might not hold on action entry (generated #16 )"} 0 <= R[iir#g];
  assert {:msg "  Channel invariant might not hold on action entry (generated #17 )"} 0 <= C[iir#f];
  assert {:msg "  Channel invariant might not hold on action entry (generated #18 )"} 0 <= R[iir#f];
  assert {:msg "  Channel invariant might not hold on action entry (generated #19 )"} 0 <= C[iir#e];
  assert {:msg "  Channel invariant might not hold on action entry (generated #20 )"} 0 <= R[iir#e];
  assert {:msg "  Channel invariant might not hold on action entry (generated #21 )"} 0 <= C[iir#d];
  assert {:msg "  Channel invariant might not hold on action entry (generated #22 )"} 0 <= R[iir#d];
  assert {:msg "  Channel invariant might not hold on action entry (generated #23 )"} 0 <= C[iir#c];
  assert {:msg "  Channel invariant might not hold on action entry (generated #24 )"} 0 <= R[iir#c];
  assert {:msg "  Channel invariant might not hold on action entry (generated #25 )"} 0 <= C[iir#b];
  assert {:msg "  Channel invariant might not hold on action entry (generated #26 )"} 0 <= R[iir#b];
  assert {:msg "  Channel invariant might not hold on action entry (generated #27 )"} (R[iir#a] + C[iir#a]) == C#init[iir#a];
  assert {:msg "  Channel invariant might not hold on action entry (generated #28 )"} 0 <= C[iir#a];
  assert {:msg "  Channel invariant might not hold on action entry (generated #29 )"} 0 <= R[iir#a];
  assert {:msg "  28.3: Channel invariant might not hold on action entry"} (171 * M[iir#g][-1]) == M[iir#f][0];
}
procedure iir#anon$5#delay#anon$2#6()
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
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#c] + C[iir#c])) ==> (M[iir#c][idx$ - 0] == (M[iir#b][idx$ - 0] + M[iir#f][idx$ - 0]))
  );
  assume R[iir#f] == (R[iir#c] + C[iir#c]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#c] + C[iir#c])) ==> (M[iir#c][idx$ - 0] == (M[iir#b][idx$ - 0] + M[iir#f][idx$ - 0]))
  );
  assume R[iir#b] == (R[iir#c] + C[iir#c]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#g] + C[iir#g])) ==> (M[iir#g][idx$ - 0] == AT#RShift(M[iir#c][idx$ - 0], 8))
  );
  assume R[iir#c] == (R[iir#g] + C[iir#g]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#d] + C[iir#d])) ==> (M[iir#d][idx$ - 0] == AT#RShift(M[iir#c][idx$ - 0], 8))
  );
  assume R[iir#c] == (R[iir#d] + C[iir#d]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#e] + C[iir#e])) ==> (M[iir#e][idx$ - 0] == (171 * M[iir#d][idx$ - 0]))
  );
  assume R[iir#d] == (R[iir#e] + C[iir#e]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#b] + C[iir#b])) ==> (M[iir#b][idx$ - 0] == (85 * M[iir#a][idx$ - 0]))
  );
  assume R[iir#a] == (R[iir#b] + C[iir#b]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < ((R[iir#f] + C[iir#f]) - 1)) ==> (M[iir#f][(idx$ + 1) - 0] == M[iir#e][idx$ - 0])
  );
  assume R[iir#e] == ((R[iir#f] + C[iir#f]) - 1);
  assume R[iir#g] == 0;
  assume 0 <= C[iir#g];
  assume 0 <= R[iir#g];
  assume 0 <= C[iir#f];
  assume 0 <= R[iir#f];
  assume 0 <= C[iir#e];
  assume 0 <= R[iir#e];
  assume 0 <= C[iir#d];
  assume 0 <= R[iir#d];
  assume 0 <= C[iir#c];
  assume 0 <= R[iir#c];
  assume 0 <= C[iir#b];
  assume 0 <= R[iir#b];
  assume (R[iir#a] + C[iir#a]) == C#init[iir#a];
  assume 0 <= C[iir#a];
  assume 0 <= R[iir#a];
  assume (171 * M[iir#g][-1]) == M[iir#f][0];
  assume true;
  assume 1 <= C[iir#e];
  in#i := M[iir#e][R[iir#e]];
  R[iir#e] := R[iir#e] + 1;
  C[iir#e] := C[iir#e] - 1;
  M[iir#f][R[iir#f] + C[iir#f]] := in#i;
  C[iir#f] := C[iir#f] + 1;
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #30)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#c] + C[iir#c])) ==> (M[iir#c][idx$ - 0] == (M[iir#b][idx$ - 0] + M[iir#f][idx$ - 0]))
  );
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #31)"} R[iir#f] == (R[iir#c] + C[iir#c]);
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #32)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#c] + C[iir#c])) ==> (M[iir#c][idx$ - 0] == (M[iir#b][idx$ - 0] + M[iir#f][idx$ - 0]))
  );
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #33)"} R[iir#b] == (R[iir#c] + C[iir#c]);
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #34)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#g] + C[iir#g])) ==> (M[iir#g][idx$ - 0] == AT#RShift(M[iir#c][idx$ - 0], 8))
  );
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #35)"} R[iir#c] == (R[iir#g] + C[iir#g]);
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #36)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#d] + C[iir#d])) ==> (M[iir#d][idx$ - 0] == AT#RShift(M[iir#c][idx$ - 0], 8))
  );
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #37)"} R[iir#c] == (R[iir#d] + C[iir#d]);
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #38)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#e] + C[iir#e])) ==> (M[iir#e][idx$ - 0] == (171 * M[iir#d][idx$ - 0]))
  );
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #39)"} R[iir#d] == (R[iir#e] + C[iir#e]);
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #40)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#b] + C[iir#b])) ==> (M[iir#b][idx$ - 0] == (85 * M[iir#a][idx$ - 0]))
  );
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #41)"} R[iir#a] == (R[iir#b] + C[iir#b]);
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #42)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < ((R[iir#f] + C[iir#f]) - 1)) ==> (M[iir#f][(idx$ + 1) - 0] == M[iir#e][idx$ - 0])
  );
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #43)"} R[iir#e] == ((R[iir#f] + C[iir#f]) - 1);
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #44)"} R[iir#g] == 0;
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #45)"} 0 <= C[iir#g];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #46)"} 0 <= R[iir#g];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #47)"} 0 <= C[iir#f];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #48)"} 0 <= R[iir#f];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #49)"} 0 <= C[iir#e];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #50)"} 0 <= R[iir#e];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #51)"} 0 <= C[iir#d];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #52)"} 0 <= R[iir#d];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #53)"} 0 <= C[iir#c];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #54)"} 0 <= R[iir#c];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #55)"} 0 <= C[iir#b];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #56)"} 0 <= R[iir#b];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #57)"} (R[iir#a] + C[iir#a]) == C#init[iir#a];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #58)"} 0 <= C[iir#a];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated #59)"} 0 <= R[iir#a];
  assert {:msg "  28.3: Sub-actor action at 9.3 might not preserve the channel invariant"} (171 * M[iir#g][-1]) == M[iir#f][0];
}
procedure iir#anon$5#mulc#anon$3#7()
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
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#c] + C[iir#c])) ==> (M[iir#c][idx$ - 0] == (M[iir#b][idx$ - 0] + M[iir#f][idx$ - 0]))
  );
  assume R[iir#f] == (R[iir#c] + C[iir#c]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#c] + C[iir#c])) ==> (M[iir#c][idx$ - 0] == (M[iir#b][idx$ - 0] + M[iir#f][idx$ - 0]))
  );
  assume R[iir#b] == (R[iir#c] + C[iir#c]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#g] + C[iir#g])) ==> (M[iir#g][idx$ - 0] == AT#RShift(M[iir#c][idx$ - 0], 8))
  );
  assume R[iir#c] == (R[iir#g] + C[iir#g]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#d] + C[iir#d])) ==> (M[iir#d][idx$ - 0] == AT#RShift(M[iir#c][idx$ - 0], 8))
  );
  assume R[iir#c] == (R[iir#d] + C[iir#d]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#e] + C[iir#e])) ==> (M[iir#e][idx$ - 0] == (171 * M[iir#d][idx$ - 0]))
  );
  assume R[iir#d] == (R[iir#e] + C[iir#e]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#b] + C[iir#b])) ==> (M[iir#b][idx$ - 0] == (85 * M[iir#a][idx$ - 0]))
  );
  assume R[iir#a] == (R[iir#b] + C[iir#b]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < ((R[iir#f] + C[iir#f]) - 1)) ==> (M[iir#f][(idx$ + 1) - 0] == M[iir#e][idx$ - 0])
  );
  assume R[iir#e] == ((R[iir#f] + C[iir#f]) - 1);
  assume R[iir#g] == 0;
  assume 0 <= C[iir#g];
  assume 0 <= R[iir#g];
  assume 0 <= C[iir#f];
  assume 0 <= R[iir#f];
  assume 0 <= C[iir#e];
  assume 0 <= R[iir#e];
  assume 0 <= C[iir#d];
  assume 0 <= R[iir#d];
  assume 0 <= C[iir#c];
  assume 0 <= R[iir#c];
  assume 0 <= C[iir#b];
  assume 0 <= R[iir#b];
  assume (R[iir#a] + C[iir#a]) == C#init[iir#a];
  assume 0 <= C[iir#a];
  assume 0 <= R[iir#a];
  assume (171 * M[iir#g][-1]) == M[iir#f][0];
  assume true;
  assume 1 <= C[iir#a];
  in#i := M[iir#a][R[iir#a]];
  R[iir#a] := R[iir#a] + 1;
  C[iir#a] := C[iir#a] - 1;
  M[iir#b][R[iir#b] + C[iir#b]] := ActorParam#c * in#i;
  C[iir#b] := C[iir#b] + 1;
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #60)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#c] + C[iir#c])) ==> (M[iir#c][idx$ - 0] == (M[iir#b][idx$ - 0] + M[iir#f][idx$ - 0]))
  );
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #61)"} R[iir#f] == (R[iir#c] + C[iir#c]);
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #62)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#c] + C[iir#c])) ==> (M[iir#c][idx$ - 0] == (M[iir#b][idx$ - 0] + M[iir#f][idx$ - 0]))
  );
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #63)"} R[iir#b] == (R[iir#c] + C[iir#c]);
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #64)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#g] + C[iir#g])) ==> (M[iir#g][idx$ - 0] == AT#RShift(M[iir#c][idx$ - 0], 8))
  );
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #65)"} R[iir#c] == (R[iir#g] + C[iir#g]);
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #66)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#d] + C[iir#d])) ==> (M[iir#d][idx$ - 0] == AT#RShift(M[iir#c][idx$ - 0], 8))
  );
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #67)"} R[iir#c] == (R[iir#d] + C[iir#d]);
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #68)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#e] + C[iir#e])) ==> (M[iir#e][idx$ - 0] == (171 * M[iir#d][idx$ - 0]))
  );
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #69)"} R[iir#d] == (R[iir#e] + C[iir#e]);
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #70)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#b] + C[iir#b])) ==> (M[iir#b][idx$ - 0] == (85 * M[iir#a][idx$ - 0]))
  );
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #71)"} R[iir#a] == (R[iir#b] + C[iir#b]);
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #72)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < ((R[iir#f] + C[iir#f]) - 1)) ==> (M[iir#f][(idx$ + 1) - 0] == M[iir#e][idx$ - 0])
  );
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #73)"} R[iir#e] == ((R[iir#f] + C[iir#f]) - 1);
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #74)"} R[iir#g] == 0;
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #75)"} 0 <= C[iir#g];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #76)"} 0 <= R[iir#g];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #77)"} 0 <= C[iir#f];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #78)"} 0 <= R[iir#f];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #79)"} 0 <= C[iir#e];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #80)"} 0 <= R[iir#e];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #81)"} 0 <= C[iir#d];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #82)"} 0 <= R[iir#d];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #83)"} 0 <= C[iir#c];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #84)"} 0 <= R[iir#c];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #85)"} 0 <= C[iir#b];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #86)"} 0 <= R[iir#b];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #87)"} (R[iir#a] + C[iir#a]) == C#init[iir#a];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #88)"} 0 <= C[iir#a];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #89)"} 0 <= R[iir#a];
  assert {:msg "  28.3: Sub-actor action at 14.3 might not preserve the channel invariant"} (171 * M[iir#g][-1]) == M[iir#f][0];
}
procedure iir#anon$5#mulc#anon$3#8()
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
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#c] + C[iir#c])) ==> (M[iir#c][idx$ - 0] == (M[iir#b][idx$ - 0] + M[iir#f][idx$ - 0]))
  );
  assume R[iir#f] == (R[iir#c] + C[iir#c]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#c] + C[iir#c])) ==> (M[iir#c][idx$ - 0] == (M[iir#b][idx$ - 0] + M[iir#f][idx$ - 0]))
  );
  assume R[iir#b] == (R[iir#c] + C[iir#c]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#g] + C[iir#g])) ==> (M[iir#g][idx$ - 0] == AT#RShift(M[iir#c][idx$ - 0], 8))
  );
  assume R[iir#c] == (R[iir#g] + C[iir#g]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#d] + C[iir#d])) ==> (M[iir#d][idx$ - 0] == AT#RShift(M[iir#c][idx$ - 0], 8))
  );
  assume R[iir#c] == (R[iir#d] + C[iir#d]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#e] + C[iir#e])) ==> (M[iir#e][idx$ - 0] == (171 * M[iir#d][idx$ - 0]))
  );
  assume R[iir#d] == (R[iir#e] + C[iir#e]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#b] + C[iir#b])) ==> (M[iir#b][idx$ - 0] == (85 * M[iir#a][idx$ - 0]))
  );
  assume R[iir#a] == (R[iir#b] + C[iir#b]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < ((R[iir#f] + C[iir#f]) - 1)) ==> (M[iir#f][(idx$ + 1) - 0] == M[iir#e][idx$ - 0])
  );
  assume R[iir#e] == ((R[iir#f] + C[iir#f]) - 1);
  assume R[iir#g] == 0;
  assume 0 <= C[iir#g];
  assume 0 <= R[iir#g];
  assume 0 <= C[iir#f];
  assume 0 <= R[iir#f];
  assume 0 <= C[iir#e];
  assume 0 <= R[iir#e];
  assume 0 <= C[iir#d];
  assume 0 <= R[iir#d];
  assume 0 <= C[iir#c];
  assume 0 <= R[iir#c];
  assume 0 <= C[iir#b];
  assume 0 <= R[iir#b];
  assume (R[iir#a] + C[iir#a]) == C#init[iir#a];
  assume 0 <= C[iir#a];
  assume 0 <= R[iir#a];
  assume (171 * M[iir#g][-1]) == M[iir#f][0];
  assume true;
  assume 1 <= C[iir#d];
  in#i := M[iir#d][R[iir#d]];
  R[iir#d] := R[iir#d] + 1;
  C[iir#d] := C[iir#d] - 1;
  M[iir#e][R[iir#e] + C[iir#e]] := ActorParam#c * in#i;
  C[iir#e] := C[iir#e] + 1;
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #90)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#c] + C[iir#c])) ==> (M[iir#c][idx$ - 0] == (M[iir#b][idx$ - 0] + M[iir#f][idx$ - 0]))
  );
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #91)"} R[iir#f] == (R[iir#c] + C[iir#c]);
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #92)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#c] + C[iir#c])) ==> (M[iir#c][idx$ - 0] == (M[iir#b][idx$ - 0] + M[iir#f][idx$ - 0]))
  );
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #93)"} R[iir#b] == (R[iir#c] + C[iir#c]);
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #94)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#g] + C[iir#g])) ==> (M[iir#g][idx$ - 0] == AT#RShift(M[iir#c][idx$ - 0], 8))
  );
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #95)"} R[iir#c] == (R[iir#g] + C[iir#g]);
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #96)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#d] + C[iir#d])) ==> (M[iir#d][idx$ - 0] == AT#RShift(M[iir#c][idx$ - 0], 8))
  );
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #97)"} R[iir#c] == (R[iir#d] + C[iir#d]);
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #98)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#e] + C[iir#e])) ==> (M[iir#e][idx$ - 0] == (171 * M[iir#d][idx$ - 0]))
  );
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #99)"} R[iir#d] == (R[iir#e] + C[iir#e]);
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #100)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#b] + C[iir#b])) ==> (M[iir#b][idx$ - 0] == (85 * M[iir#a][idx$ - 0]))
  );
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #101)"} R[iir#a] == (R[iir#b] + C[iir#b]);
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #102)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < ((R[iir#f] + C[iir#f]) - 1)) ==> (M[iir#f][(idx$ + 1) - 0] == M[iir#e][idx$ - 0])
  );
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #103)"} R[iir#e] == ((R[iir#f] + C[iir#f]) - 1);
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #104)"} R[iir#g] == 0;
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #105)"} 0 <= C[iir#g];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #106)"} 0 <= R[iir#g];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #107)"} 0 <= C[iir#f];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #108)"} 0 <= R[iir#f];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #109)"} 0 <= C[iir#e];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #110)"} 0 <= R[iir#e];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #111)"} 0 <= C[iir#d];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #112)"} 0 <= R[iir#d];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #113)"} 0 <= C[iir#c];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #114)"} 0 <= R[iir#c];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #115)"} 0 <= C[iir#b];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #116)"} 0 <= R[iir#b];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #117)"} (R[iir#a] + C[iir#a]) == C#init[iir#a];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #118)"} 0 <= C[iir#a];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated #119)"} 0 <= R[iir#a];
  assert {:msg "  28.3: Sub-actor action at 14.3 might not preserve the channel invariant"} (171 * M[iir#g][-1]) == M[iir#f][0];
}
procedure iir#anon$5#rshift#anon$4#9()
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
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#c] + C[iir#c])) ==> (M[iir#c][idx$ - 0] == (M[iir#b][idx$ - 0] + M[iir#f][idx$ - 0]))
  );
  assume R[iir#f] == (R[iir#c] + C[iir#c]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#c] + C[iir#c])) ==> (M[iir#c][idx$ - 0] == (M[iir#b][idx$ - 0] + M[iir#f][idx$ - 0]))
  );
  assume R[iir#b] == (R[iir#c] + C[iir#c]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#g] + C[iir#g])) ==> (M[iir#g][idx$ - 0] == AT#RShift(M[iir#c][idx$ - 0], 8))
  );
  assume R[iir#c] == (R[iir#g] + C[iir#g]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#d] + C[iir#d])) ==> (M[iir#d][idx$ - 0] == AT#RShift(M[iir#c][idx$ - 0], 8))
  );
  assume R[iir#c] == (R[iir#d] + C[iir#d]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#e] + C[iir#e])) ==> (M[iir#e][idx$ - 0] == (171 * M[iir#d][idx$ - 0]))
  );
  assume R[iir#d] == (R[iir#e] + C[iir#e]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#b] + C[iir#b])) ==> (M[iir#b][idx$ - 0] == (85 * M[iir#a][idx$ - 0]))
  );
  assume R[iir#a] == (R[iir#b] + C[iir#b]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < ((R[iir#f] + C[iir#f]) - 1)) ==> (M[iir#f][(idx$ + 1) - 0] == M[iir#e][idx$ - 0])
  );
  assume R[iir#e] == ((R[iir#f] + C[iir#f]) - 1);
  assume R[iir#g] == 0;
  assume 0 <= C[iir#g];
  assume 0 <= R[iir#g];
  assume 0 <= C[iir#f];
  assume 0 <= R[iir#f];
  assume 0 <= C[iir#e];
  assume 0 <= R[iir#e];
  assume 0 <= C[iir#d];
  assume 0 <= R[iir#d];
  assume 0 <= C[iir#c];
  assume 0 <= R[iir#c];
  assume 0 <= C[iir#b];
  assume 0 <= R[iir#b];
  assume (R[iir#a] + C[iir#a]) == C#init[iir#a];
  assume 0 <= C[iir#a];
  assume 0 <= R[iir#a];
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
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #120)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#c] + C[iir#c])) ==> (M[iir#c][idx$ - 0] == (M[iir#b][idx$ - 0] + M[iir#f][idx$ - 0]))
  );
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #121)"} R[iir#f] == (R[iir#c] + C[iir#c]);
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #122)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#c] + C[iir#c])) ==> (M[iir#c][idx$ - 0] == (M[iir#b][idx$ - 0] + M[iir#f][idx$ - 0]))
  );
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #123)"} R[iir#b] == (R[iir#c] + C[iir#c]);
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #124)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#g] + C[iir#g])) ==> (M[iir#g][idx$ - 0] == AT#RShift(M[iir#c][idx$ - 0], 8))
  );
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #125)"} R[iir#c] == (R[iir#g] + C[iir#g]);
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #126)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#d] + C[iir#d])) ==> (M[iir#d][idx$ - 0] == AT#RShift(M[iir#c][idx$ - 0], 8))
  );
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #127)"} R[iir#c] == (R[iir#d] + C[iir#d]);
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #128)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#e] + C[iir#e])) ==> (M[iir#e][idx$ - 0] == (171 * M[iir#d][idx$ - 0]))
  );
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #129)"} R[iir#d] == (R[iir#e] + C[iir#e]);
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #130)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#b] + C[iir#b])) ==> (M[iir#b][idx$ - 0] == (85 * M[iir#a][idx$ - 0]))
  );
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #131)"} R[iir#a] == (R[iir#b] + C[iir#b]);
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #132)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < ((R[iir#f] + C[iir#f]) - 1)) ==> (M[iir#f][(idx$ + 1) - 0] == M[iir#e][idx$ - 0])
  );
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #133)"} R[iir#e] == ((R[iir#f] + C[iir#f]) - 1);
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #134)"} R[iir#g] == 0;
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #135)"} 0 <= C[iir#g];
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #136)"} 0 <= R[iir#g];
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #137)"} 0 <= C[iir#f];
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #138)"} 0 <= R[iir#f];
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #139)"} 0 <= C[iir#e];
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #140)"} 0 <= R[iir#e];
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #141)"} 0 <= C[iir#d];
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #142)"} 0 <= R[iir#d];
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #143)"} 0 <= C[iir#c];
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #144)"} 0 <= R[iir#c];
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #145)"} 0 <= C[iir#b];
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #146)"} 0 <= R[iir#b];
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #147)"} (R[iir#a] + C[iir#a]) == C#init[iir#a];
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #148)"} 0 <= C[iir#a];
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated #149)"} 0 <= R[iir#a];
  assert {:msg "  28.3: Sub-actor action at 19.3 might not preserve the channel invariant"} (171 * M[iir#g][-1]) == M[iir#f][0];
}
procedure iir#anon$5#add#anon$0#10()
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
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#c] + C[iir#c])) ==> (M[iir#c][idx$ - 0] == (M[iir#b][idx$ - 0] + M[iir#f][idx$ - 0]))
  );
  assume R[iir#f] == (R[iir#c] + C[iir#c]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#c] + C[iir#c])) ==> (M[iir#c][idx$ - 0] == (M[iir#b][idx$ - 0] + M[iir#f][idx$ - 0]))
  );
  assume R[iir#b] == (R[iir#c] + C[iir#c]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#g] + C[iir#g])) ==> (M[iir#g][idx$ - 0] == AT#RShift(M[iir#c][idx$ - 0], 8))
  );
  assume R[iir#c] == (R[iir#g] + C[iir#g]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#d] + C[iir#d])) ==> (M[iir#d][idx$ - 0] == AT#RShift(M[iir#c][idx$ - 0], 8))
  );
  assume R[iir#c] == (R[iir#d] + C[iir#d]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#e] + C[iir#e])) ==> (M[iir#e][idx$ - 0] == (171 * M[iir#d][idx$ - 0]))
  );
  assume R[iir#d] == (R[iir#e] + C[iir#e]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#b] + C[iir#b])) ==> (M[iir#b][idx$ - 0] == (85 * M[iir#a][idx$ - 0]))
  );
  assume R[iir#a] == (R[iir#b] + C[iir#b]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < ((R[iir#f] + C[iir#f]) - 1)) ==> (M[iir#f][(idx$ + 1) - 0] == M[iir#e][idx$ - 0])
  );
  assume R[iir#e] == ((R[iir#f] + C[iir#f]) - 1);
  assume R[iir#g] == 0;
  assume 0 <= C[iir#g];
  assume 0 <= R[iir#g];
  assume 0 <= C[iir#f];
  assume 0 <= R[iir#f];
  assume 0 <= C[iir#e];
  assume 0 <= R[iir#e];
  assume 0 <= C[iir#d];
  assume 0 <= R[iir#d];
  assume 0 <= C[iir#c];
  assume 0 <= R[iir#c];
  assume 0 <= C[iir#b];
  assume 0 <= R[iir#b];
  assume (R[iir#a] + C[iir#a]) == C#init[iir#a];
  assume 0 <= C[iir#a];
  assume 0 <= R[iir#a];
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
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #150)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#c] + C[iir#c])) ==> (M[iir#c][idx$ - 0] == (M[iir#b][idx$ - 0] + M[iir#f][idx$ - 0]))
  );
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #151)"} R[iir#f] == (R[iir#c] + C[iir#c]);
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #152)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#c] + C[iir#c])) ==> (M[iir#c][idx$ - 0] == (M[iir#b][idx$ - 0] + M[iir#f][idx$ - 0]))
  );
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #153)"} R[iir#b] == (R[iir#c] + C[iir#c]);
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #154)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#g] + C[iir#g])) ==> (M[iir#g][idx$ - 0] == AT#RShift(M[iir#c][idx$ - 0], 8))
  );
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #155)"} R[iir#c] == (R[iir#g] + C[iir#g]);
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #156)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#d] + C[iir#d])) ==> (M[iir#d][idx$ - 0] == AT#RShift(M[iir#c][idx$ - 0], 8))
  );
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #157)"} R[iir#c] == (R[iir#d] + C[iir#d]);
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #158)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#e] + C[iir#e])) ==> (M[iir#e][idx$ - 0] == (171 * M[iir#d][idx$ - 0]))
  );
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #159)"} R[iir#d] == (R[iir#e] + C[iir#e]);
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #160)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#b] + C[iir#b])) ==> (M[iir#b][idx$ - 0] == (85 * M[iir#a][idx$ - 0]))
  );
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #161)"} R[iir#a] == (R[iir#b] + C[iir#b]);
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #162)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < ((R[iir#f] + C[iir#f]) - 1)) ==> (M[iir#f][(idx$ + 1) - 0] == M[iir#e][idx$ - 0])
  );
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #163)"} R[iir#e] == ((R[iir#f] + C[iir#f]) - 1);
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #164)"} R[iir#g] == 0;
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #165)"} 0 <= C[iir#g];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #166)"} 0 <= R[iir#g];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #167)"} 0 <= C[iir#f];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #168)"} 0 <= R[iir#f];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #169)"} 0 <= C[iir#e];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #170)"} 0 <= R[iir#e];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #171)"} 0 <= C[iir#d];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #172)"} 0 <= R[iir#d];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #173)"} 0 <= C[iir#c];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #174)"} 0 <= R[iir#c];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #175)"} 0 <= C[iir#b];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #176)"} 0 <= R[iir#b];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #177)"} (R[iir#a] + C[iir#a]) == C#init[iir#a];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #178)"} 0 <= C[iir#a];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #179)"} 0 <= R[iir#a];
  assert {:msg "  28.3: Sub-actor action at 3.3 might not preserve the channel invariant"} (171 * M[iir#g][-1]) == M[iir#f][0];
}
procedure iir#anon$5#exit#11()
  modifies C, R, M, St;
{
  assume C#init[iir#a] == 1;
  assume C#init[iir#b] == 0;
  assume C#init[iir#c] == 0;
  assume C#init[iir#d] == 0;
  assume C#init[iir#e] == 0;
  assume C#init[iir#g] == 0;
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#c] + C[iir#c])) ==> (M[iir#c][idx$ - 0] == (M[iir#b][idx$ - 0] + M[iir#f][idx$ - 0]))
  );
  assume R[iir#f] == (R[iir#c] + C[iir#c]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#c] + C[iir#c])) ==> (M[iir#c][idx$ - 0] == (M[iir#b][idx$ - 0] + M[iir#f][idx$ - 0]))
  );
  assume R[iir#b] == (R[iir#c] + C[iir#c]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#g] + C[iir#g])) ==> (M[iir#g][idx$ - 0] == AT#RShift(M[iir#c][idx$ - 0], 8))
  );
  assume R[iir#c] == (R[iir#g] + C[iir#g]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#d] + C[iir#d])) ==> (M[iir#d][idx$ - 0] == AT#RShift(M[iir#c][idx$ - 0], 8))
  );
  assume R[iir#c] == (R[iir#d] + C[iir#d]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#e] + C[iir#e])) ==> (M[iir#e][idx$ - 0] == (171 * M[iir#d][idx$ - 0]))
  );
  assume R[iir#d] == (R[iir#e] + C[iir#e]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[iir#b] + C[iir#b])) ==> (M[iir#b][idx$ - 0] == (85 * M[iir#a][idx$ - 0]))
  );
  assume R[iir#a] == (R[iir#b] + C[iir#b]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < ((R[iir#f] + C[iir#f]) - 1)) ==> (M[iir#f][(idx$ + 1) - 0] == M[iir#e][idx$ - 0])
  );
  assume R[iir#e] == ((R[iir#f] + C[iir#f]) - 1);
  assume R[iir#g] == 0;
  assume 0 <= C[iir#g];
  assume 0 <= R[iir#g];
  assume 0 <= C[iir#f];
  assume 0 <= R[iir#f];
  assume 0 <= C[iir#e];
  assume 0 <= R[iir#e];
  assume 0 <= C[iir#d];
  assume 0 <= R[iir#d];
  assume 0 <= C[iir#c];
  assume 0 <= R[iir#c];
  assume 0 <= C[iir#b];
  assume 0 <= R[iir#b];
  assume (R[iir#a] + C[iir#a]) == C#init[iir#a];
  assume 0 <= C[iir#a];
  assume 0 <= R[iir#a];
  assume (171 * M[iir#g][-1]) == M[iir#f][0];
  assume !(((((1 <= C[iir#e]) || (1 <= C[iir#a])) || (1 <= C[iir#d])) || (1 <= C[iir#c])) || ((1 <= C[iir#b]) && (1 <= C[iir#f])));
  assert {:msg "  23.3: The network might leave unread tokens on channel a"} C[iir#a] == 0;
  assert {:msg "  23.3: The network might leave unread tokens on channel b"} C[iir#b] == 0;
  assert {:msg "  23.3: The network might leave unread tokens on channel c"} C[iir#c] == 0;
  assert {:msg "  23.3: The network might leave unread tokens on channel d"} C[iir#d] == 0;
  assert {:msg "  23.3: The network might leave unread tokens on channel e"} C[iir#e] == 0;
  assert {:msg "  23.3: The network might not produce the specified number of tokens on output out"} C[iir#g] == 1;
  assert {:msg "  23.26: Network output might not conform to specified action output"} M[iir#g][0] == AT#RShift((171 * M[iir#g][R[iir#g] - 1]) + (85 * M[iir#a][0]), 8);
  R[iir#g] := R[iir#g] + C[iir#g];
  C[iir#g] := 0;
  assert {:msg "  25.3: The network might not preserve the network invariant"} C[iir#f] == 1;
  assert {:msg "  26.3: The network might not preserve the network invariant"} M[iir#f][R[iir#f]] == (171 * M[iir#g][R[iir#g] - 1]);
}

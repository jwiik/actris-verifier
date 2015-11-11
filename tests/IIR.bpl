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
  assert {:msg "  Channel invariant might not hold on action entry (generated)"} R[iir#f] == (R[iir#c] + C[iir#c]);
  assert {:msg "  Channel invariant might not hold on action entry (generated)"} R[iir#b] == (R[iir#c] + C[iir#c]);
  assert {:msg "  Channel invariant might not hold on action entry (generated)"} R[iir#c] == (R[iir#g] + C[iir#g]);
  assert {:msg "  Channel invariant might not hold on action entry (generated)"} R[iir#c] == (R[iir#d] + C[iir#d]);
  assert {:msg "  Channel invariant might not hold on action entry (generated)"} R[iir#d] == (R[iir#e] + C[iir#e]);
  assert {:msg "  Channel invariant might not hold on action entry (generated)"} R[iir#a] == (R[iir#b] + C[iir#b]);
  assert {:msg "  Channel invariant might not hold on action entry (generated)"} R[iir#e] == ((R[iir#f] + C[iir#f]) - 1);
  assert {:msg "  Channel invariant might not hold on action entry (generated)"} R[iir#g] == 0;
  assert {:msg "  Channel invariant might not hold on action entry (generated)"} 0 <= C[iir#g];
  assert {:msg "  Channel invariant might not hold on action entry (generated)"} 0 <= R[iir#g];
  assert {:msg "  Channel invariant might not hold on action entry (generated)"} 0 <= C[iir#f];
  assert {:msg "  Channel invariant might not hold on action entry (generated)"} 0 <= R[iir#f];
  assert {:msg "  Channel invariant might not hold on action entry (generated)"} 0 <= C[iir#e];
  assert {:msg "  Channel invariant might not hold on action entry (generated)"} 0 <= R[iir#e];
  assert {:msg "  Channel invariant might not hold on action entry (generated)"} 0 <= C[iir#d];
  assert {:msg "  Channel invariant might not hold on action entry (generated)"} 0 <= R[iir#d];
  assert {:msg "  Channel invariant might not hold on action entry (generated)"} 0 <= C[iir#c];
  assert {:msg "  Channel invariant might not hold on action entry (generated)"} 0 <= R[iir#c];
  assert {:msg "  Channel invariant might not hold on action entry (generated)"} 0 <= C[iir#b];
  assert {:msg "  Channel invariant might not hold on action entry (generated)"} 0 <= R[iir#b];
  assert {:msg "  Channel invariant might not hold on action entry (generated)"} (R[iir#a] + C[iir#a]) == C#init[iir#a];
  assert {:msg "  Channel invariant might not hold on action entry (generated)"} 0 <= C[iir#a];
  assert {:msg "  Channel invariant might not hold on action entry (generated)"} 0 <= R[iir#a];
  assert {:msg "  28.3: Channel invariant might not hold on action entry"} (171 * M[iir#g][-1]) == M[iir#f][0];
  assert {:msg "  29.3: Channel invariant might not hold on action entry"} (forall i: int :: 
    (0 <= i) && (i < (R[iir#b] + C[iir#b])) ==> (M[iir#b][i] == (85 * M[iir#a][i]))
  );
  assert {:msg "  30.3: Channel invariant might not hold on action entry"} (forall i: int :: 
    (0 <= i) && (i < (R[iir#c] + C[iir#c])) ==> (M[iir#c][i] == (M[iir#b][i] + M[iir#f][i]))
  );
  assert {:msg "  31.3: Channel invariant might not hold on action entry"} (forall i: int :: 
    (0 <= i) && (i < (R[iir#d] + C[iir#d])) ==> (M[iir#d][i] == AT#RShift(M[iir#c][i], 8))
  );
  assert {:msg "  32.3: Channel invariant might not hold on action entry"} (forall i: int :: 
    (0 <= i) && (i < (R[iir#g] + C[iir#g])) ==> (M[iir#g][i] == AT#RShift(M[iir#c][i], 8))
  );
  assert {:msg "  33.3: Channel invariant might not hold on action entry"} (forall i: int :: 
    (0 <= i) && (i < (R[iir#e] + C[iir#e])) ==> (M[iir#e][i] == (171 * M[iir#d][i]))
  );
  assert {:msg "  34.3: Channel invariant might not hold on action entry"} (forall i: int :: 
    (1 <= i) && (i < (R[iir#f] + C[iir#f])) ==> (M[iir#f][i] == M[iir#e][i - 1])
  );
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
  assume R[iir#f] == (R[iir#c] + C[iir#c]);
  assume R[iir#b] == (R[iir#c] + C[iir#c]);
  assume R[iir#c] == (R[iir#g] + C[iir#g]);
  assume R[iir#c] == (R[iir#d] + C[iir#d]);
  assume R[iir#d] == (R[iir#e] + C[iir#e]);
  assume R[iir#a] == (R[iir#b] + C[iir#b]);
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
  assume (forall i: int :: 
    (0 <= i) && (i < (R[iir#b] + C[iir#b])) ==> (M[iir#b][i] == (85 * M[iir#a][i]))
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[iir#c] + C[iir#c])) ==> (M[iir#c][i] == (M[iir#b][i] + M[iir#f][i]))
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[iir#d] + C[iir#d])) ==> (M[iir#d][i] == AT#RShift(M[iir#c][i], 8))
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[iir#g] + C[iir#g])) ==> (M[iir#g][i] == AT#RShift(M[iir#c][i], 8))
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[iir#e] + C[iir#e])) ==> (M[iir#e][i] == (171 * M[iir#d][i]))
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[iir#f] + C[iir#f])) ==> (M[iir#f][i] == M[iir#e][i - 1])
  );
  assume true;
  assume 1 <= C[iir#e];
  in#i := M[iir#e][R[iir#e]];
  R[iir#e] := R[iir#e] + 1;
  C[iir#e] := C[iir#e] - 1;
  M[iir#f][R[iir#f] + C[iir#f]] := in#i;
  C[iir#f] := C[iir#f] + 1;
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated)"} R[iir#f] == (R[iir#c] + C[iir#c]);
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated)"} R[iir#b] == (R[iir#c] + C[iir#c]);
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated)"} R[iir#c] == (R[iir#g] + C[iir#g]);
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated)"} R[iir#c] == (R[iir#d] + C[iir#d]);
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated)"} R[iir#d] == (R[iir#e] + C[iir#e]);
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated)"} R[iir#a] == (R[iir#b] + C[iir#b]);
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated)"} R[iir#e] == ((R[iir#f] + C[iir#f]) - 1);
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated)"} R[iir#g] == 0;
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated)"} 0 <= C[iir#g];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated)"} 0 <= R[iir#g];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated)"} 0 <= C[iir#f];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated)"} 0 <= R[iir#f];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated)"} 0 <= C[iir#e];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated)"} 0 <= R[iir#e];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated)"} 0 <= C[iir#d];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated)"} 0 <= R[iir#d];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated)"} 0 <= C[iir#c];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated)"} 0 <= R[iir#c];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated)"} 0 <= C[iir#b];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated)"} 0 <= R[iir#b];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated)"} (R[iir#a] + C[iir#a]) == C#init[iir#a];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated)"} 0 <= C[iir#a];
  assert {:msg "  Sub-actor action at 9.3 might not preserve the channel invariant (generated)"} 0 <= R[iir#a];
  assert {:msg "  28.3: Sub-actor action at 9.3 might not preserve the channel invariant"} (171 * M[iir#g][-1]) == M[iir#f][0];
  assert {:msg "  29.3: Sub-actor action at 9.3 might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[iir#b] + C[iir#b])) ==> (M[iir#b][i] == (85 * M[iir#a][i]))
  );
  assert {:msg "  30.3: Sub-actor action at 9.3 might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[iir#c] + C[iir#c])) ==> (M[iir#c][i] == (M[iir#b][i] + M[iir#f][i]))
  );
  assert {:msg "  31.3: Sub-actor action at 9.3 might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[iir#d] + C[iir#d])) ==> (M[iir#d][i] == AT#RShift(M[iir#c][i], 8))
  );
  assert {:msg "  32.3: Sub-actor action at 9.3 might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[iir#g] + C[iir#g])) ==> (M[iir#g][i] == AT#RShift(M[iir#c][i], 8))
  );
  assert {:msg "  33.3: Sub-actor action at 9.3 might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[iir#e] + C[iir#e])) ==> (M[iir#e][i] == (171 * M[iir#d][i]))
  );
  assert {:msg "  34.3: Sub-actor action at 9.3 might not preserve the channel invariant"} (forall i: int :: 
    (1 <= i) && (i < (R[iir#f] + C[iir#f])) ==> (M[iir#f][i] == M[iir#e][i - 1])
  );
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
  assume R[iir#f] == (R[iir#c] + C[iir#c]);
  assume R[iir#b] == (R[iir#c] + C[iir#c]);
  assume R[iir#c] == (R[iir#g] + C[iir#g]);
  assume R[iir#c] == (R[iir#d] + C[iir#d]);
  assume R[iir#d] == (R[iir#e] + C[iir#e]);
  assume R[iir#a] == (R[iir#b] + C[iir#b]);
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
  assume (forall i: int :: 
    (0 <= i) && (i < (R[iir#b] + C[iir#b])) ==> (M[iir#b][i] == (85 * M[iir#a][i]))
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[iir#c] + C[iir#c])) ==> (M[iir#c][i] == (M[iir#b][i] + M[iir#f][i]))
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[iir#d] + C[iir#d])) ==> (M[iir#d][i] == AT#RShift(M[iir#c][i], 8))
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[iir#g] + C[iir#g])) ==> (M[iir#g][i] == AT#RShift(M[iir#c][i], 8))
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[iir#e] + C[iir#e])) ==> (M[iir#e][i] == (171 * M[iir#d][i]))
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[iir#f] + C[iir#f])) ==> (M[iir#f][i] == M[iir#e][i - 1])
  );
  assume true;
  assume 1 <= C[iir#a];
  in#i := M[iir#a][R[iir#a]];
  R[iir#a] := R[iir#a] + 1;
  C[iir#a] := C[iir#a] - 1;
  M[iir#b][R[iir#b] + C[iir#b]] := ActorParam#c * in#i;
  C[iir#b] := C[iir#b] + 1;
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated)"} R[iir#f] == (R[iir#c] + C[iir#c]);
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated)"} R[iir#b] == (R[iir#c] + C[iir#c]);
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated)"} R[iir#c] == (R[iir#g] + C[iir#g]);
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated)"} R[iir#c] == (R[iir#d] + C[iir#d]);
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated)"} R[iir#d] == (R[iir#e] + C[iir#e]);
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated)"} R[iir#a] == (R[iir#b] + C[iir#b]);
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated)"} R[iir#e] == ((R[iir#f] + C[iir#f]) - 1);
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated)"} R[iir#g] == 0;
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated)"} 0 <= C[iir#g];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated)"} 0 <= R[iir#g];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated)"} 0 <= C[iir#f];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated)"} 0 <= R[iir#f];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated)"} 0 <= C[iir#e];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated)"} 0 <= R[iir#e];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated)"} 0 <= C[iir#d];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated)"} 0 <= R[iir#d];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated)"} 0 <= C[iir#c];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated)"} 0 <= R[iir#c];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated)"} 0 <= C[iir#b];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated)"} 0 <= R[iir#b];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated)"} (R[iir#a] + C[iir#a]) == C#init[iir#a];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated)"} 0 <= C[iir#a];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated)"} 0 <= R[iir#a];
  assert {:msg "  28.3: Sub-actor action at 14.3 might not preserve the channel invariant"} (171 * M[iir#g][-1]) == M[iir#f][0];
  assert {:msg "  29.3: Sub-actor action at 14.3 might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[iir#b] + C[iir#b])) ==> (M[iir#b][i] == (85 * M[iir#a][i]))
  );
  assert {:msg "  30.3: Sub-actor action at 14.3 might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[iir#c] + C[iir#c])) ==> (M[iir#c][i] == (M[iir#b][i] + M[iir#f][i]))
  );
  assert {:msg "  31.3: Sub-actor action at 14.3 might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[iir#d] + C[iir#d])) ==> (M[iir#d][i] == AT#RShift(M[iir#c][i], 8))
  );
  assert {:msg "  32.3: Sub-actor action at 14.3 might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[iir#g] + C[iir#g])) ==> (M[iir#g][i] == AT#RShift(M[iir#c][i], 8))
  );
  assert {:msg "  33.3: Sub-actor action at 14.3 might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[iir#e] + C[iir#e])) ==> (M[iir#e][i] == (171 * M[iir#d][i]))
  );
  assert {:msg "  34.3: Sub-actor action at 14.3 might not preserve the channel invariant"} (forall i: int :: 
    (1 <= i) && (i < (R[iir#f] + C[iir#f])) ==> (M[iir#f][i] == M[iir#e][i - 1])
  );
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
  assume R[iir#f] == (R[iir#c] + C[iir#c]);
  assume R[iir#b] == (R[iir#c] + C[iir#c]);
  assume R[iir#c] == (R[iir#g] + C[iir#g]);
  assume R[iir#c] == (R[iir#d] + C[iir#d]);
  assume R[iir#d] == (R[iir#e] + C[iir#e]);
  assume R[iir#a] == (R[iir#b] + C[iir#b]);
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
  assume (forall i: int :: 
    (0 <= i) && (i < (R[iir#b] + C[iir#b])) ==> (M[iir#b][i] == (85 * M[iir#a][i]))
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[iir#c] + C[iir#c])) ==> (M[iir#c][i] == (M[iir#b][i] + M[iir#f][i]))
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[iir#d] + C[iir#d])) ==> (M[iir#d][i] == AT#RShift(M[iir#c][i], 8))
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[iir#g] + C[iir#g])) ==> (M[iir#g][i] == AT#RShift(M[iir#c][i], 8))
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[iir#e] + C[iir#e])) ==> (M[iir#e][i] == (171 * M[iir#d][i]))
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[iir#f] + C[iir#f])) ==> (M[iir#f][i] == M[iir#e][i - 1])
  );
  assume true;
  assume 1 <= C[iir#d];
  in#i := M[iir#d][R[iir#d]];
  R[iir#d] := R[iir#d] + 1;
  C[iir#d] := C[iir#d] - 1;
  M[iir#e][R[iir#e] + C[iir#e]] := ActorParam#c * in#i;
  C[iir#e] := C[iir#e] + 1;
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated)"} R[iir#f] == (R[iir#c] + C[iir#c]);
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated)"} R[iir#b] == (R[iir#c] + C[iir#c]);
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated)"} R[iir#c] == (R[iir#g] + C[iir#g]);
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated)"} R[iir#c] == (R[iir#d] + C[iir#d]);
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated)"} R[iir#d] == (R[iir#e] + C[iir#e]);
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated)"} R[iir#a] == (R[iir#b] + C[iir#b]);
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated)"} R[iir#e] == ((R[iir#f] + C[iir#f]) - 1);
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated)"} R[iir#g] == 0;
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated)"} 0 <= C[iir#g];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated)"} 0 <= R[iir#g];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated)"} 0 <= C[iir#f];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated)"} 0 <= R[iir#f];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated)"} 0 <= C[iir#e];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated)"} 0 <= R[iir#e];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated)"} 0 <= C[iir#d];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated)"} 0 <= R[iir#d];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated)"} 0 <= C[iir#c];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated)"} 0 <= R[iir#c];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated)"} 0 <= C[iir#b];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated)"} 0 <= R[iir#b];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated)"} (R[iir#a] + C[iir#a]) == C#init[iir#a];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated)"} 0 <= C[iir#a];
  assert {:msg "  Sub-actor action at 14.3 might not preserve the channel invariant (generated)"} 0 <= R[iir#a];
  assert {:msg "  28.3: Sub-actor action at 14.3 might not preserve the channel invariant"} (171 * M[iir#g][-1]) == M[iir#f][0];
  assert {:msg "  29.3: Sub-actor action at 14.3 might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[iir#b] + C[iir#b])) ==> (M[iir#b][i] == (85 * M[iir#a][i]))
  );
  assert {:msg "  30.3: Sub-actor action at 14.3 might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[iir#c] + C[iir#c])) ==> (M[iir#c][i] == (M[iir#b][i] + M[iir#f][i]))
  );
  assert {:msg "  31.3: Sub-actor action at 14.3 might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[iir#d] + C[iir#d])) ==> (M[iir#d][i] == AT#RShift(M[iir#c][i], 8))
  );
  assert {:msg "  32.3: Sub-actor action at 14.3 might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[iir#g] + C[iir#g])) ==> (M[iir#g][i] == AT#RShift(M[iir#c][i], 8))
  );
  assert {:msg "  33.3: Sub-actor action at 14.3 might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[iir#e] + C[iir#e])) ==> (M[iir#e][i] == (171 * M[iir#d][i]))
  );
  assert {:msg "  34.3: Sub-actor action at 14.3 might not preserve the channel invariant"} (forall i: int :: 
    (1 <= i) && (i < (R[iir#f] + C[iir#f])) ==> (M[iir#f][i] == M[iir#e][i - 1])
  );
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
  assume R[iir#f] == (R[iir#c] + C[iir#c]);
  assume R[iir#b] == (R[iir#c] + C[iir#c]);
  assume R[iir#c] == (R[iir#g] + C[iir#g]);
  assume R[iir#c] == (R[iir#d] + C[iir#d]);
  assume R[iir#d] == (R[iir#e] + C[iir#e]);
  assume R[iir#a] == (R[iir#b] + C[iir#b]);
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
  assume (forall i: int :: 
    (0 <= i) && (i < (R[iir#b] + C[iir#b])) ==> (M[iir#b][i] == (85 * M[iir#a][i]))
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[iir#c] + C[iir#c])) ==> (M[iir#c][i] == (M[iir#b][i] + M[iir#f][i]))
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[iir#d] + C[iir#d])) ==> (M[iir#d][i] == AT#RShift(M[iir#c][i], 8))
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[iir#g] + C[iir#g])) ==> (M[iir#g][i] == AT#RShift(M[iir#c][i], 8))
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[iir#e] + C[iir#e])) ==> (M[iir#e][i] == (171 * M[iir#d][i]))
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[iir#f] + C[iir#f])) ==> (M[iir#f][i] == M[iir#e][i - 1])
  );
  assume true;
  assume 1 <= C[iir#c];
  in#i := M[iir#c][R[iir#c]];
  R[iir#c] := R[iir#c] + 1;
  C[iir#c] := C[iir#c] - 1;
  M[iir#d][R[iir#d] + C[iir#d]] := AT#RShift(in#i, ActorParam#s);
  C[iir#d] := C[iir#d] + 1;
  M[iir#g][R[iir#g] + C[iir#g]] := AT#RShift(in#i, ActorParam#s);
  C[iir#g] := C[iir#g] + 1;
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated)"} R[iir#f] == (R[iir#c] + C[iir#c]);
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated)"} R[iir#b] == (R[iir#c] + C[iir#c]);
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated)"} R[iir#c] == (R[iir#g] + C[iir#g]);
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated)"} R[iir#c] == (R[iir#d] + C[iir#d]);
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated)"} R[iir#d] == (R[iir#e] + C[iir#e]);
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated)"} R[iir#a] == (R[iir#b] + C[iir#b]);
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated)"} R[iir#e] == ((R[iir#f] + C[iir#f]) - 1);
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated)"} R[iir#g] == 0;
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated)"} 0 <= C[iir#g];
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated)"} 0 <= R[iir#g];
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated)"} 0 <= C[iir#f];
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated)"} 0 <= R[iir#f];
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated)"} 0 <= C[iir#e];
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated)"} 0 <= R[iir#e];
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated)"} 0 <= C[iir#d];
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated)"} 0 <= R[iir#d];
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated)"} 0 <= C[iir#c];
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated)"} 0 <= R[iir#c];
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated)"} 0 <= C[iir#b];
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated)"} 0 <= R[iir#b];
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated)"} (R[iir#a] + C[iir#a]) == C#init[iir#a];
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated)"} 0 <= C[iir#a];
  assert {:msg "  Sub-actor action at 19.3 might not preserve the channel invariant (generated)"} 0 <= R[iir#a];
  assert {:msg "  28.3: Sub-actor action at 19.3 might not preserve the channel invariant"} (171 * M[iir#g][-1]) == M[iir#f][0];
  assert {:msg "  29.3: Sub-actor action at 19.3 might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[iir#b] + C[iir#b])) ==> (M[iir#b][i] == (85 * M[iir#a][i]))
  );
  assert {:msg "  30.3: Sub-actor action at 19.3 might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[iir#c] + C[iir#c])) ==> (M[iir#c][i] == (M[iir#b][i] + M[iir#f][i]))
  );
  assert {:msg "  31.3: Sub-actor action at 19.3 might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[iir#d] + C[iir#d])) ==> (M[iir#d][i] == AT#RShift(M[iir#c][i], 8))
  );
  assert {:msg "  32.3: Sub-actor action at 19.3 might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[iir#g] + C[iir#g])) ==> (M[iir#g][i] == AT#RShift(M[iir#c][i], 8))
  );
  assert {:msg "  33.3: Sub-actor action at 19.3 might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[iir#e] + C[iir#e])) ==> (M[iir#e][i] == (171 * M[iir#d][i]))
  );
  assert {:msg "  34.3: Sub-actor action at 19.3 might not preserve the channel invariant"} (forall i: int :: 
    (1 <= i) && (i < (R[iir#f] + C[iir#f])) ==> (M[iir#f][i] == M[iir#e][i - 1])
  );
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
  assume R[iir#f] == (R[iir#c] + C[iir#c]);
  assume R[iir#b] == (R[iir#c] + C[iir#c]);
  assume R[iir#c] == (R[iir#g] + C[iir#g]);
  assume R[iir#c] == (R[iir#d] + C[iir#d]);
  assume R[iir#d] == (R[iir#e] + C[iir#e]);
  assume R[iir#a] == (R[iir#b] + C[iir#b]);
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
  assume (forall i: int :: 
    (0 <= i) && (i < (R[iir#b] + C[iir#b])) ==> (M[iir#b][i] == (85 * M[iir#a][i]))
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[iir#c] + C[iir#c])) ==> (M[iir#c][i] == (M[iir#b][i] + M[iir#f][i]))
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[iir#d] + C[iir#d])) ==> (M[iir#d][i] == AT#RShift(M[iir#c][i], 8))
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[iir#g] + C[iir#g])) ==> (M[iir#g][i] == AT#RShift(M[iir#c][i], 8))
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[iir#e] + C[iir#e])) ==> (M[iir#e][i] == (171 * M[iir#d][i]))
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[iir#f] + C[iir#f])) ==> (M[iir#f][i] == M[iir#e][i - 1])
  );
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
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated)"} R[iir#f] == (R[iir#c] + C[iir#c]);
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated)"} R[iir#b] == (R[iir#c] + C[iir#c]);
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated)"} R[iir#c] == (R[iir#g] + C[iir#g]);
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated)"} R[iir#c] == (R[iir#d] + C[iir#d]);
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated)"} R[iir#d] == (R[iir#e] + C[iir#e]);
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated)"} R[iir#a] == (R[iir#b] + C[iir#b]);
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated)"} R[iir#e] == ((R[iir#f] + C[iir#f]) - 1);
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated)"} R[iir#g] == 0;
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated)"} 0 <= C[iir#g];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated)"} 0 <= R[iir#g];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated)"} 0 <= C[iir#f];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated)"} 0 <= R[iir#f];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated)"} 0 <= C[iir#e];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated)"} 0 <= R[iir#e];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated)"} 0 <= C[iir#d];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated)"} 0 <= R[iir#d];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated)"} 0 <= C[iir#c];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated)"} 0 <= R[iir#c];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated)"} 0 <= C[iir#b];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated)"} 0 <= R[iir#b];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated)"} (R[iir#a] + C[iir#a]) == C#init[iir#a];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated)"} 0 <= C[iir#a];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated)"} 0 <= R[iir#a];
  assert {:msg "  28.3: Sub-actor action at 3.3 might not preserve the channel invariant"} (171 * M[iir#g][-1]) == M[iir#f][0];
  assert {:msg "  29.3: Sub-actor action at 3.3 might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[iir#b] + C[iir#b])) ==> (M[iir#b][i] == (85 * M[iir#a][i]))
  );
  assert {:msg "  30.3: Sub-actor action at 3.3 might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[iir#c] + C[iir#c])) ==> (M[iir#c][i] == (M[iir#b][i] + M[iir#f][i]))
  );
  assert {:msg "  31.3: Sub-actor action at 3.3 might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[iir#d] + C[iir#d])) ==> (M[iir#d][i] == AT#RShift(M[iir#c][i], 8))
  );
  assert {:msg "  32.3: Sub-actor action at 3.3 might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[iir#g] + C[iir#g])) ==> (M[iir#g][i] == AT#RShift(M[iir#c][i], 8))
  );
  assert {:msg "  33.3: Sub-actor action at 3.3 might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[iir#e] + C[iir#e])) ==> (M[iir#e][i] == (171 * M[iir#d][i]))
  );
  assert {:msg "  34.3: Sub-actor action at 3.3 might not preserve the channel invariant"} (forall i: int :: 
    (1 <= i) && (i < (R[iir#f] + C[iir#f])) ==> (M[iir#f][i] == M[iir#e][i - 1])
  );
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
  assume R[iir#f] == (R[iir#c] + C[iir#c]);
  assume R[iir#b] == (R[iir#c] + C[iir#c]);
  assume R[iir#c] == (R[iir#g] + C[iir#g]);
  assume R[iir#c] == (R[iir#d] + C[iir#d]);
  assume R[iir#d] == (R[iir#e] + C[iir#e]);
  assume R[iir#a] == (R[iir#b] + C[iir#b]);
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
  assume (forall i: int :: 
    (0 <= i) && (i < (R[iir#b] + C[iir#b])) ==> (M[iir#b][i] == (85 * M[iir#a][i]))
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[iir#c] + C[iir#c])) ==> (M[iir#c][i] == (M[iir#b][i] + M[iir#f][i]))
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[iir#d] + C[iir#d])) ==> (M[iir#d][i] == AT#RShift(M[iir#c][i], 8))
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[iir#g] + C[iir#g])) ==> (M[iir#g][i] == AT#RShift(M[iir#c][i], 8))
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[iir#e] + C[iir#e])) ==> (M[iir#e][i] == (171 * M[iir#d][i]))
  );
  assume (forall i: int :: 
    (1 <= i) && (i < (R[iir#f] + C[iir#f])) ==> (M[iir#f][i] == M[iir#e][i - 1])
  );
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

// ---------------------------------------------------------------
// -- Types and global variables ---------------------------------
// ---------------------------------------------------------------
type Chan a;
type Actor;
type CType = <a>[Chan a]bv32;
type MType = <a>[Chan a][bv32]a;
type State;

var M: MType;
var C: CType;
var R: CType; 
var N: CType;
var C#init: CType;
var St: [Actor]State;

const unique this#: Actor;

type List a = [bv32]a;
var AT#intlst: List bv32;


function AT#Abs(x: int): int { if 0 <= x then x else -x }
function AT#Div(int, int): int;
function AT#Mod(int, int): int;
axiom (forall a,b: int :: AT#Div(a,b)*b + AT#Mod(a,b) == a);
axiom (forall a,b: int :: 0 <= AT#Mod(a,b) && AT#Mod(a,b) < AT#Abs(b));

function {:bvbuiltin "bvand"} AT#BvAnd(a: bv32, b: bv32): bv32;
function {:bvbuiltin "bvadd"} AT#BvAdd(a: bv32, b: bv32): bv32;
function {:bvbuiltin "bvsub"} AT#BvSub(a: bv32, b: bv32): bv32;
function {:bvbuiltin "bvule"} AT#BvUle(a: bv32, b: bv32): bool;
function {:bvbuiltin "bvult"} AT#BvUlt(a: bv32, b: bv32): bool;
function AT#RShift(bv32,bv32): int;
function AT#LShift(bv32,bv32): int;

// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

procedure Add#anon$0#0()
  modifies C, R, M, St;
{
  var IV#in#i: bv32;
  assume true;
}
procedure Net#init#1()
  modifies C, R, M, St;
{
  assume C[Net#a] == 0bv32;
  assume R[Net#a] == 0bv32;
  assume C[Net#c] == 0bv32;
  assume R[Net#c] == 0bv32;
}
const unique Net#add: Actor;
const unique Net#a: Chan (bv32);
const unique Net#c: Chan (bv32);
procedure Net#anon$1#entry#2()
  modifies C, R, M, St;
{
  var ActionPH#y: bv32;
  assume C#init[Net#a] == 1bv32;
  assume C#init[Net#c] == 0bv32;
  assume R[Net#a] == 0bv32;
  assume R[Net#c] == 0bv32;
  assume C#init == C;
  assert {:msg "  Channel invariant might not hold on action entry (generated #0)"} AT#BvUle(0bv32, R[Net#a]);
  assert {:msg "  Channel invariant might not hold on action entry (generated #1)"} AT#BvUle(0bv32, C[Net#a]);
  assert {:msg "  Channel invariant might not hold on action entry (generated #2)"} AT#BvAdd(R[Net#a], C[Net#a]) == C#init[Net#a];
  assert {:msg "  Channel invariant might not hold on action entry (generated #3)"} AT#BvUle(0bv32, R[Net#c]);
  assert {:msg "  Channel invariant might not hold on action entry (generated #4)"} AT#BvUle(0bv32, C[Net#c]);
  assert {:msg "  Channel invariant might not hold on action entry (generated #5)"} R[Net#c] == 0bv32;
  assert {:msg "  Channel invariant might not hold on action entry (generated #6)"} R[Net#a] == AT#BvAdd(R[Net#c], C[Net#c]);
  assert {:msg "  Channel invariant might not hold on action entry (generated #7)"} (forall idx$: bv32 :: 
    AT#BvUle(0bv32, idx$) && AT#BvUlt(idx$, AT#BvAdd(R[Net#c], C[Net#c])) ==> (M[Net#c][idx$] == AT#BvAnd(M[Net#a][idx$], 2bv32))
  );
}
procedure Net#anon$1#Add#anon$0#3()
  modifies C, R, M, St;
{
  var St#next: State;
  var in#i: bv32;
  assume C#init[Net#a] == 1bv32;
  assume C#init[Net#c] == 0bv32;
  assume AT#BvUle(0bv32, R[Net#a]);
  assume AT#BvUle(0bv32, C[Net#a]);
  assume AT#BvAdd(R[Net#a], C[Net#a]) == C#init[Net#a];
  assume AT#BvUle(0bv32, R[Net#c]);
  assume AT#BvUle(0bv32, C[Net#c]);
  assume R[Net#c] == 0bv32;
  assume R[Net#a] == AT#BvAdd(R[Net#c], C[Net#c]);
  assume (forall idx$: bv32 :: 
    AT#BvUle(0bv32, idx$) && AT#BvUlt(idx$, AT#BvAdd(R[Net#c], C[Net#c])) ==> (M[Net#c][idx$] == AT#BvAnd(M[Net#a][idx$], 2bv32))
  );
  assume true;
  assume AT#BvUle(1bv32, C[Net#a]);
  in#i := M[Net#a][R[Net#a]];
  R[Net#a] := AT#BvAdd(R[Net#a], 1bv32);
  C[Net#a] := AT#BvSub(C[Net#a], 1bv32);
  M[Net#c][AT#BvAdd(R[Net#c], C[Net#c])] := AT#BvAnd(in#i, 2bv32);
  C[Net#c] := AT#BvAdd(C[Net#c], 1bv32);
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #8)"} AT#BvUle(0bv32, R[Net#a]);
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #9)"} AT#BvUle(0bv32, C[Net#a]);
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #10)"} AT#BvAdd(R[Net#a], C[Net#a]) == C#init[Net#a];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #11)"} AT#BvUle(0bv32, R[Net#c]);
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #12)"} AT#BvUle(0bv32, C[Net#c]);
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #13)"} R[Net#c] == 0bv32;
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #14)"} R[Net#a] == AT#BvAdd(R[Net#c], C[Net#c]);
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #15)"} (forall idx$: bv32 :: 
    AT#BvUle(0bv32, idx$) && AT#BvUlt(idx$, AT#BvAdd(R[Net#c], C[Net#c])) ==> (M[Net#c][idx$] == AT#BvAnd(M[Net#a][idx$], 2bv32))
  );
}
procedure Net#anon$1#exit#4()
  modifies C, R, M, St;
{
  var ActionPH#y: bv32;
  assume C#init[Net#a] == 1bv32;
  assume C#init[Net#c] == 0bv32;
  assume AT#BvUle(0bv32, R[Net#a]);
  assume AT#BvUle(0bv32, C[Net#a]);
  assume AT#BvAdd(R[Net#a], C[Net#a]) == C#init[Net#a];
  assume AT#BvUle(0bv32, R[Net#c]);
  assume AT#BvUle(0bv32, C[Net#c]);
  assume R[Net#c] == 0bv32;
  assume R[Net#a] == AT#BvAdd(R[Net#c], C[Net#c]);
  assume (forall idx$: bv32 :: 
    AT#BvUle(0bv32, idx$) && AT#BvUlt(idx$, AT#BvAdd(R[Net#c], C[Net#c])) ==> (M[Net#c][idx$] == AT#BvAnd(M[Net#a][idx$], 2bv32))
  );
  assume !AT#BvUle(1bv32, C[Net#a]);
  assert {:msg "  8.3: The network might leave unread tokens on channel a"} C[Net#a] == 0bv32;
  assert {:msg "  8.3: The network might not produce the specified number of tokens on output out"} C[Net#c] == 1bv32;
  ActionPH#y := M[Net#c][0bv32];
  assert {:msg "  9.13: Network action postcondition might not hold"} ActionPH#y == AT#BvAnd(M[Net#a][0bv32], 2bv32);
  R[Net#c] := AT#BvAdd(R[Net#c], C[Net#c]);
  C[Net#c] := 0bv32;
}

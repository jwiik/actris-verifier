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


function AT#Abs(x: int): int { if 0 <= x then x else -x }
function AT#Div(int, int): int;
function AT#Mod(int, int): int;
axiom (forall a,b: int :: AT#Div(a,b)*b + AT#Mod(a,b) == a);
axiom (forall a,b: int :: 0 <= AT#Mod(a,b) && AT#Mod(a,b) < AT#Abs(b));

// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

procedure Test#anon$0#0()
  modifies C, R, M, St;
{
  var IV#in#i: int;
  var IV#in#j: int;
  assume true;
}
const unique Net#t: Actor;
const unique Net#a: Chan (int);
const unique Net#b: Chan (int);
procedure Net#anon$1#entry#1()
  modifies C, R, M, St;
{
  var Net#out#0: int;
  var Net#out#1: int;
  var Net#out#2: int;
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
  assert {:msg "  Channel invariant might not hold on action entry (generated #6)"} (3 * R[Net#a]) == (2 * (R[Net#b] + C[Net#b]));
  assert {:msg "  Channel invariant might not hold on action entry (generated #7)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) && (AT#Mod(idx$, 3) == 0) ==> (M[Net#b][idx$] == (M[Net#a][AT#Div(2, 3) * idx$] + M[Net#a][(AT#Div(2, 3) * idx$) + 1]))
  );
  assert {:msg "  Channel invariant might not hold on action entry (generated #8)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) && (AT#Mod(idx$, 3) == 1) ==> (M[Net#b][idx$] == (M[Net#a][AT#Div(2, 3) * idx$] - M[Net#a][(AT#Div(2, 3) * idx$) + 1]))
  );
  assert {:msg "  Channel invariant might not hold on action entry (generated #9)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) && (AT#Mod(idx$, 3) == 2) ==> (M[Net#b][idx$] == (M[Net#a][AT#Div(2, 3) * idx$] * M[Net#a][(AT#Div(2, 3) * idx$) + 1]))
  );
}
procedure Net#anon$1#Test#anon$0#2()
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
  assume (3 * R[Net#a]) == (2 * (R[Net#b] + C[Net#b]));
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) && (AT#Mod(idx$, 3) == 0) ==> (M[Net#b][idx$] == (M[Net#a][AT#Div(2, 3) * idx$] + M[Net#a][(AT#Div(2, 3) * idx$) + 1]))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) && (AT#Mod(idx$, 3) == 1) ==> (M[Net#b][idx$] == (M[Net#a][AT#Div(2, 3) * idx$] - M[Net#a][(AT#Div(2, 3) * idx$) + 1]))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) && (AT#Mod(idx$, 3) == 2) ==> (M[Net#b][idx$] == (M[Net#a][AT#Div(2, 3) * idx$] * M[Net#a][(AT#Div(2, 3) * idx$) + 1]))
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
  M[Net#b][R[Net#b] + C[Net#b]] := in#i - in#j;
  C[Net#b] := C[Net#b] + 1;
  M[Net#b][R[Net#b] + C[Net#b]] := in#i * in#j;
  C[Net#b] := C[Net#b] + 1;
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #10)"} 0 <= R[Net#a];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #11)"} 0 <= C[Net#a];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #12)"} (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #13)"} 0 <= R[Net#b];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #14)"} 0 <= C[Net#b];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #15)"} R[Net#b] == 0;
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #16)"} (3 * R[Net#a]) == (2 * (R[Net#b] + C[Net#b]));
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #17)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) && (AT#Mod(idx$, 3) == 0) ==> (M[Net#b][idx$] == (M[Net#a][AT#Div(2, 3) * idx$] + M[Net#a][(AT#Div(2, 3) * idx$) + 1]))
  );
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #18)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) && (AT#Mod(idx$, 3) == 1) ==> (M[Net#b][idx$] == (M[Net#a][AT#Div(2, 3) * idx$] - M[Net#a][(AT#Div(2, 3) * idx$) + 1]))
  );
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #19)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) && (AT#Mod(idx$, 3) == 2) ==> (M[Net#b][idx$] == (M[Net#a][AT#Div(2, 3) * idx$] * M[Net#a][(AT#Div(2, 3) * idx$) + 1]))
  );
}
procedure Net#anon$1#exit#3()
  modifies C, R, M, St;
{
  var Net#out#0: int;
  var Net#out#1: int;
  var Net#out#2: int;
  assume C#init[Net#a] == 2;
  assume C#init[Net#b] == 0;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume R[Net#b] == 0;
  assume (3 * R[Net#a]) == (2 * (R[Net#b] + C[Net#b]));
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) && (AT#Mod(idx$, 3) == 0) ==> (M[Net#b][idx$] == (M[Net#a][AT#Div(2, 3) * idx$] + M[Net#a][(AT#Div(2, 3) * idx$) + 1]))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) && (AT#Mod(idx$, 3) == 1) ==> (M[Net#b][idx$] == (M[Net#a][AT#Div(2, 3) * idx$] - M[Net#a][(AT#Div(2, 3) * idx$) + 1]))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) && (AT#Mod(idx$, 3) == 2) ==> (M[Net#b][idx$] == (M[Net#a][AT#Div(2, 3) * idx$] * M[Net#a][(AT#Div(2, 3) * idx$) + 1]))
  );
  assume !(2 <= C[Net#a]);
  assert {:msg "  7.3: The network might leave unread tokens on channel a"} C[Net#a] == 0;
  assert {:msg "  7.3: The network might not produce the specified number of tokens on output out"} C[Net#b] == 3;
  Net#out#0 := M[Net#b][0];
  assert {:msg "  7.28: Network output might not conform to the specified action output"} Net#out#0 == (M[Net#a][0] + M[Net#a][1]);
  Net#out#1 := M[Net#b][1];
  assert {:msg "  7.32: Network output might not conform to the specified action output"} Net#out#1 == (M[Net#a][0] - M[Net#a][1]);
  Net#out#2 := M[Net#b][2];
  assert {:msg "  7.36: Network output might not conform to the specified action output"} Net#out#2 == (M[Net#a][0] * M[Net#a][1]);
  R[Net#b] := R[Net#b] + C[Net#b];
  C[Net#b] := 0;
}

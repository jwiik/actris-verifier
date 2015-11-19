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

procedure Repeater#anon$0#0()
  modifies C, R, M, St;
{
  var IV#in#i: int;
  assume true;
}
procedure Split#anon$1#1()
  modifies C, R, M, St;
{
  var IV#in#i: int;
  assume 0 <= IV#in#i;
  assume true;
}
procedure Split#anon$2#2()
  modifies C, R, M, St;
{
  var IV#in#i: int;
  assume IV#in#i < 0;
  assume true;
}
const unique Net#rep: Actor;
const unique Net#split: Actor;
const unique Net#a: Chan (int);
const unique Net#b: Chan (int);
const unique Net#c: Chan (int);
const unique Net#d: Chan (int);
procedure Net#anon$3#entry#3()
  modifies C, R, M, St;
{
  var Net#out1#0: int;
  var Net#out2#0: int;
  assume C#init[Net#a] == 2;
  assume C#init[Net#b] == 0;
  assume C#init[Net#c] == 0;
  assume C#init[Net#d] == 0;
  assume R[Net#a] == 0;
  assume R[Net#b] == 0;
  assume R[Net#c] == 0;
  assume R[Net#d] == 0;
  assume (M[Net#a][0] < 0) && (M[Net#a][1] > 0);
  assume C#init == C;
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
  assert {:msg "  Channel invariant might not hold on action entry (generated #10)"} R[Net#d] == 0;
  assert {:msg "  Channel invariant might not hold on action entry (generated #11)"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  Channel invariant might not hold on action entry (generated #12)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  20.3: Channel invariant might not hold on action entry"} (M[Net#a][0] < 0) && (M[Net#a][1] > 0);
  assert {:msg "  21.3: Channel invariant might not hold on action entry"} (R[Net#d] + C[Net#d]) == AT#Div(R[Net#b] + 1, 2);
  assert {:msg "  22.3: Channel invariant might not hold on action entry"} (R[Net#c] + C[Net#c]) == AT#Div(R[Net#b], 2);
  assert {:msg "  23.3: Channel invariant might not hold on action entry"} (forall i: int :: 
    (0 <= i) && (i < R[Net#b]) && (AT#Mod(i, 2) == 0) ==> (M[Net#b][i] == M[Net#d][AT#Div(i, 2)])
  );
  assert {:msg "  24.3: Channel invariant might not hold on action entry"} (forall i: int :: 
    (0 <= i) && (i < R[Net#b]) && (AT#Mod(i, 2) == 1) ==> (M[Net#b][i] == M[Net#c][AT#Div(i, 2)])
  );
}
procedure Net#anon$3#Repeater#anon$0#4()
  modifies C, R, M, St;
{
  var St#next: State;
  var in#i: int;
  assume C#init[Net#a] == 2;
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
  assume R[Net#d] == 0;
  assume R[Net#a] == (R[Net#b] + C[Net#b]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assume (M[Net#a][0] < 0) && (M[Net#a][1] > 0);
  assume (R[Net#d] + C[Net#d]) == AT#Div(R[Net#b] + 1, 2);
  assume (R[Net#c] + C[Net#c]) == AT#Div(R[Net#b], 2);
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#b]) && (AT#Mod(i, 2) == 0) ==> (M[Net#b][i] == M[Net#d][AT#Div(i, 2)])
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#b]) && (AT#Mod(i, 2) == 1) ==> (M[Net#b][i] == M[Net#c][AT#Div(i, 2)])
  );
  assume true;
  assume 1 <= C[Net#a];
  in#i := M[Net#a][R[Net#a]];
  R[Net#a] := R[Net#a] + 1;
  C[Net#a] := C[Net#a] - 1;
  M[Net#b][R[Net#b] + C[Net#b]] := in#i;
  C[Net#b] := C[Net#b] + 1;
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #13)"} 0 <= R[Net#a];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #14)"} 0 <= C[Net#a];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #15)"} (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #16)"} 0 <= R[Net#b];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #17)"} 0 <= C[Net#b];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #18)"} 0 <= R[Net#c];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #19)"} 0 <= C[Net#c];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #20)"} R[Net#c] == 0;
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #21)"} 0 <= R[Net#d];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #22)"} 0 <= C[Net#d];
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #23)"} R[Net#d] == 0;
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #24)"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  Sub-actor action at 3.3 might not preserve the channel invariant (generated #25)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  20.3: Sub-actor action at 3.3 might not preserve the channel invariant"} (M[Net#a][0] < 0) && (M[Net#a][1] > 0);
  assert {:msg "  21.3: Sub-actor action at 3.3 might not preserve the channel invariant"} (R[Net#d] + C[Net#d]) == AT#Div(R[Net#b] + 1, 2);
  assert {:msg "  22.3: Sub-actor action at 3.3 might not preserve the channel invariant"} (R[Net#c] + C[Net#c]) == AT#Div(R[Net#b], 2);
  assert {:msg "  23.3: Sub-actor action at 3.3 might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < R[Net#b]) && (AT#Mod(i, 2) == 0) ==> (M[Net#b][i] == M[Net#d][AT#Div(i, 2)])
  );
  assert {:msg "  24.3: Sub-actor action at 3.3 might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < R[Net#b]) && (AT#Mod(i, 2) == 1) ==> (M[Net#b][i] == M[Net#c][AT#Div(i, 2)])
  );
}
procedure Net#anon$3#Split#anon$1#5()
  modifies C, R, M, St;
{
  var St#next: State;
  var in#i: int;
  assume C#init[Net#a] == 2;
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
  assume R[Net#d] == 0;
  assume R[Net#a] == (R[Net#b] + C[Net#b]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assume (M[Net#a][0] < 0) && (M[Net#a][1] > 0);
  assume (R[Net#d] + C[Net#d]) == AT#Div(R[Net#b] + 1, 2);
  assume (R[Net#c] + C[Net#c]) == AT#Div(R[Net#b], 2);
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#b]) && (AT#Mod(i, 2) == 0) ==> (M[Net#b][i] == M[Net#d][AT#Div(i, 2)])
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#b]) && (AT#Mod(i, 2) == 1) ==> (M[Net#b][i] == M[Net#c][AT#Div(i, 2)])
  );
  assume 0 <= M[Net#b][R[Net#b] - 0];
  assume true;
  assume (1 <= C[Net#b]) && (0 <= M[Net#b][R[Net#b] - 0]);
  in#i := M[Net#b][R[Net#b]];
  R[Net#b] := R[Net#b] + 1;
  C[Net#b] := C[Net#b] - 1;
  M[Net#c][R[Net#c] + C[Net#c]] := in#i;
  C[Net#c] := C[Net#c] + 1;
  assert {:msg "  Sub-actor action at 7.3 might not preserve the channel invariant (generated #26)"} 0 <= R[Net#a];
  assert {:msg "  Sub-actor action at 7.3 might not preserve the channel invariant (generated #27)"} 0 <= C[Net#a];
  assert {:msg "  Sub-actor action at 7.3 might not preserve the channel invariant (generated #28)"} (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assert {:msg "  Sub-actor action at 7.3 might not preserve the channel invariant (generated #29)"} 0 <= R[Net#b];
  assert {:msg "  Sub-actor action at 7.3 might not preserve the channel invariant (generated #30)"} 0 <= C[Net#b];
  assert {:msg "  Sub-actor action at 7.3 might not preserve the channel invariant (generated #31)"} 0 <= R[Net#c];
  assert {:msg "  Sub-actor action at 7.3 might not preserve the channel invariant (generated #32)"} 0 <= C[Net#c];
  assert {:msg "  Sub-actor action at 7.3 might not preserve the channel invariant (generated #33)"} R[Net#c] == 0;
  assert {:msg "  Sub-actor action at 7.3 might not preserve the channel invariant (generated #34)"} 0 <= R[Net#d];
  assert {:msg "  Sub-actor action at 7.3 might not preserve the channel invariant (generated #35)"} 0 <= C[Net#d];
  assert {:msg "  Sub-actor action at 7.3 might not preserve the channel invariant (generated #36)"} R[Net#d] == 0;
  assert {:msg "  Sub-actor action at 7.3 might not preserve the channel invariant (generated #37)"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  Sub-actor action at 7.3 might not preserve the channel invariant (generated #38)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  20.3: Sub-actor action at 7.3 might not preserve the channel invariant"} (M[Net#a][0] < 0) && (M[Net#a][1] > 0);
  assert {:msg "  21.3: Sub-actor action at 7.3 might not preserve the channel invariant"} (R[Net#d] + C[Net#d]) == AT#Div(R[Net#b] + 1, 2);
  assert {:msg "  22.3: Sub-actor action at 7.3 might not preserve the channel invariant"} (R[Net#c] + C[Net#c]) == AT#Div(R[Net#b], 2);
  assert {:msg "  23.3: Sub-actor action at 7.3 might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < R[Net#b]) && (AT#Mod(i, 2) == 0) ==> (M[Net#b][i] == M[Net#d][AT#Div(i, 2)])
  );
  assert {:msg "  24.3: Sub-actor action at 7.3 might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < R[Net#b]) && (AT#Mod(i, 2) == 1) ==> (M[Net#b][i] == M[Net#c][AT#Div(i, 2)])
  );
}
procedure Net#anon$3#Split#anon$2#6()
  modifies C, R, M, St;
{
  var St#next: State;
  var in#i: int;
  assume C#init[Net#a] == 2;
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
  assume R[Net#d] == 0;
  assume R[Net#a] == (R[Net#b] + C[Net#b]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assume (M[Net#a][0] < 0) && (M[Net#a][1] > 0);
  assume (R[Net#d] + C[Net#d]) == AT#Div(R[Net#b] + 1, 2);
  assume (R[Net#c] + C[Net#c]) == AT#Div(R[Net#b], 2);
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#b]) && (AT#Mod(i, 2) == 0) ==> (M[Net#b][i] == M[Net#d][AT#Div(i, 2)])
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#b]) && (AT#Mod(i, 2) == 1) ==> (M[Net#b][i] == M[Net#c][AT#Div(i, 2)])
  );
  assume M[Net#b][R[Net#b] - 0] < 0;
  assume true;
  assume (1 <= C[Net#b]) && (M[Net#b][R[Net#b] - 0] < 0);
  in#i := M[Net#b][R[Net#b]];
  R[Net#b] := R[Net#b] + 1;
  C[Net#b] := C[Net#b] - 1;
  M[Net#d][R[Net#d] + C[Net#d]] := in#i;
  C[Net#d] := C[Net#d] + 1;
  assert {:msg "  Sub-actor action at 10.3 might not preserve the channel invariant (generated #39)"} 0 <= R[Net#a];
  assert {:msg "  Sub-actor action at 10.3 might not preserve the channel invariant (generated #40)"} 0 <= C[Net#a];
  assert {:msg "  Sub-actor action at 10.3 might not preserve the channel invariant (generated #41)"} (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assert {:msg "  Sub-actor action at 10.3 might not preserve the channel invariant (generated #42)"} 0 <= R[Net#b];
  assert {:msg "  Sub-actor action at 10.3 might not preserve the channel invariant (generated #43)"} 0 <= C[Net#b];
  assert {:msg "  Sub-actor action at 10.3 might not preserve the channel invariant (generated #44)"} 0 <= R[Net#c];
  assert {:msg "  Sub-actor action at 10.3 might not preserve the channel invariant (generated #45)"} 0 <= C[Net#c];
  assert {:msg "  Sub-actor action at 10.3 might not preserve the channel invariant (generated #46)"} R[Net#c] == 0;
  assert {:msg "  Sub-actor action at 10.3 might not preserve the channel invariant (generated #47)"} 0 <= R[Net#d];
  assert {:msg "  Sub-actor action at 10.3 might not preserve the channel invariant (generated #48)"} 0 <= C[Net#d];
  assert {:msg "  Sub-actor action at 10.3 might not preserve the channel invariant (generated #49)"} R[Net#d] == 0;
  assert {:msg "  Sub-actor action at 10.3 might not preserve the channel invariant (generated #50)"} R[Net#a] == (R[Net#b] + C[Net#b]);
  assert {:msg "  Sub-actor action at 10.3 might not preserve the channel invariant (generated #51)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assert {:msg "  20.3: Sub-actor action at 10.3 might not preserve the channel invariant"} (M[Net#a][0] < 0) && (M[Net#a][1] > 0);
  assert {:msg "  21.3: Sub-actor action at 10.3 might not preserve the channel invariant"} (R[Net#d] + C[Net#d]) == AT#Div(R[Net#b] + 1, 2);
  assert {:msg "  22.3: Sub-actor action at 10.3 might not preserve the channel invariant"} (R[Net#c] + C[Net#c]) == AT#Div(R[Net#b], 2);
  assert {:msg "  23.3: Sub-actor action at 10.3 might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < R[Net#b]) && (AT#Mod(i, 2) == 0) ==> (M[Net#b][i] == M[Net#d][AT#Div(i, 2)])
  );
  assert {:msg "  24.3: Sub-actor action at 10.3 might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < R[Net#b]) && (AT#Mod(i, 2) == 1) ==> (M[Net#b][i] == M[Net#c][AT#Div(i, 2)])
  );
}
procedure Net#anon$3#exit#7()
  modifies C, R, M, St;
{
  var Net#out1#0: int;
  var Net#out2#0: int;
  assume C#init[Net#a] == 2;
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
  assume R[Net#d] == 0;
  assume R[Net#a] == (R[Net#b] + C[Net#b]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#a][idx$])
  );
  assume (M[Net#a][0] < 0) && (M[Net#a][1] > 0);
  assume (R[Net#d] + C[Net#d]) == AT#Div(R[Net#b] + 1, 2);
  assume (R[Net#c] + C[Net#c]) == AT#Div(R[Net#b], 2);
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#b]) && (AT#Mod(i, 2) == 0) ==> (M[Net#b][i] == M[Net#d][AT#Div(i, 2)])
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#b]) && (AT#Mod(i, 2) == 1) ==> (M[Net#b][i] == M[Net#c][AT#Div(i, 2)])
  );
  assume !(((1 <= C[Net#a]) || ((1 <= C[Net#b]) && (0 <= M[Net#b][R[Net#b] - 0]))) || ((1 <= C[Net#b]) && (M[Net#b][R[Net#b] - 0] < 0)));
  assert {:msg "  16.3: The network might leave unread tokens on channel a"} C[Net#a] == 0;
  assert {:msg "  16.3: The network might leave unread tokens on channel b"} C[Net#b] == 0;
  assert {:msg "  16.3: The network might not produce the specified number of tokens on output out1"} C[Net#c] == 1;
  assert {:msg "  16.3: The network might not produce the specified number of tokens on output out2"} C[Net#d] == 1;
  Net#out1#0 := M[Net#c][0];
  assert {:msg "  16.31: Network output might not conform to the specified action output"} Net#out1#0 == M[Net#a][1];
  Net#out2#0 := M[Net#d][0];
  assert {:msg "  16.42: Network output might not conform to the specified action output"} Net#out2#0 == M[Net#a][0];
  R[Net#c] := R[Net#c] + C[Net#c];
  C[Net#c] := 0;
  R[Net#d] := R[Net#d] + C[Net#d];
  C[Net#d] := 0;
}

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

procedure Sum#anon$0#0()
  modifies C, R, M, St;
{
  var sum: int;
  assume 0 <= sum;
  sum := 0;
  assert {:msg "  6.13: Action at 8.3 might not preserve invariant"} 0 <= sum;
}
procedure Sum#anon$1#1()
  modifies C, R, M, St;
{
  var sum: int;
  var IV#in#i: int;
  assume 0 <= sum;
  assume 0 <= IV#in#i;
  sum := sum + IV#in#i;
  assert {:msg "  15.13: Action postcondition might not hold"} IV#in#i <= sum;
  assert {:msg "  6.13: Action at 13.3 might not preserve invariant"} 0 <= sum;
}
procedure Net#init#2()
  modifies C, R, M, St;
{
  assume C[Net#a] == 0;
  assume R[Net#a] == 0;
  assume C[Net#c] == 0;
  assume R[Net#c] == 0;
}
const unique Net#sumact: Actor;
const unique Net#a: Chan (int);
const unique Net#c: Chan (int);
procedure Net#anon$2#entry#3()
  modifies C, R, M, St;
{
  var Net#sumact#AV#sum: int;
  var ActionPH#y: int;
  assume C#init[Net#a] == 1;
  assume C#init[Net#c] == 0;
  assume R[Net#a] == 0;
  assume R[Net#c] == 0;
  assume C#init == C;
  assume 0 <= M[Net#a][0];
  assert {:msg "  Channel invariant might not hold on action entry (generated #0)"} 0 <= R[Net#a];
  assert {:msg "  Channel invariant might not hold on action entry (generated #1)"} 0 <= C[Net#a];
  assert {:msg "  Channel invariant might not hold on action entry (generated #2)"} (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assert {:msg "  Channel invariant might not hold on action entry (generated #3)"} 0 <= R[Net#c];
  assert {:msg "  Channel invariant might not hold on action entry (generated #4)"} 0 <= C[Net#c];
  assert {:msg "  Channel invariant might not hold on action entry (generated #5)"} R[Net#c] == 0;
  assert {:msg "  Channel invariant might not hold on action entry (generated #6)"} 0 <= M[Net#a][0];
  assert {:msg "  Channel invariant might not hold on action entry (generated #7)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Channel invariant might not hold on action entry (generated #8)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == Net#sumact#AV#sum)
  );
  assert {:msg "  28.3: Channel invariant might not hold on action entry"} (0 < R[Net#a]) ==> (M[Net#a][0] <= M[Net#c][0]);
}
procedure Net#anon$2#Sum#anon$1#4()
  modifies C, R, M, St;
{
  var Net#sumact#AV#sum: int;
  var ActionPH#y: int;
  var St#next: State;
  var in#i: int;
  assume C#init[Net#a] == 1;
  assume C#init[Net#c] == 0;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume R[Net#c] == 0;
  assume 0 <= M[Net#a][0];
  assume R[Net#a] == (R[Net#c] + C[Net#c]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == Net#sumact#AV#sum)
  );
  assume (0 < R[Net#a]) ==> (M[Net#a][0] <= M[Net#c][0]);
  assume true;
  assume 1 <= C[Net#a];
  assume 0 <= Net#sumact#AV#sum;
  in#i := M[Net#a][R[Net#a]];
  R[Net#a] := R[Net#a] + 1;
  C[Net#a] := C[Net#a] - 1;
  assert {:msg "  14.14: Precondition might not hold for instance at 31.5"} 0 <= in#i;
  assume in#i <= Net#sumact#AV#sum;
  M[Net#c][R[Net#c] + C[Net#c]] := Net#sumact#AV#sum;
  C[Net#c] := C[Net#c] + 1;
  assert {:msg "  Sub-actor action at 13.3 might not preserve the channel invariant (generated #9)"} 0 <= R[Net#a];
  assert {:msg "  Sub-actor action at 13.3 might not preserve the channel invariant (generated #10)"} 0 <= C[Net#a];
  assert {:msg "  Sub-actor action at 13.3 might not preserve the channel invariant (generated #11)"} (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assert {:msg "  Sub-actor action at 13.3 might not preserve the channel invariant (generated #12)"} 0 <= R[Net#c];
  assert {:msg "  Sub-actor action at 13.3 might not preserve the channel invariant (generated #13)"} 0 <= C[Net#c];
  assert {:msg "  Sub-actor action at 13.3 might not preserve the channel invariant (generated #14)"} R[Net#c] == 0;
  assert {:msg "  Sub-actor action at 13.3 might not preserve the channel invariant (generated #15)"} 0 <= M[Net#a][0];
  assert {:msg "  Sub-actor action at 13.3 might not preserve the channel invariant (generated #16)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Sub-actor action at 13.3 might not preserve the channel invariant (generated #17)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == Net#sumact#AV#sum)
  );
  assert {:msg "  28.3: Sub-actor action at 13.3 might not preserve the channel invariant"} (0 < R[Net#a]) ==> (M[Net#a][0] <= M[Net#c][0]);
}
procedure Net#anon$2#exit#5()
  modifies C, R, M, St;
{
  var Net#sumact#AV#sum: int;
  var ActionPH#y: int;
  assume C#init[Net#a] == 1;
  assume C#init[Net#c] == 0;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume R[Net#c] == 0;
  assume 0 <= M[Net#a][0];
  assume R[Net#a] == (R[Net#c] + C[Net#c]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == Net#sumact#AV#sum)
  );
  assume (0 < R[Net#a]) ==> (M[Net#a][0] <= M[Net#c][0]);
  assume !(1 <= C[Net#a]);
  ActionPH#y := M[Net#c][0];
  assert {:msg "  25.13: Network action postcondition might not hold"} M[Net#a][0] <= ActionPH#y;
  R[Net#c] := R[Net#c] + C[Net#c];
  C[Net#c] := C[Net#c] - 1;
  assert {:msg "  23.3: The network might leave unread tokens on channel a"} C[Net#a] == 0;
  assert {:msg "  23.3: The network might not produce the specified number of tokens on output out"} C[Net#c] == 0;
}

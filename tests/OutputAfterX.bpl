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

const unique Sum5#s0: State;
const unique Sum5#s1: State;
procedure Sum5#a0#0()
  modifies C, R, M, St;
{
  var this#: Actor;
  var sum: int;
  var count: int;
  var IV#x#i: int;
  assume (St[this#] == Sum5#s0) || (St[this#] == Sum5#s1);
  assume (0 <= count) && (count <= 5);
  assume St[this#] == Sum5#s0;
  assume count == 0;
  sum := IV#x#i;
  count := 1;
  St[this#] := Sum5#s1;
  assert {:msg "  1.1: Action at 8.3 might not preserve invariant"} (St[this#] == Sum5#s0) || (St[this#] == Sum5#s1);
  assert {:msg "  6.13: Action at 8.3 might not preserve invariant"} (0 <= count) && (count <= 5);
}
procedure Sum5#a1#1()
  modifies C, R, M, St;
{
  var this#: Actor;
  var sum: int;
  var count: int;
  var IV#x#i: int;
  assume (St[this#] == Sum5#s0) || (St[this#] == Sum5#s1);
  assume (0 <= count) && (count <= 5);
  assume St[this#] == Sum5#s1;
  assume (1 <= count) && (count < 5);
  sum := sum + IV#x#i;
  count := count + 1;
  St[this#] := Sum5#s1;
  assert {:msg "  1.1: Action at 15.3 might not preserve invariant"} (St[this#] == Sum5#s0) || (St[this#] == Sum5#s1);
  assert {:msg "  6.13: Action at 15.3 might not preserve invariant"} (0 <= count) && (count <= 5);
}
procedure Sum5#a2#2()
  modifies C, R, M, St;
{
  var this#: Actor;
  var sum: int;
  var count: int;
  assume (St[this#] == Sum5#s0) || (St[this#] == Sum5#s1);
  assume (0 <= count) && (count <= 5);
  assume St[this#] == Sum5#s1;
  assume count == 5;
  count := 0;
  St[this#] := Sum5#s0;
  assert {:msg "  1.1: Action at 22.3 might not preserve invariant"} (St[this#] == Sum5#s0) || (St[this#] == Sum5#s1);
  assert {:msg "  6.13: Action at 22.3 might not preserve invariant"} (0 <= count) && (count <= 5);
}
procedure Net#init#3()
  modifies C, R, M, St;
{
  assume C[Net#a] == 0;
  assume R[Net#a] == 0;
  assume C[Net#b] == 0;
  assume R[Net#b] == 0;
  assume St[Net#s] == Sum5#s0;
}
const unique Net#s: Actor;
const unique Net#a: Chan (int);
const unique Net#b: Chan (int);
procedure Net#anon$0#entry#4()
  modifies C, R, M, St;
{
  var Net#s#AV#sum: int;
  var Net#s#AV#count: int;
  var ActionPH#y: int;
  assume C#init[Net#a] == 5;
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
  assert {:msg "  40.3: Channel invariant might not hold on action entry"} (R[Net#b] + C[Net#b]) <= 5;
}
procedure Net#anon$0#Sum5#a0#5()
  modifies C, R, M, St;
{
  var Net#s#AV#sum: int;
  var Net#s#AV#count: int;
  var ActionPH#y: int;
  var St#next: State;
  var x#i: int;
  assume C#init[Net#a] == 5;
  assume C#init[Net#b] == 0;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume R[Net#b] == 0;
  assume (R[Net#b] + C[Net#b]) <= 5;
  assume Net#s#AV#count == 0;
  assume St[Net#s] == Sum5#s0;
  assume (1 <= C[Net#a]) && (Net#s#AV#count == 0) && (St[Net#s] == Sum5#s0);
  assume (0 <= Net#s#AV#count) && (Net#s#AV#count <= 5);
  x#i := M[Net#a][R[Net#a]];
  R[Net#a] := R[Net#a] + 1;
  C[Net#a] := C[Net#a] - 1;
  assume St#next == Sum5#s1;
  St[Net#s] := St#next;
  assert {:msg "  Sub-actor action at 8.3 might not preserve the channel invariant (generated #6)"} 0 <= R[Net#a];
  assert {:msg "  Sub-actor action at 8.3 might not preserve the channel invariant (generated #7)"} 0 <= C[Net#a];
  assert {:msg "  Sub-actor action at 8.3 might not preserve the channel invariant (generated #8)"} (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assert {:msg "  Sub-actor action at 8.3 might not preserve the channel invariant (generated #9)"} 0 <= R[Net#b];
  assert {:msg "  Sub-actor action at 8.3 might not preserve the channel invariant (generated #10)"} 0 <= C[Net#b];
  assert {:msg "  Sub-actor action at 8.3 might not preserve the channel invariant (generated #11)"} R[Net#b] == 0;
  assert {:msg "  40.3: Sub-actor action at 8.3 might not preserve the channel invariant"} (R[Net#b] + C[Net#b]) <= 5;
}
procedure Net#anon$0#Sum5#a1#6()
  modifies C, R, M, St;
{
  var Net#s#AV#sum: int;
  var Net#s#AV#count: int;
  var ActionPH#y: int;
  var St#next: State;
  var x#i: int;
  assume C#init[Net#a] == 5;
  assume C#init[Net#b] == 0;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume R[Net#b] == 0;
  assume (R[Net#b] + C[Net#b]) <= 5;
  assume (1 <= Net#s#AV#count) && (Net#s#AV#count < 5);
  assume St[Net#s] == Sum5#s1;
  assume (1 <= C[Net#a]) && (1 <= Net#s#AV#count) && (Net#s#AV#count < 5) && (St[Net#s] == Sum5#s1);
  assume (0 <= Net#s#AV#count) && (Net#s#AV#count <= 5);
  x#i := M[Net#a][R[Net#a]];
  R[Net#a] := R[Net#a] + 1;
  C[Net#a] := C[Net#a] - 1;
  assume St#next == Sum5#s1;
  St[Net#s] := St#next;
  assert {:msg "  Sub-actor action at 15.3 might not preserve the channel invariant (generated #12)"} 0 <= R[Net#a];
  assert {:msg "  Sub-actor action at 15.3 might not preserve the channel invariant (generated #13)"} 0 <= C[Net#a];
  assert {:msg "  Sub-actor action at 15.3 might not preserve the channel invariant (generated #14)"} (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assert {:msg "  Sub-actor action at 15.3 might not preserve the channel invariant (generated #15)"} 0 <= R[Net#b];
  assert {:msg "  Sub-actor action at 15.3 might not preserve the channel invariant (generated #16)"} 0 <= C[Net#b];
  assert {:msg "  Sub-actor action at 15.3 might not preserve the channel invariant (generated #17)"} R[Net#b] == 0;
  assert {:msg "  40.3: Sub-actor action at 15.3 might not preserve the channel invariant"} (R[Net#b] + C[Net#b]) <= 5;
}
procedure Net#anon$0#Sum5#a2#7()
  modifies C, R, M, St;
{
  var Net#s#AV#sum: int;
  var Net#s#AV#count: int;
  var ActionPH#y: int;
  var St#next: State;
  assume C#init[Net#a] == 5;
  assume C#init[Net#b] == 0;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume R[Net#b] == 0;
  assume (R[Net#b] + C[Net#b]) <= 5;
  assume Net#s#AV#count == 5;
  assume St[Net#s] == Sum5#s1;
  assume (Net#s#AV#count == 5) && (St[Net#s] == Sum5#s1);
  assume (0 <= Net#s#AV#count) && (Net#s#AV#count <= 5);
  M[Net#b][R[Net#b] + C[Net#b]] := Net#s#AV#sum;
  C[Net#b] := C[Net#b] + 1;
  assume St#next == Sum5#s0;
  St[Net#s] := St#next;
  assert {:msg "  Sub-actor action at 22.3 might not preserve the channel invariant (generated #18)"} 0 <= R[Net#a];
  assert {:msg "  Sub-actor action at 22.3 might not preserve the channel invariant (generated #19)"} 0 <= C[Net#a];
  assert {:msg "  Sub-actor action at 22.3 might not preserve the channel invariant (generated #20)"} (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assert {:msg "  Sub-actor action at 22.3 might not preserve the channel invariant (generated #21)"} 0 <= R[Net#b];
  assert {:msg "  Sub-actor action at 22.3 might not preserve the channel invariant (generated #22)"} 0 <= C[Net#b];
  assert {:msg "  Sub-actor action at 22.3 might not preserve the channel invariant (generated #23)"} R[Net#b] == 0;
  assert {:msg "  40.3: Sub-actor action at 22.3 might not preserve the channel invariant"} (R[Net#b] + C[Net#b]) <= 5;
}
procedure Net#anon$0#exit#8()
  modifies C, R, M, St;
{
  var Net#s#AV#sum: int;
  var Net#s#AV#count: int;
  var ActionPH#y: int;
  assume C#init[Net#a] == 5;
  assume C#init[Net#b] == 0;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume R[Net#b] == 0;
  assume (R[Net#b] + C[Net#b]) <= 5;
  assume !((((1 <= C[Net#a]) && (Net#s#AV#count == 0) && (St[Net#s] == Sum5#s0)) || ((1 <= C[Net#a]) && (1 <= Net#s#AV#count) && (Net#s#AV#count < 5) && (St[Net#s] == Sum5#s1))) || ((Net#s#AV#count == 5) && (St[Net#s] == Sum5#s1)));
  ActionPH#y := M[Net#b][0];
  R[Net#b] := R[Net#b] + C[Net#b];
  C[Net#b] := C[Net#b] - 1;
  assert {:msg "  38.3: The network might leave unread tokens on channel a"} C[Net#a] == 0;
  assert {:msg "  38.3: The network might not produce the specified number of tokens on output out"} C[Net#b] == 0;
}

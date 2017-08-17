// ---------------------------------------------------------------
// -- Types and global variables ---------------------------------
// ---------------------------------------------------------------
type Ref;
type Chan a;
type Field a;
type Actor;
type CType = <a>[Chan a]int;
type MType = <a>[Chan a][int]a;
type Obj = <a>[Field a]a;
type HType = [Ref]Obj;
type ModeType = [Actor]int;

var M#: MType;
var C#: CType;
var R#: CType;
var I#: CType;
var B#: CType;
var Mode#: ModeType;
var I#sub: CType;

var H#: HType;

const unique this#: Actor;
function AT#Min(x:int, y: int): int { if x <= y then x else y }

// ---------------------------------------------------------------
// -- Integer division and modulo --------------------------------
// ---------------------------------------------------------------
function AT#Abs(x: int): int { if 0 <= x then x else -x }
function AT#Div(int, int): int;
function AT#Mod(int, int): int;
axiom (forall a,b: int :: AT#Div(a,b)*b + AT#Mod(a,b) == a);
axiom (forall a,b: int :: 0 <= AT#Mod(a,b) && AT#Mod(a,b) < AT#Abs(b));

// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

procedure Alternate#init#0()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var x: Chan (int);
  var y: Chan (int);
  var St#: int;
  var c: int;
  var b: int;
  var a: int;
  assume x != y;
  assume c == 2;
  assume b == 1;
  assume a == 0;
  assume (I#[x] == 0) && (R#[x] == 0) && (C#[x] == 0);
  assume (I#[y] == 0) && (R#[y] == 0) && (C#[y] == 0);
  St# := a;
  assert {:msg "StateDepGuards.actor(13.3): Initialization might not establish the invariant (#0)"} ((St# == a) || (St# == b)) || (St# == c);
  assert {:msg "StateDepGuards.actor(3.20): Initialization might not establish the invariant (#1)"} (AT#Mod(R#[x], 3) == 0) ==> (St# == a);
  assert {:msg "StateDepGuards.actor(4.20): Initialization might not establish the invariant (#2)"} (AT#Mod(R#[x], 3) == 1) ==> (St# == b);
  assert {:msg "StateDepGuards.actor(5.20): Initialization might not establish the invariant (#3)"} (AT#Mod(R#[x], 3) == 2) ==> (St# == c);
  assert {:msg "Initialization might not establish the invariant (#4)"} R#[x] == C#[y];
}
procedure Alternate#plus#1()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var x: Chan (int);
  var y: Chan (int);
  var St#: int;
  var c: int;
  var b: int;
  var a: int;
  var x#0: int;
  assume x != y;
  assume c == 2;
  assume b == 1;
  assume a == 0;
  assume (0 <= I#[x]) && (I#[x] <= R#[x]) && (R#[x] <= C#[x]);
  assume (0 <= I#[y]) && (I#[y] <= R#[y]) && (R#[y] <= C#[y]);
  assume ((St# == a) || (St# == b)) || (St# == c);
  assume (AT#Mod(R#[x], 3) == 0) ==> (St# == a);
  assume (AT#Mod(R#[x], 3) == 1) ==> (St# == b);
  assume (AT#Mod(R#[x], 3) == 2) ==> (St# == c);
  assume R#[x] == C#[y];
  assume 1 <= (C#[x] - R#[x]);
  x#0 := M#[x][R#[x]];
  R#[x] := R#[x] + 1;
  assume (St# == a) || (St# == b);
  if (St# == a) {
    St# := b;
  } else {
    if (St# == b) {
      St# := c;
    }
  }
  M#[y][C#[y]] := x#0 + x#0;
  C#[y] := C#[y] + 1;
  assert {:msg "StateDepGuards.actor(13.3): Action 'plus' at <unknown_file>(-1.-1) might not preserve the invariant (#5)"} ((St# == a) || (St# == b)) || (St# == c);
  assert {:msg "StateDepGuards.actor(3.20): Action 'plus' at <unknown_file>(-1.-1) might not preserve the invariant (#6)"} (AT#Mod(R#[x], 3) == 0) ==> (St# == a);
  assert {:msg "StateDepGuards.actor(4.20): Action 'plus' at <unknown_file>(-1.-1) might not preserve the invariant (#7)"} (AT#Mod(R#[x], 3) == 1) ==> (St# == b);
  assert {:msg "StateDepGuards.actor(5.20): Action 'plus' at <unknown_file>(-1.-1) might not preserve the invariant (#8)"} (AT#Mod(R#[x], 3) == 2) ==> (St# == c);
  assert {:msg "Action 'plus' at <unknown_file>(-1.-1) might not preserve the invariant (#9)"} R#[x] == C#[y];
}
procedure Alternate#minus#2()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var x: Chan (int);
  var y: Chan (int);
  var St#: int;
  var c: int;
  var b: int;
  var a: int;
  var x#0: int;
  assume x != y;
  assume c == 2;
  assume b == 1;
  assume a == 0;
  assume (0 <= I#[x]) && (I#[x] <= R#[x]) && (R#[x] <= C#[x]);
  assume (0 <= I#[y]) && (I#[y] <= R#[y]) && (R#[y] <= C#[y]);
  assume ((St# == a) || (St# == b)) || (St# == c);
  assume (AT#Mod(R#[x], 3) == 0) ==> (St# == a);
  assume (AT#Mod(R#[x], 3) == 1) ==> (St# == b);
  assume (AT#Mod(R#[x], 3) == 2) ==> (St# == c);
  assume R#[x] == C#[y];
  assume 1 <= (C#[x] - R#[x]);
  x#0 := M#[x][R#[x]];
  R#[x] := R#[x] + 1;
  assume St# == c;
  St# := a;
  M#[y][C#[y]] := x#0 - x#0;
  C#[y] := C#[y] + 1;
  assert {:msg "StateDepGuards.actor(13.3): Action 'minus' at <unknown_file>(-1.-1) might not preserve the invariant (#10)"} ((St# == a) || (St# == b)) || (St# == c);
  assert {:msg "StateDepGuards.actor(3.20): Action 'minus' at <unknown_file>(-1.-1) might not preserve the invariant (#11)"} (AT#Mod(R#[x], 3) == 0) ==> (St# == a);
  assert {:msg "StateDepGuards.actor(4.20): Action 'minus' at <unknown_file>(-1.-1) might not preserve the invariant (#12)"} (AT#Mod(R#[x], 3) == 1) ==> (St# == b);
  assert {:msg "StateDepGuards.actor(5.20): Action 'minus' at <unknown_file>(-1.-1) might not preserve the invariant (#13)"} (AT#Mod(R#[x], 3) == 2) ==> (St# == c);
  assert {:msg "Action 'minus' at <unknown_file>(-1.-1) might not preserve the invariant (#14)"} R#[x] == C#[y];
}
procedure Alternate##GuardWD#3()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var x: Chan (int);
  var y: Chan (int);
  var St#: int;
  var c: int;
  var b: int;
  var a: int;
  var x#0: int;
  assume x != y;
  assume c == 2;
  assume b == 1;
  assume a == 0;
  assume (0 <= I#[x]) && (I#[x] <= R#[x]) && (R#[x] <= C#[x]);
  assume (0 <= I#[y]) && (I#[y] <= R#[y]) && (R#[y] <= C#[y]);
  assume ((St# == a) || (St# == b)) || (St# == c);
  assume (AT#Mod(R#[x], 3) == 0) ==> (St# == a);
  assume (AT#Mod(R#[x], 3) == 1) ==> (St# == b);
  assume (AT#Mod(R#[x], 3) == 2) ==> (St# == c);
  assume R#[x] == C#[y];
  assert {:msg "The actions 'plus' and 'minus' of actor 'Alternate' might not have mutually exclusive guards (#15)"} !(true && (1 <= (C#[x] - R#[x])) && ((St# == a) || (St# == b)) && true && (1 <= (C#[x] - R#[x])) && (St# == c));
}
procedure Alternate##GuardWD#4()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var x: Chan (int);
  var y: Chan (int);
  var St#: int;
  var c: int;
  var b: int;
  var a: int;
  assume x != y;
  assume c == 2;
  assume b == 1;
  assume a == 0;
  assume (0 <= I#[x]) && (I#[x] <= R#[x]) && (R#[x] <= C#[x]);
  assume (0 <= I#[y]) && (I#[y] <= R#[y]) && (R#[y] <= C#[y]);
  assume ((St# == a) || (St# == b)) || (St# == c);
  assume (AT#Mod(R#[x], 3) == 0) ==> (St# == a);
  assume (AT#Mod(R#[x], 3) == 1) ==> (St# == b);
  assume (AT#Mod(R#[x], 3) == 2) ==> (St# == c);
  assume R#[x] == C#[y];
}
procedure A#init#5()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var A#a: Actor;
  var A#anon$1: Chan (int);
  var A#anon$2: Chan (int);
  var anon__0: int;
  var a#St#: int;
  var a#c: int;
  var a#b: int;
  var a#a: int;
  var a#St##old: int;
  assume 0 <= I#[A#anon$1];
  assume I#[A#anon$1] <= R#[A#anon$1];
  assume R#[A#anon$1] <= C#[A#anon$1];
  assume 0 <= I#[A#anon$2];
  assume I#[A#anon$2] <= R#[A#anon$2];
  assume R#[A#anon$2] <= C#[A#anon$2];
  assume I#[A#anon$2] == R#[A#anon$2];
  assume (B#[A#anon$1] == 3) && (B#[A#anon$2] == 3);
  assume anon__0 == 0;
  assume Mode#[this#] == anon__0;
  assume C#[A#anon$1] == 0;
  assume R#[A#anon$1] == 0;
  assume C#[A#anon$2] == 0;
  assume R#[A#anon$2] == 0;
  assert {:msg "Initialization of network 'A' might not establish the channel invariant (#16)"} I#[A#anon$2] == I#[A#anon$1];
  assert {:msg "Initialization of network 'A' might not establish the channel invariant (#17)"} (Mode#[this#] == anon__0) ==> ((C#[A#anon$1] - I#[A#anon$1]) <= 3);
  I# := R#;
  assert {:msg "StateDepGuards.actor(25.13): Initialization of network 'A' might not establish the network invariant (#18)"} AT#Mod(R#[A#anon$1], 3) == 0;
  assert {:msg "Initialization of network 'A' might not establish the network invariant (#19)"} (3 * R#[A#anon$1]) == (3 * C#[A#anon$2]);
  assert {:msg "Initialization of network 'A' might not establish the network invariant: Unread tokens might be left on channel anon$1 (#20)"} (C#[A#anon$1] - R#[A#anon$1]) == 0;
  assert {:msg "Initialization of network 'A' might not establish the network invariant: Unread tokens might be left on channel anon$2 (#21)"} (C#[A#anon$2] - R#[A#anon$2]) == 0;
}
procedure A##Alternate#plus#6()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var A#a: Actor;
  var A#anon$1: Chan (int);
  var A#anon$2: Chan (int);
  var anon__0: int;
  var a#St#: int;
  var a#c: int;
  var a#b: int;
  var a#a: int;
  var a#St##old: int;
  var a#x#i: int;
  assume 0 <= I#[A#anon$1];
  assume I#[A#anon$1] <= R#[A#anon$1];
  assume R#[A#anon$1] <= C#[A#anon$1];
  assume 0 <= I#[A#anon$2];
  assume I#[A#anon$2] <= R#[A#anon$2];
  assume R#[A#anon$2] <= C#[A#anon$2];
  assume I#[A#anon$2] == R#[A#anon$2];
  assume (B#[A#anon$1] == 3) && (B#[A#anon$2] == 3);
  assume anon__0 == 0;
  assume Mode#[this#] == anon__0;
  I#sub[A#anon$1] := R#[A#anon$1];
  I#sub[A#anon$2] := C#[A#anon$2];
  assume I#[A#anon$2] == I#[A#anon$1];
  assume (Mode#[this#] == anon__0) ==> ((C#[A#anon$1] - I#[A#anon$1]) <= 3);
  assume (AT#Mod(R#[A#anon$1], 3) == 0) ==> (a#St# == a#a);
  assume (AT#Mod(R#[A#anon$1], 3) == 1) ==> (a#St# == a#b);
  assume (AT#Mod(R#[A#anon$1], 3) == 2) ==> (a#St# == a#c);
  assume R#[A#anon$1] == C#[A#anon$2];
  assume (1 <= (C#[A#anon$1] - R#[A#anon$1])) && ((a#St# == a#a) || (a#St# == a#b));
  a#x#i := M#[A#anon$1][R#[A#anon$1]];
  R#[A#anon$1] := R#[A#anon$1] + 1;
  havoc a#St#;
  M#[A#anon$2][C#[A#anon$2]] := a#x#i + a#x#i;
  C#[A#anon$2] := C#[A#anon$2] + 1;
  assume ((a#St##old == a#a) ==> (a#St# == a#b)) && ((a#St##old == a#b) ==> (a#St# == a#c));
  assert {:msg "Action at <unknown_file>(-1.-1) ('plus') for actor instance 'a' might not preserve the channel invariant (#22)"} I#[A#anon$2] == I#[A#anon$1];
  assert {:msg "Action at <unknown_file>(-1.-1) ('plus') for actor instance 'a' might not preserve the channel invariant (#23)"} (Mode#[this#] == anon__0) ==> ((C#[A#anon$1] - I#[A#anon$1]) <= 3);
}
procedure A##Alternate#minus#7()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var A#a: Actor;
  var A#anon$1: Chan (int);
  var A#anon$2: Chan (int);
  var anon__0: int;
  var a#St#: int;
  var a#c: int;
  var a#b: int;
  var a#a: int;
  var a#St##old: int;
  var a#x#i: int;
  assume 0 <= I#[A#anon$1];
  assume I#[A#anon$1] <= R#[A#anon$1];
  assume R#[A#anon$1] <= C#[A#anon$1];
  assume 0 <= I#[A#anon$2];
  assume I#[A#anon$2] <= R#[A#anon$2];
  assume R#[A#anon$2] <= C#[A#anon$2];
  assume I#[A#anon$2] == R#[A#anon$2];
  assume (B#[A#anon$1] == 3) && (B#[A#anon$2] == 3);
  assume anon__0 == 0;
  assume Mode#[this#] == anon__0;
  I#sub[A#anon$1] := R#[A#anon$1];
  I#sub[A#anon$2] := C#[A#anon$2];
  assume I#[A#anon$2] == I#[A#anon$1];
  assume (Mode#[this#] == anon__0) ==> ((C#[A#anon$1] - I#[A#anon$1]) <= 3);
  assume (AT#Mod(R#[A#anon$1], 3) == 0) ==> (a#St# == a#a);
  assume (AT#Mod(R#[A#anon$1], 3) == 1) ==> (a#St# == a#b);
  assume (AT#Mod(R#[A#anon$1], 3) == 2) ==> (a#St# == a#c);
  assume R#[A#anon$1] == C#[A#anon$2];
  assume (1 <= (C#[A#anon$1] - R#[A#anon$1])) && (a#St# == a#c);
  a#x#i := M#[A#anon$1][R#[A#anon$1]];
  R#[A#anon$1] := R#[A#anon$1] + 1;
  havoc a#St#;
  M#[A#anon$2][C#[A#anon$2]] := a#x#i - a#x#i;
  C#[A#anon$2] := C#[A#anon$2] + 1;
  assume a#St# == a#a;
  assert {:msg "Action at <unknown_file>(-1.-1) ('minus') for actor instance 'a' might not preserve the channel invariant (#24)"} I#[A#anon$2] == I#[A#anon$1];
  assert {:msg "Action at <unknown_file>(-1.-1) ('minus') for actor instance 'a' might not preserve the channel invariant (#25)"} (Mode#[this#] == anon__0) ==> ((C#[A#anon$1] - I#[A#anon$1]) <= 3);
}
procedure A#anon__0#input#x#8()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var A#a: Actor;
  var A#anon$1: Chan (int);
  var A#anon$2: Chan (int);
  var anon__0: int;
  var a#St#: int;
  var a#c: int;
  var a#b: int;
  var a#a: int;
  var a#St##old: int;
  assume 0 <= I#[A#anon$1];
  assume I#[A#anon$1] <= R#[A#anon$1];
  assume R#[A#anon$1] <= C#[A#anon$1];
  assume 0 <= I#[A#anon$2];
  assume I#[A#anon$2] <= R#[A#anon$2];
  assume R#[A#anon$2] <= C#[A#anon$2];
  assume I#[A#anon$2] == R#[A#anon$2];
  assume (B#[A#anon$1] == 3) && (B#[A#anon$2] == 3);
  assume anon__0 == 0;
  assume Mode#[this#] == anon__0;
  assume (B#[A#anon$1] == 3) && (B#[A#anon$2] == 3);
  assume Mode#[this#] == anon__0;
  assume (C#[A#anon$1] - I#[A#anon$1]) < 3;
  assume I#[A#anon$2] == I#[A#anon$1];
  assume (Mode#[this#] == anon__0) ==> ((C#[A#anon$1] - I#[A#anon$1]) <= 3);
  assume (AT#Mod(R#[A#anon$1], 3) == 0) ==> (a#St# == a#a);
  assume (AT#Mod(R#[A#anon$1], 3) == 1) ==> (a#St# == a#b);
  assume (AT#Mod(R#[A#anon$1], 3) == 2) ==> (a#St# == a#c);
  assume R#[A#anon$1] == C#[A#anon$2];
  C#[A#anon$1] := C#[A#anon$1] + 1;
  assert {:msg "Channel invariant might be falsified by network input on port 'x' for contract 'anon__0' (#26)"} I#[A#anon$2] == I#[A#anon$1];
  assert {:msg "Channel invariant might be falsified by network input on port 'x' for contract 'anon__0' (#27)"} (Mode#[this#] == anon__0) ==> ((C#[A#anon$1] - I#[A#anon$1]) <= 3);
}
procedure A#anon__0#exit#9()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var A#a: Actor;
  var A#anon$1: Chan (int);
  var A#anon$2: Chan (int);
  var anon__0: int;
  var a#St#: int;
  var a#c: int;
  var a#b: int;
  var a#a: int;
  var a#St##old: int;
  assume 0 <= I#[A#anon$1];
  assume I#[A#anon$1] <= R#[A#anon$1];
  assume R#[A#anon$1] <= C#[A#anon$1];
  assume 0 <= I#[A#anon$2];
  assume I#[A#anon$2] <= R#[A#anon$2];
  assume R#[A#anon$2] <= C#[A#anon$2];
  assume I#[A#anon$2] == R#[A#anon$2];
  assume (B#[A#anon$1] == 3) && (B#[A#anon$2] == 3);
  assume anon__0 == 0;
  assume Mode#[this#] == anon__0;
  assume Mode#[this#] == anon__0;
  assume (B#[A#anon$1] == 3) && (B#[A#anon$2] == 3);
  assume I#[A#anon$2] == I#[A#anon$1];
  assume (Mode#[this#] == anon__0) ==> ((C#[A#anon$1] - I#[A#anon$1]) <= 3);
  assume (AT#Mod(R#[A#anon$1], 3) == 0) ==> (a#St# == a#a);
  assume (AT#Mod(R#[A#anon$1], 3) == 1) ==> (a#St# == a#b);
  assume (AT#Mod(R#[A#anon$1], 3) == 2) ==> (a#St# == a#c);
  assume R#[A#anon$1] == C#[A#anon$2];
  assume (C#[A#anon$1] - I#[A#anon$1]) == 3;
  assume !((1 <= (C#[A#anon$1] - R#[A#anon$1])) && ((a#St# == a#a) || (a#St# == a#b)));
  assume !((1 <= (C#[A#anon$1] - R#[A#anon$1])) && (a#St# == a#c));
  assert {:msg "StateDepGuards.actor(23.3): The correct number of tokens might not be produced on output 'y' for contract 'anon__0' (#28)"} (C#[A#anon$2] - I#[A#anon$2]) == 3;
  R#[A#anon$2] := R#[A#anon$2] + 3;
  I# := R#;
  assert {:msg "The network might not preserve the channel invariant for contract 'anon__0' (#29)"} I#[A#anon$2] == I#[A#anon$1];
  assert {:msg "The network might not preserve the channel invariant for contract 'anon__0' (#30)"} (Mode#[this#] == anon__0) ==> ((C#[A#anon$1] - I#[A#anon$1]) <= 3);
  assert {:msg "StateDepGuards.actor(25.13): The network might not preserve the network invariant for contract 'anon__0' (#31)"} AT#Mod(R#[A#anon$1], 3) == 0;
  assert {:msg "The network might not preserve the network invariant for contract 'anon__0' (#32)"} (3 * R#[A#anon$1]) == (3 * C#[A#anon$2]);
  assert {:msg "The network might not preserve the network invariant for contract 'anon__0': Unread tokens might be left on channel anon$1 (#33)"} (C#[A#anon$1] - R#[A#anon$1]) == 0;
  assert {:msg "The network might not preserve the network invariant for contract 'anon__0': Unread tokens might be left on channel anon$2 (#34)"} (C#[A#anon$2] - R#[A#anon$2]) == 0;
}

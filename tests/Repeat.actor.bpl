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
// -- Axiomatisation for map data type ---------------------------
// ---------------------------------------------------------------
type Map a b;
function List#Empty<U>(U): Map int U;
function Map#Select<T,U>(Map T U, T): U;
function Map#Store<T,U>(Map T U, T, U): Map T U;
axiom (
  forall<T,U> m: Map T U, k1: T, val: U :: { Map#Store(m,k1,val) }
    Map#Select(Map#Store(m,k1,val),k1) == val
);
axiom (
  forall<T,U> m: Map T U, k1: T, k2: T, val: U :: { Map#Select(Map#Store(m,k1,val),k2) }
    k1 != k2 ==> Map#Select(Map#Store(m,k1,val),k2) == Map#Select(m,k2)
);

// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

procedure Repeat#init#0()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var x: Chan (int);
  var y: Chan (int);
  assume x != y;
  assume (I#[x] == 0) && (R#[x] == 0) && (C#[x] == 0);
  assume (I#[y] == 0) && (R#[y] == 0) && (C#[y] == 0);
  assert {:msg "Repeat.actor(2.20): Initialization might not establish the invariant (#0)"} C#[y] == R#[x];
  assert {:msg "Repeat.actor(3.20): Initialization might not establish the invariant (#1)"} AT#Mod(R#[x], 3) == 0;
}
procedure Repeat#anon__4#1()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var x: Chan (int);
  var y: Chan (int);
  var x#0: Map (int) (int);
  assume x != y;
  assume (0 <= I#[x]) && (I#[x] <= R#[x]) && (R#[x] <= C#[x]);
  assume (0 <= I#[y]) && (I#[y] <= R#[y]) && (R#[y] <= C#[y]);
  assume C#[y] == R#[x];
  assume AT#Mod(R#[x], 3) == 0;
  assume 3 <= (C#[x] - R#[x]);
  x#0 := Map#Store(x#0, 0, M#[x][R#[x]]);
  R#[x] := R#[x] + 1;
  x#0 := Map#Store(x#0, 1, M#[x][R#[x]]);
  R#[x] := R#[x] + 1;
  x#0 := Map#Store(x#0, 2, M#[x][R#[x]]);
  R#[x] := R#[x] + 1;
  assume true;
  M#[y][C#[y]] := Map#Select(x#0, 0);
  C#[y] := C#[y] + 1;
  M#[y][C#[y]] := Map#Select(x#0, 1);
  C#[y] := C#[y] + 1;
  M#[y][C#[y]] := Map#Select(x#0, 2);
  C#[y] := C#[y] + 1;
  assert {:msg "Repeat.actor(2.20): Action 'anon__4' at <unknown_file>(-1.-1) might not preserve the invariant (#2)"} C#[y] == R#[x];
  assert {:msg "Repeat.actor(3.20): Action 'anon__4' at <unknown_file>(-1.-1) might not preserve the invariant (#3)"} AT#Mod(R#[x], 3) == 0;
}
procedure Net#init#2()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var Net#rep: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var anon__1: int;
  assume 0 <= I#[Net#a];
  assume I#[Net#a] <= R#[Net#a];
  assume R#[Net#a] <= C#[Net#a];
  assume 0 <= I#[Net#b];
  assume I#[Net#b] <= R#[Net#b];
  assume R#[Net#b] <= C#[Net#b];
  assume I#[Net#b] == R#[Net#b];
  assume (B#[Net#a] == 3) && (B#[Net#b] == 3);
  assume anon__1 == 0;
  assume Mode#[this#] == anon__1;
  assume C#[Net#a] == 0;
  assume R#[Net#a] == 0;
  assume C#[Net#b] == 0;
  assume R#[Net#b] == 0;
  assert {:msg "Repeat.actor(12.15): Initialization of network 'Net' might not establish the channel invariant (#4)"} I#[Net#a] == I#[Net#b];
  assert {:msg "Repeat.actor(13.15): Initialization of network 'Net' might not establish the channel invariant (#5)"} C#[Net#b] == R#[Net#a];
  assert {:msg "Initialization of network 'Net' might not establish the channel invariant (#6)"} (Mode#[this#] == anon__1) ==> ((C#[Net#a] - I#[Net#a]) <= 3);
  I# := R#;
  assert {:msg "Initialization of network 'Net' might not establish the network invariant (#7)"} (3 * R#[Net#a]) == (3 * C#[Net#b]);
  assert {:msg "Initialization of network 'Net' might not establish the network invariant: Unread tokens might be left on channel a (#8)"} (C#[Net#a] - R#[Net#a]) == 0;
  assert {:msg "Initialization of network 'Net' might not establish the network invariant: Unread tokens might be left on channel b (#9)"} (C#[Net#b] - R#[Net#b]) == 0;
}
procedure Net##Repeat#anon__2#3()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var Net#rep: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var anon__1: int;
  var rep#x#i: Map (int) (int);
  assume 0 <= I#[Net#a];
  assume I#[Net#a] <= R#[Net#a];
  assume R#[Net#a] <= C#[Net#a];
  assume 0 <= I#[Net#b];
  assume I#[Net#b] <= R#[Net#b];
  assume R#[Net#b] <= C#[Net#b];
  assume I#[Net#b] == R#[Net#b];
  assume (B#[Net#a] == 3) && (B#[Net#b] == 3);
  assume anon__1 == 0;
  assume Mode#[this#] == anon__1;
  I#sub[Net#a] := R#[Net#a];
  I#sub[Net#b] := C#[Net#b];
  assume I#[Net#a] == I#[Net#b];
  assume C#[Net#b] == R#[Net#a];
  assume (Mode#[this#] == anon__1) ==> ((C#[Net#a] - I#[Net#a]) <= 3);
  assume C#[Net#b] == R#[Net#a];
  assume AT#Mod(R#[Net#a], 3) == 0;
  assume 3 <= (C#[Net#a] - R#[Net#a]);
  rep#x#i := Map#Store(rep#x#i, 0, M#[Net#a][R#[Net#a]]);
  R#[Net#a] := R#[Net#a] + 1;
  rep#x#i := Map#Store(rep#x#i, 1, M#[Net#a][R#[Net#a]]);
  R#[Net#a] := R#[Net#a] + 1;
  rep#x#i := Map#Store(rep#x#i, 2, M#[Net#a][R#[Net#a]]);
  R#[Net#a] := R#[Net#a] + 1;
  M#[Net#b][C#[Net#b]] := Map#Select(rep#x#i, 0);
  C#[Net#b] := C#[Net#b] + 1;
  M#[Net#b][C#[Net#b]] := Map#Select(rep#x#i, 1);
  C#[Net#b] := C#[Net#b] + 1;
  M#[Net#b][C#[Net#b]] := Map#Select(rep#x#i, 2);
  C#[Net#b] := C#[Net#b] + 1;
  assert {:msg "Repeat.actor(12.15): Action at <unknown_file>(-1.-1) ('anon__2') for actor instance 'rep' might not preserve the channel invariant (#10)"} I#[Net#a] == I#[Net#b];
  assert {:msg "Repeat.actor(13.15): Action at <unknown_file>(-1.-1) ('anon__2') for actor instance 'rep' might not preserve the channel invariant (#11)"} C#[Net#b] == R#[Net#a];
  assert {:msg "Action at <unknown_file>(-1.-1) ('anon__2') for actor instance 'rep' might not preserve the channel invariant (#12)"} (Mode#[this#] == anon__1) ==> ((C#[Net#a] - I#[Net#a]) <= 3);
}
procedure Net#anon__1#input#x#4()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var Net#rep: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var anon__1: int;
  assume 0 <= I#[Net#a];
  assume I#[Net#a] <= R#[Net#a];
  assume R#[Net#a] <= C#[Net#a];
  assume 0 <= I#[Net#b];
  assume I#[Net#b] <= R#[Net#b];
  assume R#[Net#b] <= C#[Net#b];
  assume I#[Net#b] == R#[Net#b];
  assume (B#[Net#a] == 3) && (B#[Net#b] == 3);
  assume anon__1 == 0;
  assume Mode#[this#] == anon__1;
  assume (B#[Net#a] == 3) && (B#[Net#b] == 3);
  assume Mode#[this#] == anon__1;
  assume (C#[Net#a] - I#[Net#a]) < 3;
  assume I#[Net#a] == I#[Net#b];
  assume C#[Net#b] == R#[Net#a];
  assume (Mode#[this#] == anon__1) ==> ((C#[Net#a] - I#[Net#a]) <= 3);
  assume C#[Net#b] == R#[Net#a];
  assume AT#Mod(R#[Net#a], 3) == 0;
  C#[Net#a] := C#[Net#a] + 1;
  assert {:msg "Repeat.actor(12.15): Channel invariant might be falsified by network input on port 'x' for contract 'anon__1' (#13)"} I#[Net#a] == I#[Net#b];
  assert {:msg "Repeat.actor(13.15): Channel invariant might be falsified by network input on port 'x' for contract 'anon__1' (#14)"} C#[Net#b] == R#[Net#a];
  assert {:msg "Channel invariant might be falsified by network input on port 'x' for contract 'anon__1' (#15)"} (Mode#[this#] == anon__1) ==> ((C#[Net#a] - I#[Net#a]) <= 3);
}
procedure Net#anon__1#exit#5()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var Net#rep: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var anon__1: int;
  assume 0 <= I#[Net#a];
  assume I#[Net#a] <= R#[Net#a];
  assume R#[Net#a] <= C#[Net#a];
  assume 0 <= I#[Net#b];
  assume I#[Net#b] <= R#[Net#b];
  assume R#[Net#b] <= C#[Net#b];
  assume I#[Net#b] == R#[Net#b];
  assume (B#[Net#a] == 3) && (B#[Net#b] == 3);
  assume anon__1 == 0;
  assume Mode#[this#] == anon__1;
  assume Mode#[this#] == anon__1;
  assume (B#[Net#a] == 3) && (B#[Net#b] == 3);
  assume I#[Net#a] == I#[Net#b];
  assume C#[Net#b] == R#[Net#a];
  assume (Mode#[this#] == anon__1) ==> ((C#[Net#a] - I#[Net#a]) <= 3);
  assume C#[Net#b] == R#[Net#a];
  assume AT#Mod(R#[Net#a], 3) == 0;
  assume (C#[Net#a] - I#[Net#a]) == 3;
  assume !(3 <= (C#[Net#a] - R#[Net#a]));
  assert {:msg "Repeat.actor(10.3): The correct number of tokens might not be produced on output 'y' for contract 'anon__1' (#16)"} (C#[Net#b] - I#[Net#b]) == 3;
  R#[Net#b] := R#[Net#b] + 3;
  I# := R#;
  assert {:msg "Repeat.actor(12.15): The network might not preserve the channel invariant for contract 'anon__1' (#17)"} I#[Net#a] == I#[Net#b];
  assert {:msg "Repeat.actor(13.15): The network might not preserve the channel invariant for contract 'anon__1' (#18)"} C#[Net#b] == R#[Net#a];
  assert {:msg "The network might not preserve the channel invariant for contract 'anon__1' (#19)"} (Mode#[this#] == anon__1) ==> ((C#[Net#a] - I#[Net#a]) <= 3);
  assert {:msg "The network might not preserve the network invariant for contract 'anon__1' (#20)"} (3 * R#[Net#a]) == (3 * C#[Net#b]);
  assert {:msg "The network might not preserve the network invariant for contract 'anon__1': Unread tokens might be left on channel a (#21)"} (C#[Net#a] - R#[Net#a]) == 0;
  assert {:msg "The network might not preserve the network invariant for contract 'anon__1': Unread tokens might be left on channel b (#22)"} (C#[Net#b] - R#[Net#b]) == 0;
}

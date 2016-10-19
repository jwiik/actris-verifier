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
var I: CType;
var St: [Actor]State;

const unique this#: Actor;
type List a = [int]a;
var AT#intlst: List int;

function AT#Min(x:int, y: int): int { if x <= y then x else y }

// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

procedure TimeDep#init#0()
  modifies C, R, M, I, St;
{
  var in: Chan (int);
  var out: Chan (int);
  assume in != out;
  assume R[in] == 0;
  assume C[out] == 0;
}
procedure TimeDep#A#1()
  modifies C, R, M, I, St;
{
  var in: Chan (int);
  var out: Chan (int);
  var in#0: int;
  assume in != out;
  assume 0 <= R[in];
  assume 0 <= C[out];
  in#0 := M[in][R[in]];
  R[in] := R[in] + 1;
  assume true;
  M[out][C[out]] := in#0;
  C[out] := C[out] + 1;
}
procedure TimeDep#B#2()
  modifies C, R, M, I, St;
{
  var in: Chan (int);
  var out: Chan (int);
  var in#0: int;
  var in#1: int;
  assume in != out;
  assume 0 <= R[in];
  assume 0 <= C[out];
  in#0 := M[in][R[in]];
  R[in] := R[in] + 1;
  in#1 := M[in][R[in]];
  R[in] := R[in] + 1;
  assume true;
  M[out][C[out]] := in#0;
  C[out] := C[out] + 1;
}
procedure TimeDep##GuardWD#3()
  modifies C, R, M, I, St;
{
  var in: Chan (int);
  var out: Chan (int);
  var in#0: int;
  var in#1: int;
  assume in != out;
  assert {:msg "1.1: The actions of actor 'TimeDep' might not have mutually exclusive guards (#0)"} !((1 <= (C[in] - R[in])) && (2 <= (C[in] - R[in])));
}
procedure Net#init#4()
  modifies C, R, M, I, St;
{
  var Net#tp: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  assume Net#a != Net#b;
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume I[Net#b] == R[Net#b];
  assume C[Net#a] == 0;
  assume R[Net#a] == 0;
  assume C[Net#b] == 0;
  assume R[Net#b] == 0;
  assert {:msg "11.15: Initialization of network 'Net' might not establish the channel invariant (#1)"} I[Net#a] == I[Net#b];
  assert {:msg "12.15: Initialization of network 'Net' might not establish the channel invariant (#2)"} (C[Net#b] - I[Net#b]) == (R[Net#a] - I[Net#a]);
  assert {:msg "Initialization of network 'Net' might not establish the channel invariant (#3)"} true;
  I := R;
  assert {:msg "19.5: The initialization might produce unspecified tokens on channel a (#4)"} (C[Net#a] - R[Net#a]) == 0;
  assert {:msg "20.5: The initialization might produce unspecified tokens on channel b (#5)"} (C[Net#b] - R[Net#b]) == 0;
}
procedure Net##TimeDep#A#5()
  modifies C, R, M, I, St;
{
  var Net#tp: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var in#i: int;
  assume Net#a != Net#b;
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume I[Net#b] == R[Net#b];
  assume I[Net#a] == I[Net#b];
  assume (C[Net#b] - I[Net#b]) == (R[Net#a] - I[Net#a]);
  assume true;
  assume 1 <= (C[Net#a] - R[Net#a]);
  in#i := M[Net#a][R[Net#a]];
  R[Net#a] := R[Net#a] + 1;
  M[Net#b][C[Net#b]] := in#i;
  C[Net#b] := C[Net#b] + 1;
  assert {:msg "11.15: Action at 2.3 ('A') for actor instance 'tp' might not preserve the channel invariant (#6)"} I[Net#a] == I[Net#b];
  assert {:msg "12.15: Action at 2.3 ('A') for actor instance 'tp' might not preserve the channel invariant (#7)"} (C[Net#b] - I[Net#b]) == (R[Net#a] - I[Net#a]);
  assert {:msg "Action at 2.3 ('A') for actor instance 'tp' might not preserve the channel invariant (#8)"} true;
}
procedure Net##TimeDep#B#6()
  modifies C, R, M, I, St;
{
  var Net#tp: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var in#i: int;
  var in#j: int;
  assume Net#a != Net#b;
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume I[Net#b] == R[Net#b];
  assume I[Net#a] == I[Net#b];
  assume (C[Net#b] - I[Net#b]) == (R[Net#a] - I[Net#a]);
  assume true;
  assume (!(1 <= (C[Net#a] - R[Net#a]))) && (2 <= (C[Net#a] - R[Net#a]));
  in#i := M[Net#a][R[Net#a]];
  R[Net#a] := R[Net#a] + 1;
  in#j := M[Net#a][R[Net#a]];
  R[Net#a] := R[Net#a] + 1;
  M[Net#b][C[Net#b]] := in#i;
  C[Net#b] := C[Net#b] + 1;
  assert {:msg "11.15: Action at 3.3 ('B') for actor instance 'tp' might not preserve the channel invariant (#9)"} I[Net#a] == I[Net#b];
  assert {:msg "12.15: Action at 3.3 ('B') for actor instance 'tp' might not preserve the channel invariant (#10)"} (C[Net#b] - I[Net#b]) == (R[Net#a] - I[Net#a]);
  assert {:msg "Action at 3.3 ('B') for actor instance 'tp' might not preserve the channel invariant (#11)"} true;
}
procedure Net#entry()
  modifies C, R, M, I, St;
{
  var Net#tp: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  assume Net#a != Net#b;
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume I[Net#b] == R[Net#b];
  assume C[Net#a] == R[Net#a];
  assume C[Net#b] == R[Net#b];
  assume I[Net#a] == I[Net#b];
  assume (C[Net#b] - I[Net#b]) == (R[Net#a] - I[Net#a]);
  assume true;
  assert {:msg "7.1: Sub-actors in the network might fire without network input. This is not permitted. (#12)"} !((!(1 <= (C[Net#a] - R[Net#a]))) && (2 <= (C[Net#a] - R[Net#a])));
  assert {:msg "7.1: Sub-actors in the network might fire without network input. This is not permitted. (#13)"} !(1 <= (C[Net#a] - R[Net#a]));
}
procedure Net#anon$0#input#in#7()
  modifies C, R, M, I, St;
{
  var Net#tp: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  assume Net#a != Net#b;
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume I[Net#b] == R[Net#b];
  assume C[Net#a] < 1;
  assume I[Net#a] == I[Net#b];
  assume (C[Net#b] - I[Net#b]) == (R[Net#a] - I[Net#a]);
  assume true;
  C[Net#a] := C[Net#a] + 1;
  assert {:msg "11.15: Channel invariant might be falsified by network input (#14)"} I[Net#a] == I[Net#b];
  assert {:msg "12.15: Channel invariant might be falsified by network input (#15)"} (C[Net#b] - I[Net#b]) == (R[Net#a] - I[Net#a]);
  assert {:msg "Channel invariant might be falsified by network input (#16)"} true;
}
procedure Net#anon$0#exit#8()
  modifies C, R, M, I, St;
{
  var Net#tp: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  assume Net#a != Net#b;
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume I[Net#b] == R[Net#b];
  assume I[Net#a] == I[Net#b];
  assume (C[Net#b] - I[Net#b]) == (R[Net#a] - I[Net#a]);
  assume true;
  assume (C[Net#a] - I[Net#a]) == 1;
  assume !((!(1 <= (C[Net#a] - R[Net#a]))) && (2 <= (C[Net#a] - R[Net#a])));
  assume !(1 <= (C[Net#a] - R[Net#a]));
  R[Net#b] := R[Net#b] + 1;
  I := R;
  assert {:msg "11.15: The network might not preserve the channel invariant (#17)"} I[Net#a] == I[Net#b];
  assert {:msg "12.15: The network might not preserve the channel invariant (#18)"} (C[Net#b] - I[Net#b]) == (R[Net#a] - I[Net#a]);
  assert {:msg "The network might not preserve the channel invariant (#19)"} true;
  assert {:msg "9.3: The network might leave unread tokens on channel a (#20)"} C[Net#a] == R[Net#a];
  assert {:msg "9.3: The network might not produce the specified number of tokens on output out (#21)"} C[Net#b] == R[Net#b];
}

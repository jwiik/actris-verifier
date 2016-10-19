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

function AT#Abs(x: int): int { if 0 <= x then x else -x }
function AT#Div(int, int): int;
function AT#Mod(int, int): int;
axiom (forall a,b: int :: AT#Div(a,b)*b + AT#Mod(a,b) == a);
axiom (forall a,b: int :: 0 <= AT#Mod(a,b) && AT#Mod(a,b) < AT#Abs(b));

function AT#BvAnd(a: int, b: int): int;

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
  AT#RShift(a,8) == AT#Div(a,256) &&
  AT#RShift(a,9) == AT#Div(a,512)
));
axiom (forall a: int :: (
  AT#LShift(a,1) == a * 2 &&
  AT#LShift(a,2) == a * 4 &&
  AT#LShift(a,3) == a * 8 &&
  AT#LShift(a,4) == a * 16 &&
  AT#LShift(a,5) == a * 32 &&
  AT#LShift(a,6) == a * 64 &&
  AT#LShift(a,7) == a * 128 &&
  AT#LShift(a,8) == a * 256 &&
  AT#LShift(a,9) == a * 512
));

// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

procedure chipMapper#init#0()
  modifies C, R, M, I, St;
{
  var data: Chan (int);
  var chip: Chan (int);
  var dataV: int;
  var offset: int;
  var ind: int;
  assume data != chip;
  assume R[data] == 0;
  assume C[chip] == 0;
  offset := 8;
  assert {:msg "9.22: Initialization might not establish the invariant (#0)"} ((offset == 0) || (offset == 4)) || (offset == 8);
  assert {:msg "10.22: Initialization might not establish the invariant (#1)"} (2 * R[data]) == (C[chip] + AT#Div(8 - offset, 4));
}
procedure chipMapper#read#1()
  modifies C, R, M, I, St;
{
  var data: Chan (int);
  var chip: Chan (int);
  var dataV: int;
  var offset: int;
  var ind: int;
  var data#0: int;
  assume data != chip;
  assume 0 <= R[data];
  assume 0 <= C[chip];
  assume ((offset == 0) || (offset == 4)) || (offset == 8);
  assume (2 * R[data]) == (C[chip] + AT#Div(8 - offset, 4));
  data#0 := M[data][R[data]];
  R[data] := R[data] + 1;
  assume offset == 8;
  dataV := data#0;
  offset := 0;
  assert {:msg "9.22: Action at 19.2 might not preserve invariant (#2)"} ((offset == 0) || (offset == 4)) || (offset == 8);
  assert {:msg "10.22: Action at 19.2 might not preserve invariant (#3)"} (2 * R[data]) == (C[chip] + AT#Div(8 - offset, 4));
}
procedure chipMapper#write#2()
  modifies C, R, M, I, St;
{
  var data: Chan (int);
  var chip: Chan (int);
  var dataV: int;
  var offset: int;
  var ind: int;
  assume data != chip;
  assume 0 <= R[data];
  assume 0 <= C[chip];
  assume ((offset == 0) || (offset == 4)) || (offset == 8);
  assume (2 * R[data]) == (C[chip] + AT#Div(8 - offset, 4));
  assume offset < 8;
  ind := AT#BvAnd(AT#RShift(dataV, offset), 15);
  offset := offset + 4;
  M[chip][C[chip]] := ind;
  C[chip] := C[chip] + 1;
  assert {:msg "9.22: Action at 28.2 might not preserve invariant (#4)"} ((offset == 0) || (offset == 4)) || (offset == 8);
  assert {:msg "10.22: Action at 28.2 might not preserve invariant (#5)"} (2 * R[data]) == (C[chip] + AT#Div(8 - offset, 4));
}
procedure chipMapper##GuardWD#3()
  modifies C, R, M, I, St;
{
  var data: Chan (int);
  var chip: Chan (int);
  var dataV: int;
  var offset: int;
  var ind: int;
  var data#0: int;
  assume data != chip;
  assert {:msg "1.1: The actions of actor 'chipMapper' might not have mutually exclusive guards (#6)"} !((1 <= (C[data] - R[data])) && (offset == 8) && (offset < 8));
}
procedure Net#init#4()
  modifies C, R, M, I, St;
{
  var Net#cm: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var AV#cm#dataV: int;
  var AV#cm#offset: int;
  var AV#cm#ind: int;
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
  assume ((AV#cm#offset == 0) || (AV#cm#offset == 4)) || (AV#cm#offset == 8);
  assume (2 * R[Net#a]) == (C[Net#b] + AT#Div(8 - AV#cm#offset, 4));
  assert {:msg "49.15: Initialization of network 'Net' might not establish the channel invariant (#7)"} (2 * I[Net#a]) == I[Net#b];
  assert {:msg "Initialization of network 'Net' might not establish the channel invariant (#8)"} true;
  I := R;
  assert {:msg "47.13: Network initialization might not establish the network invariant (#9)"} AV#cm#offset == 8;
  assert {:msg "56.5: The initialization might produce unspecified tokens on channel a (#10)"} (C[Net#a] - R[Net#a]) == 0;
  assert {:msg "57.5: The initialization might produce unspecified tokens on channel b (#11)"} (C[Net#b] - R[Net#b]) == 0;
}
procedure Net##chipMapper#write#5()
  modifies C, R, M, I, St;
{
  var Net#cm: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var AV#cm#dataV: int;
  var AV#cm#offset: int;
  var AV#cm#ind: int;
  assume Net#a != Net#b;
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume I[Net#b] == R[Net#b];
  assume (2 * I[Net#a]) == I[Net#b];
  assume true;
  assume ((AV#cm#offset == 0) || (AV#cm#offset == 4)) || (AV#cm#offset == 8);
  assume (2 * R[Net#a]) == (C[Net#b] + AT#Div(8 - AV#cm#offset, 4));
  assume AV#cm#offset < 8;
  assume ((AV#cm#offset == 0) || (AV#cm#offset == 4)) || (AV#cm#offset == 8);
  assume (2 * R[Net#a]) == (C[Net#b] + AT#Div(8 - AV#cm#offset, 4));
  havoc AV#cm#dataV;
  havoc AV#cm#offset;
  havoc AV#cm#ind;
  M[Net#b][C[Net#b]] := AV#cm#ind;
  C[Net#b] := C[Net#b] + 1;
  assume ((AV#cm#offset == 0) || (AV#cm#offset == 4)) || (AV#cm#offset == 8);
  assume (2 * R[Net#a]) == (C[Net#b] + AT#Div(8 - AV#cm#offset, 4));
  assert {:msg "49.15: Action at 28.2 ('write') for actor instance 'cm' might not preserve the channel invariant (#12)"} (2 * I[Net#a]) == I[Net#b];
  assert {:msg "Action at 28.2 ('write') for actor instance 'cm' might not preserve the channel invariant (#13)"} true;
}
procedure Net##chipMapper#read#6()
  modifies C, R, M, I, St;
{
  var Net#cm: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var AV#cm#dataV: int;
  var AV#cm#offset: int;
  var AV#cm#ind: int;
  var data#data_in: int;
  assume Net#a != Net#b;
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume I[Net#b] == R[Net#b];
  assume (2 * I[Net#a]) == I[Net#b];
  assume true;
  assume ((AV#cm#offset == 0) || (AV#cm#offset == 4)) || (AV#cm#offset == 8);
  assume (2 * R[Net#a]) == (C[Net#b] + AT#Div(8 - AV#cm#offset, 4));
  assume (!(AV#cm#offset < 8)) && (1 <= (C[Net#a] - R[Net#a])) && (AV#cm#offset == 8);
  assume ((AV#cm#offset == 0) || (AV#cm#offset == 4)) || (AV#cm#offset == 8);
  assume (2 * R[Net#a]) == (C[Net#b] + AT#Div(8 - AV#cm#offset, 4));
  data#data_in := M[Net#a][R[Net#a]];
  R[Net#a] := R[Net#a] + 1;
  havoc AV#cm#dataV;
  havoc AV#cm#offset;
  havoc AV#cm#ind;
  assume ((AV#cm#offset == 0) || (AV#cm#offset == 4)) || (AV#cm#offset == 8);
  assume (2 * R[Net#a]) == (C[Net#b] + AT#Div(8 - AV#cm#offset, 4));
  assert {:msg "49.15: Action at 19.2 ('read') for actor instance 'cm' might not preserve the channel invariant (#14)"} (2 * I[Net#a]) == I[Net#b];
  assert {:msg "Action at 19.2 ('read') for actor instance 'cm' might not preserve the channel invariant (#15)"} true;
}
procedure Net#entry()
  modifies C, R, M, I, St;
{
  var Net#cm: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var AV#cm#dataV: int;
  var AV#cm#offset: int;
  var AV#cm#ind: int;
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
  assume AV#cm#offset == 8;
  assume (2 * I[Net#a]) == I[Net#b];
  assume true;
  assume ((AV#cm#offset == 0) || (AV#cm#offset == 4)) || (AV#cm#offset == 8);
  assume (2 * R[Net#a]) == (C[Net#b] + AT#Div(8 - AV#cm#offset, 4));
  assert {:msg "43.1: Sub-actors in the network might fire without network input. This is not permitted. (#16)"} !((!(AV#cm#offset < 8)) && (1 <= (C[Net#a] - R[Net#a])) && (AV#cm#offset == 8));
  assert {:msg "43.1: Sub-actors in the network might fire without network input. This is not permitted. (#17)"} !(AV#cm#offset < 8);
}
procedure Net#anon$0#input#in#7()
  modifies C, R, M, I, St;
{
  var Net#cm: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var AV#cm#dataV: int;
  var AV#cm#offset: int;
  var AV#cm#ind: int;
  assume Net#a != Net#b;
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume I[Net#b] == R[Net#b];
  assume C[Net#a] < 1;
  assume (2 * I[Net#a]) == I[Net#b];
  assume true;
  assume ((AV#cm#offset == 0) || (AV#cm#offset == 4)) || (AV#cm#offset == 8);
  assume (2 * R[Net#a]) == (C[Net#b] + AT#Div(8 - AV#cm#offset, 4));
  C[Net#a] := C[Net#a] + 1;
  assert {:msg "49.15: Channel invariant might be falsified by network input (#18)"} (2 * I[Net#a]) == I[Net#b];
  assert {:msg "Channel invariant might be falsified by network input (#19)"} true;
}
procedure Net#anon$0#exit#8()
  modifies C, R, M, I, St;
{
  var Net#cm: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var AV#cm#dataV: int;
  var AV#cm#offset: int;
  var AV#cm#ind: int;
  assume Net#a != Net#b;
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume I[Net#b] == R[Net#b];
  assume (2 * I[Net#a]) == I[Net#b];
  assume true;
  assume ((AV#cm#offset == 0) || (AV#cm#offset == 4)) || (AV#cm#offset == 8);
  assume (2 * R[Net#a]) == (C[Net#b] + AT#Div(8 - AV#cm#offset, 4));
  assume (C[Net#a] - I[Net#a]) == 1;
  assume !((!(AV#cm#offset < 8)) && (1 <= (C[Net#a] - R[Net#a])) && (AV#cm#offset == 8));
  assume !(AV#cm#offset < 8);
  R[Net#b] := R[Net#b] + 2;
  I := R;
  assert {:msg "49.15: The network might not preserve the channel invariant (#20)"} (2 * I[Net#a]) == I[Net#b];
  assert {:msg "The network might not preserve the channel invariant (#21)"} true;
  assert {:msg "47.13: The network might not preserve the network invariant (#22)"} AV#cm#offset == 8;
  assert {:msg "45.3: The network might leave unread tokens on channel a (#23)"} C[Net#a] == R[Net#a];
  assert {:msg "45.3: The network might not produce the specified number of tokens on output out (#24)"} C[Net#b] == R[Net#b];
}

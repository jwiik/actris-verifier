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

// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

procedure RW#init#0()
  modifies C, R, M, I, St;
{
  var in: Chan (int);
  var out: Chan (int);
  var step: int;
  var data: int;
  assume in != out;
  assume R[in] == 0;
  assume C[out] == 0;
  step := 2;
  assert {:msg "3.22: Initialization might not establish the invariant (#0)"} ((step == 0) || (step == 1)) || (step == 2);
  assert {:msg "4.22: Initialization might not establish the invariant (#1)"} (2 * R[in]) == (C[out] + (2 - step));
  assert {:msg "5.23: Initialization might not establish the invariant (#2)"} (forall i: int :: 
    (0 <= i) && (i < C[out]) ==> (M[out][i] == ((M[in][AT#Div(i, 2)] + AT#Mod(i, 2)) + 1))
  );
  assert {:msg "6.22: Initialization might not establish the invariant (#3)"} (R[in] > 0) ==> (M[in][R[in] - 1] == data);
}
procedure RW#read#1()
  modifies C, R, M, I, St;
{
  var in: Chan (int);
  var out: Chan (int);
  var step: int;
  var data: int;
  var in#0: int;
  assume in != out;
  assume 0 <= R[in];
  assume 0 <= C[out];
  assume ((step == 0) || (step == 1)) || (step == 2);
  assume (2 * R[in]) == (C[out] + (2 - step));
  assume (forall i: int :: 
    (0 <= i) && (i < C[out]) ==> (M[out][i] == ((M[in][AT#Div(i, 2)] + AT#Mod(i, 2)) + 1))
  );
  assume (R[in] > 0) ==> (M[in][R[in] - 1] == data);
  in#0 := M[in][R[in]];
  R[in] := R[in] + 1;
  assume step == 2;
  step := 0;
  data := in#0;
  assert {:msg "3.22: Action at 13.2 might not preserve invariant (#4)"} ((step == 0) || (step == 1)) || (step == 2);
  assert {:msg "4.22: Action at 13.2 might not preserve invariant (#5)"} (2 * R[in]) == (C[out] + (2 - step));
  assert {:msg "5.23: Action at 13.2 might not preserve invariant (#6)"} (forall i: int :: 
    (0 <= i) && (i < C[out]) ==> (M[out][i] == ((M[in][AT#Div(i, 2)] + AT#Mod(i, 2)) + 1))
  );
  assert {:msg "6.22: Action at 13.2 might not preserve invariant (#7)"} (R[in] > 0) ==> (M[in][R[in] - 1] == data);
}
procedure RW#write#2()
  modifies C, R, M, I, St;
{
  var in: Chan (int);
  var out: Chan (int);
  var step: int;
  var data: int;
  assume in != out;
  assume 0 <= R[in];
  assume 0 <= C[out];
  assume ((step == 0) || (step == 1)) || (step == 2);
  assume (2 * R[in]) == (C[out] + (2 - step));
  assume (forall i: int :: 
    (0 <= i) && (i < C[out]) ==> (M[out][i] == ((M[in][AT#Div(i, 2)] + AT#Mod(i, 2)) + 1))
  );
  assume (R[in] > 0) ==> (M[in][R[in] - 1] == data);
  assume step < 2;
  step := step + 1;
  M[out][C[out]] := data + step;
  C[out] := C[out] + 1;
  assert {:msg "3.22: Action at 20.2 might not preserve invariant (#8)"} ((step == 0) || (step == 1)) || (step == 2);
  assert {:msg "4.22: Action at 20.2 might not preserve invariant (#9)"} (2 * R[in]) == (C[out] + (2 - step));
  assert {:msg "5.23: Action at 20.2 might not preserve invariant (#10)"} (forall i: int :: 
    (0 <= i) && (i < C[out]) ==> (M[out][i] == ((M[in][AT#Div(i, 2)] + AT#Mod(i, 2)) + 1))
  );
  assert {:msg "6.22: Action at 20.2 might not preserve invariant (#11)"} (R[in] > 0) ==> (M[in][R[in] - 1] == data);
}
procedure RW##GuardWD#3()
  modifies C, R, M, I, St;
{
  var in: Chan (int);
  var out: Chan (int);
  var step: int;
  var data: int;
  var in#0: int;
  assume in != out;
  assert {:msg "1.1: The actions of actor 'RW' might not have mutually exclusive guards (#12)"} !((1 <= (C[in] - R[in])) && (step == 2) && (step < 2));
}
procedure Net#init#4()
  modifies C, R, M, I, St;
{
  var Net#rw: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var AV#rw#step: int;
  var AV#rw#data: int;
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
  assume ((AV#rw#step == 0) || (AV#rw#step == 1)) || (AV#rw#step == 2);
  assume (2 * R[Net#a]) == (C[Net#b] + (2 - AV#rw#step));
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#b]) ==> (M[Net#b][i] == ((M[Net#a][AT#Div(i, 2)] + AT#Mod(i, 2)) + 1))
  );
  assume (R[Net#a] > 0) ==> (M[Net#a][R[Net#a] - 1] == AV#rw#data);
  assert {:msg "40.15: Initialization of network 'Net' might not establish the channel invariant (#13)"} (2 * I[Net#a]) == I[Net#b];
  assert {:msg "Initialization of network 'Net' might not establish the channel invariant (#14)"} true;
  I := R;
  assert {:msg "38.13: Network initialization might not establish the network invariant (#15)"} AV#rw#step == 2;
  assert {:msg "50.5: The initialization might produce unspecified tokens on channel a (#16)"} (C[Net#a] - R[Net#a]) == 0;
  assert {:msg "51.5: The initialization might produce unspecified tokens on channel b (#17)"} (C[Net#b] - R[Net#b]) == 0;
}
procedure Net##RW#write#5()
  modifies C, R, M, I, St;
{
  var Net#rw: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var AV#rw#step: int;
  var AV#rw#data: int;
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
  assume ((AV#rw#step == 0) || (AV#rw#step == 1)) || (AV#rw#step == 2);
  assume (2 * R[Net#a]) == (C[Net#b] + (2 - AV#rw#step));
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#b]) ==> (M[Net#b][i] == ((M[Net#a][AT#Div(i, 2)] + AT#Mod(i, 2)) + 1))
  );
  assume (R[Net#a] > 0) ==> (M[Net#a][R[Net#a] - 1] == AV#rw#data);
  assume AV#rw#step < 2;
  assume ((AV#rw#step == 0) || (AV#rw#step == 1)) || (AV#rw#step == 2);
  assume (2 * R[Net#a]) == (C[Net#b] + (2 - AV#rw#step));
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#b]) ==> (M[Net#b][i] == ((M[Net#a][AT#Div(i, 2)] + AT#Mod(i, 2)) + 1))
  );
  assume (R[Net#a] > 0) ==> (M[Net#a][R[Net#a] - 1] == AV#rw#data);
  havoc AV#rw#step;
  havoc AV#rw#data;
  M[Net#b][C[Net#b]] := AV#rw#data + AV#rw#step;
  C[Net#b] := C[Net#b] + 1;
  assume ((AV#rw#step == 0) || (AV#rw#step == 1)) || (AV#rw#step == 2);
  assume (2 * R[Net#a]) == (C[Net#b] + (2 - AV#rw#step));
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#b]) ==> (M[Net#b][i] == ((M[Net#a][AT#Div(i, 2)] + AT#Mod(i, 2)) + 1))
  );
  assume (R[Net#a] > 0) ==> (M[Net#a][R[Net#a] - 1] == AV#rw#data);
  assert {:msg "40.15: Action at 20.2 ('write') for actor instance 'rw' might not preserve the channel invariant (#18)"} (2 * I[Net#a]) == I[Net#b];
  assert {:msg "Action at 20.2 ('write') for actor instance 'rw' might not preserve the channel invariant (#19)"} true;
}
procedure Net##RW#read#6()
  modifies C, R, M, I, St;
{
  var Net#rw: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var AV#rw#step: int;
  var AV#rw#data: int;
  var in#data_in: int;
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
  assume ((AV#rw#step == 0) || (AV#rw#step == 1)) || (AV#rw#step == 2);
  assume (2 * R[Net#a]) == (C[Net#b] + (2 - AV#rw#step));
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#b]) ==> (M[Net#b][i] == ((M[Net#a][AT#Div(i, 2)] + AT#Mod(i, 2)) + 1))
  );
  assume (R[Net#a] > 0) ==> (M[Net#a][R[Net#a] - 1] == AV#rw#data);
  assume (!(AV#rw#step < 2)) && (1 <= (C[Net#a] - R[Net#a])) && (AV#rw#step == 2);
  assume ((AV#rw#step == 0) || (AV#rw#step == 1)) || (AV#rw#step == 2);
  assume (2 * R[Net#a]) == (C[Net#b] + (2 - AV#rw#step));
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#b]) ==> (M[Net#b][i] == ((M[Net#a][AT#Div(i, 2)] + AT#Mod(i, 2)) + 1))
  );
  assume (R[Net#a] > 0) ==> (M[Net#a][R[Net#a] - 1] == AV#rw#data);
  in#data_in := M[Net#a][R[Net#a]];
  R[Net#a] := R[Net#a] + 1;
  havoc AV#rw#step;
  havoc AV#rw#data;
  assume ((AV#rw#step == 0) || (AV#rw#step == 1)) || (AV#rw#step == 2);
  assume (2 * R[Net#a]) == (C[Net#b] + (2 - AV#rw#step));
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#b]) ==> (M[Net#b][i] == ((M[Net#a][AT#Div(i, 2)] + AT#Mod(i, 2)) + 1))
  );
  assume (R[Net#a] > 0) ==> (M[Net#a][R[Net#a] - 1] == AV#rw#data);
  assert {:msg "40.15: Action at 13.2 ('read') for actor instance 'rw' might not preserve the channel invariant (#20)"} (2 * I[Net#a]) == I[Net#b];
  assert {:msg "Action at 13.2 ('read') for actor instance 'rw' might not preserve the channel invariant (#21)"} true;
}
procedure Net#entry()
  modifies C, R, M, I, St;
{
  var Net#rw: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var AV#rw#step: int;
  var AV#rw#data: int;
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
  assume AV#rw#step == 2;
  assume (2 * I[Net#a]) == I[Net#b];
  assume true;
  assume ((AV#rw#step == 0) || (AV#rw#step == 1)) || (AV#rw#step == 2);
  assume (2 * R[Net#a]) == (C[Net#b] + (2 - AV#rw#step));
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#b]) ==> (M[Net#b][i] == ((M[Net#a][AT#Div(i, 2)] + AT#Mod(i, 2)) + 1))
  );
  assume (R[Net#a] > 0) ==> (M[Net#a][R[Net#a] - 1] == AV#rw#data);
  assert {:msg "31.1: Sub-actors in the network might fire without network input. This is not permitted. (#22)"} !(AV#rw#step < 2);
  assert {:msg "31.1: Sub-actors in the network might fire without network input. This is not permitted. (#23)"} !((!(AV#rw#step < 2)) && (1 <= (C[Net#a] - R[Net#a])) && (AV#rw#step == 2));
}
procedure Net#anon$0#input#in#7()
  modifies C, R, M, I, St;
{
  var Net#rw: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var AV#rw#step: int;
  var AV#rw#data: int;
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
  assume ((AV#rw#step == 0) || (AV#rw#step == 1)) || (AV#rw#step == 2);
  assume (2 * R[Net#a]) == (C[Net#b] + (2 - AV#rw#step));
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#b]) ==> (M[Net#b][i] == ((M[Net#a][AT#Div(i, 2)] + AT#Mod(i, 2)) + 1))
  );
  assume (R[Net#a] > 0) ==> (M[Net#a][R[Net#a] - 1] == AV#rw#data);
  C[Net#a] := C[Net#a] + 1;
  assert {:msg "40.15: Channel invariant might be falsified by network input (#24)"} (2 * I[Net#a]) == I[Net#b];
  assert {:msg "Channel invariant might be falsified by network input (#25)"} true;
}
procedure Net#anon$0#exit#8()
  modifies C, R, M, I, St;
{
  var Net#rw: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var AV#rw#step: int;
  var AV#rw#data: int;
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
  assume ((AV#rw#step == 0) || (AV#rw#step == 1)) || (AV#rw#step == 2);
  assume (2 * R[Net#a]) == (C[Net#b] + (2 - AV#rw#step));
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#b]) ==> (M[Net#b][i] == ((M[Net#a][AT#Div(i, 2)] + AT#Mod(i, 2)) + 1))
  );
  assume (R[Net#a] > 0) ==> (M[Net#a][R[Net#a] - 1] == AV#rw#data);
  assume (C[Net#a] - I[Net#a]) == 1;
  assume !(AV#rw#step < 2);
  assume !((!(AV#rw#step < 2)) && (1 <= (C[Net#a] - R[Net#a])) && (AV#rw#step == 2));
  assert {:msg "34.13: Network action postcondition might not hold (#26)"} M[Net#b][I[Net#b]] == (M[Net#a][I[Net#a]] + 1);
  assert {:msg "35.13: Network action postcondition might not hold (#27)"} M[Net#b][I[Net#b] + 1] == (M[Net#a][I[Net#a]] + 2);
  R[Net#b] := R[Net#b] + 2;
  I := R;
  assert {:msg "40.15: The network might not preserve the channel invariant (#28)"} (2 * I[Net#a]) == I[Net#b];
  assert {:msg "The network might not preserve the channel invariant (#29)"} true;
  assert {:msg "38.13: The network might not preserve the network invariant (#30)"} AV#rw#step == 2;
  assert {:msg "33.3: The network might leave unread tokens on channel a (#31)"} C[Net#a] == R[Net#a];
  assert {:msg "33.3: The network might not produce the specified number of tokens on output out (#32)"} C[Net#b] == R[Net#b];
}

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

var M: MType;
var C: CType;
var R: CType;
var I: CType;

var H: HType;

const unique this#: Actor;

function AT#Min(x:int, y: int): int { if x <= y then x else y }

// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

procedure HowMany#init#0()
  modifies C, R, M, I, H;
{
  var In: Chan (int);
  var Out: Chan (bool);
  var curr: int;
  var amount: int;
  var rd_str: int;
  var tot_str: int;
  assume true;
  assume R[In] == 0;
  assume C[Out] == 0;
  rd_str := 0;
  tot_str := 0;
  curr := 0;
  amount := 0;
  assert {:msg "9.13: Initialization might not establish the invariant (#0)"} (0 <= curr) && (curr <= amount);
  assert {:msg "10.13: Initialization might not establish the invariant (#1)"} (R[In] > 0) ==> (amount == M[In][R[In] - 1]);
  assert {:msg "11.13: Initialization might not establish the invariant (#2)"} (C[Out] - tot_str) == curr;
}
procedure HowMany#anon$1#1()
  modifies C, R, M, I, H;
{
  var In: Chan (int);
  var Out: Chan (bool);
  var curr: int;
  var amount: int;
  var rd_str: int;
  var tot_str: int;
  var In#0: int;
  assume true;
  assume 0 <= R[In];
  assume 0 <= C[Out];
  assume (0 <= curr) && (curr <= amount);
  assume (R[In] > 0) ==> (amount == M[In][R[In] - 1]);
  assume (C[Out] - tot_str) == curr;
  In#0 := M[In][R[In]];
  R[In] := R[In] + 1;
  assume 0 <= In#0;
  assume curr == amount;
  rd_str := R[In];
  tot_str := C[Out];
  amount := In#0;
  curr := 0;
  assert {:msg "9.13: Action at 21.3 might not preserve invariant (#3)"} (0 <= curr) && (curr <= amount);
  assert {:msg "10.13: Action at 21.3 might not preserve invariant (#4)"} (R[In] > 0) ==> (amount == M[In][R[In] - 1]);
  assert {:msg "11.13: Action at 21.3 might not preserve invariant (#5)"} (C[Out] - tot_str) == curr;
}
procedure HowMany#anon$2#2()
  modifies C, R, M, I, H;
{
  var In: Chan (int);
  var Out: Chan (bool);
  var curr: int;
  var amount: int;
  var rd_str: int;
  var tot_str: int;
  var In#0: int;
  assume true;
  assume 0 <= R[In];
  assume 0 <= C[Out];
  assume (0 <= curr) && (curr <= amount);
  assume (R[In] > 0) ==> (amount == M[In][R[In] - 1]);
  assume (C[Out] - tot_str) == curr;
  assume curr < amount;
  curr := curr + 1;
  M[Out][C[Out]] := true;
  C[Out] := C[Out] + 1;
  assert {:msg "9.13: Action at 31.3 might not preserve invariant (#6)"} (0 <= curr) && (curr <= amount);
  assert {:msg "10.13: Action at 31.3 might not preserve invariant (#7)"} (R[In] > 0) ==> (amount == M[In][R[In] - 1]);
  assert {:msg "11.13: Action at 31.3 might not preserve invariant (#8)"} (C[Out] - tot_str) == curr;
}
procedure HowMany##GuardWD#3()
  modifies C, R, M, I, H;
{
  var In: Chan (int);
  var Out: Chan (bool);
  var curr: int;
  var amount: int;
  var rd_str: int;
  var tot_str: int;
  var In#0: int;
  assume true;
  assert {:msg "1.1: The actions 'anon$1' and 'anon$2' of actor 'HowMany' might not have mutually exclusive guards (#9)"} !(true && (1 <= (C[In] - R[In])) && (curr == amount) && true && true && (curr < amount));
}
procedure HowManyNet#init#4()
  modifies C, R, M, I, H;
{
  var HowManyNet#a: Actor;
  var HowManyNet#anon$4: Chan (int);
  var HowManyNet#anon$5: Chan (bool);
  var AV#a#curr: int;
  var AV#a#amount: int;
  var AV#a#rd_str: int;
  var AV#a#tot_str: int;
  assume 0 <= I[HowManyNet#anon$4];
  assume I[HowManyNet#anon$4] <= R[HowManyNet#anon$4];
  assume R[HowManyNet#anon$4] <= C[HowManyNet#anon$4];
  assume 0 <= I[HowManyNet#anon$5];
  assume I[HowManyNet#anon$5] <= R[HowManyNet#anon$5];
  assume R[HowManyNet#anon$5] <= C[HowManyNet#anon$5];
  assume I[HowManyNet#anon$5] == R[HowManyNet#anon$5];
  assume C[HowManyNet#anon$4] == 0;
  assume R[HowManyNet#anon$4] == 0;
  assume C[HowManyNet#anon$5] == 0;
  assume R[HowManyNet#anon$5] == 0;
  assert {:msg "45.15: Initialization of network 'HowManyNet' might not establish the channel invariant (#10)"} ((R[HowManyNet#anon$4] - I[HowManyNet#anon$4]) == 0) ==> ((C[HowManyNet#anon$5] - I[HowManyNet#anon$5]) == 0);
  assert {:msg "46.15: Initialization of network 'HowManyNet' might not establish the channel invariant (#11)"} ((C[HowManyNet#anon$4] - I[HowManyNet#anon$4]) > 0) ==> ((C[HowManyNet#anon$5] - I[HowManyNet#anon$5]) <= M[HowManyNet#anon$4][I[HowManyNet#anon$4]]);
  assert {:msg "47.15: Initialization of network 'HowManyNet' might not establish the channel invariant (#12)"} (C[HowManyNet#anon$4] - I[HowManyNet#anon$4]) <= 1;
  assert {:msg "48.15: Initialization of network 'HowManyNet' might not establish the channel invariant (#13)"} ((C[HowManyNet#anon$4] - I[HowManyNet#anon$4]) > 0) ==> (0 <= M[HowManyNet#anon$4][I[HowManyNet#anon$4]]);
  I := R;
  assert {:msg "Initialization of network 'HowManyNet' might not establish the network invariant: Unread tokens might be left on channel anon$4 (#14)"} (C[HowManyNet#anon$4] - R[HowManyNet#anon$4]) == 0;
  assert {:msg "Initialization of network 'HowManyNet' might not establish the network invariant: Unread tokens might be left on channel anon$5 (#15)"} (C[HowManyNet#anon$5] - R[HowManyNet#anon$5]) == 0;
}
procedure HowManyNet##HowMany#anon$1#5()
  modifies C, R, M, I, H;
{
  var HowManyNet#a: Actor;
  var HowManyNet#anon$4: Chan (int);
  var HowManyNet#anon$5: Chan (bool);
  var AV#a#curr: int;
  var AV#a#amount: int;
  var AV#a#rd_str: int;
  var AV#a#tot_str: int;
  var In#i: int;
  assume 0 <= I[HowManyNet#anon$4];
  assume I[HowManyNet#anon$4] <= R[HowManyNet#anon$4];
  assume R[HowManyNet#anon$4] <= C[HowManyNet#anon$4];
  assume 0 <= I[HowManyNet#anon$5];
  assume I[HowManyNet#anon$5] <= R[HowManyNet#anon$5];
  assume R[HowManyNet#anon$5] <= C[HowManyNet#anon$5];
  assume I[HowManyNet#anon$5] == R[HowManyNet#anon$5];
  assume ((R[HowManyNet#anon$4] - I[HowManyNet#anon$4]) == 0) ==> ((C[HowManyNet#anon$5] - I[HowManyNet#anon$5]) == 0);
  assume ((C[HowManyNet#anon$4] - I[HowManyNet#anon$4]) > 0) ==> ((C[HowManyNet#anon$5] - I[HowManyNet#anon$5]) <= M[HowManyNet#anon$4][I[HowManyNet#anon$4]]);
  assume (C[HowManyNet#anon$4] - I[HowManyNet#anon$4]) <= 1;
  assume ((C[HowManyNet#anon$4] - I[HowManyNet#anon$4]) > 0) ==> (0 <= M[HowManyNet#anon$4][I[HowManyNet#anon$4]]);
  assume M[HowManyNet#anon$4][I[HowManyNet#anon$4]] == 1;
  assume (1 <= (C[HowManyNet#anon$4] - R[HowManyNet#anon$4])) && (AV#a#curr == AV#a#amount);
  In#i := M[HowManyNet#anon$4][R[HowManyNet#anon$4]];
  R[HowManyNet#anon$4] := R[HowManyNet#anon$4] + 1;
  assert {:msg "23.12: Precondition might not hold for instance at 51.5 (#16)"} 0 <= In#i;
  havoc AV#a#rd_str;
  havoc AV#a#tot_str;
  havoc AV#a#amount;
  havoc AV#a#curr;
  assert {:msg "45.15: Action at 21.3 ('anon$1') for actor instance 'a' might not preserve the channel invariant (#17)"} ((R[HowManyNet#anon$4] - I[HowManyNet#anon$4]) == 0) ==> ((C[HowManyNet#anon$5] - I[HowManyNet#anon$5]) == 0);
  assert {:msg "46.15: Action at 21.3 ('anon$1') for actor instance 'a' might not preserve the channel invariant (#18)"} ((C[HowManyNet#anon$4] - I[HowManyNet#anon$4]) > 0) ==> ((C[HowManyNet#anon$5] - I[HowManyNet#anon$5]) <= M[HowManyNet#anon$4][I[HowManyNet#anon$4]]);
  assert {:msg "47.15: Action at 21.3 ('anon$1') for actor instance 'a' might not preserve the channel invariant (#19)"} (C[HowManyNet#anon$4] - I[HowManyNet#anon$4]) <= 1;
  assert {:msg "48.15: Action at 21.3 ('anon$1') for actor instance 'a' might not preserve the channel invariant (#20)"} ((C[HowManyNet#anon$4] - I[HowManyNet#anon$4]) > 0) ==> (0 <= M[HowManyNet#anon$4][I[HowManyNet#anon$4]]);
}
procedure HowManyNet##HowMany#anon$2#6()
  modifies C, R, M, I, H;
{
  var HowManyNet#a: Actor;
  var HowManyNet#anon$4: Chan (int);
  var HowManyNet#anon$5: Chan (bool);
  var AV#a#curr: int;
  var AV#a#amount: int;
  var AV#a#rd_str: int;
  var AV#a#tot_str: int;
  assume 0 <= I[HowManyNet#anon$4];
  assume I[HowManyNet#anon$4] <= R[HowManyNet#anon$4];
  assume R[HowManyNet#anon$4] <= C[HowManyNet#anon$4];
  assume 0 <= I[HowManyNet#anon$5];
  assume I[HowManyNet#anon$5] <= R[HowManyNet#anon$5];
  assume R[HowManyNet#anon$5] <= C[HowManyNet#anon$5];
  assume I[HowManyNet#anon$5] == R[HowManyNet#anon$5];
  assume ((R[HowManyNet#anon$4] - I[HowManyNet#anon$4]) == 0) ==> ((C[HowManyNet#anon$5] - I[HowManyNet#anon$5]) == 0);
  assume ((C[HowManyNet#anon$4] - I[HowManyNet#anon$4]) > 0) ==> ((C[HowManyNet#anon$5] - I[HowManyNet#anon$5]) <= M[HowManyNet#anon$4][I[HowManyNet#anon$4]]);
  assume (C[HowManyNet#anon$4] - I[HowManyNet#anon$4]) <= 1;
  assume ((C[HowManyNet#anon$4] - I[HowManyNet#anon$4]) > 0) ==> (0 <= M[HowManyNet#anon$4][I[HowManyNet#anon$4]]);
  assume M[HowManyNet#anon$4][I[HowManyNet#anon$4]] == 1;
  assume AV#a#curr < AV#a#amount;
  havoc AV#a#curr;
  M[HowManyNet#anon$5][C[HowManyNet#anon$5]] := true;
  C[HowManyNet#anon$5] := C[HowManyNet#anon$5] + 1;
  assert {:msg "45.15: Action at 31.3 ('anon$2') for actor instance 'a' might not preserve the channel invariant (#21)"} ((R[HowManyNet#anon$4] - I[HowManyNet#anon$4]) == 0) ==> ((C[HowManyNet#anon$5] - I[HowManyNet#anon$5]) == 0);
  assert {:msg "46.15: Action at 31.3 ('anon$2') for actor instance 'a' might not preserve the channel invariant (#22)"} ((C[HowManyNet#anon$4] - I[HowManyNet#anon$4]) > 0) ==> ((C[HowManyNet#anon$5] - I[HowManyNet#anon$5]) <= M[HowManyNet#anon$4][I[HowManyNet#anon$4]]);
  assert {:msg "47.15: Action at 31.3 ('anon$2') for actor instance 'a' might not preserve the channel invariant (#23)"} (C[HowManyNet#anon$4] - I[HowManyNet#anon$4]) <= 1;
  assert {:msg "48.15: Action at 31.3 ('anon$2') for actor instance 'a' might not preserve the channel invariant (#24)"} ((C[HowManyNet#anon$4] - I[HowManyNet#anon$4]) > 0) ==> (0 <= M[HowManyNet#anon$4][I[HowManyNet#anon$4]]);
}
procedure HowManyNet#anon$3#input#In#7()
  modifies C, R, M, I, H;
{
  var HowManyNet#a: Actor;
  var HowManyNet#anon$4: Chan (int);
  var HowManyNet#anon$5: Chan (bool);
  var AV#a#curr: int;
  var AV#a#amount: int;
  var AV#a#rd_str: int;
  var AV#a#tot_str: int;
  assume 0 <= I[HowManyNet#anon$4];
  assume I[HowManyNet#anon$4] <= R[HowManyNet#anon$4];
  assume R[HowManyNet#anon$4] <= C[HowManyNet#anon$4];
  assume 0 <= I[HowManyNet#anon$5];
  assume I[HowManyNet#anon$5] <= R[HowManyNet#anon$5];
  assume R[HowManyNet#anon$5] <= C[HowManyNet#anon$5];
  assume I[HowManyNet#anon$5] == R[HowManyNet#anon$5];
  assume (C[HowManyNet#anon$4] - I[HowManyNet#anon$4]) < 1;
  assume ((R[HowManyNet#anon$4] - I[HowManyNet#anon$4]) == 0) ==> ((C[HowManyNet#anon$5] - I[HowManyNet#anon$5]) == 0);
  assume ((C[HowManyNet#anon$4] - I[HowManyNet#anon$4]) > 0) ==> ((C[HowManyNet#anon$5] - I[HowManyNet#anon$5]) <= M[HowManyNet#anon$4][I[HowManyNet#anon$4]]);
  assume (C[HowManyNet#anon$4] - I[HowManyNet#anon$4]) <= 1;
  assume ((C[HowManyNet#anon$4] - I[HowManyNet#anon$4]) > 0) ==> (0 <= M[HowManyNet#anon$4][I[HowManyNet#anon$4]]);
  assume M[HowManyNet#anon$4][I[HowManyNet#anon$4]] == 1;
  C[HowManyNet#anon$4] := C[HowManyNet#anon$4] + 1;
  assume M[HowManyNet#anon$4][I[HowManyNet#anon$4]] == 1;
  assert {:msg "45.15: Channel invariant might be falsified by network input (#25)"} ((R[HowManyNet#anon$4] - I[HowManyNet#anon$4]) == 0) ==> ((C[HowManyNet#anon$5] - I[HowManyNet#anon$5]) == 0);
  assert {:msg "46.15: Channel invariant might be falsified by network input (#26)"} ((C[HowManyNet#anon$4] - I[HowManyNet#anon$4]) > 0) ==> ((C[HowManyNet#anon$5] - I[HowManyNet#anon$5]) <= M[HowManyNet#anon$4][I[HowManyNet#anon$4]]);
  assert {:msg "47.15: Channel invariant might be falsified by network input (#27)"} (C[HowManyNet#anon$4] - I[HowManyNet#anon$4]) <= 1;
  assert {:msg "48.15: Channel invariant might be falsified by network input (#28)"} ((C[HowManyNet#anon$4] - I[HowManyNet#anon$4]) > 0) ==> (0 <= M[HowManyNet#anon$4][I[HowManyNet#anon$4]]);
  assert {:msg "42.14: Channel invariant might be falsified by network input (#29)"} M[HowManyNet#anon$4][I[HowManyNet#anon$4]] == 1;
}
procedure HowManyNet#anon$3#exit#8()
  modifies C, R, M, I, H;
{
  var HowManyNet#a: Actor;
  var HowManyNet#anon$4: Chan (int);
  var HowManyNet#anon$5: Chan (bool);
  var AV#a#curr: int;
  var AV#a#amount: int;
  var AV#a#rd_str: int;
  var AV#a#tot_str: int;
  assume 0 <= I[HowManyNet#anon$4];
  assume I[HowManyNet#anon$4] <= R[HowManyNet#anon$4];
  assume R[HowManyNet#anon$4] <= C[HowManyNet#anon$4];
  assume 0 <= I[HowManyNet#anon$5];
  assume I[HowManyNet#anon$5] <= R[HowManyNet#anon$5];
  assume R[HowManyNet#anon$5] <= C[HowManyNet#anon$5];
  assume I[HowManyNet#anon$5] == R[HowManyNet#anon$5];
  assume ((R[HowManyNet#anon$4] - I[HowManyNet#anon$4]) == 0) ==> ((C[HowManyNet#anon$5] - I[HowManyNet#anon$5]) == 0);
  assume ((C[HowManyNet#anon$4] - I[HowManyNet#anon$4]) > 0) ==> ((C[HowManyNet#anon$5] - I[HowManyNet#anon$5]) <= M[HowManyNet#anon$4][I[HowManyNet#anon$4]]);
  assume (C[HowManyNet#anon$4] - I[HowManyNet#anon$4]) <= 1;
  assume ((C[HowManyNet#anon$4] - I[HowManyNet#anon$4]) > 0) ==> (0 <= M[HowManyNet#anon$4][I[HowManyNet#anon$4]]);
  assume M[HowManyNet#anon$4][I[HowManyNet#anon$4]] == 1;
  assume (C[HowManyNet#anon$4] - I[HowManyNet#anon$4]) == 1;
  assume M[HowManyNet#anon$4][I[HowManyNet#anon$4]] == 1;
  assume !((1 <= (C[HowManyNet#anon$4] - R[HowManyNet#anon$4])) && (AV#a#curr == AV#a#amount));
  assume !(AV#a#curr < AV#a#amount);
  R[HowManyNet#anon$5] := R[HowManyNet#anon$5] + 1;
  I := R;
  assert {:msg "45.15: The network might not preserve the channel invariant (#30)"} ((R[HowManyNet#anon$4] - I[HowManyNet#anon$4]) == 0) ==> ((C[HowManyNet#anon$5] - I[HowManyNet#anon$5]) == 0);
  assert {:msg "46.15: The network might not preserve the channel invariant (#31)"} ((C[HowManyNet#anon$4] - I[HowManyNet#anon$4]) > 0) ==> ((C[HowManyNet#anon$5] - I[HowManyNet#anon$5]) <= M[HowManyNet#anon$4][I[HowManyNet#anon$4]]);
  assert {:msg "47.15: The network might not preserve the channel invariant (#32)"} (C[HowManyNet#anon$4] - I[HowManyNet#anon$4]) <= 1;
  assert {:msg "48.15: The network might not preserve the channel invariant (#33)"} ((C[HowManyNet#anon$4] - I[HowManyNet#anon$4]) > 0) ==> (0 <= M[HowManyNet#anon$4][I[HowManyNet#anon$4]]);
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel anon$4 (#34)"} (C[HowManyNet#anon$4] - R[HowManyNet#anon$4]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel anon$5 (#35)"} (C[HowManyNet#anon$5] - R[HowManyNet#anon$5]) == 0;
}

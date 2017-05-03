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
var B: CType;
var I#sub: CType;

var H: HType;

const unique this#: Actor;

function AT#Min(x:int, y: int): int { if x <= y then x else y }

// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

procedure Sum#init#0()
  modifies C, R, M, I, H, I#sub;
{
  var x: Chan (int);
  var y: Chan (int);
  var Ch#sum: Chan (int);
  var sum: int;
  assume x != y;
  assume (I[x] == 0) && (R[x] == 0) && (C[x] == 0);
  assume (I[y] == 0) && (R[y] == 0) && (C[y] == 0);
  assume (R[Ch#sum] == 0) && (C[Ch#sum] == 0);
  sum := 0;
  assert {:msg "Sum_ContractAction.actor(11.13): Initialization might not establish the invariant (#0)"} R[x] == C[y];
  assert {:msg "Sum_ContractAction.actor(12.13): Initialization might not establish the invariant (#1)"} I[x] == I[y];
  assert {:msg "Sum_ContractAction.actor(13.13): Initialization might not establish the invariant (#2)"} (R[x] == 0) ==> (sum == 0);
  assert {:msg "Sum_ContractAction.actor(14.13): Initialization might not establish the invariant (#3)"} (C[y] > 0) ==> (sum == M[y][C[y] - 1]);
  assert {:msg "Sum_ContractAction.actor(15.13): Initialization might not establish the invariant (#4)"} (C[y] > 0) ==> (M[y][0] == M[x][0]);
  assert {:msg "Sum_ContractAction.actor(16.14): Initialization might not establish the invariant (#5)"} (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[y] - 0)) ==> (M[y][i] == (M[y][i - 1] + M[x][i]))
  );
}
procedure Sum#anon$2#1()
  modifies C, R, M, I, H, I#sub;
{
  var x: Chan (int);
  var y: Chan (int);
  var Ch#sum: Chan (int);
  var sum: int;
  var x#0: int;
  assume x != y;
  assume (0 <= I[x]) && (I[x] <= R[x]) && (R[x] <= C[x]);
  assume (0 <= I[y]) && (I[y] <= R[y]) && (R[y] <= C[y]);
  assume (0 <= R[Ch#sum]) && (C[Ch#sum] == (R[Ch#sum] + 1));
  assume R[x] == C[y];
  assume I[x] == I[y];
  assume (R[x] == 0) ==> (sum == 0);
  assume (C[y] > 0) ==> (sum == M[y][C[y] - 1]);
  assume (C[y] > 0) ==> (M[y][0] == M[x][0]);
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[y] - 0)) ==> (M[y][i] == (M[y][i - 1] + M[x][i]))
  );
  assume R[x] == C[y];
  x#0 := M[x][R[x]];
  R[x] := R[x] + 1;
  sum := sum + x#0;
  M[y][C[y]] := sum;
  C[y] := C[y] + 1;
  assert {:msg "Sum_ContractAction.actor(11.13): Action at Sum_ContractAction.actor(23.3) might not preserve invariant (#6)"} R[x] == C[y];
  assert {:msg "Sum_ContractAction.actor(12.13): Action at Sum_ContractAction.actor(23.3) might not preserve invariant (#7)"} I[x] == I[y];
  assert {:msg "Sum_ContractAction.actor(13.13): Action at Sum_ContractAction.actor(23.3) might not preserve invariant (#8)"} (R[x] == 0) ==> (sum == 0);
  assert {:msg "Sum_ContractAction.actor(14.13): Action at Sum_ContractAction.actor(23.3) might not preserve invariant (#9)"} (C[y] > 0) ==> (sum == M[y][C[y] - 1]);
  assert {:msg "Sum_ContractAction.actor(15.13): Action at Sum_ContractAction.actor(23.3) might not preserve invariant (#10)"} (C[y] > 0) ==> (M[y][0] == M[x][0]);
  assert {:msg "Sum_ContractAction.actor(16.14): Action at Sum_ContractAction.actor(23.3) might not preserve invariant (#11)"} (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[y] - 0)) ==> (M[y][i] == (M[y][i - 1] + M[x][i]))
  );
}
procedure Sum#contract#anon$0#2()
  modifies C, R, M, I, H, I#sub;
{
  var x: Chan (int);
  var y: Chan (int);
  var Ch#sum: Chan (int);
  var sum: int;
  assume x != y;
  assume (0 <= I[x]) && (I[x] <= R[x]) && (R[x] <= C[x]);
  assume (0 <= I[y]) && (I[y] <= R[y]) && (R[y] <= C[y]);
  assume (0 <= R[Ch#sum]) && (C[Ch#sum] == (R[Ch#sum] + 1));
  assume R[y] == I[y];
  assume R[x] == C[y];
  assume I[x] == I[y];
  assume (R[x] == 0) ==> (sum == 0);
  assume (C[y] > 0) ==> (sum == M[y][C[y] - 1]);
  assume (C[y] > 0) ==> (M[y][0] == M[x][0]);
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[y] - 0)) ==> (M[y][i] == (M[y][i - 1] + M[x][i]))
  );
  assume R[x] == C[y];
  assume (C[x] - I[x]) == 1;
  assume 0 <= M[x][I[x]];
  assume !(true && (1 <= (C[x] - R[x])) && true);
  assert {:msg "Sum_ContractAction.actor(5.3): The correct number of tokens might not be produced on output 'y' (#12)"} (C[y] - I[y]) == 1;
  assert {:msg "Sum_ContractAction.actor(7.13): Contract action postcondition might not hold (#13)"} M[y][0] == M[x][0];
  assert {:msg "Sum_ContractAction.actor(8.13): Contract action postcondition might not hold (#14)"} (0 < I[y]) ==> (M[y][I[y]] == (M[y][I[y] - 1] + M[x][I[x]]));
  R[y] := R[y] + 1;
  I := R;
  assert {:msg "Sum_ContractAction.actor(11.13): The actor might not preserve the channel invariant (#15)"} R[x] == C[y];
  assert {:msg "Sum_ContractAction.actor(12.13): The actor might not preserve the channel invariant (#16)"} I[x] == I[y];
  assert {:msg "Sum_ContractAction.actor(13.13): The actor might not preserve the channel invariant (#17)"} (R[x] == 0) ==> (sum == 0);
  assert {:msg "Sum_ContractAction.actor(14.13): The actor might not preserve the channel invariant (#18)"} (C[y] > 0) ==> (sum == M[y][C[y] - 1]);
  assert {:msg "Sum_ContractAction.actor(15.13): The actor might not preserve the channel invariant (#19)"} (C[y] > 0) ==> (M[y][0] == M[x][0]);
  assert {:msg "Sum_ContractAction.actor(16.14): The actor might not preserve the channel invariant (#20)"} (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[y] - 0)) ==> (M[y][i] == (M[y][i - 1] + M[x][i]))
  );
}
procedure Add2#init#3()
  modifies C, R, M, I, H, I#sub;
{
  var x: Chan (int);
  var y: Chan (int);
  var Ch#t1: Chan (int);
  var Ch#t2: Chan (int);
  var Ch#step: Chan (int);
  var t1: int;
  var t2: int;
  var step: int;
  assume x != y;
  assume (I[x] == 0) && (R[x] == 0) && (C[x] == 0);
  assume (I[y] == 0) && (R[y] == 0) && (C[y] == 0);
  assume (R[Ch#t1] == 0) && (C[Ch#t1] == 0);
  assume (R[Ch#t2] == 0) && (C[Ch#t2] == 0);
  assume (R[Ch#step] == 0) && (C[Ch#step] == 0);
  step := 0;
  assert {:msg "Sum_ContractAction.actor(41.13): Initialization might not establish the invariant (#21)"} (0 <= step) && (step <= 2);
  assert {:msg "Sum_ContractAction.actor(42.13): Initialization might not establish the invariant (#22)"} (2 * (C[y] - I[y])) == ((R[x] - I[x]) - step);
  assert {:msg "Sum_ContractAction.actor(44.13): Initialization might not establish the invariant (#23)"} (step == 1) ==> (t1 == M[x][R[x] - 1]);
  assert {:msg "Sum_ContractAction.actor(45.13): Initialization might not establish the invariant (#24)"} (step == 2) ==> (t1 == M[x][(R[x] - 1) - 1]) && (t2 == M[x][R[x] - 1]);
  assert {:msg "Sum_ContractAction.actor(46.13): Initialization might not establish the invariant (#25)"} (step == 0) && (C[y] > 0) ==> (M[y][C[y] - 1] == (M[x][(R[x] - 1) - 1] + M[x][R[x] - 1]));
}
procedure Add2#anon$5#4()
  modifies C, R, M, I, H, I#sub;
{
  var x: Chan (int);
  var y: Chan (int);
  var Ch#t1: Chan (int);
  var Ch#t2: Chan (int);
  var Ch#step: Chan (int);
  var t1: int;
  var t2: int;
  var step: int;
  var x#0: int;
  assume x != y;
  assume (0 <= I[x]) && (I[x] <= R[x]) && (R[x] <= C[x]);
  assume (0 <= I[y]) && (I[y] <= R[y]) && (R[y] <= C[y]);
  assume (0 <= R[Ch#t1]) && (C[Ch#t1] == (R[Ch#t1] + 1));
  assume (0 <= R[Ch#t2]) && (C[Ch#t2] == (R[Ch#t2] + 1));
  assume (0 <= R[Ch#step]) && (C[Ch#step] == (R[Ch#step] + 1));
  assume (0 <= step) && (step <= 2);
  assume (2 * (C[y] - I[y])) == ((R[x] - I[x]) - step);
  assume (step == 1) ==> (t1 == M[x][R[x] - 1]);
  assume (step == 2) ==> (t1 == M[x][(R[x] - 1) - 1]) && (t2 == M[x][R[x] - 1]);
  assume (step == 0) && (C[y] > 0) ==> (M[y][C[y] - 1] == (M[x][(R[x] - 1) - 1] + M[x][R[x] - 1]));
  x#0 := M[x][R[x]];
  R[x] := R[x] + 1;
  assume step == 0;
  t1 := x#0;
  step := 1;
  assert {:msg "Sum_ContractAction.actor(41.13): Action at Sum_ContractAction.actor(50.3) might not preserve invariant (#26)"} (0 <= step) && (step <= 2);
  assert {:msg "Sum_ContractAction.actor(42.13): Action at Sum_ContractAction.actor(50.3) might not preserve invariant (#27)"} (2 * (C[y] - I[y])) == ((R[x] - I[x]) - step);
  assert {:msg "Sum_ContractAction.actor(44.13): Action at Sum_ContractAction.actor(50.3) might not preserve invariant (#28)"} (step == 1) ==> (t1 == M[x][R[x] - 1]);
  assert {:msg "Sum_ContractAction.actor(45.13): Action at Sum_ContractAction.actor(50.3) might not preserve invariant (#29)"} (step == 2) ==> (t1 == M[x][(R[x] - 1) - 1]) && (t2 == M[x][R[x] - 1]);
  assert {:msg "Sum_ContractAction.actor(46.13): Action at Sum_ContractAction.actor(50.3) might not preserve invariant (#30)"} (step == 0) && (C[y] > 0) ==> (M[y][C[y] - 1] == (M[x][(R[x] - 1) - 1] + M[x][R[x] - 1]));
}
procedure Add2#anon$6#5()
  modifies C, R, M, I, H, I#sub;
{
  var x: Chan (int);
  var y: Chan (int);
  var Ch#t1: Chan (int);
  var Ch#t2: Chan (int);
  var Ch#step: Chan (int);
  var t1: int;
  var t2: int;
  var step: int;
  var x#0: int;
  assume x != y;
  assume (0 <= I[x]) && (I[x] <= R[x]) && (R[x] <= C[x]);
  assume (0 <= I[y]) && (I[y] <= R[y]) && (R[y] <= C[y]);
  assume (0 <= R[Ch#t1]) && (C[Ch#t1] == (R[Ch#t1] + 1));
  assume (0 <= R[Ch#t2]) && (C[Ch#t2] == (R[Ch#t2] + 1));
  assume (0 <= R[Ch#step]) && (C[Ch#step] == (R[Ch#step] + 1));
  assume (0 <= step) && (step <= 2);
  assume (2 * (C[y] - I[y])) == ((R[x] - I[x]) - step);
  assume (step == 1) ==> (t1 == M[x][R[x] - 1]);
  assume (step == 2) ==> (t1 == M[x][(R[x] - 1) - 1]) && (t2 == M[x][R[x] - 1]);
  assume (step == 0) && (C[y] > 0) ==> (M[y][C[y] - 1] == (M[x][(R[x] - 1) - 1] + M[x][R[x] - 1]));
  x#0 := M[x][R[x]];
  R[x] := R[x] + 1;
  assume step == 1;
  t2 := x#0;
  step := 2;
  assert {:msg "Sum_ContractAction.actor(41.13): Action at Sum_ContractAction.actor(57.3) might not preserve invariant (#31)"} (0 <= step) && (step <= 2);
  assert {:msg "Sum_ContractAction.actor(42.13): Action at Sum_ContractAction.actor(57.3) might not preserve invariant (#32)"} (2 * (C[y] - I[y])) == ((R[x] - I[x]) - step);
  assert {:msg "Sum_ContractAction.actor(44.13): Action at Sum_ContractAction.actor(57.3) might not preserve invariant (#33)"} (step == 1) ==> (t1 == M[x][R[x] - 1]);
  assert {:msg "Sum_ContractAction.actor(45.13): Action at Sum_ContractAction.actor(57.3) might not preserve invariant (#34)"} (step == 2) ==> (t1 == M[x][(R[x] - 1) - 1]) && (t2 == M[x][R[x] - 1]);
  assert {:msg "Sum_ContractAction.actor(46.13): Action at Sum_ContractAction.actor(57.3) might not preserve invariant (#35)"} (step == 0) && (C[y] > 0) ==> (M[y][C[y] - 1] == (M[x][(R[x] - 1) - 1] + M[x][R[x] - 1]));
}
procedure Add2#anon$7#6()
  modifies C, R, M, I, H, I#sub;
{
  var x: Chan (int);
  var y: Chan (int);
  var Ch#t1: Chan (int);
  var Ch#t2: Chan (int);
  var Ch#step: Chan (int);
  var t1: int;
  var t2: int;
  var step: int;
  var x#0: int;
  assume x != y;
  assume (0 <= I[x]) && (I[x] <= R[x]) && (R[x] <= C[x]);
  assume (0 <= I[y]) && (I[y] <= R[y]) && (R[y] <= C[y]);
  assume (0 <= R[Ch#t1]) && (C[Ch#t1] == (R[Ch#t1] + 1));
  assume (0 <= R[Ch#t2]) && (C[Ch#t2] == (R[Ch#t2] + 1));
  assume (0 <= R[Ch#step]) && (C[Ch#step] == (R[Ch#step] + 1));
  assume (0 <= step) && (step <= 2);
  assume (2 * (C[y] - I[y])) == ((R[x] - I[x]) - step);
  assume (step == 1) ==> (t1 == M[x][R[x] - 1]);
  assume (step == 2) ==> (t1 == M[x][(R[x] - 1) - 1]) && (t2 == M[x][R[x] - 1]);
  assume (step == 0) && (C[y] > 0) ==> (M[y][C[y] - 1] == (M[x][(R[x] - 1) - 1] + M[x][R[x] - 1]));
  assume step == 2;
  step := 0;
  M[y][C[y]] := t1 + t2;
  C[y] := C[y] + 1;
  assert {:msg "Sum_ContractAction.actor(41.13): Action at Sum_ContractAction.actor(64.3) might not preserve invariant (#36)"} (0 <= step) && (step <= 2);
  assert {:msg "Sum_ContractAction.actor(42.13): Action at Sum_ContractAction.actor(64.3) might not preserve invariant (#37)"} (2 * (C[y] - I[y])) == ((R[x] - I[x]) - step);
  assert {:msg "Sum_ContractAction.actor(44.13): Action at Sum_ContractAction.actor(64.3) might not preserve invariant (#38)"} (step == 1) ==> (t1 == M[x][R[x] - 1]);
  assert {:msg "Sum_ContractAction.actor(45.13): Action at Sum_ContractAction.actor(64.3) might not preserve invariant (#39)"} (step == 2) ==> (t1 == M[x][(R[x] - 1) - 1]) && (t2 == M[x][R[x] - 1]);
  assert {:msg "Sum_ContractAction.actor(46.13): Action at Sum_ContractAction.actor(64.3) might not preserve invariant (#40)"} (step == 0) && (C[y] > 0) ==> (M[y][C[y] - 1] == (M[x][(R[x] - 1) - 1] + M[x][R[x] - 1]));
}
procedure Add2##GuardWD#7()
  modifies C, R, M, I, H, I#sub;
{
  var x: Chan (int);
  var y: Chan (int);
  var Ch#t1: Chan (int);
  var Ch#t2: Chan (int);
  var Ch#step: Chan (int);
  var t1: int;
  var t2: int;
  var step: int;
  var x#0: int;
  assume x != y;
  assume (0 <= step) && (step <= 2);
  assume (2 * (C[y] - I[y])) == ((R[x] - I[x]) - step);
  assume (step == 1) ==> (t1 == M[x][R[x] - 1]);
  assume (step == 2) ==> (t1 == M[x][(R[x] - 1) - 1]) && (t2 == M[x][R[x] - 1]);
  assume (step == 0) && (C[y] > 0) ==> (M[y][C[y] - 1] == (M[x][(R[x] - 1) - 1] + M[x][R[x] - 1]));
  assert {:msg "Sum_ContractAction.actor(31.1): The actions 'anon$5' and 'anon$6' of actor 'Add2' might not have mutually exclusive guards (#41)"} !(true && (1 <= (C[x] - R[x])) && (step == 0) && true && (1 <= (C[x] - R[x])) && (step == 1));
  assert {:msg "Sum_ContractAction.actor(31.1): The actions 'anon$5' and 'anon$7' of actor 'Add2' might not have mutually exclusive guards (#42)"} !(true && (1 <= (C[x] - R[x])) && (step == 0) && true && true && (step == 2));
  assert {:msg "Sum_ContractAction.actor(31.1): The actions 'anon$6' and 'anon$7' of actor 'Add2' might not have mutually exclusive guards (#43)"} !(true && (1 <= (C[x] - R[x])) && (step == 1) && true && true && (step == 2));
}
procedure Add2#contract#anon$3#8()
  modifies C, R, M, I, H, I#sub;
{
  var x: Chan (int);
  var y: Chan (int);
  var Ch#t1: Chan (int);
  var Ch#t2: Chan (int);
  var Ch#step: Chan (int);
  var t1: int;
  var t2: int;
  var step: int;
  assume x != y;
  assume (0 <= I[x]) && (I[x] <= R[x]) && (R[x] <= C[x]);
  assume (0 <= I[y]) && (I[y] <= R[y]) && (R[y] <= C[y]);
  assume (0 <= R[Ch#t1]) && (C[Ch#t1] == (R[Ch#t1] + 1));
  assume (0 <= R[Ch#t2]) && (C[Ch#t2] == (R[Ch#t2] + 1));
  assume (0 <= R[Ch#step]) && (C[Ch#step] == (R[Ch#step] + 1));
  assume R[y] == I[y];
  assume (0 <= step) && (step <= 2);
  assume (2 * (C[y] - I[y])) == ((R[x] - I[x]) - step);
  assume (step == 1) ==> (t1 == M[x][R[x] - 1]);
  assume (step == 2) ==> (t1 == M[x][(R[x] - 1) - 1]) && (t2 == M[x][R[x] - 1]);
  assume (step == 0) && (C[y] > 0) ==> (M[y][C[y] - 1] == (M[x][(R[x] - 1) - 1] + M[x][R[x] - 1]));
  assume (C[x] - I[x]) == 2;
  assume !(true && (1 <= (C[x] - R[x])) && (step == 0));
  assume !(true && (1 <= (C[x] - R[x])) && (step == 1));
  assume !(true && true && (step == 2));
  assert {:msg "Sum_ContractAction.actor(37.3): The correct number of tokens might not be produced on output 'y' (#44)"} (C[y] - I[y]) == 1;
  assert {:msg "Sum_ContractAction.actor(38.13): Contract action postcondition might not hold (#45)"} M[y][I[y]] == (M[x][I[x]] + M[x][I[x] + 1]);
  R[y] := R[y] + 1;
  I := R;
  assert {:msg "Sum_ContractAction.actor(41.13): The actor might not preserve the channel invariant (#46)"} (0 <= step) && (step <= 2);
  assert {:msg "Sum_ContractAction.actor(42.13): The actor might not preserve the channel invariant (#47)"} (2 * (C[y] - I[y])) == ((R[x] - I[x]) - step);
  assert {:msg "Sum_ContractAction.actor(44.13): The actor might not preserve the channel invariant (#48)"} (step == 1) ==> (t1 == M[x][R[x] - 1]);
  assert {:msg "Sum_ContractAction.actor(45.13): The actor might not preserve the channel invariant (#49)"} (step == 2) ==> (t1 == M[x][(R[x] - 1) - 1]) && (t2 == M[x][R[x] - 1]);
  assert {:msg "Sum_ContractAction.actor(46.13): The actor might not preserve the channel invariant (#50)"} (step == 0) && (C[y] > 0) ==> (M[y][C[y] - 1] == (M[x][(R[x] - 1) - 1] + M[x][R[x] - 1]));
}

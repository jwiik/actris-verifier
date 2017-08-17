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
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

procedure Sum#init#0()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var x: Chan (int);
  var y: Chan (int);
  var Ch#sum: Chan (int);
  var anon__0: int;
  var sum: int;
  assume x != y;
  assume anon__0 == 0;
  assume Mode#[this#] == anon__0;
  assume (I#[x] == 0) && (R#[x] == 0) && (C#[x] == 0);
  assume (I#[y] == 0) && (R#[y] == 0) && (C#[y] == 0);
  sum := 0;
  assert {:msg "Sum_ContractAction.actor(11.13): Initialization might not establish the invariant (#0)"} R#[x] == C#[y];
  assert {:msg "Sum_ContractAction.actor(12.13): Initialization might not establish the invariant (#1)"} I#[x] == I#[y];
  assert {:msg "Sum_ContractAction.actor(13.13): Initialization might not establish the invariant (#2)"} (R#[x] == 0) ==> (sum == 0);
  assert {:msg "Sum_ContractAction.actor(14.13): Initialization might not establish the invariant (#3)"} (C#[y] > 0) ==> (sum == M#[y][C#[y] - 1]);
  assert {:msg "Sum_ContractAction.actor(15.13): Initialization might not establish the invariant (#4)"} (C#[y] > 0) ==> (M#[y][0] == M#[x][0]);
  assert {:msg "Sum_ContractAction.actor(16.14): Initialization might not establish the invariant (#5)"} (forall i: int :: 
    ((0 + 1) <= i) && (i < (C#[y] - 0)) ==> (M#[y][i] == (M#[y][i - 1] + M#[x][i]))
  );
  assert {:msg "Initialization might not establish the invariant (#6)"} R#[x] == C#[y];
  assert {:msg "Initialization might not establish the invariant (#7)"} (Mode#[this#] == anon__0) ==> (((C#[x] - I#[x]) >= 1) ==> (0 <= M#[x][I#[x]]));
  assert {:msg "Initialization might not establish the invariant (#8)"} (Mode#[this#] == anon__0) ==> ((C#[x] - I#[x]) <= 1);
}
procedure Sum#anon__35#1()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var x: Chan (int);
  var y: Chan (int);
  var Ch#sum: Chan (int);
  var anon__0: int;
  var sum: int;
  var x#0: int;
  assume x != y;
  assume anon__0 == 0;
  assume Mode#[this#] == anon__0;
  assume (0 <= I#[x]) && (I#[x] <= R#[x]) && (R#[x] <= C#[x]);
  assume (0 <= I#[y]) && (I#[y] <= R#[y]) && (R#[y] <= C#[y]);
  assume R#[x] == C#[y];
  assume I#[x] == I#[y];
  assume (R#[x] == 0) ==> (sum == 0);
  assume (C#[y] > 0) ==> (sum == M#[y][C#[y] - 1]);
  assume (C#[y] > 0) ==> (M#[y][0] == M#[x][0]);
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C#[y] - 0)) ==> (M#[y][i] == (M#[y][i - 1] + M#[x][i]))
  );
  assume R#[x] == C#[y];
  assume (Mode#[this#] == anon__0) ==> (((C#[x] - I#[x]) >= 1) ==> (0 <= M#[x][I#[x]]));
  assume (Mode#[this#] == anon__0) ==> ((C#[x] - I#[x]) <= 1);
  assume 1 <= (C#[x] - R#[x]);
  x#0 := M#[x][R#[x]];
  R#[x] := R#[x] + 1;
  assume true;
  sum := sum + x#0;
  M#[y][C#[y]] := sum;
  C#[y] := C#[y] + 1;
  assert {:msg "Sum_ContractAction.actor(11.13): Action 'anon__35' at <unknown_file>(-1.-1) might not preserve the invariant (#9)"} R#[x] == C#[y];
  assert {:msg "Sum_ContractAction.actor(12.13): Action 'anon__35' at <unknown_file>(-1.-1) might not preserve the invariant (#10)"} I#[x] == I#[y];
  assert {:msg "Sum_ContractAction.actor(13.13): Action 'anon__35' at <unknown_file>(-1.-1) might not preserve the invariant (#11)"} (R#[x] == 0) ==> (sum == 0);
  assert {:msg "Sum_ContractAction.actor(14.13): Action 'anon__35' at <unknown_file>(-1.-1) might not preserve the invariant (#12)"} (C#[y] > 0) ==> (sum == M#[y][C#[y] - 1]);
  assert {:msg "Sum_ContractAction.actor(15.13): Action 'anon__35' at <unknown_file>(-1.-1) might not preserve the invariant (#13)"} (C#[y] > 0) ==> (M#[y][0] == M#[x][0]);
  assert {:msg "Sum_ContractAction.actor(16.14): Action 'anon__35' at <unknown_file>(-1.-1) might not preserve the invariant (#14)"} (forall i: int :: 
    ((0 + 1) <= i) && (i < (C#[y] - 0)) ==> (M#[y][i] == (M#[y][i - 1] + M#[x][i]))
  );
  assert {:msg "Action 'anon__35' at <unknown_file>(-1.-1) might not preserve the invariant (#15)"} R#[x] == C#[y];
  assert {:msg "Action 'anon__35' at <unknown_file>(-1.-1) might not preserve the invariant (#16)"} (Mode#[this#] == anon__0) ==> (((C#[x] - I#[x]) >= 1) ==> (0 <= M#[x][I#[x]]));
  assert {:msg "Action 'anon__35' at <unknown_file>(-1.-1) might not preserve the invariant (#17)"} (Mode#[this#] == anon__0) ==> ((C#[x] - I#[x]) <= 1);
}
procedure Sum#contract#anon__0#input#2()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var x: Chan (int);
  var y: Chan (int);
  var Ch#sum: Chan (int);
  var anon__0: int;
  var sum: int;
  assume x != y;
  assume anon__0 == 0;
  assume Mode#[this#] == anon__0;
  assume (0 <= I#[x]) && (I#[x] <= R#[x]) && (R#[x] <= C#[x]);
  assume (0 <= I#[y]) && (I#[y] <= R#[y]) && (R#[y] <= C#[y]);
  assume Mode#[this#] == anon__0;
  assume R#[y] == I#[y];
  assume R#[x] == C#[y];
  assume I#[x] == I#[y];
  assume (R#[x] == 0) ==> (sum == 0);
  assume (C#[y] > 0) ==> (sum == M#[y][C#[y] - 1]);
  assume (C#[y] > 0) ==> (M#[y][0] == M#[x][0]);
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C#[y] - 0)) ==> (M#[y][i] == (M#[y][i - 1] + M#[x][i]))
  );
  assume R#[x] == C#[y];
  assume (Mode#[this#] == anon__0) ==> (((C#[x] - I#[x]) >= 1) ==> (0 <= M#[x][I#[x]]));
  assume (Mode#[this#] == anon__0) ==> ((C#[x] - I#[x]) <= 1);
  assume (C#[x] - I#[x]) < 1;
  C#[x] := C#[x] + 1;
  assume 0 <= M#[x][I#[x]];
  assert {:msg "Sum_ContractAction.actor(11.13): Invariant might be falsified by actor input (#18)"} R#[x] == C#[y];
  assert {:msg "Sum_ContractAction.actor(12.13): Invariant might be falsified by actor input (#19)"} I#[x] == I#[y];
  assert {:msg "Sum_ContractAction.actor(13.13): Invariant might be falsified by actor input (#20)"} (R#[x] == 0) ==> (sum == 0);
  assert {:msg "Sum_ContractAction.actor(14.13): Invariant might be falsified by actor input (#21)"} (C#[y] > 0) ==> (sum == M#[y][C#[y] - 1]);
  assert {:msg "Sum_ContractAction.actor(15.13): Invariant might be falsified by actor input (#22)"} (C#[y] > 0) ==> (M#[y][0] == M#[x][0]);
  assert {:msg "Sum_ContractAction.actor(16.14): Invariant might be falsified by actor input (#23)"} (forall i: int :: 
    ((0 + 1) <= i) && (i < (C#[y] - 0)) ==> (M#[y][i] == (M#[y][i - 1] + M#[x][i]))
  );
  assert {:msg "Invariant might be falsified by actor input (#24)"} R#[x] == C#[y];
  assert {:msg "Invariant might be falsified by actor input (#25)"} (Mode#[this#] == anon__0) ==> (((C#[x] - I#[x]) >= 1) ==> (0 <= M#[x][I#[x]]));
  assert {:msg "Invariant might be falsified by actor input (#26)"} (Mode#[this#] == anon__0) ==> ((C#[x] - I#[x]) <= 1);
}
procedure Sum#contract#anon__0#exit#3()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var x: Chan (int);
  var y: Chan (int);
  var Ch#sum: Chan (int);
  var anon__0: int;
  var sum: int;
  assume x != y;
  assume anon__0 == 0;
  assume Mode#[this#] == anon__0;
  assume (0 <= I#[x]) && (I#[x] <= R#[x]) && (R#[x] <= C#[x]);
  assume (0 <= I#[y]) && (I#[y] <= R#[y]) && (R#[y] <= C#[y]);
  assume Mode#[this#] == anon__0;
  assume R#[y] == I#[y];
  assume R#[x] == C#[y];
  assume I#[x] == I#[y];
  assume (R#[x] == 0) ==> (sum == 0);
  assume (C#[y] > 0) ==> (sum == M#[y][C#[y] - 1]);
  assume (C#[y] > 0) ==> (M#[y][0] == M#[x][0]);
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C#[y] - 0)) ==> (M#[y][i] == (M#[y][i - 1] + M#[x][i]))
  );
  assume R#[x] == C#[y];
  assume (Mode#[this#] == anon__0) ==> (((C#[x] - I#[x]) >= 1) ==> (0 <= M#[x][I#[x]]));
  assume (Mode#[this#] == anon__0) ==> ((C#[x] - I#[x]) <= 1);
  assume (C#[x] - I#[x]) == 1;
  assume 0 <= M#[x][I#[x]];
  assume !(true && (1 <= (C#[x] - R#[x])) && true);
  assert {:msg "Sum_ContractAction.actor(5.3): The correct number of tokens might not be produced on output 'y' with contract 'anon__0' (#27)"} (C#[y] - I#[y]) == 1;
  assert {:msg "Contract action postcondition might not hold (#28)"} M#[y][0] == M#[x][0];
  assert {:msg "Contract action postcondition might not hold (#29)"} (0 < I#[y]) ==> (M#[y][I#[y]] == (M#[y][I#[y] - 1] + M#[x][I#[x]]));
  R#[y] := R#[y] + 1;
  I# := R#;
  assert {:msg "Sum_ContractAction.actor(11.13): The actor might not preserve the invariant with contract 'anon__0' at Sum_ContractAction.actor(5.3) (#30)"} R#[x] == C#[y];
  assert {:msg "Sum_ContractAction.actor(12.13): The actor might not preserve the invariant with contract 'anon__0' at Sum_ContractAction.actor(5.3) (#31)"} I#[x] == I#[y];
  assert {:msg "Sum_ContractAction.actor(13.13): The actor might not preserve the invariant with contract 'anon__0' at Sum_ContractAction.actor(5.3) (#32)"} (R#[x] == 0) ==> (sum == 0);
  assert {:msg "Sum_ContractAction.actor(14.13): The actor might not preserve the invariant with contract 'anon__0' at Sum_ContractAction.actor(5.3) (#33)"} (C#[y] > 0) ==> (sum == M#[y][C#[y] - 1]);
  assert {:msg "Sum_ContractAction.actor(15.13): The actor might not preserve the invariant with contract 'anon__0' at Sum_ContractAction.actor(5.3) (#34)"} (C#[y] > 0) ==> (M#[y][0] == M#[x][0]);
  assert {:msg "Sum_ContractAction.actor(16.14): The actor might not preserve the invariant with contract 'anon__0' at Sum_ContractAction.actor(5.3) (#35)"} (forall i: int :: 
    ((0 + 1) <= i) && (i < (C#[y] - 0)) ==> (M#[y][i] == (M#[y][i - 1] + M#[x][i]))
  );
  assert {:msg "The actor might not preserve the invariant with contract 'anon__0' at Sum_ContractAction.actor(5.3) (#36)"} R#[x] == C#[y];
  assert {:msg "The actor might not preserve the invariant with contract 'anon__0' at Sum_ContractAction.actor(5.3) (#37)"} (Mode#[this#] == anon__0) ==> (((C#[x] - I#[x]) >= 1) ==> (0 <= M#[x][I#[x]]));
  assert {:msg "The actor might not preserve the invariant with contract 'anon__0' at Sum_ContractAction.actor(5.3) (#38)"} (Mode#[this#] == anon__0) ==> ((C#[x] - I#[x]) <= 1);
}
procedure Add2#init#4()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var x: Chan (int);
  var y: Chan (int);
  var Ch#t1: Chan (int);
  var Ch#t2: Chan (int);
  var Ch#step: Chan (int);
  var anon__3: int;
  var t1: int;
  var t2: int;
  var step: int;
  assume x != y;
  assume anon__3 == 0;
  assume Mode#[this#] == anon__3;
  assume (I#[x] == 0) && (R#[x] == 0) && (C#[x] == 0);
  assume (I#[y] == 0) && (R#[y] == 0) && (C#[y] == 0);
  step := 0;
  assert {:msg "Sum_ContractAction.actor(41.13): Initialization might not establish the invariant (#39)"} (0 <= step) && (step <= 2);
  assert {:msg "Sum_ContractAction.actor(42.13): Initialization might not establish the invariant (#40)"} (2 * (C#[y] - I#[y])) == ((R#[x] - I#[x]) - step);
  assert {:msg "Sum_ContractAction.actor(44.13): Initialization might not establish the invariant (#41)"} (step == 1) ==> (t1 == M#[x][R#[x] - 1]);
  assert {:msg "Sum_ContractAction.actor(45.13): Initialization might not establish the invariant (#42)"} (step == 2) ==> (t1 == M#[x][(R#[x] - 1) - 1]) && (t2 == M#[x][R#[x] - 1]);
  assert {:msg "Sum_ContractAction.actor(46.13): Initialization might not establish the invariant (#43)"} (step == 0) && (C#[y] > 0) ==> (M#[y][C#[y] - 1] == (M#[x][(R#[x] - 1) - 1] + M#[x][R#[x] - 1]));
  assert {:msg "Initialization might not establish the invariant (#44)"} (Mode#[this#] == anon__3) ==> ((C#[x] - I#[x]) <= 2);
}
procedure Add2#anon__37#5()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var x: Chan (int);
  var y: Chan (int);
  var Ch#t1: Chan (int);
  var Ch#t2: Chan (int);
  var Ch#step: Chan (int);
  var anon__3: int;
  var t1: int;
  var t2: int;
  var step: int;
  var x#0: int;
  assume x != y;
  assume anon__3 == 0;
  assume Mode#[this#] == anon__3;
  assume (0 <= I#[x]) && (I#[x] <= R#[x]) && (R#[x] <= C#[x]);
  assume (0 <= I#[y]) && (I#[y] <= R#[y]) && (R#[y] <= C#[y]);
  assume (0 <= step) && (step <= 2);
  assume (2 * (C#[y] - I#[y])) == ((R#[x] - I#[x]) - step);
  assume (step == 1) ==> (t1 == M#[x][R#[x] - 1]);
  assume (step == 2) ==> (t1 == M#[x][(R#[x] - 1) - 1]) && (t2 == M#[x][R#[x] - 1]);
  assume (step == 0) && (C#[y] > 0) ==> (M#[y][C#[y] - 1] == (M#[x][(R#[x] - 1) - 1] + M#[x][R#[x] - 1]));
  assume (Mode#[this#] == anon__3) ==> ((C#[x] - I#[x]) <= 2);
  assume 1 <= (C#[x] - R#[x]);
  x#0 := M#[x][R#[x]];
  R#[x] := R#[x] + 1;
  assume step == 0;
  t1 := x#0;
  step := 1;
  assert {:msg "Sum_ContractAction.actor(41.13): Action 'anon__37' at <unknown_file>(-1.-1) might not preserve the invariant (#45)"} (0 <= step) && (step <= 2);
  assert {:msg "Sum_ContractAction.actor(42.13): Action 'anon__37' at <unknown_file>(-1.-1) might not preserve the invariant (#46)"} (2 * (C#[y] - I#[y])) == ((R#[x] - I#[x]) - step);
  assert {:msg "Sum_ContractAction.actor(44.13): Action 'anon__37' at <unknown_file>(-1.-1) might not preserve the invariant (#47)"} (step == 1) ==> (t1 == M#[x][R#[x] - 1]);
  assert {:msg "Sum_ContractAction.actor(45.13): Action 'anon__37' at <unknown_file>(-1.-1) might not preserve the invariant (#48)"} (step == 2) ==> (t1 == M#[x][(R#[x] - 1) - 1]) && (t2 == M#[x][R#[x] - 1]);
  assert {:msg "Sum_ContractAction.actor(46.13): Action 'anon__37' at <unknown_file>(-1.-1) might not preserve the invariant (#49)"} (step == 0) && (C#[y] > 0) ==> (M#[y][C#[y] - 1] == (M#[x][(R#[x] - 1) - 1] + M#[x][R#[x] - 1]));
  assert {:msg "Action 'anon__37' at <unknown_file>(-1.-1) might not preserve the invariant (#50)"} (Mode#[this#] == anon__3) ==> ((C#[x] - I#[x]) <= 2);
}
procedure Add2#anon__38#6()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var x: Chan (int);
  var y: Chan (int);
  var Ch#t1: Chan (int);
  var Ch#t2: Chan (int);
  var Ch#step: Chan (int);
  var anon__3: int;
  var t1: int;
  var t2: int;
  var step: int;
  var x#0: int;
  assume x != y;
  assume anon__3 == 0;
  assume Mode#[this#] == anon__3;
  assume (0 <= I#[x]) && (I#[x] <= R#[x]) && (R#[x] <= C#[x]);
  assume (0 <= I#[y]) && (I#[y] <= R#[y]) && (R#[y] <= C#[y]);
  assume (0 <= step) && (step <= 2);
  assume (2 * (C#[y] - I#[y])) == ((R#[x] - I#[x]) - step);
  assume (step == 1) ==> (t1 == M#[x][R#[x] - 1]);
  assume (step == 2) ==> (t1 == M#[x][(R#[x] - 1) - 1]) && (t2 == M#[x][R#[x] - 1]);
  assume (step == 0) && (C#[y] > 0) ==> (M#[y][C#[y] - 1] == (M#[x][(R#[x] - 1) - 1] + M#[x][R#[x] - 1]));
  assume (Mode#[this#] == anon__3) ==> ((C#[x] - I#[x]) <= 2);
  assume 1 <= (C#[x] - R#[x]);
  x#0 := M#[x][R#[x]];
  R#[x] := R#[x] + 1;
  assume step == 1;
  t2 := x#0;
  step := 2;
  assert {:msg "Sum_ContractAction.actor(41.13): Action 'anon__38' at <unknown_file>(-1.-1) might not preserve the invariant (#51)"} (0 <= step) && (step <= 2);
  assert {:msg "Sum_ContractAction.actor(42.13): Action 'anon__38' at <unknown_file>(-1.-1) might not preserve the invariant (#52)"} (2 * (C#[y] - I#[y])) == ((R#[x] - I#[x]) - step);
  assert {:msg "Sum_ContractAction.actor(44.13): Action 'anon__38' at <unknown_file>(-1.-1) might not preserve the invariant (#53)"} (step == 1) ==> (t1 == M#[x][R#[x] - 1]);
  assert {:msg "Sum_ContractAction.actor(45.13): Action 'anon__38' at <unknown_file>(-1.-1) might not preserve the invariant (#54)"} (step == 2) ==> (t1 == M#[x][(R#[x] - 1) - 1]) && (t2 == M#[x][R#[x] - 1]);
  assert {:msg "Sum_ContractAction.actor(46.13): Action 'anon__38' at <unknown_file>(-1.-1) might not preserve the invariant (#55)"} (step == 0) && (C#[y] > 0) ==> (M#[y][C#[y] - 1] == (M#[x][(R#[x] - 1) - 1] + M#[x][R#[x] - 1]));
  assert {:msg "Action 'anon__38' at <unknown_file>(-1.-1) might not preserve the invariant (#56)"} (Mode#[this#] == anon__3) ==> ((C#[x] - I#[x]) <= 2);
}
procedure Add2#anon__39#7()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var x: Chan (int);
  var y: Chan (int);
  var Ch#t1: Chan (int);
  var Ch#t2: Chan (int);
  var Ch#step: Chan (int);
  var anon__3: int;
  var t1: int;
  var t2: int;
  var step: int;
  var x#0: int;
  assume x != y;
  assume anon__3 == 0;
  assume Mode#[this#] == anon__3;
  assume (0 <= I#[x]) && (I#[x] <= R#[x]) && (R#[x] <= C#[x]);
  assume (0 <= I#[y]) && (I#[y] <= R#[y]) && (R#[y] <= C#[y]);
  assume (0 <= step) && (step <= 2);
  assume (2 * (C#[y] - I#[y])) == ((R#[x] - I#[x]) - step);
  assume (step == 1) ==> (t1 == M#[x][R#[x] - 1]);
  assume (step == 2) ==> (t1 == M#[x][(R#[x] - 1) - 1]) && (t2 == M#[x][R#[x] - 1]);
  assume (step == 0) && (C#[y] > 0) ==> (M#[y][C#[y] - 1] == (M#[x][(R#[x] - 1) - 1] + M#[x][R#[x] - 1]));
  assume (Mode#[this#] == anon__3) ==> ((C#[x] - I#[x]) <= 2);
  assume true;
  assume step == 2;
  step := 0;
  M#[y][C#[y]] := t1 + t2;
  C#[y] := C#[y] + 1;
  assert {:msg "Sum_ContractAction.actor(41.13): Action 'anon__39' at <unknown_file>(-1.-1) might not preserve the invariant (#57)"} (0 <= step) && (step <= 2);
  assert {:msg "Sum_ContractAction.actor(42.13): Action 'anon__39' at <unknown_file>(-1.-1) might not preserve the invariant (#58)"} (2 * (C#[y] - I#[y])) == ((R#[x] - I#[x]) - step);
  assert {:msg "Sum_ContractAction.actor(44.13): Action 'anon__39' at <unknown_file>(-1.-1) might not preserve the invariant (#59)"} (step == 1) ==> (t1 == M#[x][R#[x] - 1]);
  assert {:msg "Sum_ContractAction.actor(45.13): Action 'anon__39' at <unknown_file>(-1.-1) might not preserve the invariant (#60)"} (step == 2) ==> (t1 == M#[x][(R#[x] - 1) - 1]) && (t2 == M#[x][R#[x] - 1]);
  assert {:msg "Sum_ContractAction.actor(46.13): Action 'anon__39' at <unknown_file>(-1.-1) might not preserve the invariant (#61)"} (step == 0) && (C#[y] > 0) ==> (M#[y][C#[y] - 1] == (M#[x][(R#[x] - 1) - 1] + M#[x][R#[x] - 1]));
  assert {:msg "Action 'anon__39' at <unknown_file>(-1.-1) might not preserve the invariant (#62)"} (Mode#[this#] == anon__3) ==> ((C#[x] - I#[x]) <= 2);
}
procedure Add2##GuardWD#8()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var x: Chan (int);
  var y: Chan (int);
  var Ch#t1: Chan (int);
  var Ch#t2: Chan (int);
  var Ch#step: Chan (int);
  var anon__3: int;
  var t1: int;
  var t2: int;
  var step: int;
  var x#0: int;
  assume x != y;
  assume anon__3 == 0;
  assume Mode#[this#] == anon__3;
  assume (0 <= I#[x]) && (I#[x] <= R#[x]) && (R#[x] <= C#[x]);
  assume (0 <= I#[y]) && (I#[y] <= R#[y]) && (R#[y] <= C#[y]);
  assume (0 <= step) && (step <= 2);
  assume (2 * (C#[y] - I#[y])) == ((R#[x] - I#[x]) - step);
  assume (step == 1) ==> (t1 == M#[x][R#[x] - 1]);
  assume (step == 2) ==> (t1 == M#[x][(R#[x] - 1) - 1]) && (t2 == M#[x][R#[x] - 1]);
  assume (step == 0) && (C#[y] > 0) ==> (M#[y][C#[y] - 1] == (M#[x][(R#[x] - 1) - 1] + M#[x][R#[x] - 1]));
  assume (Mode#[this#] == anon__3) ==> ((C#[x] - I#[x]) <= 2);
  assert {:msg "The actions 'anon__37' and 'anon__38' of actor 'Add2' might not have mutually exclusive guards (#63)"} !(true && (1 <= (C#[x] - R#[x])) && (step == 0) && true && (1 <= (C#[x] - R#[x])) && (step == 1));
  assert {:msg "The actions 'anon__37' and 'anon__39' of actor 'Add2' might not have mutually exclusive guards (#64)"} !(true && (1 <= (C#[x] - R#[x])) && (step == 0) && true && true && (step == 2));
  assert {:msg "The actions 'anon__38' and 'anon__39' of actor 'Add2' might not have mutually exclusive guards (#65)"} !(true && (1 <= (C#[x] - R#[x])) && (step == 1) && true && true && (step == 2));
}
procedure Add2#contract#anon__3#input#9()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var x: Chan (int);
  var y: Chan (int);
  var Ch#t1: Chan (int);
  var Ch#t2: Chan (int);
  var Ch#step: Chan (int);
  var anon__3: int;
  var t1: int;
  var t2: int;
  var step: int;
  assume x != y;
  assume anon__3 == 0;
  assume Mode#[this#] == anon__3;
  assume (0 <= I#[x]) && (I#[x] <= R#[x]) && (R#[x] <= C#[x]);
  assume (0 <= I#[y]) && (I#[y] <= R#[y]) && (R#[y] <= C#[y]);
  assume Mode#[this#] == anon__3;
  assume R#[y] == I#[y];
  assume (0 <= step) && (step <= 2);
  assume (2 * (C#[y] - I#[y])) == ((R#[x] - I#[x]) - step);
  assume (step == 1) ==> (t1 == M#[x][R#[x] - 1]);
  assume (step == 2) ==> (t1 == M#[x][(R#[x] - 1) - 1]) && (t2 == M#[x][R#[x] - 1]);
  assume (step == 0) && (C#[y] > 0) ==> (M#[y][C#[y] - 1] == (M#[x][(R#[x] - 1) - 1] + M#[x][R#[x] - 1]));
  assume (Mode#[this#] == anon__3) ==> ((C#[x] - I#[x]) <= 2);
  assume (C#[x] - I#[x]) < 2;
  C#[x] := C#[x] + 1;
  assert {:msg "Sum_ContractAction.actor(41.13): Invariant might be falsified by actor input (#66)"} (0 <= step) && (step <= 2);
  assert {:msg "Sum_ContractAction.actor(42.13): Invariant might be falsified by actor input (#67)"} (2 * (C#[y] - I#[y])) == ((R#[x] - I#[x]) - step);
  assert {:msg "Sum_ContractAction.actor(44.13): Invariant might be falsified by actor input (#68)"} (step == 1) ==> (t1 == M#[x][R#[x] - 1]);
  assert {:msg "Sum_ContractAction.actor(45.13): Invariant might be falsified by actor input (#69)"} (step == 2) ==> (t1 == M#[x][(R#[x] - 1) - 1]) && (t2 == M#[x][R#[x] - 1]);
  assert {:msg "Sum_ContractAction.actor(46.13): Invariant might be falsified by actor input (#70)"} (step == 0) && (C#[y] > 0) ==> (M#[y][C#[y] - 1] == (M#[x][(R#[x] - 1) - 1] + M#[x][R#[x] - 1]));
  assert {:msg "Invariant might be falsified by actor input (#71)"} (Mode#[this#] == anon__3) ==> ((C#[x] - I#[x]) <= 2);
}
procedure Add2#contract#anon__3#exit#10()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var x: Chan (int);
  var y: Chan (int);
  var Ch#t1: Chan (int);
  var Ch#t2: Chan (int);
  var Ch#step: Chan (int);
  var anon__3: int;
  var t1: int;
  var t2: int;
  var step: int;
  assume x != y;
  assume anon__3 == 0;
  assume Mode#[this#] == anon__3;
  assume (0 <= I#[x]) && (I#[x] <= R#[x]) && (R#[x] <= C#[x]);
  assume (0 <= I#[y]) && (I#[y] <= R#[y]) && (R#[y] <= C#[y]);
  assume Mode#[this#] == anon__3;
  assume R#[y] == I#[y];
  assume (0 <= step) && (step <= 2);
  assume (2 * (C#[y] - I#[y])) == ((R#[x] - I#[x]) - step);
  assume (step == 1) ==> (t1 == M#[x][R#[x] - 1]);
  assume (step == 2) ==> (t1 == M#[x][(R#[x] - 1) - 1]) && (t2 == M#[x][R#[x] - 1]);
  assume (step == 0) && (C#[y] > 0) ==> (M#[y][C#[y] - 1] == (M#[x][(R#[x] - 1) - 1] + M#[x][R#[x] - 1]));
  assume (Mode#[this#] == anon__3) ==> ((C#[x] - I#[x]) <= 2);
  assume (C#[x] - I#[x]) == 2;
  assume !(true && (1 <= (C#[x] - R#[x])) && (step == 0));
  assume !(true && (1 <= (C#[x] - R#[x])) && (step == 1));
  assume !(true && true && (step == 2));
  assert {:msg "Sum_ContractAction.actor(37.3): The correct number of tokens might not be produced on output 'y' with contract 'anon__3' (#72)"} (C#[y] - I#[y]) == 1;
  assert {:msg "Contract action postcondition might not hold (#73)"} M#[y][I#[y]] == (M#[x][I#[x]] + M#[x][I#[x] + 1]);
  R#[y] := R#[y] + 1;
  I# := R#;
  assert {:msg "Sum_ContractAction.actor(41.13): The actor might not preserve the invariant with contract 'anon__3' at Sum_ContractAction.actor(37.3) (#74)"} (0 <= step) && (step <= 2);
  assert {:msg "Sum_ContractAction.actor(42.13): The actor might not preserve the invariant with contract 'anon__3' at Sum_ContractAction.actor(37.3) (#75)"} (2 * (C#[y] - I#[y])) == ((R#[x] - I#[x]) - step);
  assert {:msg "Sum_ContractAction.actor(44.13): The actor might not preserve the invariant with contract 'anon__3' at Sum_ContractAction.actor(37.3) (#76)"} (step == 1) ==> (t1 == M#[x][R#[x] - 1]);
  assert {:msg "Sum_ContractAction.actor(45.13): The actor might not preserve the invariant with contract 'anon__3' at Sum_ContractAction.actor(37.3) (#77)"} (step == 2) ==> (t1 == M#[x][(R#[x] - 1) - 1]) && (t2 == M#[x][R#[x] - 1]);
  assert {:msg "Sum_ContractAction.actor(46.13): The actor might not preserve the invariant with contract 'anon__3' at Sum_ContractAction.actor(37.3) (#78)"} (step == 0) && (C#[y] > 0) ==> (M#[y][C#[y] - 1] == (M#[x][(R#[x] - 1) - 1] + M#[x][R#[x] - 1]));
  assert {:msg "The actor might not preserve the invariant with contract 'anon__3' at Sum_ContractAction.actor(37.3) (#79)"} (Mode#[this#] == anon__3) ==> ((C#[x] - I#[x]) <= 2);
}
procedure Add2##GuardWD#11()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var x: Chan (int);
  var y: Chan (int);
  var Ch#t1: Chan (int);
  var Ch#t2: Chan (int);
  var Ch#step: Chan (int);
  var anon__3: int;
  var t1: int;
  var t2: int;
  var step: int;
  assume x != y;
  assume anon__3 == 0;
  assume Mode#[this#] == anon__3;
  assume (0 <= I#[x]) && (I#[x] <= R#[x]) && (R#[x] <= C#[x]);
  assume (0 <= I#[y]) && (I#[y] <= R#[y]) && (R#[y] <= C#[y]);
  assume (0 <= step) && (step <= 2);
  assume (2 * (C#[y] - I#[y])) == ((R#[x] - I#[x]) - step);
  assume (step == 1) ==> (t1 == M#[x][R#[x] - 1]);
  assume (step == 2) ==> (t1 == M#[x][(R#[x] - 1) - 1]) && (t2 == M#[x][R#[x] - 1]);
  assume (step == 0) && (C#[y] > 0) ==> (M#[y][C#[y] - 1] == (M#[x][(R#[x] - 1) - 1] + M#[x][R#[x] - 1]));
  assume (Mode#[this#] == anon__3) ==> ((C#[x] - I#[x]) <= 2);
}

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

procedure N#anon__0()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var N#a: Actor;
  var N#anon$2: Chan (int);
  var N#anon$3: Chan (int);
  var anon__0: int;
  var anon__1: int;
  var a#x#i: int;
  assume 0 <= I#[N#anon$2];
  assume I#[N#anon$2] <= R#[N#anon$2];
  assume R#[N#anon$2] <= C#[N#anon$2];
  assume 0 <= I#[N#anon$3];
  assume I#[N#anon$3] <= R#[N#anon$3];
  assume R#[N#anon$3] <= C#[N#anon$3];
  assume I#[N#anon$3] == R#[N#anon$3];
  assume ((B#[N#anon$2] == 1) && (B#[N#anon$3] == 1)) || ((B#[N#anon$2] == 1) && (B#[N#anon$3] == 1));
  assume anon__0 == 0;
  assume anon__1 == 1;
  assume (Mode#[this#] == anon__0) || (Mode#[this#] == anon__1);
  assume R# == I#;
  assume (C#[N#anon$2] - R#[N#anon$2]) == 0;
  assume (C#[N#anon$3] - R#[N#anon$3]) == 0;
  C#[N#anon$2] := C#[N#anon$2] + 1;
  assume 0 <= M#[N#anon$2][I#[N#anon$2]];
  // Instance: a, Action: pos
  assert {:msg "TooGeneralContract.actor(2.3): Firing rule might not be satisfied for action 'pos' of instance 'a' (#0)"} (1 <= (C#[N#anon$2] - R#[N#anon$2])) && (0 <= M#[N#anon$2][R#[N#anon$2]]);
  a#x#i := M#[N#anon$2][R#[N#anon$2]];
  R#[N#anon$2] := R#[N#anon$2] + 1;
  M#[N#anon$3][C#[N#anon$3]] := a#x#i;
  C#[N#anon$3] := C#[N#anon$3] + 1;
}
procedure N#anon__1()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var N#a: Actor;
  var N#anon$2: Chan (int);
  var N#anon$3: Chan (int);
  var anon__0: int;
  var anon__1: int;
  var a#x#i: int;
  assume 0 <= I#[N#anon$2];
  assume I#[N#anon$2] <= R#[N#anon$2];
  assume R#[N#anon$2] <= C#[N#anon$2];
  assume 0 <= I#[N#anon$3];
  assume I#[N#anon$3] <= R#[N#anon$3];
  assume R#[N#anon$3] <= C#[N#anon$3];
  assume I#[N#anon$3] == R#[N#anon$3];
  assume ((B#[N#anon$2] == 1) && (B#[N#anon$3] == 1)) || ((B#[N#anon$2] == 1) && (B#[N#anon$3] == 1));
  assume anon__0 == 0;
  assume anon__1 == 1;
  assume (Mode#[this#] == anon__0) || (Mode#[this#] == anon__1);
  assume R# == I#;
  assume (C#[N#anon$2] - R#[N#anon$2]) == 0;
  assume (C#[N#anon$3] - R#[N#anon$3]) == 0;
  C#[N#anon$2] := C#[N#anon$2] + 1;
  assume M#[N#anon$2][I#[N#anon$2]] < 0;
  // Instance: a, Action: neg
  assert {:msg "TooGeneralContract.actor(5.3): Firing rule might not be satisfied for action 'neg' of instance 'a' (#1)"} (1 <= (C#[N#anon$2] - R#[N#anon$2])) && (M#[N#anon$2][R#[N#anon$2]] < 0);
  a#x#i := M#[N#anon$2][R#[N#anon$2]];
  R#[N#anon$2] := R#[N#anon$2] + 1;
  M#[N#anon$3][C#[N#anon$3]] := -a#x#i;
  C#[N#anon$3] := C#[N#anon$3] + 1;
}

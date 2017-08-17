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

procedure N#anon__4()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var N#a: Actor;
  var N#b: Actor;
  var N#anon$5: Chan (int);
  var N#anon$6: Chan (bool);
  var N#anon$7: Chan (int);
  var anon__4: int;
  var b#x#i: bool;
  assume N#a != N#b;
  assume 0 <= I#[N#anon$5];
  assume I#[N#anon$5] <= R#[N#anon$5];
  assume R#[N#anon$5] <= C#[N#anon$5];
  assume 0 <= I#[N#anon$6];
  assume I#[N#anon$6] <= R#[N#anon$6];
  assume R#[N#anon$6] <= C#[N#anon$6];
  assume 0 <= I#[N#anon$7];
  assume I#[N#anon$7] <= R#[N#anon$7];
  assume R#[N#anon$7] <= C#[N#anon$7];
  assume I#[N#anon$7] == R#[N#anon$7];
  assume (B#[N#anon$5] == 2) && (B#[N#anon$7] == 2);
  assume anon__4 == 0;
  assume Mode#[this#] == anon__4;
  assume R# == I#;
  assume (C#[N#anon$5] - R#[N#anon$5]) == 0;
  assume (C#[N#anon$6] - R#[N#anon$6]) == 0;
  assume (C#[N#anon$7] - R#[N#anon$7]) == 0;
  C#[N#anon$5] := C#[N#anon$5] + 2;
  assume 0 <= M#[N#anon$5][I#[N#anon$5]];
  assume 0 < M#[N#anon$5][I#[N#anon$5] + 1];
  // Instance: a, Action: anon__0
  I#sub[N#anon$5] := R#[N#anon$5];
  I#sub[N#anon$6] := C#[N#anon$6];
  assert {:msg "InterActorDataDependency.actor(2.3): Firing rule might not be satisfied for action 'anon__0' of instance 'a' (#1)"} 1 <= (C#[N#anon$5] - R#[N#anon$5]);
  R#[N#anon$5] := R#[N#anon$5] + 1;
  C#[N#anon$6] := C#[N#anon$6] + 1;
  assume (if 0 <= M#[N#anon$5][I#sub[N#anon$5]] then M#[N#anon$6][I#sub[N#anon$6]] else !M#[N#anon$6][I#sub[N#anon$6]]);
  // Instance: a, Action: anon__0
  I#sub[N#anon$5] := R#[N#anon$5];
  I#sub[N#anon$6] := C#[N#anon$6];
  assert {:msg "InterActorDataDependency.actor(2.3): Firing rule might not be satisfied for action 'anon__0' of instance 'a' (#2)"} 1 <= (C#[N#anon$5] - R#[N#anon$5]);
  R#[N#anon$5] := R#[N#anon$5] + 1;
  C#[N#anon$6] := C#[N#anon$6] + 1;
  assume (if 0 <= M#[N#anon$5][I#sub[N#anon$5]] then M#[N#anon$6][I#sub[N#anon$6]] else !M#[N#anon$6][I#sub[N#anon$6]]);
  // Instance: b, Action: anon__2
  I#sub[N#anon$6] := R#[N#anon$6];
  I#sub[N#anon$7] := C#[N#anon$7];
  assert {:msg "InterActorDataDependency.actor(9.3): Firing rule might not be satisfied for action 'anon__2' of instance 'b' (#3)"} (1 <= (C#[N#anon$6] - R#[N#anon$6])) && M#[N#anon$6][R#[N#anon$6]];
  b#x#i := M#[N#anon$6][R#[N#anon$6]];
  R#[N#anon$6] := R#[N#anon$6] + 1;
  M#[N#anon$7][C#[N#anon$7]] := 1;
  C#[N#anon$7] := C#[N#anon$7] + 1;
  // Instance: b, Action: anon__2
  I#sub[N#anon$6] := R#[N#anon$6];
  I#sub[N#anon$7] := C#[N#anon$7];
  assert {:msg "InterActorDataDependency.actor(9.3): Firing rule might not be satisfied for action 'anon__2' of instance 'b' (#4)"} (1 <= (C#[N#anon$6] - R#[N#anon$6])) && M#[N#anon$6][R#[N#anon$6]];
  b#x#i := M#[N#anon$6][R#[N#anon$6]];
  R#[N#anon$6] := R#[N#anon$6] + 1;
  M#[N#anon$7][C#[N#anon$7]] := 1;
  C#[N#anon$7] := C#[N#anon$7] + 1;
}

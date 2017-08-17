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

procedure Net#anon__0()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var Net#rw64: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var anon__0: int;
  var rw64#X#i: int;
  assume 0 <= I#[Net#a];
  assume I#[Net#a] <= R#[Net#a];
  assume R#[Net#a] <= C#[Net#a];
  assume 0 <= I#[Net#b];
  assume I#[Net#b] <= R#[Net#b];
  assume R#[Net#b] <= C#[Net#b];
  assume I#[Net#b] == R#[Net#b];
  assume (B#[Net#a] == 5) && (B#[Net#b] == 5);
  assume anon__0 == 0;
  assume Mode#[this#] == anon__0;
  assume Mode#[this#] == anon__0;
  assume R# == I#;
  assume (5 * R#[Net#a]) == (5 * C#[Net#b]);
  assume (C#[Net#a] - R#[Net#a]) == 0;
  assume (C#[Net#b] - R#[Net#b]) == 0;
  assume (Mode#[this#] == anon__0) ==> ((C#[Net#a] - I#[Net#a]) <= 5);
  C#[Net#a] := C#[Net#a] + 5;
  // Instance: rw64, Action: read
  I#sub[Net#a] := R#[Net#a];
  I#sub[Net#b] := C#[Net#b];
  assert {:msg "anon__0: Firing rule might not be satisfied for action 'read' of instance 'rw64' (#0)"} (1 <= (C#[Net#a] - R#[Net#a])) && (count < 5);
  rw64#X#i := M#[Net#a][R#[Net#a]];
  R#[Net#a] := R#[Net#a] + 1;
  havoc count;
  M#[Net#b][C#[Net#b]] := rw64#X#i;
  C#[Net#b] := C#[Net#b] + 1;
  // Instance: rw64, Action: read
  I#sub[Net#a] := R#[Net#a];
  I#sub[Net#b] := C#[Net#b];
  assert {:msg "anon__0: Firing rule might not be satisfied for action 'read' of instance 'rw64' (#1)"} (1 <= (C#[Net#a] - R#[Net#a])) && (count < 5);
  rw64#X#i := M#[Net#a][R#[Net#a]];
  R#[Net#a] := R#[Net#a] + 1;
  havoc count;
  M#[Net#b][C#[Net#b]] := rw64#X#i;
  C#[Net#b] := C#[Net#b] + 1;
  // Instance: rw64, Action: read
  I#sub[Net#a] := R#[Net#a];
  I#sub[Net#b] := C#[Net#b];
  assert {:msg "anon__0: Firing rule might not be satisfied for action 'read' of instance 'rw64' (#2)"} (1 <= (C#[Net#a] - R#[Net#a])) && (count < 5);
  rw64#X#i := M#[Net#a][R#[Net#a]];
  R#[Net#a] := R#[Net#a] + 1;
  havoc count;
  M#[Net#b][C#[Net#b]] := rw64#X#i;
  C#[Net#b] := C#[Net#b] + 1;
  // Instance: rw64, Action: read
  I#sub[Net#a] := R#[Net#a];
  I#sub[Net#b] := C#[Net#b];
  assert {:msg "anon__0: Firing rule might not be satisfied for action 'read' of instance 'rw64' (#3)"} (1 <= (C#[Net#a] - R#[Net#a])) && (count < 5);
  rw64#X#i := M#[Net#a][R#[Net#a]];
  R#[Net#a] := R#[Net#a] + 1;
  havoc count;
  M#[Net#b][C#[Net#b]] := rw64#X#i;
  C#[Net#b] := C#[Net#b] + 1;
  // Instance: rw64, Action: read
  I#sub[Net#a] := R#[Net#a];
  I#sub[Net#b] := C#[Net#b];
  assert {:msg "anon__0: Firing rule might not be satisfied for action 'read' of instance 'rw64' (#4)"} (1 <= (C#[Net#a] - R#[Net#a])) && (count < 5);
  rw64#X#i := M#[Net#a][R#[Net#a]];
  R#[Net#a] := R#[Net#a] + 1;
  havoc count;
  M#[Net#b][C#[Net#b]] := rw64#X#i;
  C#[Net#b] := C#[Net#b] + 1;
  // Instance: rw64, Action: done
  I#sub[Net#a] := R#[Net#a];
  I#sub[Net#b] := C#[Net#b];
  assert {:msg "anon__0: Firing rule might not be satisfied for action 'done' of instance 'rw64' (#5)"} count == 5;
  havoc count;
  assert {:msg "The correct amount of tokens might not be produced on output Y (#6)"} (C#[Net#b] - R#[Net#b]) == 5;
}

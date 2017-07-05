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

procedure Net#anon__4()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var Net#add: Actor;
  var Net#del: Actor;
  var Net#spl: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (int);
  var Net#d: Chan (int);
  var Net#e: Chan (int);
  var anon__4: int;
  var add#in1#i: int;
  var add#in2#j: int;
  var spl#in1#i: int;
  var del#in1#i: int;
  assume (Net#add != Net#del) && (Net#add != Net#spl) && (Net#del != Net#spl);
  assume (Net#a != Net#b) && (Net#a != Net#c) && (Net#a != Net#d) && (Net#a != Net#e) && (Net#b != Net#c) && (Net#b != Net#d) && (Net#b != Net#e) && (Net#c != Net#d) && (Net#c != Net#e) && (Net#d != Net#e);
  assume 0 <= I#[Net#a];
  assume I#[Net#a] <= R#[Net#a];
  assume R#[Net#a] <= C#[Net#a];
  assume 0 <= I#[Net#b];
  assume I#[Net#b] <= R#[Net#b];
  assume R#[Net#b] <= C#[Net#b];
  assume 0 <= I#[Net#c];
  assume I#[Net#c] <= R#[Net#c];
  assume R#[Net#c] <= C#[Net#c];
  assume 0 <= I#[Net#d];
  assume I#[Net#d] <= R#[Net#d];
  assume R#[Net#d] <= C#[Net#d];
  assume I#[Net#d] == R#[Net#d];
  assume 0 <= I#[Net#e];
  assume I#[Net#e] <= R#[Net#e];
  assume R#[Net#e] <= C#[Net#e];
  assume (B#[Net#a] == 2) && (B#[Net#d] == 2);
  assume anon__4 == 0;
  assume Mode#[this#] == anon__4;
  assume Mode#[this#] == anon__4;
  assume R# == I#;
  assume (C#[Net#b] - R#[Net#b]) == 1;
  assume (C#[Net#a] - R#[Net#a]) == 0;
  assume (C#[Net#c] - R#[Net#c]) == 0;
  assume (C#[Net#d] - R#[Net#d]) == 0;
  assume (C#[Net#e] - R#[Net#e]) == 0;
  assume M#[Net#b][0] == 0;
  assume 0 <= M#[Net#b][I#[Net#b]];
  C#[Net#a] := C#[Net#a] + 2;
  assume 0 <= M#[Net#a][I#[Net#a]];
  // Instance: add, Action: anon__22
  I#sub[Net#a] := R#[Net#a];
  I#sub[Net#b] := R#[Net#b];
  I#sub[Net#c] := C#[Net#c];
  assert {:msg "anon__4: Firing rule might not be satisfied for action 'anon__22' of instance 'add' (#0)"} (1 <= (C#[Net#a] - R#[Net#a])) && (1 <= (C#[Net#b] - R#[Net#b]));
  add#in1#i := M#[Net#a][R#[Net#a]];
  R#[Net#a] := R#[Net#a] + 1;
  add#in2#j := M#[Net#b][R#[Net#b]];
  R#[Net#b] := R#[Net#b] + 1;
  M#[Net#c][C#[Net#c]] := add#in1#i + add#in2#j;
  C#[Net#c] := C#[Net#c] + 1;
  // Instance: spl, Action: anon__23
  I#sub[Net#c] := R#[Net#c];
  I#sub[Net#d] := C#[Net#d];
  I#sub[Net#e] := C#[Net#e];
  assert {:msg "anon__4: Firing rule might not be satisfied for action 'anon__23' of instance 'spl' (#1)"} 1 <= (C#[Net#c] - R#[Net#c]);
  spl#in1#i := M#[Net#c][R#[Net#c]];
  R#[Net#c] := R#[Net#c] + 1;
  M#[Net#d][C#[Net#d]] := spl#in1#i;
  C#[Net#d] := C#[Net#d] + 1;
  M#[Net#e][C#[Net#e]] := spl#in1#i;
  C#[Net#e] := C#[Net#e] + 1;
  // Instance: del, Action: anon__25
  I#sub[Net#e] := R#[Net#e];
  I#sub[Net#b] := C#[Net#b];
  assert {:msg "anon__4: Firing rule might not be satisfied for action 'anon__25' of instance 'del' (#2)"} 1 <= (C#[Net#e] - R#[Net#e]);
  del#in1#i := M#[Net#e][R#[Net#e]];
  R#[Net#e] := R#[Net#e] + 1;
  M#[Net#b][C#[Net#b]] := del#in1#i;
  C#[Net#b] := C#[Net#b] + 1;
  // Instance: add, Action: anon__22
  I#sub[Net#a] := R#[Net#a];
  I#sub[Net#b] := R#[Net#b];
  I#sub[Net#c] := C#[Net#c];
  assert {:msg "anon__4: Firing rule might not be satisfied for action 'anon__22' of instance 'add' (#3)"} (1 <= (C#[Net#a] - R#[Net#a])) && (1 <= (C#[Net#b] - R#[Net#b]));
  add#in1#i := M#[Net#a][R#[Net#a]];
  R#[Net#a] := R#[Net#a] + 1;
  add#in2#j := M#[Net#b][R#[Net#b]];
  R#[Net#b] := R#[Net#b] + 1;
  M#[Net#c][C#[Net#c]] := add#in1#i + add#in2#j;
  C#[Net#c] := C#[Net#c] + 1;
  // Instance: spl, Action: anon__23
  I#sub[Net#c] := R#[Net#c];
  I#sub[Net#d] := C#[Net#d];
  I#sub[Net#e] := C#[Net#e];
  assert {:msg "anon__4: Firing rule might not be satisfied for action 'anon__23' of instance 'spl' (#4)"} 1 <= (C#[Net#c] - R#[Net#c]);
  spl#in1#i := M#[Net#c][R#[Net#c]];
  R#[Net#c] := R#[Net#c] + 1;
  M#[Net#d][C#[Net#d]] := spl#in1#i;
  C#[Net#d] := C#[Net#d] + 1;
  M#[Net#e][C#[Net#e]] := spl#in1#i;
  C#[Net#e] := C#[Net#e] + 1;
  // Instance: del, Action: anon__25
  I#sub[Net#e] := R#[Net#e];
  I#sub[Net#b] := C#[Net#b];
  assert {:msg "anon__4: Firing rule might not be satisfied for action 'anon__25' of instance 'del' (#5)"} 1 <= (C#[Net#e] - R#[Net#e]);
  del#in1#i := M#[Net#e][R#[Net#e]];
  R#[Net#e] := R#[Net#e] + 1;
  M#[Net#b][C#[Net#b]] := del#in1#i;
  C#[Net#b] := C#[Net#b] + 1;
  assert {:msg "The correct amount of tokens might not be produced on output out (#6)"} (C#[Net#d] - R#[Net#d]) == 2;
}

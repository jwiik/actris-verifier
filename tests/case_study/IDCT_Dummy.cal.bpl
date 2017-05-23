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

procedure IDCT_Dummy#init#0()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var IN: Chan (bv13);
  var SIGNED: Chan (bool);
  var OUT: Chan (bv9);
  var anon$0: int;
  assume true;
  assume anon$0 == 0;
  assume Mode#[this#] == anon$0;
  assume (I#[IN] == 0) && (R#[IN] == 0) && (C#[IN] == 0);
  assume (I#[SIGNED] == 0) && (R#[SIGNED] == 0) && (C#[SIGNED] == 0);
  assume (I#[OUT] == 0) && (R#[OUT] == 0) && (C#[OUT] == 0);
  assert {:msg "Initialization might not establish the invariant (#0)"} (Mode#[this#] == anon$0) ==> ((C#[IN] - I#[IN]) <= 64) && ((C#[SIGNED] - I#[SIGNED]) <= 1);
}
procedure IDCT_Dummy#contract#anon$0#input#1()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var IN: Chan (bv13);
  var SIGNED: Chan (bool);
  var OUT: Chan (bv9);
  var anon$0: int;
  assume true;
  assume anon$0 == 0;
  assume Mode#[this#] == anon$0;
  assume (0 <= I#[IN]) && (I#[IN] <= R#[IN]) && (R#[IN] <= C#[IN]);
  assume (0 <= I#[SIGNED]) && (I#[SIGNED] <= R#[SIGNED]) && (R#[SIGNED] <= C#[SIGNED]);
  assume (0 <= I#[OUT]) && (I#[OUT] <= R#[OUT]) && (R#[OUT] <= C#[OUT]);
  assume Mode#[this#] == anon$0;
  assume R#[OUT] == I#[OUT];
  assume (Mode#[this#] == anon$0) ==> ((C#[IN] - I#[IN]) <= 64) && ((C#[SIGNED] - I#[SIGNED]) <= 1);
  assume (C#[IN] - I#[IN]) < 64;
  C#[IN] := C#[IN] + 1;
  assert {:msg "Invariant might be falsified by actor input (#1)"} (Mode#[this#] == anon$0) ==> ((C#[IN] - I#[IN]) <= 64) && ((C#[SIGNED] - I#[SIGNED]) <= 1);
}
procedure IDCT_Dummy#contract#anon$0#input#2()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var IN: Chan (bv13);
  var SIGNED: Chan (bool);
  var OUT: Chan (bv9);
  var anon$0: int;
  assume true;
  assume anon$0 == 0;
  assume Mode#[this#] == anon$0;
  assume (0 <= I#[IN]) && (I#[IN] <= R#[IN]) && (R#[IN] <= C#[IN]);
  assume (0 <= I#[SIGNED]) && (I#[SIGNED] <= R#[SIGNED]) && (R#[SIGNED] <= C#[SIGNED]);
  assume (0 <= I#[OUT]) && (I#[OUT] <= R#[OUT]) && (R#[OUT] <= C#[OUT]);
  assume Mode#[this#] == anon$0;
  assume R#[OUT] == I#[OUT];
  assume (Mode#[this#] == anon$0) ==> ((C#[IN] - I#[IN]) <= 64) && ((C#[SIGNED] - I#[SIGNED]) <= 1);
  assume (C#[SIGNED] - I#[SIGNED]) < 1;
  C#[SIGNED] := C#[SIGNED] + 1;
  assert {:msg "Invariant might be falsified by actor input (#2)"} (Mode#[this#] == anon$0) ==> ((C#[IN] - I#[IN]) <= 64) && ((C#[SIGNED] - I#[SIGNED]) <= 1);
}
procedure IDCT_Dummy#contract#anon$0#exit#3()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var IN: Chan (bv13);
  var SIGNED: Chan (bool);
  var OUT: Chan (bv9);
  var anon$0: int;
  assume true;
  assume anon$0 == 0;
  assume Mode#[this#] == anon$0;
  assume (0 <= I#[IN]) && (I#[IN] <= R#[IN]) && (R#[IN] <= C#[IN]);
  assume (0 <= I#[SIGNED]) && (I#[SIGNED] <= R#[SIGNED]) && (R#[SIGNED] <= C#[SIGNED]);
  assume (0 <= I#[OUT]) && (I#[OUT] <= R#[OUT]) && (R#[OUT] <= C#[OUT]);
  assume Mode#[this#] == anon$0;
  assume R#[OUT] == I#[OUT];
  assume (Mode#[this#] == anon$0) ==> ((C#[IN] - I#[IN]) <= 64) && ((C#[SIGNED] - I#[SIGNED]) <= 1);
  assume (C#[IN] - I#[IN]) == 64;
  assume (C#[SIGNED] - I#[SIGNED]) == 1;
  assert {:msg "IDCT_Dummy.cal(4.2): The correct number of tokens might not be produced on output 'OUT' with contract 'anon$0' (#3)"} (C#[OUT] - I#[OUT]) == 64;
  R#[OUT] := R#[OUT] + 64;
  I# := R#;
  assert {:msg "The actor might not preserve the invariant with contract 'anon$0' at IDCT_Dummy.cal(4.2) (#4)"} (Mode#[this#] == anon$0) ==> ((C#[IN] - I#[IN]) <= 64) && ((C#[SIGNED] - I#[SIGNED]) <= 1);
}

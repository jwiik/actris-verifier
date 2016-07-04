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
var C#init: CType;
var St: [Actor]State;

const unique this#: Actor;

type List a = [int]a;
var AT#intlst: List int;

function AT#Min(x:int, y: int): int { if x <= y then x else y }


// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

procedure Test1#anon$0#0()
  modifies C, R, M, St;
{
  var IV#in#0: int;
  assume true;
  assume true;
}
procedure Test1#anon$1#1()
  modifies C, R, M, St;
{
  assume true;
  assume true;
}
procedure Test1##GuardWD#2()
  modifies C, R, M, St;
{
  var IV#in#0: int;
  var in#NumRead: int;
  assert {:msg "  1.1: The actions might not have mutually exclusive guards"} !((1 <= in#NumRead) && true && true);
}
const unique Test2#s0: State;
const unique Test2#s1: State;
procedure Test2#a#3()
  modifies C, R, M, St;
{
  var this#: Actor;
  var IV#in#0: int;
  assume (St[this#] == Test2#s0) || (St[this#] == Test2#s1);
  assume St[this#] == Test2#s0;
  assume true;
  St[this#] := Test2#s1;
  assume (St[this#] == Test2#s0) || (St[this#] == Test2#s1);
}
procedure Test2#b#4()
  modifies C, R, M, St;
{
  var this#: Actor;
  var IV#in#0: int;
  var IV#in#1: int;
  assume (St[this#] == Test2#s0) || (St[this#] == Test2#s1);
  assume St[this#] == Test2#s1;
  assume true;
  St[this#] := Test2#s0;
  assume (St[this#] == Test2#s0) || (St[this#] == Test2#s1);
}
procedure Test2##GuardWD#5()
  modifies C, R, M, St;
{
  var this#: Actor;
  var IV#in#1: int;
  var IV#in#0: int;
  var in#NumRead: int;
  assert {:msg "  6.1: The actions might not have mutually exclusive guards"} !((1 <= in#NumRead) && (St[this#] == Test2#s0) && (2 <= in#NumRead) && (St[this#] == Test2#s1));
}

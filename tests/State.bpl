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


// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

procedure Sum#anon$0#0()
  modifies C, R, M, St;
{
  var sum: int;
  assume 0 <= sum;
  sum := 0;
  assert {:msg "  6.13: Action at 8.3 might not preserve invariant"} 0 <= sum;
}
procedure Sum#anon$1#1()
  modifies C, R, M, St;
{
  var sum: int;
  var IV#in1#i: int;
  assume 0 <= sum;
  assume 0 <= IV#in1#i;
  sum := sum + IV#in1#i;
  assert {:msg "  6.13: Action at 13.3 might not preserve invariant"} 0 <= sum;
}

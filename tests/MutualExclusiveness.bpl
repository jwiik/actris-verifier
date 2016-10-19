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
var I: CType;
var St: [Actor]State;

const unique this#: Actor;
type List a = [int]a;
var AT#intlst: List int;

function AT#Min(x:int, y: int): int { if x <= y then x else y }

// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

procedure NonDetMerge2#a1#0()
  modifies C, R, M, I, St;
{
  var x1: Chan (int);
  var x2: Chan (int);
  var y: Chan (int);
  assume true;
}
procedure NonDetMerge2#a2#1()
  modifies C, R, M, I, St;
{
  var x1: Chan (int);
  var x2: Chan (int);
  var y: Chan (int);
  assume true;
}
procedure NonDetMerge2##GuardWD#2()
  modifies C, R, M, I, St;
{
  var x2: Chan (int);
  var y: Chan (int);
  var x1: Chan (int);
  assert {:msg "4.1: The actions of actor 'NonDetMerge2' might not have mutually exclusive guards (#0)"} !((1 <= (C[x1] - R[x1])) && (1 <= (C[x2] - R[x2])));
}
procedure NonDetMerge3#a1#3()
  modifies C, R, M, I, St;
{
  var x1: Chan (int);
  var x2: Chan (int);
  var x3: Chan (int);
  var y: Chan (int);
  assume true;
}
procedure NonDetMerge3#a2#4()
  modifies C, R, M, I, St;
{
  var x1: Chan (int);
  var x2: Chan (int);
  var x3: Chan (int);
  var y: Chan (int);
  assume true;
}
procedure NonDetMerge3#a3#5()
  modifies C, R, M, I, St;
{
  var x1: Chan (int);
  var x2: Chan (int);
  var x3: Chan (int);
  var y: Chan (int);
  assume true;
}
procedure NonDetMerge3##GuardWD#6()
  modifies C, R, M, I, St;
{
  var x2: Chan (int);
  var y: Chan (int);
  var x1: Chan (int);
  var x3: Chan (int);
  assert {:msg "9.1: The actions of actor 'NonDetMerge3' might not have mutually exclusive guards (#1)"} !((1 <= (C[x1] - R[x1])) && (1 <= (C[x2] - R[x2])));
  assert {:msg "9.1: The actions of actor 'NonDetMerge3' might not have mutually exclusive guards (#2)"} !((1 <= (C[x1] - R[x1])) && (1 <= (C[x3] - R[x3])));
  assert {:msg "9.1: The actions of actor 'NonDetMerge3' might not have mutually exclusive guards (#3)"} !((1 <= (C[x2] - R[x2])) && (1 <= (C[x3] - R[x3])));
}
procedure DetMerge#a1#7()
  modifies C, R, M, I, St;
{
  var ctrl: Chan (int);
  var x1: Chan (int);
  var x2: Chan (int);
  var x3: Chan (int);
  var y: Chan (int);
  assume M[ctrl][0] == 1;
  assume true;
}
procedure DetMerge#a2#8()
  modifies C, R, M, I, St;
{
  var ctrl: Chan (int);
  var x1: Chan (int);
  var x2: Chan (int);
  var x3: Chan (int);
  var y: Chan (int);
  assume M[ctrl][0] == 2;
  assume true;
}
procedure DetMerge#a3#9()
  modifies C, R, M, I, St;
{
  var ctrl: Chan (int);
  var x1: Chan (int);
  var x2: Chan (int);
  var x3: Chan (int);
  var y: Chan (int);
  assume M[ctrl][0] == 3;
  assume true;
}
procedure DetMerge##GuardWD#10()
  modifies C, R, M, I, St;
{
  var x2: Chan (int);
  var y: Chan (int);
  var ctrl: Chan (int);
  var x1: Chan (int);
  var x3: Chan (int);
  assert {:msg "16.1: The actions of actor 'DetMerge' might not have mutually exclusive guards (#4)"} !((1 <= (C[ctrl] - R[ctrl])) && (1 <= (C[x1] - R[x1])) && (M[ctrl][0] == 1) && (1 <= (C[ctrl] - R[ctrl])) && (1 <= (C[x2] - R[x2])) && (M[ctrl][0] == 2));
  assert {:msg "16.1: The actions of actor 'DetMerge' might not have mutually exclusive guards (#5)"} !((1 <= (C[ctrl] - R[ctrl])) && (1 <= (C[x1] - R[x1])) && (M[ctrl][0] == 1) && (1 <= (C[ctrl] - R[ctrl])) && (1 <= (C[x3] - R[x3])) && (M[ctrl][0] == 3));
  assert {:msg "16.1: The actions of actor 'DetMerge' might not have mutually exclusive guards (#6)"} !((1 <= (C[ctrl] - R[ctrl])) && (1 <= (C[x2] - R[x2])) && (M[ctrl][0] == 2) && (1 <= (C[ctrl] - R[ctrl])) && (1 <= (C[x3] - R[x3])) && (M[ctrl][0] == 3));
}

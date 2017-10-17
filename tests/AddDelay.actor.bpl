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

procedure Add#Add#gen$init#init#0()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var in1: Chan (int);
  var in2: Chan (int);
  var out: Chan (int);
  assume (in1 != in2) && (in1 != out) && (in2 != out);
  assume (0 <= I#[in1]) && (I#[in1] <= R#[in1]) && (R#[in1] <= C#[in1]);
  assume (0 <= I#[in2]) && (I#[in2] <= R#[in2]) && (R#[in2] <= C#[in2]);
  assume (0 <= I#[out]) && (I#[out] <= R#[out]) && (R#[out] <= C#[out]);
  assume (I#[in1] == 0) && (R#[in1] == 0) && (C#[in1] == 0);
  assume (I#[in2] == 0) && (R#[in2] == 0) && (C#[in2] == 0);
  assume (I#[out] == 0) && (R#[out] == 0) && (C#[out] == 0);
  assume true;
  assert {:msg "Initialization might not establish the invariant (#0)"} R#[in1] == C#[out];
  assert {:msg "Initialization might not establish the invariant (#1)"} R#[in2] == C#[out];
  assert {:msg "Initialization might not establish the invariant (#2)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C#[out]) ==> (M#[out][idx$] == (M#[in1][idx$] + M#[in2][idx$]))
  );
}
procedure Add#anon__22#1()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var in1: Chan (int);
  var in2: Chan (int);
  var out: Chan (int);
  var in1#0: int;
  var in2#0: int;
  assume (in1 != in2) && (in1 != out) && (in2 != out);
  assume (0 <= I#[in1]) && (I#[in1] <= R#[in1]) && (R#[in1] <= C#[in1]);
  assume (0 <= I#[in2]) && (I#[in2] <= R#[in2]) && (R#[in2] <= C#[in2]);
  assume (0 <= I#[out]) && (I#[out] <= R#[out]) && (R#[out] <= C#[out]);
  assume in1#0 != in2#0;
  assume R#[in1] == C#[out];
  assume R#[in2] == C#[out];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C#[out]) ==> (M#[out][idx$] == (M#[in1][idx$] + M#[in2][idx$]))
  );
  assume (1 <= (C#[in1] - R#[in1])) && (1 <= (C#[in2] - R#[in2]));
  in1#0 := M#[in1][R#[in1]];
  R#[in1] := R#[in1] + 1;
  in2#0 := M#[in2][R#[in2]];
  R#[in2] := R#[in2] + 1;
  assume true;
  M#[out][C#[out]] := in1#0 + in2#0;
  C#[out] := C#[out] + 1;
  assert {:msg "Action 'anon__22' at AddDelay.actor(2.3) might not preserve the invariant (#3)"} R#[in1] == C#[out];
  assert {:msg "Action 'anon__22' at AddDelay.actor(2.3) might not preserve the invariant (#4)"} R#[in2] == C#[out];
  assert {:msg "Action 'anon__22' at AddDelay.actor(2.3) might not preserve the invariant (#5)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C#[out]) ==> (M#[out][idx$] == (M#[in1][idx$] + M#[in2][idx$]))
  );
}

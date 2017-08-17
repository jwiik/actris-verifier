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

procedure Nested#Main()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var Nested#net: Actor;
  var Nested#sum: Actor;
  var Nested#spl: Actor;
  var Nested#a: Chan (int);
  var Nested#b: Chan (int);
  var Nested#c: Chan (int);
  var Nested#d: Chan (int);
  var Nested#e: Chan (int);
  var Main: int;
  var sum#sum: int;
  var spl#in1#i: int;
  var sum#x#i: int;
  assume (Nested#net != Nested#sum) && (Nested#net != Nested#spl) && (Nested#sum != Nested#spl);
  assume (Nested#a != Nested#b) && (Nested#a != Nested#c) && (Nested#a != Nested#d) && (Nested#a != Nested#e) && (Nested#b != Nested#c) && (Nested#b != Nested#d) && (Nested#b != Nested#e) && (Nested#c != Nested#d) && (Nested#c != Nested#e) && (Nested#d != Nested#e);
  assume 0 <= I#[Nested#a];
  assume I#[Nested#a] <= R#[Nested#a];
  assume R#[Nested#a] <= C#[Nested#a];
  assume 0 <= I#[Nested#b];
  assume I#[Nested#b] <= R#[Nested#b];
  assume R#[Nested#b] <= C#[Nested#b];
  assume 0 <= I#[Nested#c];
  assume I#[Nested#c] <= R#[Nested#c];
  assume R#[Nested#c] <= C#[Nested#c];
  assume 0 <= I#[Nested#d];
  assume I#[Nested#d] <= R#[Nested#d];
  assume R#[Nested#d] <= C#[Nested#d];
  assume I#[Nested#d] == R#[Nested#d];
  assume 0 <= I#[Nested#e];
  assume I#[Nested#e] <= R#[Nested#e];
  assume R#[Nested#e] <= C#[Nested#e];
  assume I#[Nested#e] == R#[Nested#e];
  assume (B#[Nested#a] == 2) && (B#[Nested#d] == 2) && (B#[Nested#e] == 2);
  assume Main == 0;
  assume Mode#[this#] == Main;
  assume Mode#[this#] == Main;
  assume R# == I#;
  assume (C#[Nested#a] - R#[Nested#a]) == 0;
  assume (C#[Nested#b] - R#[Nested#b]) == 0;
  assume (C#[Nested#c] - R#[Nested#c]) == 0;
  assume (C#[Nested#d] - R#[Nested#d]) == 0;
  assume (C#[Nested#e] - R#[Nested#e]) == 0;
  assume (forall i: int :: 
    (0 <= i) && (i < I#[Nested#d]) ==> (M#[Nested#d][i] == M#[Nested#e][i])
  );
  assume I#[Nested#d] == I#[Nested#b];
  assume I#[Nested#e] == I#[Nested#c];
  assume R#[Nested#b] == C#[Nested#d];
  assume (C#[Nested#d] > 0) ==> (M#[Nested#d][0] == M#[Nested#b][0]);
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C#[Nested#d] - 0)) ==> (M#[Nested#d][i] == (M#[Nested#d][i - 1] + M#[Nested#b][i]))
  );
  assume R#[Nested#c] == C#[Nested#e];
  assume (C#[Nested#e] > 0) ==> (M#[Nested#e][0] == M#[Nested#c][0]);
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C#[Nested#e] - 0)) ==> (M#[Nested#e][i] == (M#[Nested#e][i - 1] + M#[Nested#c][i]))
  );
  C#[Nested#a] := C#[Nested#a] + 2;
  assume 0 <= M#[Nested#a][I#[Nested#a]];
  assume 0 <= M#[Nested#a][I#[Nested#a] + 1];
  // Instance: spl, Action: anon__33
  I#sub[Nested#a] := R#[Nested#a];
  I#sub[Nested#b] := C#[Nested#b];
  I#sub[Nested#c] := C#[Nested#c];
  assert {:msg "Main: Firing rule might not be satisfied for action 'anon__33' of instance 'spl' (#4)"} 1 <= (C#[Nested#a] - R#[Nested#a]);
  spl#in1#i := M#[Nested#a][R#[Nested#a]];
  R#[Nested#a] := R#[Nested#a] + 1;
  M#[Nested#b][C#[Nested#b]] := spl#in1#i;
  C#[Nested#b] := C#[Nested#b] + 1;
  M#[Nested#c][C#[Nested#c]] := spl#in1#i;
  C#[Nested#c] := C#[Nested#c] + 1;
  // Instance: sum, Action: anon__37
  I#sub[Nested#c] := R#[Nested#c];
  I#sub[Nested#e] := C#[Nested#e];
  assert {:msg "Main: Firing rule might not be satisfied for action 'anon__37' of instance 'sum' (#5)"} 1 <= (C#[Nested#c] - R#[Nested#c]);
  sum#x#i := M#[Nested#c][R#[Nested#c]];
  R#[Nested#c] := R#[Nested#c] + 1;
  assert {:msg "Precondition might not hold (#6)"} 0 <= sum#x#i;
  havoc sum#sum;
  M#[Nested#e][C#[Nested#e]] := sum#sum;
  C#[Nested#e] := C#[Nested#e] + 1;
  assume sum#x#i <= sum#sum;
  assume R#[Nested#c] == C#[Nested#e];
  assume (C#[Nested#e] > 0) ==> (M#[Nested#e][0] == M#[Nested#c][0]);
  assume (forall i: int :: 
    ((0 + 1) <= sum#x#i) && (sum#x#i < (C#[Nested#e] - 0)) ==> (M#[Nested#e][sum#x#i] == (M#[Nested#e][sum#x#i - 1] + M#[Nested#c][sum#x#i]))
  );
  // Instance: net, Action: Main
  I#sub[Nested#b] := R#[Nested#b];
  I#sub[Nested#d] := C#[Nested#d];
  assert {:msg "Nested.actor(19.3): Main: Firing rule might not be satisfied for action 'Main' of instance 'net' (#7)"} 1 <= (C#[Nested#b] - R#[Nested#b]);
  R#[Nested#b] := R#[Nested#b] + 1;
  assert {:msg "Precondition might not hold (#8)"} 0 <= M#[Nested#b][I#sub[Nested#b]];
  C#[Nested#d] := C#[Nested#d] + 1;
  assume M#[Nested#d][0] == M#[Nested#b][0];
  assume M#[Nested#d][I#sub[Nested#d]] >= M#[Nested#b][I#sub[Nested#b]];
  assume (0 < I#sub[Nested#d]) ==> (M#[Nested#d][I#sub[Nested#d]] == (M#[Nested#d][I#sub[Nested#d] - 1] + M#[Nested#b][I#sub[Nested#b]]));
  assume R#[Nested#b] == C#[Nested#d];
  assume (C#[Nested#d] > 0) ==> (M#[Nested#d][0] == M#[Nested#b][0]);
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C#[Nested#d] - 0)) ==> (M#[Nested#d][i] == (M#[Nested#d][i - 1] + M#[Nested#b][i]))
  );
  // Instance: spl, Action: anon__33
  I#sub[Nested#a] := R#[Nested#a];
  I#sub[Nested#b] := C#[Nested#b];
  I#sub[Nested#c] := C#[Nested#c];
  assert {:msg "Main: Firing rule might not be satisfied for action 'anon__33' of instance 'spl' (#9)"} 1 <= (C#[Nested#a] - R#[Nested#a]);
  spl#in1#i := M#[Nested#a][R#[Nested#a]];
  R#[Nested#a] := R#[Nested#a] + 1;
  M#[Nested#b][C#[Nested#b]] := spl#in1#i;
  C#[Nested#b] := C#[Nested#b] + 1;
  M#[Nested#c][C#[Nested#c]] := spl#in1#i;
  C#[Nested#c] := C#[Nested#c] + 1;
  // Instance: net, Action: Main
  I#sub[Nested#b] := R#[Nested#b];
  I#sub[Nested#d] := C#[Nested#d];
  assert {:msg "Nested.actor(19.3): Main: Firing rule might not be satisfied for action 'Main' of instance 'net' (#10)"} 1 <= (C#[Nested#b] - R#[Nested#b]);
  R#[Nested#b] := R#[Nested#b] + 1;
  assert {:msg "Precondition might not hold (#11)"} 0 <= M#[Nested#b][I#sub[Nested#b]];
  C#[Nested#d] := C#[Nested#d] + 1;
  assume M#[Nested#d][0] == M#[Nested#b][0];
  assume M#[Nested#d][I#sub[Nested#d]] >= M#[Nested#b][I#sub[Nested#b]];
  assume (0 < I#sub[Nested#d]) ==> (M#[Nested#d][I#sub[Nested#d]] == (M#[Nested#d][I#sub[Nested#d] - 1] + M#[Nested#b][I#sub[Nested#b]]));
  assume R#[Nested#b] == C#[Nested#d];
  assume (C#[Nested#d] > 0) ==> (M#[Nested#d][0] == M#[Nested#b][0]);
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C#[Nested#d] - 0)) ==> (M#[Nested#d][i] == (M#[Nested#d][i - 1] + M#[Nested#b][i]))
  );
  // Instance: sum, Action: anon__37
  I#sub[Nested#c] := R#[Nested#c];
  I#sub[Nested#e] := C#[Nested#e];
  assert {:msg "Main: Firing rule might not be satisfied for action 'anon__37' of instance 'sum' (#12)"} 1 <= (C#[Nested#c] - R#[Nested#c]);
  sum#x#i := M#[Nested#c][R#[Nested#c]];
  R#[Nested#c] := R#[Nested#c] + 1;
  assert {:msg "Precondition might not hold (#13)"} 0 <= sum#x#i;
  havoc sum#sum;
  M#[Nested#e][C#[Nested#e]] := sum#sum;
  C#[Nested#e] := C#[Nested#e] + 1;
  assume sum#x#i <= sum#sum;
  assume R#[Nested#c] == C#[Nested#e];
  assume (C#[Nested#e] > 0) ==> (M#[Nested#e][0] == M#[Nested#c][0]);
  assume (forall i: int :: 
    ((0 + 1) <= sum#x#i) && (sum#x#i < (C#[Nested#e] - 0)) ==> (M#[Nested#e][sum#x#i] == (M#[Nested#e][sum#x#i - 1] + M#[Nested#c][sum#x#i]))
  );
  assert {:msg "The correct amount of tokens might not be produced on output out1 (#14)"} (C#[Nested#d] - R#[Nested#d]) == 2;
  assert {:msg "The correct amount of tokens might not be produced on output out2 (#15)"} (C#[Nested#e] - R#[Nested#e]) == 2;
}

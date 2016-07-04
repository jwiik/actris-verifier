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

procedure Route#anon$0#0()
  modifies C, R, M, St;
{
  var IV#in1#0: int;
  assume true;
  assume true;
}
procedure Route#anon$1#1()
  modifies C, R, M, St;
{
  var IV#in2#0: int;
  assume true;
  assume true;
}
procedure Repeat#anon$2#2()
  modifies C, R, M, St;
{
  var IV#in#0: int;
  assume true;
  assume true;
}
procedure Net#init#3()
  modifies C, R, M, St;
{
  assume C[Net#a] == 0;
  assume R[Net#a] == 0;
  assume C[Net#b] == 0;
  assume R[Net#b] == 0;
  assume C[Net#c] == 0;
  assume R[Net#c] == 0;
  assume C[Net#d] == 0;
  assume R[Net#d] == 0;
}
const unique Net#rou: Actor;
const unique Net#rep: Actor;
const unique Net#a: Chan (int);
const unique Net#b: Chan (int);
const unique Net#c: Chan (int);
const unique Net#d: Chan (int);
procedure Net#anon$3#entry#4()
  modifies C, R, M, St;
{
  var ActionPH#y: int;
  assume C#init[Net#a] == 1;
  assume C#init[Net#b] == 0;
  assume C#init[Net#c] == 0;
  assume C#init[Net#d] == 0;
  assume R[Net#a] == 0;
  assume R[Net#b] == 0;
  assume R[Net#c] == 0;
  assume R[Net#d] == 0;
  assume C#init == C;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume 0 <= R[Net#d];
  assume 0 <= C[Net#d];
  assume R[Net#d] == 0;
  assert {:msg "  Channel invariant might not hold on action entry (#10)"} R[Net#b] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Channel invariant might not hold on action entry (#11)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#b][idx$])
  );
  assert {:msg "  16.3: Channel invariant might not hold on action entry (#12)"} (R[Net#b] + C[Net#b]) == R[Net#a];
  assert {:msg "  17.3: Channel invariant might not hold on action entry (#13)"} (R[Net#d] + C[Net#d]) == R[Net#c];
}
procedure Net#anon$3#Route#anon$0#5()
  modifies C, R, M, St;
{
  var ActionPH#y: int;
  var St#next: State;
  var in1#i: int;
  assume C#init[Net#a] == 1;
  assume C#init[Net#b] == 0;
  assume C#init[Net#c] == 0;
  assume C#init[Net#d] == 0;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume 0 <= R[Net#d];
  assume 0 <= C[Net#d];
  assume R[Net#d] == 0;
  assume R[Net#b] == (R[Net#c] + C[Net#c]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#b][idx$])
  );
  assume (R[Net#b] + C[Net#b]) == R[Net#a];
  assume (R[Net#d] + C[Net#d]) == R[Net#c];
  assume true;
  assume 1 <= C[Net#a];
  in1#i := M[Net#a][R[Net#a]];
  R[Net#a] := R[Net#a] + 1;
  C[Net#a] := C[Net#a] - 1;
  M[Net#b][R[Net#b] + C[Net#b]] := in1#i;
  C[Net#b] := C[Net#b] + 1;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume 0 <= R[Net#d];
  assume 0 <= C[Net#d];
  assume R[Net#d] == 0;
  assert {:msg "  Action at 2.3 ('anon$0') for actor instance 'rou' might not preserve the channel invariant (#24)"} R[Net#b] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Action at 2.3 ('anon$0') for actor instance 'rou' might not preserve the channel invariant (#25)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#b][idx$])
  );
  assert {:msg "  16.3: Action at 2.3 ('anon$0') for actor instance 'rou' might not preserve the channel invariant (#26)"} (R[Net#b] + C[Net#b]) == R[Net#a];
  assert {:msg "  17.3: Action at 2.3 ('anon$0') for actor instance 'rou' might not preserve the channel invariant (#27)"} (R[Net#d] + C[Net#d]) == R[Net#c];
}
procedure Net#anon$3#Route#anon$1#6()
  modifies C, R, M, St;
{
  var ActionPH#y: int;
  var St#next: State;
  var in2#i: int;
  assume C#init[Net#a] == 1;
  assume C#init[Net#b] == 0;
  assume C#init[Net#c] == 0;
  assume C#init[Net#d] == 0;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume 0 <= R[Net#d];
  assume 0 <= C[Net#d];
  assume R[Net#d] == 0;
  assume R[Net#b] == (R[Net#c] + C[Net#c]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#b][idx$])
  );
  assume (R[Net#b] + C[Net#b]) == R[Net#a];
  assume (R[Net#d] + C[Net#d]) == R[Net#c];
  assume true;
  assume 1 <= C[Net#c];
  in2#i := M[Net#c][R[Net#c]];
  R[Net#c] := R[Net#c] + 1;
  C[Net#c] := C[Net#c] - 1;
  M[Net#d][R[Net#d] + C[Net#d]] := in2#i;
  C[Net#d] := C[Net#d] + 1;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume 0 <= R[Net#d];
  assume 0 <= C[Net#d];
  assume R[Net#d] == 0;
  assert {:msg "  Action at 3.3 ('anon$1') for actor instance 'rou' might not preserve the channel invariant (#38)"} R[Net#b] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Action at 3.3 ('anon$1') for actor instance 'rou' might not preserve the channel invariant (#39)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#b][idx$])
  );
  assert {:msg "  16.3: Action at 3.3 ('anon$1') for actor instance 'rou' might not preserve the channel invariant (#40)"} (R[Net#b] + C[Net#b]) == R[Net#a];
  assert {:msg "  17.3: Action at 3.3 ('anon$1') for actor instance 'rou' might not preserve the channel invariant (#41)"} (R[Net#d] + C[Net#d]) == R[Net#c];
}
procedure Net#anon$3#Repeat#anon$2#7()
  modifies C, R, M, St;
{
  var ActionPH#y: int;
  var St#next: State;
  var in#i: int;
  assume C#init[Net#a] == 1;
  assume C#init[Net#b] == 0;
  assume C#init[Net#c] == 0;
  assume C#init[Net#d] == 0;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume 0 <= R[Net#d];
  assume 0 <= C[Net#d];
  assume R[Net#d] == 0;
  assume R[Net#b] == (R[Net#c] + C[Net#c]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#b][idx$])
  );
  assume (R[Net#b] + C[Net#b]) == R[Net#a];
  assume (R[Net#d] + C[Net#d]) == R[Net#c];
  assume true;
  assume 1 <= C[Net#b];
  in#i := M[Net#b][R[Net#b]];
  R[Net#b] := R[Net#b] + 1;
  C[Net#b] := C[Net#b] - 1;
  M[Net#c][R[Net#c] + C[Net#c]] := in#i;
  C[Net#c] := C[Net#c] + 1;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume 0 <= R[Net#d];
  assume 0 <= C[Net#d];
  assume R[Net#d] == 0;
  assert {:msg "  Action at 8.3 ('anon$2') for actor instance 'rep' might not preserve the channel invariant (#52)"} R[Net#b] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Action at 8.3 ('anon$2') for actor instance 'rep' might not preserve the channel invariant (#53)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#b][idx$])
  );
  assert {:msg "  16.3: Action at 8.3 ('anon$2') for actor instance 'rep' might not preserve the channel invariant (#54)"} (R[Net#b] + C[Net#b]) == R[Net#a];
  assert {:msg "  17.3: Action at 8.3 ('anon$2') for actor instance 'rep' might not preserve the channel invariant (#55)"} (R[Net#d] + C[Net#d]) == R[Net#c];
}
procedure Net#anon$3#exit#8()
  modifies C, R, M, St;
{
  var ActionPH#y: int;
  assume C#init[Net#a] == 1;
  assume C#init[Net#b] == 0;
  assume C#init[Net#c] == 0;
  assume C#init[Net#d] == 0;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) == C#init[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume 0 <= R[Net#d];
  assume 0 <= C[Net#d];
  assume R[Net#d] == 0;
  assume R[Net#b] == (R[Net#c] + C[Net#c]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == M[Net#b][idx$])
  );
  assume (R[Net#b] + C[Net#b]) == R[Net#a];
  assume (R[Net#d] + C[Net#d]) == R[Net#c];
  assume !(1 <= C[Net#c]);
  assume !(1 <= C[Net#a]);
  assume !(1 <= C[Net#b]);
  ActionPH#y := M[Net#d][0];
  R[Net#d] := R[Net#d] + C[Net#d];
  C[Net#d] := C[Net#d] - 1;
  assert {:msg "  14.3: The network might leave unread tokens on channel a"} C[Net#a] == 0;
  assert {:msg "  14.3: The network might leave unread tokens on channel b"} C[Net#b] == 0;
  assert {:msg "  14.3: The network might leave unread tokens on channel c"} C[Net#c] == 0;
  assert {:msg "  14.3: The network might not produce the specified number of tokens on output out"} C[Net#d] == 0;
}

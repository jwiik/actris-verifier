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
var L: CType;
var St: [Actor]State;
const Base#L: int;
axiom 1 <= Base#L;

const unique this#: Actor;
type List a = [int]a;
var AT#intlst: List int;

function AT#Min(x:int, y: int): int { if x <= y then x else y }


// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

procedure Add#anon$0#0()
  modifies C, R, M, St;
{
  var IV#in1#0: int;
  var IV#in2#0: int;
  assume true;
  assume true;
}
procedure Net#init#1()
  modifies C, R, M, St;
{
  assume C[Net#a] == 0;
  assume R[Net#a] == 0;
  assume C[Net#b] == 0;
  assume R[Net#b] == 0;
  assume C[Net#c] == 0;
  assume R[Net#c] == 0;
}
const unique Net#add: Actor;
const unique Net#a: Chan (int);
const unique Net#b: Chan (int);
const unique Net#c: Chan (int);
procedure Net#anon$1#entry#2()
  modifies C, R, M, St;
{
  var ActionPH#y: int;
  assume L[Net#a] == (1 * Base#L);
  assume L[Net#b] == (1 * Base#L);
  assume R[Net#a] == 0;
  assume C[Net#a] == 0;
  assume R[Net#b] == 0;
  assume C[Net#b] == 0;
  assume R[Net#c] == 0;
  assume C[Net#c] == 0;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) <= L[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume (R[Net#b] + C[Net#b]) <= L[Net#b];
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume R[Net#c] == 0;
  assert {:msg "  Channel invariant might not hold on action entry (#9)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Channel invariant might not hold on action entry (#10)"} R[Net#b] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Channel invariant might not hold on action entry (#11)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
}
procedure Net#anon$1#Add#anon$0#3()
  modifies C, R, M, St;
{
  var ActionPH#y: int;
  var St#next: State;
  var in1#i: int;
  var in2#j: int;
  assume L[Net#a] == (1 * Base#L);
  assume L[Net#b] == (1 * Base#L);
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) <= L[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume (R[Net#b] + C[Net#b]) <= L[Net#b];
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume R[Net#c] == 0;
  assume R[Net#a] == (R[Net#c] + C[Net#c]);
  assume R[Net#b] == (R[Net#c] + C[Net#c]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assume true;
  assume (1 <= C[Net#a]) && (1 <= C[Net#b]);
  in1#i := M[Net#a][R[Net#a]];
  R[Net#a] := R[Net#a] + 1;
  C[Net#a] := C[Net#a] - 1;
  in2#j := M[Net#b][R[Net#b]];
  R[Net#b] := R[Net#b] + 1;
  C[Net#b] := C[Net#b] - 1;
  M[Net#c][R[Net#c] + C[Net#c]] := in1#i + in2#j;
  C[Net#c] := C[Net#c] + 1;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) <= L[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume (R[Net#b] + C[Net#b]) <= L[Net#b];
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume R[Net#c] == 0;
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#21)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#22)"} R[Net#b] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#23)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
}
procedure Net#anon$1#exit#4()
  modifies C, R, M, St;
{
  var ActionPH#y: int;
  assume L[Net#a] == (1 * Base#L);
  assume L[Net#b] == (1 * Base#L);
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) <= L[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume (R[Net#b] + C[Net#b]) <= L[Net#b];
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume R[Net#c] == 0;
  assume R[Net#a] == (R[Net#c] + C[Net#c]);
  assume R[Net#b] == (R[Net#c] + C[Net#c]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assume !((R[Net#a] + C[Net#a]) < L[Net#a]);
  assume !((R[Net#b] + C[Net#b]) < L[Net#b]);
  assume !((1 <= C[Net#a]) && (1 <= C[Net#b]));
  ActionPH#y := M[Net#c][0];
  assert {:msg "  9.13: Network action postcondition might not hold"} ActionPH#y == (M[Net#a][0] + M[Net#b][0]);
  R[Net#c] := R[Net#c] + C[Net#c];
  C[Net#c] := C[Net#c] - (1 * Base#L);
  assert {:msg "  8.3: The network might leave unread tokens on channel a"} C[Net#a] == 0;
  assert {:msg "  8.3: The network might leave unread tokens on channel b"} C[Net#b] == 0;
  assert {:msg "  8.3: The network might not produce the specified number of tokens on output out"} C[Net#c] == 0;
}

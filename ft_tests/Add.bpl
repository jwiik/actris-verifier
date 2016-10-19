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

// -- Sequence numbering for FT ----------------------------------
var SqnCh: <a>[Chan a][int]int;
var SqnAct: [Actor]int;

// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

procedure Add#anon$0#0()
  modifies C, R, M, St, SqnCh, SqnAct;
{
  var in1: Chan (int);
  var in2: Chan (int);
  var out: Chan (int);
  assume SqnCh[in1][0] == SqnCh[in2][0];
  assume true;
  assume true;
}
procedure Net#init#1()
  modifies C, R, M, St, SqnCh, SqnAct;
{
  assume C[Net#a] == 0;
  assume R[Net#a] == 0;
  assume C[Net#b] == 0;
  assume R[Net#b] == 0;
  assume C[Net#c] == 0;
  assume R[Net#c] == 0;
  assume SqnAct[Net#add] == 0;
  assert {:msg "  Network initialization might not establish the channel invariant (#9)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (0 <= M[Net#a][i])
  );
  assert {:msg "  Network initialization might not establish the channel invariant (#10)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (0 <= M[Net#b][i])
  );
  assert {:msg "  Network initialization might not establish the channel invariant (#11)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Network initialization might not establish the channel invariant (#12)"} R[Net#b] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Network initialization might not establish the channel invariant (#13)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assert {:msg "  Network initialization might not establish the channel invariant (#14)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][idx$] == idx$)
  );
  assert {:msg "  Network initialization might not establish the channel invariant (#15)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (SqnCh[Net#b][idx$] == idx$)
  );
  assert {:msg "  17.15: Network initialization might not establish the channel invariant (#16)"} SqnAct[Net#add] == R[Net#a];
  assert {:msg "  18.16: Network initialization might not establish the channel invariant (#17)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][i] == SqnCh[Net#b][i])
  );
  assert {:msg "  19.16: Network initialization might not establish the channel invariant (#18)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#a]) ==> (SqnCh[Net#a][i] == SqnCh[Net#c][i])
  );
}
const unique Net#add: Actor;
const unique Net#a: Chan (int);
const unique Net#b: Chan (int);
const unique Net#c: Chan (int);
procedure Net#anon$1#entry#2()
  modifies C, R, M, St, SqnCh, SqnAct;
{
  assume L[Net#a] == (1 * Base#L);
  assume L[Net#b] == (1 * Base#L);
  assume C[Net#a] == 0;
  assume C[Net#b] == 0;
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
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (0 <= M[Net#a][i])
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (0 <= M[Net#b][i])
  );
  assume R[Net#a] == (R[Net#c] + C[Net#c]);
  assume R[Net#b] == (R[Net#c] + C[Net#c]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][idx$] == idx$)
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (SqnCh[Net#b][idx$] == idx$)
  );
  assume SqnAct[Net#add] == R[Net#a];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][i] == SqnCh[Net#b][i])
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#a]) ==> (SqnCh[Net#a][i] == SqnCh[Net#c][i])
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (0 <= M[Net#a][i])
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (0 <= M[Net#b][i])
  );
  assert {:msg "  Channel invariant might not hold on action entry (#19)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (0 <= M[Net#a][i])
  );
  assert {:msg "  Channel invariant might not hold on action entry (#20)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (0 <= M[Net#b][i])
  );
  assert {:msg "  Channel invariant might not hold on action entry (#21)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Channel invariant might not hold on action entry (#22)"} R[Net#b] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Channel invariant might not hold on action entry (#23)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assert {:msg "  Channel invariant might not hold on action entry (#24)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][idx$] == idx$)
  );
  assert {:msg "  Channel invariant might not hold on action entry (#25)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (SqnCh[Net#b][idx$] == idx$)
  );
  assert {:msg "  17.15: Channel invariant might not hold on action entry (#26)"} SqnAct[Net#add] == R[Net#a];
  assert {:msg "  18.16: Channel invariant might not hold on action entry (#27)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][i] == SqnCh[Net#b][i])
  );
  assert {:msg "  19.16: Channel invariant might not hold on action entry (#28)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#a]) ==> (SqnCh[Net#a][i] == SqnCh[Net#c][i])
  );
}
procedure Net#anon$1#Add#anon$0#3()
  modifies C, R, M, St, SqnCh, SqnAct;
{
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
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (0 <= M[Net#a][i])
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (0 <= M[Net#b][i])
  );
  assume R[Net#a] == (R[Net#c] + C[Net#c]);
  assume R[Net#b] == (R[Net#c] + C[Net#c]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][idx$] == idx$)
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (SqnCh[Net#b][idx$] == idx$)
  );
  assume SqnAct[Net#add] == R[Net#a];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][i] == SqnCh[Net#b][i])
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#a]) ==> (SqnCh[Net#a][i] == SqnCh[Net#c][i])
  );
  assume true;
  assume (1 <= C[Net#a]) && (1 <= C[Net#b]);
  assert {:msg "  4.14: Precondition might not hold for instance at 22.5"} SqnCh[Net#a][R[Net#a] - 0] == SqnCh[Net#b][R[Net#b] - 0];
  in1#i := M[Net#a][R[Net#a]];
  R[Net#a] := R[Net#a] + 1;
  C[Net#a] := C[Net#a] - 1;
  in2#j := M[Net#b][R[Net#b]];
  R[Net#b] := R[Net#b] + 1;
  C[Net#b] := C[Net#b] - 1;
  M[Net#c][R[Net#c] + C[Net#c]] := in1#i + in2#j;
  SqnCh[Net#c][R[Net#c] + C[Net#c]] := SqnAct[Net#add];
  C[Net#c] := C[Net#c] + 1;
  SqnAct[Net#add] := SqnAct[Net#add] + 1;
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#29)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (0 <= M[Net#a][i])
  );
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#30)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (0 <= M[Net#b][i])
  );
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#31)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#32)"} R[Net#b] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#33)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#34)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][idx$] == idx$)
  );
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#35)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (SqnCh[Net#b][idx$] == idx$)
  );
  assert {:msg "  17.15: Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#36)"} SqnAct[Net#add] == R[Net#a];
  assert {:msg "  18.16: Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#37)"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][i] == SqnCh[Net#b][i])
  );
  assert {:msg "  19.16: Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#38)"} (forall i: int :: 
    (0 <= i) && (i < R[Net#a]) ==> (SqnCh[Net#a][i] == SqnCh[Net#c][i])
  );
}
procedure Net#anon$1#exit#4()
  modifies C, R, M, St, SqnCh, SqnAct;
{
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
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (0 <= M[Net#a][i])
  );
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (0 <= M[Net#b][i])
  );
  assume R[Net#a] == (R[Net#c] + C[Net#c]);
  assume R[Net#b] == (R[Net#c] + C[Net#c]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][idx$] == idx$)
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (SqnCh[Net#b][idx$] == idx$)
  );
  assume SqnAct[Net#add] == R[Net#a];
  assume (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][i] == SqnCh[Net#b][i])
  );
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#a]) ==> (SqnCh[Net#a][i] == SqnCh[Net#c][i])
  );
  assume !((R[Net#a] + C[Net#a]) < L[Net#a]);
  assume !((R[Net#b] + C[Net#b]) < L[Net#b]);
  assume !((1 <= C[Net#a]) && (1 <= C[Net#b]));
  assert {:msg "  13.14: Network action postcondition might not hold"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (0 <= M[Net#c][i])
  );
  assert {:msg "  14.14: Network action postcondition might not hold"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (SqnCh[Net#c][i] == i)
  );
  R[Net#c] := R[Net#c] + C[Net#c];
  C[Net#c] := C[Net#c] - (1 * Base#L);
  assert {:msg "  The network might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (0 <= M[Net#a][i])
  );
  assert {:msg "  The network might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#b] + C[Net#b])) ==> (0 <= M[Net#b][i])
  );
  assert {:msg "  The network might not preserve the channel invariant"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  The network might not preserve the channel invariant"} R[Net#b] == (R[Net#c] + C[Net#c]);
  assert {:msg "  The network might not preserve the channel invariant"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assert {:msg "  The network might not preserve the channel invariant"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][idx$] == idx$)
  );
  assert {:msg "  The network might not preserve the channel invariant"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (SqnCh[Net#b][idx$] == idx$)
  );
  assert {:msg "  17.15: The network might not preserve the channel invariant"} SqnAct[Net#add] == R[Net#a];
  assert {:msg "  18.16: The network might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < (R[Net#a] + C[Net#a])) ==> (SqnCh[Net#a][i] == SqnCh[Net#b][i])
  );
  assert {:msg "  19.16: The network might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < R[Net#a]) ==> (SqnCh[Net#a][i] == SqnCh[Net#c][i])
  );
  assert {:msg "  10.3: The network might leave unread tokens on channel a"} C[Net#a] == 0;
  assert {:msg "  10.3: The network might leave unread tokens on channel b"} C[Net#b] == 0;
  assert {:msg "  10.3: The network might not produce the specified number of tokens on output out"} C[Net#c] == 0;
}

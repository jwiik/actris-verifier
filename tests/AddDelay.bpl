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
  var in1: Chan (int);
  var in2: Chan (int);
  var out: Chan (int);
  assume true;
  assume true;
}
procedure Delay#anon$1#1()
  modifies C, R, M, St;
{
  var in: Chan (int);
  var out: Chan (int);
  assume true;
  assume true;
}
procedure Delay#anon$2#2()
  modifies C, R, M, St;
{
  var in: Chan (int);
  var out: Chan (int);
  assume true;
  assume true;
}
procedure Net#init#3()
  modifies C, R, M, St;
{
  var ActorParam#del#k: int;
  assume C[Net#a] == 0;
  assume R[Net#a] == 0;
  assume C[Net#b] == 0;
  assume R[Net#b] == 0;
  assume C[Net#c] == 0;
  assume R[Net#c] == 0;
  assume C[Net#d] == 0;
  assume R[Net#d] == 0;
  assume ActorParam#del#k == 0;
  M[Net#b][R[Net#b] + C[Net#b]] := ActorParam#del#k;
  C[Net#b] := C[Net#b] + 1;
  C[Net#b] := C[Net#b] - 1;
}
const unique Net#add: Actor;
const unique Net#del: Actor;
const unique Net#a: Chan (int);
const unique Net#b: Chan (int);
const unique Net#c: Chan (int);
const unique Net#d: Chan (int);
procedure Net#anon$3#entry#4()
  modifies C, R, M, St;
{
  assume L[Net#a] == (1 * Base#L);
  assume C[Net#a] == 0;
  assume C[Net#b] == 0;
  assume C[Net#c] == 0;
  assume C[Net#d] == 0;
  C[Net#b] := C[Net#b] + 1;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) <= L[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume R[Net#c] == 0;
  assume 0 <= R[Net#d];
  assume 0 <= C[Net#d];
  assume (forall i: int :: 
    (0 <= i) && (i < L[Net#a]) ==> (0 < M[Net#a][i])
  );
  assume R[Net#a] == (R[Net#c] + C[Net#c]);
  assume R[Net#b] == (R[Net#c] + C[Net#c]);
  assume R[Net#a] == (R[Net#d] + C[Net#d]);
  assume R[Net#b] == (R[Net#d] + C[Net#d]);
  assume R[Net#d] == ((R[Net#b] + C[Net#b]) - 1);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#d][idx$ - 1])
  );
  assume (forall i: int :: 
    (0 <= i) && (i < L[Net#a]) ==> (0 < M[Net#a][i])
  );
  assert {:msg "  Channel invariant might not hold on action entry (#0)"} (forall i: int :: 
    (0 <= i) && (i < L[Net#a]) ==> (0 < M[Net#a][i])
  );
  assert {:msg "  Channel invariant might not hold on action entry (#1)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Channel invariant might not hold on action entry (#2)"} R[Net#b] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Channel invariant might not hold on action entry (#3)"} R[Net#a] == (R[Net#d] + C[Net#d]);
  assert {:msg "  Channel invariant might not hold on action entry (#4)"} R[Net#b] == (R[Net#d] + C[Net#d]);
  assert {:msg "  Channel invariant might not hold on action entry (#5)"} R[Net#d] == ((R[Net#b] + C[Net#b]) - 1);
  assert {:msg "  Channel invariant might not hold on action entry (#6)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assert {:msg "  Channel invariant might not hold on action entry (#7)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assert {:msg "  Channel invariant might not hold on action entry (#8)"} (forall idx$: int :: 
    (1 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#d][idx$ - 1])
  );
}
procedure Net#anon$3#Add#anon$0#5()
  modifies C, R, M, St;
{
  var St#next: State;
  var in1#i: int;
  var in2#j: int;
  assume L[Net#a] == (1 * Base#L);
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) <= L[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume R[Net#c] == 0;
  assume 0 <= R[Net#d];
  assume 0 <= C[Net#d];
  assume (forall i: int :: 
    (0 <= i) && (i < L[Net#a]) ==> (0 < M[Net#a][i])
  );
  assume R[Net#a] == (R[Net#c] + C[Net#c]);
  assume R[Net#b] == (R[Net#c] + C[Net#c]);
  assume R[Net#a] == (R[Net#d] + C[Net#d]);
  assume R[Net#b] == (R[Net#d] + C[Net#d]);
  assume R[Net#d] == ((R[Net#b] + C[Net#b]) - 1);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#d][idx$ - 1])
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
  M[Net#d][R[Net#d] + C[Net#d]] := in1#i + in2#j;
  C[Net#d] := C[Net#d] + 1;
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#9)"} (forall i: int :: 
    (0 <= i) && (i < L[Net#a]) ==> (0 < M[Net#a][i])
  );
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#10)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#11)"} R[Net#b] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#12)"} R[Net#a] == (R[Net#d] + C[Net#d]);
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#13)"} R[Net#b] == (R[Net#d] + C[Net#d]);
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#14)"} R[Net#d] == ((R[Net#b] + C[Net#b]) - 1);
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#15)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#16)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#17)"} (forall idx$: int :: 
    (1 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#d][idx$ - 1])
  );
}
procedure Net#anon$3#Delay#anon$2#6()
  modifies C, R, M, St;
{
  var ActorParam#k: int;
  var St#next: State;
  var in#i: int;
  assume ActorParam#k == 0;
  assume L[Net#a] == (1 * Base#L);
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) <= L[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume R[Net#c] == 0;
  assume 0 <= R[Net#d];
  assume 0 <= C[Net#d];
  assume (forall i: int :: 
    (0 <= i) && (i < L[Net#a]) ==> (0 < M[Net#a][i])
  );
  assume R[Net#a] == (R[Net#c] + C[Net#c]);
  assume R[Net#b] == (R[Net#c] + C[Net#c]);
  assume R[Net#a] == (R[Net#d] + C[Net#d]);
  assume R[Net#b] == (R[Net#d] + C[Net#d]);
  assume R[Net#d] == ((R[Net#b] + C[Net#b]) - 1);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#d][idx$ - 1])
  );
  assume true;
  assume 1 <= C[Net#d];
  in#i := M[Net#d][R[Net#d]];
  R[Net#d] := R[Net#d] + 1;
  C[Net#d] := C[Net#d] - 1;
  M[Net#b][R[Net#b] + C[Net#b]] := in#i;
  C[Net#b] := C[Net#b] + 1;
  assert {:msg "  Action at 9.3 ('anon$2') for actor instance 'del' might not preserve the channel invariant (#18)"} (forall i: int :: 
    (0 <= i) && (i < L[Net#a]) ==> (0 < M[Net#a][i])
  );
  assert {:msg "  Action at 9.3 ('anon$2') for actor instance 'del' might not preserve the channel invariant (#19)"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Action at 9.3 ('anon$2') for actor instance 'del' might not preserve the channel invariant (#20)"} R[Net#b] == (R[Net#c] + C[Net#c]);
  assert {:msg "  Action at 9.3 ('anon$2') for actor instance 'del' might not preserve the channel invariant (#21)"} R[Net#a] == (R[Net#d] + C[Net#d]);
  assert {:msg "  Action at 9.3 ('anon$2') for actor instance 'del' might not preserve the channel invariant (#22)"} R[Net#b] == (R[Net#d] + C[Net#d]);
  assert {:msg "  Action at 9.3 ('anon$2') for actor instance 'del' might not preserve the channel invariant (#23)"} R[Net#d] == ((R[Net#b] + C[Net#b]) - 1);
  assert {:msg "  Action at 9.3 ('anon$2') for actor instance 'del' might not preserve the channel invariant (#24)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assert {:msg "  Action at 9.3 ('anon$2') for actor instance 'del' might not preserve the channel invariant (#25)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assert {:msg "  Action at 9.3 ('anon$2') for actor instance 'del' might not preserve the channel invariant (#26)"} (forall idx$: int :: 
    (1 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#d][idx$ - 1])
  );
}
procedure Net#anon$3#exit#7()
  modifies C, R, M, St;
{
  assume L[Net#a] == (1 * Base#L);
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) <= L[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume R[Net#c] == 0;
  assume 0 <= R[Net#d];
  assume 0 <= C[Net#d];
  assume (forall i: int :: 
    (0 <= i) && (i < L[Net#a]) ==> (0 < M[Net#a][i])
  );
  assume R[Net#a] == (R[Net#c] + C[Net#c]);
  assume R[Net#b] == (R[Net#c] + C[Net#c]);
  assume R[Net#a] == (R[Net#d] + C[Net#d]);
  assume R[Net#b] == (R[Net#d] + C[Net#d]);
  assume R[Net#d] == ((R[Net#b] + C[Net#b]) - 1);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#d][idx$ - 1])
  );
  assume !((R[Net#a] + C[Net#a]) < L[Net#a]);
  assume !((1 <= C[Net#a]) && (1 <= C[Net#b]));
  assume !(1 <= C[Net#d]);
  assert {:msg "  21.14: Network action postcondition might not hold"} (forall i: int :: 
    (1 <= i) && (i < (R[Net#c] + C[Net#c])) ==> (M[Net#c][i] == (M[Net#a][i] + M[Net#c][i - 1]))
  );
  R[Net#c] := R[Net#c] + C[Net#c];
  C[Net#c] := C[Net#c] - (1 * Base#L);
  assert {:msg "  The network might not preserve the channel invariant"} (forall i: int :: 
    (0 <= i) && (i < L[Net#a]) ==> (0 < M[Net#a][i])
  );
  assert {:msg "  The network might not preserve the channel invariant"} R[Net#a] == (R[Net#c] + C[Net#c]);
  assert {:msg "  The network might not preserve the channel invariant"} R[Net#b] == (R[Net#c] + C[Net#c]);
  assert {:msg "  The network might not preserve the channel invariant"} R[Net#a] == (R[Net#d] + C[Net#d]);
  assert {:msg "  The network might not preserve the channel invariant"} R[Net#b] == (R[Net#d] + C[Net#d]);
  assert {:msg "  The network might not preserve the channel invariant"} R[Net#d] == ((R[Net#b] + C[Net#b]) - 1);
  assert {:msg "  The network might not preserve the channel invariant"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) ==> (M[Net#c][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assert {:msg "  The network might not preserve the channel invariant"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#d] + C[Net#d])) ==> (M[Net#d][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assert {:msg "  The network might not preserve the channel invariant"} (forall idx$: int :: 
    (1 <= idx$) && (idx$ < (R[Net#b] + C[Net#b])) ==> (M[Net#b][idx$] == M[Net#d][idx$ - 1])
  );
  C[Net#b] := C[Net#b] - 1;
  assert {:msg "  19.3: The network might leave unread tokens on channel a"} C[Net#a] == 0;
  assert {:msg "  19.3: The network might leave unread tokens on channel b"} C[Net#b] == 0;
  assert {:msg "  19.3: The network might not produce the specified number of tokens on output out"} C[Net#c] == 0;
  assert {:msg "  19.3: The network might leave unread tokens on channel d"} C[Net#d] == 0;
}

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
var I: CType;
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
  modifies C, R, M, I, St;
{
  var in1: Chan (int);
  var in2: Chan (int);
  var out: Chan (int);
  assume true;
  assume true;
}
procedure Delay#anon$1#1()
  modifies C, R, M, I, St;
{
  var in: Chan (int);
  var out: Chan (int);
  assume true;
  assume true;
}
procedure Delay#anon$2#2()
  modifies C, R, M, I, St;
{
  var in: Chan (int);
  var out: Chan (int);
  assume true;
  assume true;
}
procedure Net#init#3()
  modifies C, R, M, I, St;
{
  var ActorParam#del#k: int;
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume 0 <= I[Net#c];
  assume I[Net#c] <= R[Net#c];
  assume R[Net#c] <= C[Net#c];
  assume I[Net#c] == R[Net#c];
  assume 0 <= I[Net#d];
  assume I[Net#d] <= R[Net#d];
  assume R[Net#d] <= C[Net#d];
  assume C[Net#a] == 0;
  assume R[Net#a] == 0;
  assume C[Net#b] == 0;
  assume R[Net#b] == 0;
  assume C[Net#c] == 0;
  assume R[Net#c] == 0;
  assume C[Net#d] == 0;
  assume R[Net#d] == 0;
  assume ActorParam#del#k == 0;
  M[Net#b][C[Net#b]] := ActorParam#del#k;
  C[Net#b] := C[Net#b] + 1;
  assert {:msg "  Network initialization might not establish the channel invariant (#0)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#a]) ==> (0 < M[Net#a][i])
  );
  assert {:msg "  Network initialization might not establish the channel invariant (#1)"} R[Net#a] == C[Net#c];
  assert {:msg "  Network initialization might not establish the channel invariant (#2)"} R[Net#b] == C[Net#c];
  assert {:msg "  Network initialization might not establish the channel invariant (#3)"} R[Net#a] == C[Net#d];
  assert {:msg "  Network initialization might not establish the channel invariant (#4)"} R[Net#b] == C[Net#d];
  assert {:msg "  Network initialization might not establish the channel invariant (#5)"} R[Net#d] == (C[Net#b] - 1);
  assert {:msg "  Network initialization might not establish the channel invariant (#6)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assert {:msg "  Network initialization might not establish the channel invariant (#7)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assert {:msg "  Network initialization might not establish the channel invariant (#8)"} (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == M[Net#d][idx$ - 1])
  );
  assert {:msg "  22.15: Network initialization might not establish the channel invariant (#9)"} I[Net#a] == I[Net#c];
  assert {:msg "  23.15: Network initialization might not establish the channel invariant (#10)"} M[Net#b][0] == 0;
  C[Net#b] := C[Net#b] - 1;
}
const unique Net#add: Actor;
const unique Net#del: Actor;
const unique Net#a: Chan (int);
const unique Net#b: Chan (int);
const unique Net#c: Chan (int);
const unique Net#d: Chan (int);
procedure Net#anon$3#entry#4()
  modifies C, R, M, I, St;
{
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume 0 <= I[Net#c];
  assume I[Net#c] <= R[Net#c];
  assume R[Net#c] <= C[Net#c];
  assume I[Net#c] == R[Net#c];
  assume 0 <= I[Net#d];
  assume I[Net#d] <= R[Net#d];
  assume R[Net#d] <= C[Net#d];
  assume L[Net#a] == (1 * Base#L);
  assume (R[Net#a] - I[Net#a]) <= L[Net#a];
  assume (C[Net#a] - R[Net#a]) == 0;
  assume (C[Net#b] - R[Net#b]) == 0;
  assume (C[Net#c] - R[Net#c]) == 0;
  assume (C[Net#d] - R[Net#d]) == 0;
  assume I == R;
  C[Net#b] := C[Net#b] + 1;
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#a]) ==> (0 < M[Net#a][i])
  );
  assume R[Net#a] == C[Net#c];
  assume R[Net#b] == C[Net#c];
  assume R[Net#a] == C[Net#d];
  assume R[Net#b] == C[Net#d];
  assume R[Net#d] == (C[Net#b] - 1);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == M[Net#d][idx$ - 1])
  );
  assume I[Net#a] == I[Net#c];
  assume M[Net#b][0] == 0;
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#a]) ==> (0 < M[Net#a][i])
  );
  assert {:msg "  Channel invariant might not hold on action entry (#11)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#a]) ==> (0 < M[Net#a][i])
  );
  assert {:msg "  Channel invariant might not hold on action entry (#12)"} R[Net#a] == C[Net#c];
  assert {:msg "  Channel invariant might not hold on action entry (#13)"} R[Net#b] == C[Net#c];
  assert {:msg "  Channel invariant might not hold on action entry (#14)"} R[Net#a] == C[Net#d];
  assert {:msg "  Channel invariant might not hold on action entry (#15)"} R[Net#b] == C[Net#d];
  assert {:msg "  Channel invariant might not hold on action entry (#16)"} R[Net#d] == (C[Net#b] - 1);
  assert {:msg "  Channel invariant might not hold on action entry (#17)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assert {:msg "  Channel invariant might not hold on action entry (#18)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assert {:msg "  Channel invariant might not hold on action entry (#19)"} (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == M[Net#d][idx$ - 1])
  );
  assert {:msg "  22.15: Channel invariant might not hold on action entry (#20)"} I[Net#a] == I[Net#c];
  assert {:msg "  23.15: Channel invariant might not hold on action entry (#21)"} M[Net#b][0] == 0;
}
procedure Net#anon$3#Add#anon$0#5()
  modifies C, R, M, I, St;
{
  var St#next: State;
  var in1#i: int;
  var in2#j: int;
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume 0 <= I[Net#c];
  assume I[Net#c] <= R[Net#c];
  assume R[Net#c] <= C[Net#c];
  assume I[Net#c] == R[Net#c];
  assume 0 <= I[Net#d];
  assume I[Net#d] <= R[Net#d];
  assume R[Net#d] <= C[Net#d];
  assume L[Net#a] == (1 * Base#L);
  assume (R[Net#a] - I[Net#a]) <= L[Net#a];
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#a]) ==> (0 < M[Net#a][i])
  );
  assume R[Net#a] == C[Net#c];
  assume R[Net#b] == C[Net#c];
  assume R[Net#a] == C[Net#d];
  assume R[Net#b] == C[Net#d];
  assume R[Net#d] == (C[Net#b] - 1);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == M[Net#d][idx$ - 1])
  );
  assume I[Net#a] == I[Net#c];
  assume M[Net#b][0] == 0;
  assume true;
  assume (1 <= (C[Net#a] - R[Net#a])) && (1 <= (C[Net#b] - R[Net#b]));
  in1#i := M[Net#a][R[Net#a]];
  R[Net#a] := R[Net#a] + 1;
  in2#j := M[Net#b][R[Net#b]];
  R[Net#b] := R[Net#b] + 1;
  M[Net#c][C[Net#c]] := in1#i + in2#j;
  C[Net#c] := C[Net#c] + 1;
  M[Net#d][C[Net#d]] := in1#i + in2#j;
  C[Net#d] := C[Net#d] + 1;
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#22)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#a]) ==> (0 < M[Net#a][i])
  );
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#23)"} R[Net#a] == C[Net#c];
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#24)"} R[Net#b] == C[Net#c];
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#25)"} R[Net#a] == C[Net#d];
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#26)"} R[Net#b] == C[Net#d];
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#27)"} R[Net#d] == (C[Net#b] - 1);
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#28)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#29)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assert {:msg "  Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#30)"} (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == M[Net#d][idx$ - 1])
  );
  assert {:msg "  22.15: Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#31)"} I[Net#a] == I[Net#c];
  assert {:msg "  23.15: Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#32)"} M[Net#b][0] == 0;
}
procedure Net#anon$3#Delay#anon$2#6()
  modifies C, R, M, I, St;
{
  var ActorParam#k: int;
  var St#next: State;
  var in#i: int;
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume 0 <= I[Net#c];
  assume I[Net#c] <= R[Net#c];
  assume R[Net#c] <= C[Net#c];
  assume I[Net#c] == R[Net#c];
  assume 0 <= I[Net#d];
  assume I[Net#d] <= R[Net#d];
  assume R[Net#d] <= C[Net#d];
  assume ActorParam#k == 0;
  assume L[Net#a] == (1 * Base#L);
  assume (R[Net#a] - I[Net#a]) <= L[Net#a];
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#a]) ==> (0 < M[Net#a][i])
  );
  assume R[Net#a] == C[Net#c];
  assume R[Net#b] == C[Net#c];
  assume R[Net#a] == C[Net#d];
  assume R[Net#b] == C[Net#d];
  assume R[Net#d] == (C[Net#b] - 1);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == M[Net#d][idx$ - 1])
  );
  assume I[Net#a] == I[Net#c];
  assume M[Net#b][0] == 0;
  assume true;
  assume 1 <= (C[Net#d] - R[Net#d]);
  in#i := M[Net#d][R[Net#d]];
  R[Net#d] := R[Net#d] + 1;
  M[Net#b][C[Net#b]] := in#i;
  C[Net#b] := C[Net#b] + 1;
  assert {:msg "  Action at 9.3 ('anon$2') for actor instance 'del' might not preserve the channel invariant (#33)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#a]) ==> (0 < M[Net#a][i])
  );
  assert {:msg "  Action at 9.3 ('anon$2') for actor instance 'del' might not preserve the channel invariant (#34)"} R[Net#a] == C[Net#c];
  assert {:msg "  Action at 9.3 ('anon$2') for actor instance 'del' might not preserve the channel invariant (#35)"} R[Net#b] == C[Net#c];
  assert {:msg "  Action at 9.3 ('anon$2') for actor instance 'del' might not preserve the channel invariant (#36)"} R[Net#a] == C[Net#d];
  assert {:msg "  Action at 9.3 ('anon$2') for actor instance 'del' might not preserve the channel invariant (#37)"} R[Net#b] == C[Net#d];
  assert {:msg "  Action at 9.3 ('anon$2') for actor instance 'del' might not preserve the channel invariant (#38)"} R[Net#d] == (C[Net#b] - 1);
  assert {:msg "  Action at 9.3 ('anon$2') for actor instance 'del' might not preserve the channel invariant (#39)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assert {:msg "  Action at 9.3 ('anon$2') for actor instance 'del' might not preserve the channel invariant (#40)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assert {:msg "  Action at 9.3 ('anon$2') for actor instance 'del' might not preserve the channel invariant (#41)"} (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == M[Net#d][idx$ - 1])
  );
  assert {:msg "  22.15: Action at 9.3 ('anon$2') for actor instance 'del' might not preserve the channel invariant (#42)"} I[Net#a] == I[Net#c];
  assert {:msg "  23.15: Action at 9.3 ('anon$2') for actor instance 'del' might not preserve the channel invariant (#43)"} M[Net#b][0] == 0;
}
procedure Net#anon$3#exit#7()
  modifies C, R, M, I, St;
{
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume 0 <= I[Net#c];
  assume I[Net#c] <= R[Net#c];
  assume R[Net#c] <= C[Net#c];
  assume I[Net#c] == R[Net#c];
  assume 0 <= I[Net#d];
  assume I[Net#d] <= R[Net#d];
  assume R[Net#d] <= C[Net#d];
  assume L[Net#a] == (1 * Base#L);
  assume (R[Net#a] - I[Net#a]) <= L[Net#a];
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#a]) ==> (0 < M[Net#a][i])
  );
  assume R[Net#a] == C[Net#c];
  assume R[Net#b] == C[Net#c];
  assume R[Net#a] == C[Net#d];
  assume R[Net#b] == C[Net#d];
  assume R[Net#d] == (C[Net#b] - 1);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == M[Net#d][idx$ - 1])
  );
  assume I[Net#a] == I[Net#c];
  assume M[Net#b][0] == 0;
  assume !((R[Net#a] - I[Net#a]) < L[Net#a]);
  assume !((1 <= (C[Net#a] - R[Net#a])) && (1 <= (C[Net#b] - R[Net#b])));
  assume !(1 <= (C[Net#d] - R[Net#d]));
  assert {:msg "  16.13: Network action postcondition might not hold"} M[Net#c][0] == M[Net#a][0];
  assert {:msg "  17.14: Network action postcondition might not hold"} (forall i: int :: 
    (1 <= i) && (i < C[Net#c]) ==> (M[Net#c][i] == (M[Net#a][i] + M[Net#c][i - 1]))
  );
  R[Net#c] := R[Net#c] + (1 * Base#L);
  I := R;
  assert {:msg "  The network might not preserve the channel invariant (#44)"} (forall i: int :: 
    (0 <= i) && (i < C[Net#a]) ==> (0 < M[Net#a][i])
  );
  assert {:msg "  The network might not preserve the channel invariant (#45)"} R[Net#a] == C[Net#c];
  assert {:msg "  The network might not preserve the channel invariant (#46)"} R[Net#b] == C[Net#c];
  assert {:msg "  The network might not preserve the channel invariant (#47)"} R[Net#a] == C[Net#d];
  assert {:msg "  The network might not preserve the channel invariant (#48)"} R[Net#b] == C[Net#d];
  assert {:msg "  The network might not preserve the channel invariant (#49)"} R[Net#d] == (C[Net#b] - 1);
  assert {:msg "  The network might not preserve the channel invariant (#50)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assert {:msg "  The network might not preserve the channel invariant (#51)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assert {:msg "  The network might not preserve the channel invariant (#52)"} (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == M[Net#d][idx$ - 1])
  );
  assert {:msg "  22.15: The network might not preserve the channel invariant (#53)"} I[Net#a] == I[Net#c];
  assert {:msg "  23.15: The network might not preserve the channel invariant (#54)"} M[Net#b][0] == 0;
  C[Net#b] := C[Net#b] - 1;
  assert {:msg "  14.3: The network might leave unread tokens on channel a"} (C[Net#a] - R[Net#a]) == 0;
  assert {:msg "  14.3: The network might leave unread tokens on channel b"} (C[Net#b] - R[Net#b]) == 0;
  assert {:msg "  14.3: The network might not produce the specified number of tokens on output out"} (C[Net#c] - R[Net#c]) == 0;
  assert {:msg "  14.3: The network might leave unread tokens on channel d"} (C[Net#d] - R[Net#d]) == 0;
}

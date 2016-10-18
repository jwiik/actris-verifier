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

function AT#Abs(x: int): int { if 0 <= x then x else -x }
function AT#Div(int, int): int;
function AT#Mod(int, int): int;
axiom (forall a,b: int :: AT#Div(a,b)*b + AT#Mod(a,b) == a);
axiom (forall a,b: int :: 0 <= AT#Mod(a,b) && AT#Mod(a,b) < AT#Abs(b));

// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

procedure AddSeq#anon$0#0()
  modifies C, R, M, I, St;
{
  var in: Chan (int);
  var out: Chan (int);
  assume true;
}
procedure Mod4#anon$1#1()
  modifies C, R, M, I, St;
{
  var in: Chan (int);
  var out: Chan (int);
  assume true;
}
const unique SumMod4#add: Actor;
const unique SumMod4#mod: Actor;
const unique SumMod4#a: Chan (int);
const unique SumMod4#b: Chan (int);
const unique SumMod4#c: Chan (int);
procedure SumMod4#init#2()
  modifies C, R, M, I, St;
{
  assume 0 <= I[SumMod4#a];
  assume I[SumMod4#a] <= R[SumMod4#a];
  assume R[SumMod4#a] <= C[SumMod4#a];
  assume 0 <= I[SumMod4#b];
  assume I[SumMod4#b] <= R[SumMod4#b];
  assume R[SumMod4#b] <= C[SumMod4#b];
  assume 0 <= I[SumMod4#c];
  assume I[SumMod4#c] <= R[SumMod4#c];
  assume R[SumMod4#c] <= C[SumMod4#c];
  assume I[SumMod4#c] == R[SumMod4#c];
  assume C[SumMod4#a] == 0;
  assume R[SumMod4#a] == 0;
  assume C[SumMod4#b] == 0;
  assume R[SumMod4#b] == 0;
  assume C[SumMod4#c] == 0;
  assume R[SumMod4#c] == 0;
  assert {:msg "Network initialization might not establish the channel invariant (#0)"} R[SumMod4#a] == (4 * C[SumMod4#b]);
  assert {:msg "Network initialization might not establish the channel invariant (#1)"} (4 * I[SumMod4#b]) == I[SumMod4#a];
  assert {:msg "Network initialization might not establish the channel invariant (#2)"} R[SumMod4#b] == C[SumMod4#c];
  assert {:msg "Network initialization might not establish the channel invariant (#3)"} I[SumMod4#c] == I[SumMod4#b];
  assert {:msg "Network initialization might not establish the channel invariant (#4)"} (forall idx$: int :: 
    (I[SumMod4#b] <= idx$) && (idx$ < C[SumMod4#b]) ==> (M[SumMod4#b][idx$] == (((M[SumMod4#a][4 * idx$] + M[SumMod4#a][(4 * idx$) + 1]) + M[SumMod4#a][(4 * idx$) + 2]) + M[SumMod4#a][(4 * idx$) + 3]))
  );
  assert {:msg "Network initialization might not establish the channel invariant (#5)"} (forall idx$: int :: 
    (I[SumMod4#c] <= idx$) && (idx$ < C[SumMod4#c]) ==> (M[SumMod4#c][idx$] == AT#Mod(M[SumMod4#b][idx$], 4))
  );
  I := R;
  assert {:msg "24.5: The initialization might unspecified tokens on channel a (#6)"} (C[SumMod4#a] - R[SumMod4#a]) == 0;
  assert {:msg "25.5: The initialization might unspecified tokens on channel b (#7)"} (C[SumMod4#b] - R[SumMod4#b]) == 0;
  assert {:msg "26.5: The initialization might unspecified tokens on channel c (#8)"} (C[SumMod4#c] - R[SumMod4#c]) == 0;
}
procedure SumMod4##AddSeq#anon$0#3()
  modifies C, R, M, I, St;
{
  var St#next: State;
  var in#i: int;
  var in#j: int;
  var in#k: int;
  var in#l: int;
  assume 0 <= I[SumMod4#a];
  assume I[SumMod4#a] <= R[SumMod4#a];
  assume R[SumMod4#a] <= C[SumMod4#a];
  assume 0 <= I[SumMod4#b];
  assume I[SumMod4#b] <= R[SumMod4#b];
  assume R[SumMod4#b] <= C[SumMod4#b];
  assume 0 <= I[SumMod4#c];
  assume I[SumMod4#c] <= R[SumMod4#c];
  assume R[SumMod4#c] <= C[SumMod4#c];
  assume I[SumMod4#c] == R[SumMod4#c];
  assume R[SumMod4#a] == (4 * C[SumMod4#b]);
  assume (4 * I[SumMod4#b]) == I[SumMod4#a];
  assume R[SumMod4#b] == C[SumMod4#c];
  assume I[SumMod4#c] == I[SumMod4#b];
  assume (forall idx$: int :: 
    (I[SumMod4#b] <= idx$) && (idx$ < C[SumMod4#b]) ==> (M[SumMod4#b][idx$] == (((M[SumMod4#a][4 * idx$] + M[SumMod4#a][(4 * idx$) + 1]) + M[SumMod4#a][(4 * idx$) + 2]) + M[SumMod4#a][(4 * idx$) + 3]))
  );
  assume (forall idx$: int :: 
    (I[SumMod4#c] <= idx$) && (idx$ < C[SumMod4#c]) ==> (M[SumMod4#c][idx$] == AT#Mod(M[SumMod4#b][idx$], 4))
  );
  assume true;
  assume 4 <= (C[SumMod4#a] - R[SumMod4#a]);
  in#i := M[SumMod4#a][R[SumMod4#a]];
  R[SumMod4#a] := R[SumMod4#a] + 1;
  in#j := M[SumMod4#a][R[SumMod4#a]];
  R[SumMod4#a] := R[SumMod4#a] + 1;
  in#k := M[SumMod4#a][R[SumMod4#a]];
  R[SumMod4#a] := R[SumMod4#a] + 1;
  in#l := M[SumMod4#a][R[SumMod4#a]];
  R[SumMod4#a] := R[SumMod4#a] + 1;
  M[SumMod4#b][C[SumMod4#b]] := ((in#i + in#j) + in#k) + in#l;
  C[SumMod4#b] := C[SumMod4#b] + 1;
  assert {:msg "Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#9)"} R[SumMod4#a] == (4 * C[SumMod4#b]);
  assert {:msg "Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#10)"} (4 * I[SumMod4#b]) == I[SumMod4#a];
  assert {:msg "Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#11)"} R[SumMod4#b] == C[SumMod4#c];
  assert {:msg "Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#12)"} I[SumMod4#c] == I[SumMod4#b];
  assert {:msg "Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#13)"} (forall idx$: int :: 
    (I[SumMod4#b] <= idx$) && (idx$ < C[SumMod4#b]) ==> (M[SumMod4#b][idx$] == (((M[SumMod4#a][4 * idx$] + M[SumMod4#a][(4 * idx$) + 1]) + M[SumMod4#a][(4 * idx$) + 2]) + M[SumMod4#a][(4 * idx$) + 3]))
  );
  assert {:msg "Action at 3.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#14)"} (forall idx$: int :: 
    (I[SumMod4#c] <= idx$) && (idx$ < C[SumMod4#c]) ==> (M[SumMod4#c][idx$] == AT#Mod(M[SumMod4#b][idx$], 4))
  );
}
procedure SumMod4##Mod4#anon$1#4()
  modifies C, R, M, I, St;
{
  var St#next: State;
  var in#i: int;
  assume 0 <= I[SumMod4#a];
  assume I[SumMod4#a] <= R[SumMod4#a];
  assume R[SumMod4#a] <= C[SumMod4#a];
  assume 0 <= I[SumMod4#b];
  assume I[SumMod4#b] <= R[SumMod4#b];
  assume R[SumMod4#b] <= C[SumMod4#b];
  assume 0 <= I[SumMod4#c];
  assume I[SumMod4#c] <= R[SumMod4#c];
  assume R[SumMod4#c] <= C[SumMod4#c];
  assume I[SumMod4#c] == R[SumMod4#c];
  assume R[SumMod4#a] == (4 * C[SumMod4#b]);
  assume (4 * I[SumMod4#b]) == I[SumMod4#a];
  assume R[SumMod4#b] == C[SumMod4#c];
  assume I[SumMod4#c] == I[SumMod4#b];
  assume (forall idx$: int :: 
    (I[SumMod4#b] <= idx$) && (idx$ < C[SumMod4#b]) ==> (M[SumMod4#b][idx$] == (((M[SumMod4#a][4 * idx$] + M[SumMod4#a][(4 * idx$) + 1]) + M[SumMod4#a][(4 * idx$) + 2]) + M[SumMod4#a][(4 * idx$) + 3]))
  );
  assume (forall idx$: int :: 
    (I[SumMod4#c] <= idx$) && (idx$ < C[SumMod4#c]) ==> (M[SumMod4#c][idx$] == AT#Mod(M[SumMod4#b][idx$], 4))
  );
  assume true;
  assume 1 <= (C[SumMod4#b] - R[SumMod4#b]);
  in#i := M[SumMod4#b][R[SumMod4#b]];
  R[SumMod4#b] := R[SumMod4#b] + 1;
  M[SumMod4#c][C[SumMod4#c]] := AT#Mod(in#i, 4);
  C[SumMod4#c] := C[SumMod4#c] + 1;
  assert {:msg "Action at 8.3 ('anon$1') for actor instance 'mod' might not preserve the channel invariant (#15)"} R[SumMod4#a] == (4 * C[SumMod4#b]);
  assert {:msg "Action at 8.3 ('anon$1') for actor instance 'mod' might not preserve the channel invariant (#16)"} (4 * I[SumMod4#b]) == I[SumMod4#a];
  assert {:msg "Action at 8.3 ('anon$1') for actor instance 'mod' might not preserve the channel invariant (#17)"} R[SumMod4#b] == C[SumMod4#c];
  assert {:msg "Action at 8.3 ('anon$1') for actor instance 'mod' might not preserve the channel invariant (#18)"} I[SumMod4#c] == I[SumMod4#b];
  assert {:msg "Action at 8.3 ('anon$1') for actor instance 'mod' might not preserve the channel invariant (#19)"} (forall idx$: int :: 
    (I[SumMod4#b] <= idx$) && (idx$ < C[SumMod4#b]) ==> (M[SumMod4#b][idx$] == (((M[SumMod4#a][4 * idx$] + M[SumMod4#a][(4 * idx$) + 1]) + M[SumMod4#a][(4 * idx$) + 2]) + M[SumMod4#a][(4 * idx$) + 3]))
  );
  assert {:msg "Action at 8.3 ('anon$1') for actor instance 'mod' might not preserve the channel invariant (#20)"} (forall idx$: int :: 
    (I[SumMod4#c] <= idx$) && (idx$ < C[SumMod4#c]) ==> (M[SumMod4#c][idx$] == AT#Mod(M[SumMod4#b][idx$], 4))
  );
}
procedure SumMod4#anon$2#entry#5()
  modifies C, R, M, I, St;
{
  assume 0 <= I[SumMod4#a];
  assume I[SumMod4#a] <= R[SumMod4#a];
  assume R[SumMod4#a] <= C[SumMod4#a];
  assume 0 <= I[SumMod4#b];
  assume I[SumMod4#b] <= R[SumMod4#b];
  assume R[SumMod4#b] <= C[SumMod4#b];
  assume 0 <= I[SumMod4#c];
  assume I[SumMod4#c] <= R[SumMod4#c];
  assume R[SumMod4#c] <= C[SumMod4#c];
  assume I[SumMod4#c] == R[SumMod4#c];
  assume I == R;
  assume R[SumMod4#a] == C[SumMod4#a];
  assume R[SumMod4#b] == C[SumMod4#b];
  assume R[SumMod4#c] == C[SumMod4#c];
  assume R[SumMod4#a] == (4 * C[SumMod4#b]);
  assume (4 * I[SumMod4#b]) == I[SumMod4#a];
  assume R[SumMod4#b] == C[SumMod4#c];
  assume I[SumMod4#c] == I[SumMod4#b];
  assume (forall idx$: int :: 
    (I[SumMod4#b] <= idx$) && (idx$ < C[SumMod4#b]) ==> (M[SumMod4#b][idx$] == (((M[SumMod4#a][4 * idx$] + M[SumMod4#a][(4 * idx$) + 1]) + M[SumMod4#a][(4 * idx$) + 2]) + M[SumMod4#a][(4 * idx$) + 3]))
  );
  assume (forall idx$: int :: 
    (I[SumMod4#c] <= idx$) && (idx$ < C[SumMod4#c]) ==> (M[SumMod4#c][idx$] == AT#Mod(M[SumMod4#b][idx$], 4))
  );
}
procedure SumMod4#anon$2#input#in#6()
  modifies C, R, M, I, St;
{
  assume 0 <= I[SumMod4#a];
  assume I[SumMod4#a] <= R[SumMod4#a];
  assume R[SumMod4#a] <= C[SumMod4#a];
  assume 0 <= I[SumMod4#b];
  assume I[SumMod4#b] <= R[SumMod4#b];
  assume R[SumMod4#b] <= C[SumMod4#b];
  assume 0 <= I[SumMod4#c];
  assume I[SumMod4#c] <= R[SumMod4#c];
  assume R[SumMod4#c] <= C[SumMod4#c];
  assume I[SumMod4#c] == R[SumMod4#c];
  assume C[SumMod4#a] < 64;
  assume R[SumMod4#a] == (4 * C[SumMod4#b]);
  assume (4 * I[SumMod4#b]) == I[SumMod4#a];
  assume R[SumMod4#b] == C[SumMod4#c];
  assume I[SumMod4#c] == I[SumMod4#b];
  assume (forall idx$: int :: 
    (I[SumMod4#b] <= idx$) && (idx$ < C[SumMod4#b]) ==> (M[SumMod4#b][idx$] == (((M[SumMod4#a][4 * idx$] + M[SumMod4#a][(4 * idx$) + 1]) + M[SumMod4#a][(4 * idx$) + 2]) + M[SumMod4#a][(4 * idx$) + 3]))
  );
  assume (forall idx$: int :: 
    (I[SumMod4#c] <= idx$) && (idx$ < C[SumMod4#c]) ==> (M[SumMod4#c][idx$] == AT#Mod(M[SumMod4#b][idx$], 4))
  );
  C[SumMod4#a] := C[SumMod4#a] + 1;
  assume (forall i: int :: 
    (I[SumMod4#a] <= i) && (i < C[SumMod4#a]) ==> (AT#Mod(M[SumMod4#a][i], 2) == 1)
  );
  assert {:msg "Channel invariant might be falsified by network input (#21)"} R[SumMod4#a] == (4 * C[SumMod4#b]);
  assert {:msg "Channel invariant might be falsified by network input (#22)"} (4 * I[SumMod4#b]) == I[SumMod4#a];
  assert {:msg "Channel invariant might be falsified by network input (#23)"} R[SumMod4#b] == C[SumMod4#c];
  assert {:msg "Channel invariant might be falsified by network input (#24)"} I[SumMod4#c] == I[SumMod4#b];
  assert {:msg "Channel invariant might be falsified by network input (#25)"} (forall idx$: int :: 
    (I[SumMod4#b] <= idx$) && (idx$ < C[SumMod4#b]) ==> (M[SumMod4#b][idx$] == (((M[SumMod4#a][4 * idx$] + M[SumMod4#a][(4 * idx$) + 1]) + M[SumMod4#a][(4 * idx$) + 2]) + M[SumMod4#a][(4 * idx$) + 3]))
  );
  assert {:msg "Channel invariant might be falsified by network input (#26)"} (forall idx$: int :: 
    (I[SumMod4#c] <= idx$) && (idx$ < C[SumMod4#c]) ==> (M[SumMod4#c][idx$] == AT#Mod(M[SumMod4#b][idx$], 4))
  );
}
procedure SumMod4#anon$2#exit#7()
  modifies C, R, M, I, St;
{
  assume 0 <= I[SumMod4#a];
  assume I[SumMod4#a] <= R[SumMod4#a];
  assume R[SumMod4#a] <= C[SumMod4#a];
  assume 0 <= I[SumMod4#b];
  assume I[SumMod4#b] <= R[SumMod4#b];
  assume R[SumMod4#b] <= C[SumMod4#b];
  assume 0 <= I[SumMod4#c];
  assume I[SumMod4#c] <= R[SumMod4#c];
  assume R[SumMod4#c] <= C[SumMod4#c];
  assume I[SumMod4#c] == R[SumMod4#c];
  assume R[SumMod4#a] == (4 * C[SumMod4#b]);
  assume (4 * I[SumMod4#b]) == I[SumMod4#a];
  assume R[SumMod4#b] == C[SumMod4#c];
  assume I[SumMod4#c] == I[SumMod4#b];
  assume (forall idx$: int :: 
    (I[SumMod4#b] <= idx$) && (idx$ < C[SumMod4#b]) ==> (M[SumMod4#b][idx$] == (((M[SumMod4#a][4 * idx$] + M[SumMod4#a][(4 * idx$) + 1]) + M[SumMod4#a][(4 * idx$) + 2]) + M[SumMod4#a][(4 * idx$) + 3]))
  );
  assume (forall idx$: int :: 
    (I[SumMod4#c] <= idx$) && (idx$ < C[SumMod4#c]) ==> (M[SumMod4#c][idx$] == AT#Mod(M[SumMod4#b][idx$], 4))
  );
  assume (C[SumMod4#a] - I[SumMod4#a]) == 64;
  assume (forall i: int :: 
    (I[SumMod4#a] <= i) && (i < C[SumMod4#a]) ==> (AT#Mod(M[SumMod4#a][i], 2) == 1)
  );
  assume !(4 <= (C[SumMod4#a] - R[SumMod4#a]));
  assume !(1 <= (C[SumMod4#b] - R[SumMod4#b]));
  assert {:msg "15.15: Network action postcondition might not hold (#27)"} (forall i: int :: 
    (I[SumMod4#c] <= i) && (i < C[SumMod4#c]) ==> ((M[SumMod4#c][i] == 0) || (M[SumMod4#c][i] == 2))
  );
  R[SumMod4#c] := R[SumMod4#c] + 16;
  I := R;
  assert {:msg "The network might not preserve the channel invariant (#28)"} R[SumMod4#a] == (4 * C[SumMod4#b]);
  assert {:msg "The network might not preserve the channel invariant (#29)"} (4 * I[SumMod4#b]) == I[SumMod4#a];
  assert {:msg "The network might not preserve the channel invariant (#30)"} R[SumMod4#b] == C[SumMod4#c];
  assert {:msg "The network might not preserve the channel invariant (#31)"} I[SumMod4#c] == I[SumMod4#b];
  assert {:msg "The network might not preserve the channel invariant (#32)"} (forall idx$: int :: 
    (I[SumMod4#b] <= idx$) && (idx$ < C[SumMod4#b]) ==> (M[SumMod4#b][idx$] == (((M[SumMod4#a][4 * idx$] + M[SumMod4#a][(4 * idx$) + 1]) + M[SumMod4#a][(4 * idx$) + 2]) + M[SumMod4#a][(4 * idx$) + 3]))
  );
  assert {:msg "The network might not preserve the channel invariant (#33)"} (forall idx$: int :: 
    (I[SumMod4#c] <= idx$) && (idx$ < C[SumMod4#c]) ==> (M[SumMod4#c][idx$] == AT#Mod(M[SumMod4#b][idx$], 4))
  );
  assert {:msg "13.3: The network might leave unread tokens on channel a (#34)"} C[SumMod4#a] == R[SumMod4#a];
  assert {:msg "13.3: The network might leave unread tokens on channel b (#35)"} C[SumMod4#b] == R[SumMod4#b];
  assert {:msg "13.3: The network might not produce the specified number of tokens on output out (#36)"} C[SumMod4#c] == R[SumMod4#c];
}

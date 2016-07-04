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


function AT#Abs(x: int): int { if 0 <= x then x else -x }
function AT#Div(int, int): int;
function AT#Mod(int, int): int;
axiom (forall a,b: int :: AT#Div(a,b)*b + AT#Mod(a,b) == a);
axiom (forall a,b: int :: 0 <= AT#Mod(a,b) && AT#Mod(a,b) < AT#Abs(b));

// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

procedure Rep#anon$0#0()
  modifies C, R, M, St;
{
  var IV#in#0: int;
  assume true;
  assume true;
}
procedure UnreliableRep#anon$1#1()
  modifies C, R, M, St;
{
  var IV#in#0: int;
  assume true;
  assume true;
}
procedure UnreliableRep#anon$2#2()
  modifies C, R, M, St;
{
  var IV#in#0: int;
  var IV#err#0: bool;
  assume true;
  assume true;
}
procedure Dupl#anon$3#3()
  modifies C, R, M, St;
{
  var IV#in#0: int;
  assume true;
  assume true;
}
procedure Dec#anon$4#4()
  modifies C, R, M, St;
{
  var IV#in#0: int;
  var IV#in#1: int;
  assume true;
  assume true;
}
procedure Dec#anon$5#5()
  modifies C, R, M, St;
{
  var IV#in#0: int;
  assume true;
  assume true;
}
procedure Net#init#6()
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
  assume C[Net#e] == 0;
  assume R[Net#e] == 0;
}
const unique Net#rep: Actor;
const unique Net#dup: Actor;
const unique Net#dec: Actor;
const unique Net#a: Chan (int);
const unique Net#b: Chan (bool);
const unique Net#c: Chan (int);
const unique Net#d: Chan (int);
const unique Net#e: Chan (int);
procedure Net#anon$6#entry#7()
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
  assume R[Net#d] == 0;
  assume C[Net#d] == 0;
  assume R[Net#e] == 0;
  assume C[Net#e] == 0;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) <= L[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume (R[Net#b] + C[Net#b]) <= L[Net#b];
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume 0 <= R[Net#d];
  assume 0 <= C[Net#d];
  assume 0 <= R[Net#e];
  assume 0 <= C[Net#e];
  assume R[Net#e] == 0;
  assert {:msg "  Channel invariant might not hold on action entry (#13)"} (2 * R[Net#a]) == (R[Net#c] + C[Net#c]);
  assert {:msg "  Channel invariant might not hold on action entry (#14)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) && (AT#Mod(idx$, 2) == 0) ==> (M[Net#c][idx$] == M[Net#a][AT#Div(idx$, 2)])
  );
  assert {:msg "  Channel invariant might not hold on action entry (#15)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) && (AT#Mod(idx$, 2) == 1) ==> (M[Net#c][idx$] == M[Net#a][AT#Div(idx$, 2)])
  );
}
procedure Net#anon$6#UnreliableRep#anon$1#8()
  modifies C, R, M, St;
{
  var ActionPH#y: int;
  var St#next: State;
  var in#i: int;
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
  assume 0 <= R[Net#d];
  assume 0 <= C[Net#d];
  assume 0 <= R[Net#e];
  assume 0 <= C[Net#e];
  assume R[Net#e] == 0;
  assume (2 * R[Net#a]) == (R[Net#c] + C[Net#c]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) && (AT#Mod(idx$, 2) == 0) ==> (M[Net#c][idx$] == M[Net#a][AT#Div(idx$, 2)])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) && (AT#Mod(idx$, 2) == 1) ==> (M[Net#c][idx$] == M[Net#a][AT#Div(idx$, 2)])
  );
  assume true;
  assume 1 <= C[Net#c];
  in#i := M[Net#c][R[Net#c]];
  R[Net#c] := R[Net#c] + 1;
  C[Net#c] := C[Net#c] - 1;
  M[Net#d][R[Net#d] + C[Net#d]] := in#i;
  C[Net#d] := C[Net#d] + 1;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) <= L[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume (R[Net#b] + C[Net#b]) <= L[Net#b];
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume 0 <= R[Net#d];
  assume 0 <= C[Net#d];
  assume 0 <= R[Net#e];
  assume 0 <= C[Net#e];
  assume R[Net#e] == 0;
  assert {:msg "  Action at 7.3 ('anon$1') for actor instance 'rep' might not preserve the channel invariant (#29)"} (2 * R[Net#a]) == (R[Net#c] + C[Net#c]);
  assert {:msg "  Action at 7.3 ('anon$1') for actor instance 'rep' might not preserve the channel invariant (#30)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) && (AT#Mod(idx$, 2) == 0) ==> (M[Net#c][idx$] == M[Net#a][AT#Div(idx$, 2)])
  );
  assert {:msg "  Action at 7.3 ('anon$1') for actor instance 'rep' might not preserve the channel invariant (#31)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) && (AT#Mod(idx$, 2) == 1) ==> (M[Net#c][idx$] == M[Net#a][AT#Div(idx$, 2)])
  );
}
procedure Net#anon$6#UnreliableRep#anon$2#9()
  modifies C, R, M, St;
{
  var ActionPH#y: int;
  var St#next: State;
  var in#i: int;
  var err#e: bool;
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
  assume 0 <= R[Net#d];
  assume 0 <= C[Net#d];
  assume 0 <= R[Net#e];
  assume 0 <= C[Net#e];
  assume R[Net#e] == 0;
  assume (2 * R[Net#a]) == (R[Net#c] + C[Net#c]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) && (AT#Mod(idx$, 2) == 0) ==> (M[Net#c][idx$] == M[Net#a][AT#Div(idx$, 2)])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) && (AT#Mod(idx$, 2) == 1) ==> (M[Net#c][idx$] == M[Net#a][AT#Div(idx$, 2)])
  );
  assume true;
  assume (1 <= C[Net#c]) && (1 <= C[Net#b]);
  in#i := M[Net#c][R[Net#c]];
  R[Net#c] := R[Net#c] + 1;
  C[Net#c] := C[Net#c] - 1;
  err#e := M[Net#b][R[Net#b]];
  R[Net#b] := R[Net#b] + 1;
  C[Net#b] := C[Net#b] - 1;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) <= L[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume (R[Net#b] + C[Net#b]) <= L[Net#b];
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume 0 <= R[Net#d];
  assume 0 <= C[Net#d];
  assume 0 <= R[Net#e];
  assume 0 <= C[Net#e];
  assume R[Net#e] == 0;
  assert {:msg "  Action at 8.3 ('anon$2') for actor instance 'rep' might not preserve the channel invariant (#45)"} (2 * R[Net#a]) == (R[Net#c] + C[Net#c]);
  assert {:msg "  Action at 8.3 ('anon$2') for actor instance 'rep' might not preserve the channel invariant (#46)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) && (AT#Mod(idx$, 2) == 0) ==> (M[Net#c][idx$] == M[Net#a][AT#Div(idx$, 2)])
  );
  assert {:msg "  Action at 8.3 ('anon$2') for actor instance 'rep' might not preserve the channel invariant (#47)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) && (AT#Mod(idx$, 2) == 1) ==> (M[Net#c][idx$] == M[Net#a][AT#Div(idx$, 2)])
  );
}
procedure Net#anon$6#Dupl#anon$3#10()
  modifies C, R, M, St;
{
  var ActionPH#y: int;
  var St#next: State;
  var in#i: int;
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
  assume 0 <= R[Net#d];
  assume 0 <= C[Net#d];
  assume 0 <= R[Net#e];
  assume 0 <= C[Net#e];
  assume R[Net#e] == 0;
  assume (2 * R[Net#a]) == (R[Net#c] + C[Net#c]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) && (AT#Mod(idx$, 2) == 0) ==> (M[Net#c][idx$] == M[Net#a][AT#Div(idx$, 2)])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) && (AT#Mod(idx$, 2) == 1) ==> (M[Net#c][idx$] == M[Net#a][AT#Div(idx$, 2)])
  );
  assume true;
  assume 1 <= C[Net#a];
  in#i := M[Net#a][R[Net#a]];
  R[Net#a] := R[Net#a] + 1;
  C[Net#a] := C[Net#a] - 1;
  M[Net#c][R[Net#c] + C[Net#c]] := in#i;
  C[Net#c] := C[Net#c] + 1;
  M[Net#c][R[Net#c] + C[Net#c]] := in#i;
  C[Net#c] := C[Net#c] + 1;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) <= L[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume (R[Net#b] + C[Net#b]) <= L[Net#b];
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume 0 <= R[Net#d];
  assume 0 <= C[Net#d];
  assume 0 <= R[Net#e];
  assume 0 <= C[Net#e];
  assume R[Net#e] == 0;
  assert {:msg "  Action at 13.3 ('anon$3') for actor instance 'dup' might not preserve the channel invariant (#61)"} (2 * R[Net#a]) == (R[Net#c] + C[Net#c]);
  assert {:msg "  Action at 13.3 ('anon$3') for actor instance 'dup' might not preserve the channel invariant (#62)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) && (AT#Mod(idx$, 2) == 0) ==> (M[Net#c][idx$] == M[Net#a][AT#Div(idx$, 2)])
  );
  assert {:msg "  Action at 13.3 ('anon$3') for actor instance 'dup' might not preserve the channel invariant (#63)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) && (AT#Mod(idx$, 2) == 1) ==> (M[Net#c][idx$] == M[Net#a][AT#Div(idx$, 2)])
  );
}
procedure Net#anon$6#Dec#anon$4#11()
  modifies C, R, M, St;
{
  var ActionPH#y: int;
  var St#next: State;
  var in#i: int;
  var in#j: int;
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
  assume 0 <= R[Net#d];
  assume 0 <= C[Net#d];
  assume 0 <= R[Net#e];
  assume 0 <= C[Net#e];
  assume R[Net#e] == 0;
  assume (2 * R[Net#a]) == (R[Net#c] + C[Net#c]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) && (AT#Mod(idx$, 2) == 0) ==> (M[Net#c][idx$] == M[Net#a][AT#Div(idx$, 2)])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) && (AT#Mod(idx$, 2) == 1) ==> (M[Net#c][idx$] == M[Net#a][AT#Div(idx$, 2)])
  );
  assume true;
  assume 2 <= C[Net#d];
  in#i := M[Net#d][R[Net#d]];
  R[Net#d] := R[Net#d] + 1;
  C[Net#d] := C[Net#d] - 1;
  in#j := M[Net#d][R[Net#d]];
  R[Net#d] := R[Net#d] + 1;
  C[Net#d] := C[Net#d] - 1;
  M[Net#e][R[Net#e] + C[Net#e]] := in#i;
  C[Net#e] := C[Net#e] + 1;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) <= L[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume (R[Net#b] + C[Net#b]) <= L[Net#b];
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume 0 <= R[Net#d];
  assume 0 <= C[Net#d];
  assume 0 <= R[Net#e];
  assume 0 <= C[Net#e];
  assume R[Net#e] == 0;
  assert {:msg "  Action at 17.3 ('anon$4') for actor instance 'dec' might not preserve the channel invariant (#77)"} (2 * R[Net#a]) == (R[Net#c] + C[Net#c]);
  assert {:msg "  Action at 17.3 ('anon$4') for actor instance 'dec' might not preserve the channel invariant (#78)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) && (AT#Mod(idx$, 2) == 0) ==> (M[Net#c][idx$] == M[Net#a][AT#Div(idx$, 2)])
  );
  assert {:msg "  Action at 17.3 ('anon$4') for actor instance 'dec' might not preserve the channel invariant (#79)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) && (AT#Mod(idx$, 2) == 1) ==> (M[Net#c][idx$] == M[Net#a][AT#Div(idx$, 2)])
  );
}
procedure Net#anon$6#Dec#anon$5#12()
  modifies C, R, M, St;
{
  var ActionPH#y: int;
  var St#next: State;
  var in#i: int;
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
  assume 0 <= R[Net#d];
  assume 0 <= C[Net#d];
  assume 0 <= R[Net#e];
  assume 0 <= C[Net#e];
  assume R[Net#e] == 0;
  assume (2 * R[Net#a]) == (R[Net#c] + C[Net#c]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) && (AT#Mod(idx$, 2) == 0) ==> (M[Net#c][idx$] == M[Net#a][AT#Div(idx$, 2)])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) && (AT#Mod(idx$, 2) == 1) ==> (M[Net#c][idx$] == M[Net#a][AT#Div(idx$, 2)])
  );
  assume true;
  assume 1 <= C[Net#d];
  in#i := M[Net#d][R[Net#d]];
  R[Net#d] := R[Net#d] + 1;
  C[Net#d] := C[Net#d] - 1;
  M[Net#e][R[Net#e] + C[Net#e]] := in#i;
  C[Net#e] := C[Net#e] + 1;
  assume 0 <= R[Net#a];
  assume 0 <= C[Net#a];
  assume (R[Net#a] + C[Net#a]) <= L[Net#a];
  assume 0 <= R[Net#b];
  assume 0 <= C[Net#b];
  assume (R[Net#b] + C[Net#b]) <= L[Net#b];
  assume 0 <= R[Net#c];
  assume 0 <= C[Net#c];
  assume 0 <= R[Net#d];
  assume 0 <= C[Net#d];
  assume 0 <= R[Net#e];
  assume 0 <= C[Net#e];
  assume R[Net#e] == 0;
  assert {:msg "  Action at 18.3 ('anon$5') for actor instance 'dec' might not preserve the channel invariant (#93)"} (2 * R[Net#a]) == (R[Net#c] + C[Net#c]);
  assert {:msg "  Action at 18.3 ('anon$5') for actor instance 'dec' might not preserve the channel invariant (#94)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) && (AT#Mod(idx$, 2) == 0) ==> (M[Net#c][idx$] == M[Net#a][AT#Div(idx$, 2)])
  );
  assert {:msg "  Action at 18.3 ('anon$5') for actor instance 'dec' might not preserve the channel invariant (#95)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) && (AT#Mod(idx$, 2) == 1) ==> (M[Net#c][idx$] == M[Net#a][AT#Div(idx$, 2)])
  );
}
procedure Net#anon$6#exit#13()
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
  assume 0 <= R[Net#d];
  assume 0 <= C[Net#d];
  assume 0 <= R[Net#e];
  assume 0 <= C[Net#e];
  assume R[Net#e] == 0;
  assume (2 * R[Net#a]) == (R[Net#c] + C[Net#c]);
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) && (AT#Mod(idx$, 2) == 0) ==> (M[Net#c][idx$] == M[Net#a][AT#Div(idx$, 2)])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < (R[Net#c] + C[Net#c])) && (AT#Mod(idx$, 2) == 1) ==> (M[Net#c][idx$] == M[Net#a][AT#Div(idx$, 2)])
  );
  assume !((R[Net#a] + C[Net#a]) < L[Net#a]);
  assume !((R[Net#b] + C[Net#b]) < L[Net#b]);
  assume !(1 <= C[Net#c]);
  assume !((1 <= C[Net#c]) && (1 <= C[Net#b]));
  assume !(1 <= C[Net#a]);
  assume !(2 <= C[Net#d]);
  assume !(1 <= C[Net#d]);
  ActionPH#y := M[Net#e][0];
  R[Net#e] := R[Net#e] + C[Net#e];
  C[Net#e] := C[Net#e] - (1 * Base#L);
  assert {:msg "  25.3: The network might leave unread tokens on channel a"} C[Net#a] == 0;
  assert {:msg "  25.3: The network might leave unread tokens on channel b"} C[Net#b] == 0;
  assert {:msg "  25.3: The network might leave unread tokens on channel c"} C[Net#c] == 0;
  assert {:msg "  25.3: The network might leave unread tokens on channel d"} C[Net#d] == 0;
  assert {:msg "  25.3: The network might not produce the specified number of tokens on output out"} C[Net#e] == 0;
}

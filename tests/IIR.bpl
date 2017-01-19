// ---------------------------------------------------------------
// -- Types and global variables ---------------------------------
// ---------------------------------------------------------------
type Chan;
type Field a;
type Actor;
type CType = [Chan]int;
type MType = <a>[Chan][int][Field a]a;
type State;

var M: MType;
var C: CType;
var R: CType;
var I: CType;

const unique this#: Actor;

const unique data#int: Field int;
const unique data#bool: Field bool;

type List a = [int]a;
var AT#intlst: List int;

function AT#Min(x:int, y: int): int { if x <= y then x else y }

function AT#Abs(x: int): int { if 0 <= x then x else -x }
function AT#Div(int, int): int;
function AT#Mod(int, int): int;
axiom (forall a,b: int :: AT#Div(a,b)*b + AT#Mod(a,b) == a);
axiom (forall a,b: int :: 0 <= AT#Mod(a,b) && AT#Mod(a,b) < AT#Abs(b));

function AT#BvAnd(a: int, b: int): int;

function AT#RShift(int, int): int;
function AT#LShift(int, int): int;
axiom (forall a: int :: (
  AT#RShift(a,1) == AT#Div(a,2) &&
  AT#RShift(a,2) == AT#Div(a,4) &&
  AT#RShift(a,3) == AT#Div(a,8) &&
  AT#RShift(a,4) == AT#Div(a,16) &&
  AT#RShift(a,5) == AT#Div(a,32) &&
  AT#RShift(a,6) == AT#Div(a,64) &&
  AT#RShift(a,7) == AT#Div(a,128) &&
  AT#RShift(a,8) == AT#Div(a,256) &&
  AT#RShift(a,9) == AT#Div(a,512)
));
axiom (forall a: int :: (
  AT#LShift(a,1) == a * 2 &&
  AT#LShift(a,2) == a * 4 &&
  AT#LShift(a,3) == a * 8 &&
  AT#LShift(a,4) == a * 16 &&
  AT#LShift(a,5) == a * 32 &&
  AT#LShift(a,6) == a * 64 &&
  AT#LShift(a,7) == a * 128 &&
  AT#LShift(a,8) == a * 256 &&
  AT#LShift(a,9) == a * 512
));

// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

procedure add#init#0()
  modifies C, R, M, I;
{
  var in1: Chan;
  var in2: Chan;
  var out: Chan;
  assume (in1 != in2) && (in1 != out) && (in2 != out);
  assume R[in1] == 0;
  assume R[in2] == 0;
  assume C[out] == 0;
  assert {:msg "Initialization might not establish the invariant (#0)"} R[in1] == C[out];
  assert {:msg "Initialization might not establish the invariant (#1)"} R[in2] == C[out];
  assert {:msg "Initialization might not establish the invariant (#2)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$][data#int] == (M[in1][idx$][data#int] + M[in2][idx$][data#int]))
  );
}
procedure add#anon$0#1()
  modifies C, R, M, I;
{
  var in1: Chan;
  var in2: Chan;
  var out: Chan;
  var in1#0: int;
  var in2#0: int;
  assume (in1 != in2) && (in1 != out) && (in2 != out);
  assume 0 <= R[in1];
  assume 0 <= R[in2];
  assume 0 <= C[out];
  assume R[in1] == C[out];
  assume R[in2] == C[out];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$][data#int] == (M[in1][idx$][data#int] + M[in2][idx$][data#int]))
  );
  in1#0 := M[in1][R[in1]][data#int];
  R[in1] := R[in1] + 1;
  in2#0 := M[in2][R[in2]][data#int];
  R[in2] := R[in2] + 1;
  M[out][C[out]][data#int] := in1#0 + in2#0;
  C[out] := C[out] + 1;
  assert {:msg "Action at 2.3 might not preserve invariant (#3)"} R[in1] == C[out];
  assert {:msg "Action at 2.3 might not preserve invariant (#4)"} R[in2] == C[out];
  assert {:msg "Action at 2.3 might not preserve invariant (#5)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$][data#int] == (M[in1][idx$][data#int] + M[in2][idx$][data#int]))
  );
}
procedure delay#init#2()
  modifies C, R, M, I;
{
  var in: Chan;
  var out: Chan;
  var k: int;
  assume in != out;
  assume R[in] == 0;
  assume C[out] == 0;
  M[out][C[out]][data#int] := k;
  C[out] := C[out] + 1;
  assert {:msg "6.20: Initialization might not establish the invariant (#6)"} M[out][0][data#int] == k;
  assert {:msg "Initialization might not establish the invariant (#7)"} R[in] == (C[out] - 1);
  assert {:msg "Initialization might not establish the invariant (#8)"} (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$][data#int] == M[in][idx$ - 1][data#int])
  );
}
procedure delay#anon$2#3()
  modifies C, R, M, I;
{
  var in: Chan;
  var out: Chan;
  var k: int;
  var in#0: int;
  assume in != out;
  assume 0 <= R[in];
  assume 0 <= C[out];
  assume M[out][0][data#int] == k;
  assume R[in] == (C[out] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$][data#int] == M[in][idx$ - 1][data#int])
  );
  in#0 := M[in][R[in]][data#int];
  R[in] := R[in] + 1;
  M[out][C[out]][data#int] := in#0;
  C[out] := C[out] + 1;
  assert {:msg "6.20: Action at 8.3 might not preserve invariant (#9)"} M[out][0][data#int] == k;
  assert {:msg "Action at 8.3 might not preserve invariant (#10)"} R[in] == (C[out] - 1);
  assert {:msg "Action at 8.3 might not preserve invariant (#11)"} (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$][data#int] == M[in][idx$ - 1][data#int])
  );
}
procedure mulc#init#4()
  modifies C, R, M, I;
{
  var in: Chan;
  var out: Chan;
  var c: int;
  assume in != out;
  assume R[in] == 0;
  assume C[out] == 0;
  assert {:msg "Initialization might not establish the invariant (#12)"} R[in] == C[out];
  assert {:msg "Initialization might not establish the invariant (#13)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$][data#int] == (c * M[in][idx$][data#int]))
  );
}
procedure mulc#anon$3#5()
  modifies C, R, M, I;
{
  var in: Chan;
  var out: Chan;
  var c: int;
  var in#0: int;
  assume in != out;
  assume 0 <= R[in];
  assume 0 <= C[out];
  assume R[in] == C[out];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$][data#int] == (c * M[in][idx$][data#int]))
  );
  in#0 := M[in][R[in]][data#int];
  R[in] := R[in] + 1;
  M[out][C[out]][data#int] := c * in#0;
  C[out] := C[out] + 1;
  assert {:msg "Action at 12.3 might not preserve invariant (#14)"} R[in] == C[out];
  assert {:msg "Action at 12.3 might not preserve invariant (#15)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$][data#int] == (c * M[in][idx$][data#int]))
  );
}
procedure rshift#init#6()
  modifies C, R, M, I;
{
  var in: Chan;
  var out: Chan;
  var s: int;
  assume in != out;
  assume R[in] == 0;
  assume C[out] == 0;
  assert {:msg "Initialization might not establish the invariant (#16)"} R[in] == C[out];
  assert {:msg "Initialization might not establish the invariant (#17)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$][data#int] == AT#RShift(M[in][idx$][data#int], s))
  );
}
procedure rshift#anon$4#7()
  modifies C, R, M, I;
{
  var in: Chan;
  var out: Chan;
  var s: int;
  var in#0: int;
  assume in != out;
  assume 0 <= R[in];
  assume 0 <= C[out];
  assume R[in] == C[out];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$][data#int] == AT#RShift(M[in][idx$][data#int], s))
  );
  in#0 := M[in][R[in]][data#int];
  R[in] := R[in] + 1;
  M[out][C[out]][data#int] := AT#RShift(in#0, s);
  C[out] := C[out] + 1;
  assert {:msg "Action at 16.3 might not preserve invariant (#18)"} R[in] == C[out];
  assert {:msg "Action at 16.3 might not preserve invariant (#19)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$][data#int] == AT#RShift(M[in][idx$][data#int], s))
  );
}
procedure split#init#8()
  modifies C, R, M, I;
{
  var in: Chan;
  var out1: Chan;
  var out2: Chan;
  assume (in != out1) && (in != out2) && (out1 != out2);
  assume R[in] == 0;
  assume C[out1] == 0;
  assume C[out2] == 0;
  assert {:msg "Initialization might not establish the invariant (#20)"} R[in] == C[out1];
  assert {:msg "Initialization might not establish the invariant (#21)"} R[in] == C[out2];
  assert {:msg "Initialization might not establish the invariant (#22)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out1]) ==> (M[out1][idx$][data#int] == M[in][idx$][data#int])
  );
  assert {:msg "Initialization might not establish the invariant (#23)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out2]) ==> (M[out2][idx$][data#int] == M[in][idx$][data#int])
  );
}
procedure split#anon$5#9()
  modifies C, R, M, I;
{
  var in: Chan;
  var out1: Chan;
  var out2: Chan;
  var in#0: int;
  assume (in != out1) && (in != out2) && (out1 != out2);
  assume 0 <= R[in];
  assume 0 <= C[out1];
  assume 0 <= C[out2];
  assume R[in] == C[out1];
  assume R[in] == C[out2];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out1]) ==> (M[out1][idx$][data#int] == M[in][idx$][data#int])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out2]) ==> (M[out2][idx$][data#int] == M[in][idx$][data#int])
  );
  in#0 := M[in][R[in]][data#int];
  R[in] := R[in] + 1;
  M[out1][C[out1]][data#int] := in#0;
  C[out1] := C[out1] + 1;
  M[out2][C[out2]][data#int] := in#0;
  C[out2] := C[out2] + 1;
  assert {:msg "Action at 20.3 might not preserve invariant (#24)"} R[in] == C[out1];
  assert {:msg "Action at 20.3 might not preserve invariant (#25)"} R[in] == C[out2];
  assert {:msg "Action at 20.3 might not preserve invariant (#26)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out1]) ==> (M[out1][idx$][data#int] == M[in][idx$][data#int])
  );
  assert {:msg "Action at 20.3 might not preserve invariant (#27)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out2]) ==> (M[out2][idx$][data#int] == M[in][idx$][data#int])
  );
}
procedure iir#init#10()
  modifies C, R, M, I;
{
  var iir#del1: Actor;
  var iir#mul1: Actor;
  var iir#mul2: Actor;
  var iir#rsh1: Actor;
  var iir#add1: Actor;
  var iir#spl1: Actor;
  var iir#a: Chan;
  var iir#a#data: Field (int);
  var iir#b: Chan;
  var iir#b#data: Field (int);
  var iir#c: Chan;
  var iir#c#data: Field (int);
  var iir#d: Chan;
  var iir#d#data: Field (int);
  var iir#e: Chan;
  var iir#e#data: Field (int);
  var iir#f: Chan;
  var iir#f#data: Field (int);
  var iir#g: Chan;
  var iir#g#data: Field (int);
  var iir#h: Chan;
  var iir#h#data: Field (int);
  assume (iir#del1 != iir#mul1) && (iir#del1 != iir#mul2) && (iir#del1 != iir#rsh1) && (iir#del1 != iir#add1) && (iir#del1 != iir#spl1) && (iir#mul1 != iir#mul2) && (iir#mul1 != iir#rsh1) && (iir#mul1 != iir#add1) && (iir#mul1 != iir#spl1) && (iir#mul2 != iir#rsh1) && (iir#mul2 != iir#add1) && (iir#mul2 != iir#spl1) && (iir#rsh1 != iir#add1) && (iir#rsh1 != iir#spl1) && (iir#add1 != iir#spl1);
  assume (iir#a != iir#b) && (iir#a != iir#c) && (iir#a != iir#d) && (iir#a != iir#e) && (iir#a != iir#f) && (iir#a != iir#g) && (iir#a != iir#h) && (iir#a#data != iir#b#data) && (iir#a#data != iir#c#data) && (iir#a#data != iir#d#data) && (iir#a#data != iir#e#data) && (iir#a#data != iir#f#data) && (iir#a#data != iir#g#data) && (iir#a#data != iir#h#data) && (iir#b != iir#c) && (iir#b != iir#d) && (iir#b != iir#e) && (iir#b != iir#f) && (iir#b != iir#g) && (iir#b != iir#h) && (iir#b#data != iir#c#data) && (iir#b#data != iir#d#data) && (iir#b#data != iir#e#data) && (iir#b#data != iir#f#data) && (iir#b#data != iir#g#data) && (iir#b#data != iir#h#data) && (iir#c != iir#d) && (iir#c != iir#e) && (iir#c != iir#f) && (iir#c != iir#g) && (iir#c != iir#h) && (iir#c#data != iir#d#data) && (iir#c#data != iir#e#data) && (iir#c#data != iir#f#data) && (iir#c#data != iir#g#data) && (iir#c#data != iir#h#data) && (iir#d != iir#e) && (iir#d != iir#f) && (iir#d != iir#g) && (iir#d != iir#h) && (iir#d#data != iir#e#data) && (iir#d#data != iir#f#data) && (iir#d#data != iir#g#data) && (iir#d#data != iir#h#data) && (iir#e != iir#f) && (iir#e != iir#g) && (iir#e != iir#h) && (iir#e#data != iir#f#data) && (iir#e#data != iir#g#data) && (iir#e#data != iir#h#data) && (iir#f != iir#g) && (iir#f != iir#h) && (iir#f#data != iir#g#data) && (iir#f#data != iir#h#data) && (iir#g != iir#h) && (iir#g#data != iir#h#data);
  assume 0 <= I[iir#a];
  assume I[iir#a] <= R[iir#a];
  assume R[iir#a] <= C[iir#a];
  assume 0 <= I[iir#b];
  assume I[iir#b] <= R[iir#b];
  assume R[iir#b] <= C[iir#b];
  assume 0 <= I[iir#c];
  assume I[iir#c] <= R[iir#c];
  assume R[iir#c] <= C[iir#c];
  assume 0 <= I[iir#d];
  assume I[iir#d] <= R[iir#d];
  assume R[iir#d] <= C[iir#d];
  assume 0 <= I[iir#e];
  assume I[iir#e] <= R[iir#e];
  assume R[iir#e] <= C[iir#e];
  assume 0 <= I[iir#f];
  assume I[iir#f] <= R[iir#f];
  assume R[iir#f] <= C[iir#f];
  assume 0 <= I[iir#g];
  assume I[iir#g] <= R[iir#g];
  assume R[iir#g] <= C[iir#g];
  assume 0 <= I[iir#h];
  assume I[iir#h] <= R[iir#h];
  assume R[iir#h] <= C[iir#h];
  assume I[iir#h] == R[iir#h];
  assume C[iir#a] == 0;
  assume R[iir#a] == 0;
  assume C[iir#b] == 0;
  assume R[iir#b] == 0;
  assume C[iir#c] == 0;
  assume R[iir#c] == 0;
  assume C[iir#d] == 0;
  assume R[iir#d] == 0;
  assume C[iir#e] == 0;
  assume R[iir#e] == 0;
  assume C[iir#f] == 0;
  assume R[iir#f] == 0;
  assume C[iir#g] == 0;
  assume R[iir#g] == 0;
  assume C[iir#h] == 0;
  assume R[iir#h] == 0;
  assume 0 == 0;
  M[iir#f][C[iir#f]][data#int] := 0;
  C[iir#f] := C[iir#f] + 1;
  assume 85 == 85;
  assume 171 == 171;
  assume 8 == 8;
  assert {:msg "Initialization of network 'iir' might not establish the channel invariant (#28)"} I[iir#f] == I[iir#e];
  assert {:msg "Initialization of network 'iir' might not establish the channel invariant (#29)"} I[iir#b] == I[iir#a];
  assert {:msg "Initialization of network 'iir' might not establish the channel invariant (#30)"} I[iir#e] == I[iir#d];
  assert {:msg "Initialization of network 'iir' might not establish the channel invariant (#31)"} I[iir#g] == I[iir#c];
  assert {:msg "Initialization of network 'iir' might not establish the channel invariant (#32)"} I[iir#c] == I[iir#b];
  assert {:msg "Initialization of network 'iir' might not establish the channel invariant (#33)"} I[iir#c] == I[iir#f];
  assert {:msg "Initialization of network 'iir' might not establish the channel invariant (#34)"} I[iir#d] == I[iir#g];
  assert {:msg "Initialization of network 'iir' might not establish the channel invariant (#35)"} I[iir#h] == I[iir#g];
  I := R;
  assert {:msg "30.13: Initialization of network 'iir' might not establish the network invariant (#36)"} (C[iir#f] - R[iir#f]) == 1;
  assert {:msg "Initialization of network 'iir' might not establish the network invariant: Unread tokens might be left on channel a (#37)"} (C[iir#a] - R[iir#a]) == 0;
  assert {:msg "Initialization of network 'iir' might not establish the network invariant: Unread tokens might be left on channel b (#38)"} (C[iir#b] - R[iir#b]) == 0;
  assert {:msg "Initialization of network 'iir' might not establish the network invariant: Unread tokens might be left on channel c (#39)"} (C[iir#c] - R[iir#c]) == 0;
  assert {:msg "Initialization of network 'iir' might not establish the network invariant: Unread tokens might be left on channel d (#40)"} (C[iir#d] - R[iir#d]) == 0;
  assert {:msg "Initialization of network 'iir' might not establish the network invariant: Unread tokens might be left on channel e (#41)"} (C[iir#e] - R[iir#e]) == 0;
  assert {:msg "Initialization of network 'iir' might not establish the network invariant: Unread tokens might be left on channel g (#42)"} (C[iir#g] - R[iir#g]) == 0;
  assert {:msg "Initialization of network 'iir' might not establish the network invariant: Unread tokens might be left on channel h (#43)"} (C[iir#h] - R[iir#h]) == 0;
}
procedure iir##delay#anon$2#11()
  modifies C, R, M, I;
{
  var iir#del1: Actor;
  var iir#mul1: Actor;
  var iir#mul2: Actor;
  var iir#rsh1: Actor;
  var iir#add1: Actor;
  var iir#spl1: Actor;
  var iir#a: Chan;
  var iir#a#data: Field (int);
  var iir#b: Chan;
  var iir#b#data: Field (int);
  var iir#c: Chan;
  var iir#c#data: Field (int);
  var iir#d: Chan;
  var iir#d#data: Field (int);
  var iir#e: Chan;
  var iir#e#data: Field (int);
  var iir#f: Chan;
  var iir#f#data: Field (int);
  var iir#g: Chan;
  var iir#g#data: Field (int);
  var iir#h: Chan;
  var iir#h#data: Field (int);
  var in#i: int;
  assume (iir#del1 != iir#mul1) && (iir#del1 != iir#mul2) && (iir#del1 != iir#rsh1) && (iir#del1 != iir#add1) && (iir#del1 != iir#spl1) && (iir#mul1 != iir#mul2) && (iir#mul1 != iir#rsh1) && (iir#mul1 != iir#add1) && (iir#mul1 != iir#spl1) && (iir#mul2 != iir#rsh1) && (iir#mul2 != iir#add1) && (iir#mul2 != iir#spl1) && (iir#rsh1 != iir#add1) && (iir#rsh1 != iir#spl1) && (iir#add1 != iir#spl1);
  assume (iir#a != iir#b) && (iir#a != iir#c) && (iir#a != iir#d) && (iir#a != iir#e) && (iir#a != iir#f) && (iir#a != iir#g) && (iir#a != iir#h) && (iir#a#data != iir#b#data) && (iir#a#data != iir#c#data) && (iir#a#data != iir#d#data) && (iir#a#data != iir#e#data) && (iir#a#data != iir#f#data) && (iir#a#data != iir#g#data) && (iir#a#data != iir#h#data) && (iir#b != iir#c) && (iir#b != iir#d) && (iir#b != iir#e) && (iir#b != iir#f) && (iir#b != iir#g) && (iir#b != iir#h) && (iir#b#data != iir#c#data) && (iir#b#data != iir#d#data) && (iir#b#data != iir#e#data) && (iir#b#data != iir#f#data) && (iir#b#data != iir#g#data) && (iir#b#data != iir#h#data) && (iir#c != iir#d) && (iir#c != iir#e) && (iir#c != iir#f) && (iir#c != iir#g) && (iir#c != iir#h) && (iir#c#data != iir#d#data) && (iir#c#data != iir#e#data) && (iir#c#data != iir#f#data) && (iir#c#data != iir#g#data) && (iir#c#data != iir#h#data) && (iir#d != iir#e) && (iir#d != iir#f) && (iir#d != iir#g) && (iir#d != iir#h) && (iir#d#data != iir#e#data) && (iir#d#data != iir#f#data) && (iir#d#data != iir#g#data) && (iir#d#data != iir#h#data) && (iir#e != iir#f) && (iir#e != iir#g) && (iir#e != iir#h) && (iir#e#data != iir#f#data) && (iir#e#data != iir#g#data) && (iir#e#data != iir#h#data) && (iir#f != iir#g) && (iir#f != iir#h) && (iir#f#data != iir#g#data) && (iir#f#data != iir#h#data) && (iir#g != iir#h) && (iir#g#data != iir#h#data);
  assume 0 <= I[iir#a];
  assume I[iir#a] <= R[iir#a];
  assume R[iir#a] <= C[iir#a];
  assume 0 <= I[iir#b];
  assume I[iir#b] <= R[iir#b];
  assume R[iir#b] <= C[iir#b];
  assume 0 <= I[iir#c];
  assume I[iir#c] <= R[iir#c];
  assume R[iir#c] <= C[iir#c];
  assume 0 <= I[iir#d];
  assume I[iir#d] <= R[iir#d];
  assume R[iir#d] <= C[iir#d];
  assume 0 <= I[iir#e];
  assume I[iir#e] <= R[iir#e];
  assume R[iir#e] <= C[iir#e];
  assume 0 <= I[iir#f];
  assume I[iir#f] <= R[iir#f];
  assume R[iir#f] <= C[iir#f];
  assume 0 <= I[iir#g];
  assume I[iir#g] <= R[iir#g];
  assume R[iir#g] <= C[iir#g];
  assume 0 <= I[iir#h];
  assume I[iir#h] <= R[iir#h];
  assume R[iir#h] <= C[iir#h];
  assume I[iir#h] == R[iir#h];
  assume I[iir#f] == I[iir#e];
  assume I[iir#b] == I[iir#a];
  assume I[iir#e] == I[iir#d];
  assume I[iir#g] == I[iir#c];
  assume I[iir#c] == I[iir#b];
  assume I[iir#c] == I[iir#f];
  assume I[iir#d] == I[iir#g];
  assume I[iir#h] == I[iir#g];
  assume M[iir#f][0][data#int] == 0;
  assume R[iir#e] == (C[iir#f] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[iir#f]) ==> (M[iir#f][idx$][data#int] == M[iir#e][idx$ - 1][data#int])
  );
  assume R[iir#a] == C[iir#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#b]) ==> (M[iir#b][idx$][data#int] == (85 * M[iir#a][idx$][data#int]))
  );
  assume R[iir#d] == C[iir#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#e]) ==> (M[iir#e][idx$][data#int] == (171 * M[iir#d][idx$][data#int]))
  );
  assume R[iir#c] == C[iir#g];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#g]) ==> (M[iir#g][idx$][data#int] == AT#RShift(M[iir#c][idx$][data#int], 8))
  );
  assume R[iir#b] == C[iir#c];
  assume R[iir#f] == C[iir#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#c]) ==> (M[iir#c][idx$][data#int] == (M[iir#b][idx$][data#int] + M[iir#f][idx$][data#int]))
  );
  assume R[iir#g] == C[iir#d];
  assume R[iir#g] == C[iir#h];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#d]) ==> (M[iir#d][idx$][data#int] == M[iir#g][idx$][data#int])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#h]) ==> (M[iir#h][idx$][data#int] == M[iir#g][idx$][data#int])
  );
  assume 1 <= (C[iir#e] - R[iir#e]);
  in#i := M[iir#e][R[iir#e]][data#int];
  R[iir#e] := R[iir#e] + 1;
  M[iir#f][C[iir#f]][data#int] := in#i;
  C[iir#f] := C[iir#f] + 1;
  assume M[iir#f][0][data#int] == 0;
  assume R[iir#e] == (C[iir#f] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[iir#f]) ==> (M[iir#f][idx$][data#int] == M[iir#e][idx$ - 1][data#int])
  );
  assume R[iir#a] == C[iir#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#b]) ==> (M[iir#b][idx$][data#int] == (85 * M[iir#a][idx$][data#int]))
  );
  assume R[iir#d] == C[iir#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#e]) ==> (M[iir#e][idx$][data#int] == (171 * M[iir#d][idx$][data#int]))
  );
  assume R[iir#c] == C[iir#g];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#g]) ==> (M[iir#g][idx$][data#int] == AT#RShift(M[iir#c][idx$][data#int], 8))
  );
  assume R[iir#b] == C[iir#c];
  assume R[iir#f] == C[iir#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#c]) ==> (M[iir#c][idx$][data#int] == (M[iir#b][idx$][data#int] + M[iir#f][idx$][data#int]))
  );
  assume R[iir#g] == C[iir#d];
  assume R[iir#g] == C[iir#h];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#d]) ==> (M[iir#d][idx$][data#int] == M[iir#g][idx$][data#int])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#h]) ==> (M[iir#h][idx$][data#int] == M[iir#g][idx$][data#int])
  );
  assert {:msg "Action at 8.3 ('anon$2') for actor instance 'del1' might not preserve the channel invariant (#44)"} I[iir#f] == I[iir#e];
  assert {:msg "Action at 8.3 ('anon$2') for actor instance 'del1' might not preserve the channel invariant (#45)"} I[iir#b] == I[iir#a];
  assert {:msg "Action at 8.3 ('anon$2') for actor instance 'del1' might not preserve the channel invariant (#46)"} I[iir#e] == I[iir#d];
  assert {:msg "Action at 8.3 ('anon$2') for actor instance 'del1' might not preserve the channel invariant (#47)"} I[iir#g] == I[iir#c];
  assert {:msg "Action at 8.3 ('anon$2') for actor instance 'del1' might not preserve the channel invariant (#48)"} I[iir#c] == I[iir#b];
  assert {:msg "Action at 8.3 ('anon$2') for actor instance 'del1' might not preserve the channel invariant (#49)"} I[iir#c] == I[iir#f];
  assert {:msg "Action at 8.3 ('anon$2') for actor instance 'del1' might not preserve the channel invariant (#50)"} I[iir#d] == I[iir#g];
  assert {:msg "Action at 8.3 ('anon$2') for actor instance 'del1' might not preserve the channel invariant (#51)"} I[iir#h] == I[iir#g];
}
procedure iir##mulc#anon$3#12()
  modifies C, R, M, I;
{
  var iir#del1: Actor;
  var iir#mul1: Actor;
  var iir#mul2: Actor;
  var iir#rsh1: Actor;
  var iir#add1: Actor;
  var iir#spl1: Actor;
  var iir#a: Chan;
  var iir#a#data: Field (int);
  var iir#b: Chan;
  var iir#b#data: Field (int);
  var iir#c: Chan;
  var iir#c#data: Field (int);
  var iir#d: Chan;
  var iir#d#data: Field (int);
  var iir#e: Chan;
  var iir#e#data: Field (int);
  var iir#f: Chan;
  var iir#f#data: Field (int);
  var iir#g: Chan;
  var iir#g#data: Field (int);
  var iir#h: Chan;
  var iir#h#data: Field (int);
  var in#i: int;
  assume (iir#del1 != iir#mul1) && (iir#del1 != iir#mul2) && (iir#del1 != iir#rsh1) && (iir#del1 != iir#add1) && (iir#del1 != iir#spl1) && (iir#mul1 != iir#mul2) && (iir#mul1 != iir#rsh1) && (iir#mul1 != iir#add1) && (iir#mul1 != iir#spl1) && (iir#mul2 != iir#rsh1) && (iir#mul2 != iir#add1) && (iir#mul2 != iir#spl1) && (iir#rsh1 != iir#add1) && (iir#rsh1 != iir#spl1) && (iir#add1 != iir#spl1);
  assume (iir#a != iir#b) && (iir#a != iir#c) && (iir#a != iir#d) && (iir#a != iir#e) && (iir#a != iir#f) && (iir#a != iir#g) && (iir#a != iir#h) && (iir#a#data != iir#b#data) && (iir#a#data != iir#c#data) && (iir#a#data != iir#d#data) && (iir#a#data != iir#e#data) && (iir#a#data != iir#f#data) && (iir#a#data != iir#g#data) && (iir#a#data != iir#h#data) && (iir#b != iir#c) && (iir#b != iir#d) && (iir#b != iir#e) && (iir#b != iir#f) && (iir#b != iir#g) && (iir#b != iir#h) && (iir#b#data != iir#c#data) && (iir#b#data != iir#d#data) && (iir#b#data != iir#e#data) && (iir#b#data != iir#f#data) && (iir#b#data != iir#g#data) && (iir#b#data != iir#h#data) && (iir#c != iir#d) && (iir#c != iir#e) && (iir#c != iir#f) && (iir#c != iir#g) && (iir#c != iir#h) && (iir#c#data != iir#d#data) && (iir#c#data != iir#e#data) && (iir#c#data != iir#f#data) && (iir#c#data != iir#g#data) && (iir#c#data != iir#h#data) && (iir#d != iir#e) && (iir#d != iir#f) && (iir#d != iir#g) && (iir#d != iir#h) && (iir#d#data != iir#e#data) && (iir#d#data != iir#f#data) && (iir#d#data != iir#g#data) && (iir#d#data != iir#h#data) && (iir#e != iir#f) && (iir#e != iir#g) && (iir#e != iir#h) && (iir#e#data != iir#f#data) && (iir#e#data != iir#g#data) && (iir#e#data != iir#h#data) && (iir#f != iir#g) && (iir#f != iir#h) && (iir#f#data != iir#g#data) && (iir#f#data != iir#h#data) && (iir#g != iir#h) && (iir#g#data != iir#h#data);
  assume 0 <= I[iir#a];
  assume I[iir#a] <= R[iir#a];
  assume R[iir#a] <= C[iir#a];
  assume 0 <= I[iir#b];
  assume I[iir#b] <= R[iir#b];
  assume R[iir#b] <= C[iir#b];
  assume 0 <= I[iir#c];
  assume I[iir#c] <= R[iir#c];
  assume R[iir#c] <= C[iir#c];
  assume 0 <= I[iir#d];
  assume I[iir#d] <= R[iir#d];
  assume R[iir#d] <= C[iir#d];
  assume 0 <= I[iir#e];
  assume I[iir#e] <= R[iir#e];
  assume R[iir#e] <= C[iir#e];
  assume 0 <= I[iir#f];
  assume I[iir#f] <= R[iir#f];
  assume R[iir#f] <= C[iir#f];
  assume 0 <= I[iir#g];
  assume I[iir#g] <= R[iir#g];
  assume R[iir#g] <= C[iir#g];
  assume 0 <= I[iir#h];
  assume I[iir#h] <= R[iir#h];
  assume R[iir#h] <= C[iir#h];
  assume I[iir#h] == R[iir#h];
  assume I[iir#f] == I[iir#e];
  assume I[iir#b] == I[iir#a];
  assume I[iir#e] == I[iir#d];
  assume I[iir#g] == I[iir#c];
  assume I[iir#c] == I[iir#b];
  assume I[iir#c] == I[iir#f];
  assume I[iir#d] == I[iir#g];
  assume I[iir#h] == I[iir#g];
  assume M[iir#f][0][data#int] == 0;
  assume R[iir#e] == (C[iir#f] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[iir#f]) ==> (M[iir#f][idx$][data#int] == M[iir#e][idx$ - 1][data#int])
  );
  assume R[iir#a] == C[iir#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#b]) ==> (M[iir#b][idx$][data#int] == (85 * M[iir#a][idx$][data#int]))
  );
  assume R[iir#d] == C[iir#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#e]) ==> (M[iir#e][idx$][data#int] == (171 * M[iir#d][idx$][data#int]))
  );
  assume R[iir#c] == C[iir#g];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#g]) ==> (M[iir#g][idx$][data#int] == AT#RShift(M[iir#c][idx$][data#int], 8))
  );
  assume R[iir#b] == C[iir#c];
  assume R[iir#f] == C[iir#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#c]) ==> (M[iir#c][idx$][data#int] == (M[iir#b][idx$][data#int] + M[iir#f][idx$][data#int]))
  );
  assume R[iir#g] == C[iir#d];
  assume R[iir#g] == C[iir#h];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#d]) ==> (M[iir#d][idx$][data#int] == M[iir#g][idx$][data#int])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#h]) ==> (M[iir#h][idx$][data#int] == M[iir#g][idx$][data#int])
  );
  assume 1 <= (C[iir#a] - R[iir#a]);
  in#i := M[iir#a][R[iir#a]][data#int];
  R[iir#a] := R[iir#a] + 1;
  M[iir#b][C[iir#b]][data#int] := 85 * in#i;
  C[iir#b] := C[iir#b] + 1;
  assume M[iir#f][0][data#int] == 0;
  assume R[iir#e] == (C[iir#f] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[iir#f]) ==> (M[iir#f][idx$][data#int] == M[iir#e][idx$ - 1][data#int])
  );
  assume R[iir#a] == C[iir#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#b]) ==> (M[iir#b][idx$][data#int] == (85 * M[iir#a][idx$][data#int]))
  );
  assume R[iir#d] == C[iir#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#e]) ==> (M[iir#e][idx$][data#int] == (171 * M[iir#d][idx$][data#int]))
  );
  assume R[iir#c] == C[iir#g];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#g]) ==> (M[iir#g][idx$][data#int] == AT#RShift(M[iir#c][idx$][data#int], 8))
  );
  assume R[iir#b] == C[iir#c];
  assume R[iir#f] == C[iir#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#c]) ==> (M[iir#c][idx$][data#int] == (M[iir#b][idx$][data#int] + M[iir#f][idx$][data#int]))
  );
  assume R[iir#g] == C[iir#d];
  assume R[iir#g] == C[iir#h];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#d]) ==> (M[iir#d][idx$][data#int] == M[iir#g][idx$][data#int])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#h]) ==> (M[iir#h][idx$][data#int] == M[iir#g][idx$][data#int])
  );
  assert {:msg "Action at 12.3 ('anon$3') for actor instance 'mul1' might not preserve the channel invariant (#52)"} I[iir#f] == I[iir#e];
  assert {:msg "Action at 12.3 ('anon$3') for actor instance 'mul1' might not preserve the channel invariant (#53)"} I[iir#b] == I[iir#a];
  assert {:msg "Action at 12.3 ('anon$3') for actor instance 'mul1' might not preserve the channel invariant (#54)"} I[iir#e] == I[iir#d];
  assert {:msg "Action at 12.3 ('anon$3') for actor instance 'mul1' might not preserve the channel invariant (#55)"} I[iir#g] == I[iir#c];
  assert {:msg "Action at 12.3 ('anon$3') for actor instance 'mul1' might not preserve the channel invariant (#56)"} I[iir#c] == I[iir#b];
  assert {:msg "Action at 12.3 ('anon$3') for actor instance 'mul1' might not preserve the channel invariant (#57)"} I[iir#c] == I[iir#f];
  assert {:msg "Action at 12.3 ('anon$3') for actor instance 'mul1' might not preserve the channel invariant (#58)"} I[iir#d] == I[iir#g];
  assert {:msg "Action at 12.3 ('anon$3') for actor instance 'mul1' might not preserve the channel invariant (#59)"} I[iir#h] == I[iir#g];
}
procedure iir##mulc#anon$3#13()
  modifies C, R, M, I;
{
  var iir#del1: Actor;
  var iir#mul1: Actor;
  var iir#mul2: Actor;
  var iir#rsh1: Actor;
  var iir#add1: Actor;
  var iir#spl1: Actor;
  var iir#a: Chan;
  var iir#a#data: Field (int);
  var iir#b: Chan;
  var iir#b#data: Field (int);
  var iir#c: Chan;
  var iir#c#data: Field (int);
  var iir#d: Chan;
  var iir#d#data: Field (int);
  var iir#e: Chan;
  var iir#e#data: Field (int);
  var iir#f: Chan;
  var iir#f#data: Field (int);
  var iir#g: Chan;
  var iir#g#data: Field (int);
  var iir#h: Chan;
  var iir#h#data: Field (int);
  var in#i: int;
  assume (iir#del1 != iir#mul1) && (iir#del1 != iir#mul2) && (iir#del1 != iir#rsh1) && (iir#del1 != iir#add1) && (iir#del1 != iir#spl1) && (iir#mul1 != iir#mul2) && (iir#mul1 != iir#rsh1) && (iir#mul1 != iir#add1) && (iir#mul1 != iir#spl1) && (iir#mul2 != iir#rsh1) && (iir#mul2 != iir#add1) && (iir#mul2 != iir#spl1) && (iir#rsh1 != iir#add1) && (iir#rsh1 != iir#spl1) && (iir#add1 != iir#spl1);
  assume (iir#a != iir#b) && (iir#a != iir#c) && (iir#a != iir#d) && (iir#a != iir#e) && (iir#a != iir#f) && (iir#a != iir#g) && (iir#a != iir#h) && (iir#a#data != iir#b#data) && (iir#a#data != iir#c#data) && (iir#a#data != iir#d#data) && (iir#a#data != iir#e#data) && (iir#a#data != iir#f#data) && (iir#a#data != iir#g#data) && (iir#a#data != iir#h#data) && (iir#b != iir#c) && (iir#b != iir#d) && (iir#b != iir#e) && (iir#b != iir#f) && (iir#b != iir#g) && (iir#b != iir#h) && (iir#b#data != iir#c#data) && (iir#b#data != iir#d#data) && (iir#b#data != iir#e#data) && (iir#b#data != iir#f#data) && (iir#b#data != iir#g#data) && (iir#b#data != iir#h#data) && (iir#c != iir#d) && (iir#c != iir#e) && (iir#c != iir#f) && (iir#c != iir#g) && (iir#c != iir#h) && (iir#c#data != iir#d#data) && (iir#c#data != iir#e#data) && (iir#c#data != iir#f#data) && (iir#c#data != iir#g#data) && (iir#c#data != iir#h#data) && (iir#d != iir#e) && (iir#d != iir#f) && (iir#d != iir#g) && (iir#d != iir#h) && (iir#d#data != iir#e#data) && (iir#d#data != iir#f#data) && (iir#d#data != iir#g#data) && (iir#d#data != iir#h#data) && (iir#e != iir#f) && (iir#e != iir#g) && (iir#e != iir#h) && (iir#e#data != iir#f#data) && (iir#e#data != iir#g#data) && (iir#e#data != iir#h#data) && (iir#f != iir#g) && (iir#f != iir#h) && (iir#f#data != iir#g#data) && (iir#f#data != iir#h#data) && (iir#g != iir#h) && (iir#g#data != iir#h#data);
  assume 0 <= I[iir#a];
  assume I[iir#a] <= R[iir#a];
  assume R[iir#a] <= C[iir#a];
  assume 0 <= I[iir#b];
  assume I[iir#b] <= R[iir#b];
  assume R[iir#b] <= C[iir#b];
  assume 0 <= I[iir#c];
  assume I[iir#c] <= R[iir#c];
  assume R[iir#c] <= C[iir#c];
  assume 0 <= I[iir#d];
  assume I[iir#d] <= R[iir#d];
  assume R[iir#d] <= C[iir#d];
  assume 0 <= I[iir#e];
  assume I[iir#e] <= R[iir#e];
  assume R[iir#e] <= C[iir#e];
  assume 0 <= I[iir#f];
  assume I[iir#f] <= R[iir#f];
  assume R[iir#f] <= C[iir#f];
  assume 0 <= I[iir#g];
  assume I[iir#g] <= R[iir#g];
  assume R[iir#g] <= C[iir#g];
  assume 0 <= I[iir#h];
  assume I[iir#h] <= R[iir#h];
  assume R[iir#h] <= C[iir#h];
  assume I[iir#h] == R[iir#h];
  assume I[iir#f] == I[iir#e];
  assume I[iir#b] == I[iir#a];
  assume I[iir#e] == I[iir#d];
  assume I[iir#g] == I[iir#c];
  assume I[iir#c] == I[iir#b];
  assume I[iir#c] == I[iir#f];
  assume I[iir#d] == I[iir#g];
  assume I[iir#h] == I[iir#g];
  assume M[iir#f][0][data#int] == 0;
  assume R[iir#e] == (C[iir#f] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[iir#f]) ==> (M[iir#f][idx$][data#int] == M[iir#e][idx$ - 1][data#int])
  );
  assume R[iir#a] == C[iir#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#b]) ==> (M[iir#b][idx$][data#int] == (85 * M[iir#a][idx$][data#int]))
  );
  assume R[iir#d] == C[iir#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#e]) ==> (M[iir#e][idx$][data#int] == (171 * M[iir#d][idx$][data#int]))
  );
  assume R[iir#c] == C[iir#g];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#g]) ==> (M[iir#g][idx$][data#int] == AT#RShift(M[iir#c][idx$][data#int], 8))
  );
  assume R[iir#b] == C[iir#c];
  assume R[iir#f] == C[iir#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#c]) ==> (M[iir#c][idx$][data#int] == (M[iir#b][idx$][data#int] + M[iir#f][idx$][data#int]))
  );
  assume R[iir#g] == C[iir#d];
  assume R[iir#g] == C[iir#h];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#d]) ==> (M[iir#d][idx$][data#int] == M[iir#g][idx$][data#int])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#h]) ==> (M[iir#h][idx$][data#int] == M[iir#g][idx$][data#int])
  );
  assume 1 <= (C[iir#d] - R[iir#d]);
  in#i := M[iir#d][R[iir#d]][data#int];
  R[iir#d] := R[iir#d] + 1;
  M[iir#e][C[iir#e]][data#int] := 171 * in#i;
  C[iir#e] := C[iir#e] + 1;
  assume M[iir#f][0][data#int] == 0;
  assume R[iir#e] == (C[iir#f] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[iir#f]) ==> (M[iir#f][idx$][data#int] == M[iir#e][idx$ - 1][data#int])
  );
  assume R[iir#a] == C[iir#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#b]) ==> (M[iir#b][idx$][data#int] == (85 * M[iir#a][idx$][data#int]))
  );
  assume R[iir#d] == C[iir#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#e]) ==> (M[iir#e][idx$][data#int] == (171 * M[iir#d][idx$][data#int]))
  );
  assume R[iir#c] == C[iir#g];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#g]) ==> (M[iir#g][idx$][data#int] == AT#RShift(M[iir#c][idx$][data#int], 8))
  );
  assume R[iir#b] == C[iir#c];
  assume R[iir#f] == C[iir#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#c]) ==> (M[iir#c][idx$][data#int] == (M[iir#b][idx$][data#int] + M[iir#f][idx$][data#int]))
  );
  assume R[iir#g] == C[iir#d];
  assume R[iir#g] == C[iir#h];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#d]) ==> (M[iir#d][idx$][data#int] == M[iir#g][idx$][data#int])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#h]) ==> (M[iir#h][idx$][data#int] == M[iir#g][idx$][data#int])
  );
  assert {:msg "Action at 12.3 ('anon$3') for actor instance 'mul2' might not preserve the channel invariant (#60)"} I[iir#f] == I[iir#e];
  assert {:msg "Action at 12.3 ('anon$3') for actor instance 'mul2' might not preserve the channel invariant (#61)"} I[iir#b] == I[iir#a];
  assert {:msg "Action at 12.3 ('anon$3') for actor instance 'mul2' might not preserve the channel invariant (#62)"} I[iir#e] == I[iir#d];
  assert {:msg "Action at 12.3 ('anon$3') for actor instance 'mul2' might not preserve the channel invariant (#63)"} I[iir#g] == I[iir#c];
  assert {:msg "Action at 12.3 ('anon$3') for actor instance 'mul2' might not preserve the channel invariant (#64)"} I[iir#c] == I[iir#b];
  assert {:msg "Action at 12.3 ('anon$3') for actor instance 'mul2' might not preserve the channel invariant (#65)"} I[iir#c] == I[iir#f];
  assert {:msg "Action at 12.3 ('anon$3') for actor instance 'mul2' might not preserve the channel invariant (#66)"} I[iir#d] == I[iir#g];
  assert {:msg "Action at 12.3 ('anon$3') for actor instance 'mul2' might not preserve the channel invariant (#67)"} I[iir#h] == I[iir#g];
}
procedure iir##rshift#anon$4#14()
  modifies C, R, M, I;
{
  var iir#del1: Actor;
  var iir#mul1: Actor;
  var iir#mul2: Actor;
  var iir#rsh1: Actor;
  var iir#add1: Actor;
  var iir#spl1: Actor;
  var iir#a: Chan;
  var iir#a#data: Field (int);
  var iir#b: Chan;
  var iir#b#data: Field (int);
  var iir#c: Chan;
  var iir#c#data: Field (int);
  var iir#d: Chan;
  var iir#d#data: Field (int);
  var iir#e: Chan;
  var iir#e#data: Field (int);
  var iir#f: Chan;
  var iir#f#data: Field (int);
  var iir#g: Chan;
  var iir#g#data: Field (int);
  var iir#h: Chan;
  var iir#h#data: Field (int);
  var in#i: int;
  assume (iir#del1 != iir#mul1) && (iir#del1 != iir#mul2) && (iir#del1 != iir#rsh1) && (iir#del1 != iir#add1) && (iir#del1 != iir#spl1) && (iir#mul1 != iir#mul2) && (iir#mul1 != iir#rsh1) && (iir#mul1 != iir#add1) && (iir#mul1 != iir#spl1) && (iir#mul2 != iir#rsh1) && (iir#mul2 != iir#add1) && (iir#mul2 != iir#spl1) && (iir#rsh1 != iir#add1) && (iir#rsh1 != iir#spl1) && (iir#add1 != iir#spl1);
  assume (iir#a != iir#b) && (iir#a != iir#c) && (iir#a != iir#d) && (iir#a != iir#e) && (iir#a != iir#f) && (iir#a != iir#g) && (iir#a != iir#h) && (iir#a#data != iir#b#data) && (iir#a#data != iir#c#data) && (iir#a#data != iir#d#data) && (iir#a#data != iir#e#data) && (iir#a#data != iir#f#data) && (iir#a#data != iir#g#data) && (iir#a#data != iir#h#data) && (iir#b != iir#c) && (iir#b != iir#d) && (iir#b != iir#e) && (iir#b != iir#f) && (iir#b != iir#g) && (iir#b != iir#h) && (iir#b#data != iir#c#data) && (iir#b#data != iir#d#data) && (iir#b#data != iir#e#data) && (iir#b#data != iir#f#data) && (iir#b#data != iir#g#data) && (iir#b#data != iir#h#data) && (iir#c != iir#d) && (iir#c != iir#e) && (iir#c != iir#f) && (iir#c != iir#g) && (iir#c != iir#h) && (iir#c#data != iir#d#data) && (iir#c#data != iir#e#data) && (iir#c#data != iir#f#data) && (iir#c#data != iir#g#data) && (iir#c#data != iir#h#data) && (iir#d != iir#e) && (iir#d != iir#f) && (iir#d != iir#g) && (iir#d != iir#h) && (iir#d#data != iir#e#data) && (iir#d#data != iir#f#data) && (iir#d#data != iir#g#data) && (iir#d#data != iir#h#data) && (iir#e != iir#f) && (iir#e != iir#g) && (iir#e != iir#h) && (iir#e#data != iir#f#data) && (iir#e#data != iir#g#data) && (iir#e#data != iir#h#data) && (iir#f != iir#g) && (iir#f != iir#h) && (iir#f#data != iir#g#data) && (iir#f#data != iir#h#data) && (iir#g != iir#h) && (iir#g#data != iir#h#data);
  assume 0 <= I[iir#a];
  assume I[iir#a] <= R[iir#a];
  assume R[iir#a] <= C[iir#a];
  assume 0 <= I[iir#b];
  assume I[iir#b] <= R[iir#b];
  assume R[iir#b] <= C[iir#b];
  assume 0 <= I[iir#c];
  assume I[iir#c] <= R[iir#c];
  assume R[iir#c] <= C[iir#c];
  assume 0 <= I[iir#d];
  assume I[iir#d] <= R[iir#d];
  assume R[iir#d] <= C[iir#d];
  assume 0 <= I[iir#e];
  assume I[iir#e] <= R[iir#e];
  assume R[iir#e] <= C[iir#e];
  assume 0 <= I[iir#f];
  assume I[iir#f] <= R[iir#f];
  assume R[iir#f] <= C[iir#f];
  assume 0 <= I[iir#g];
  assume I[iir#g] <= R[iir#g];
  assume R[iir#g] <= C[iir#g];
  assume 0 <= I[iir#h];
  assume I[iir#h] <= R[iir#h];
  assume R[iir#h] <= C[iir#h];
  assume I[iir#h] == R[iir#h];
  assume I[iir#f] == I[iir#e];
  assume I[iir#b] == I[iir#a];
  assume I[iir#e] == I[iir#d];
  assume I[iir#g] == I[iir#c];
  assume I[iir#c] == I[iir#b];
  assume I[iir#c] == I[iir#f];
  assume I[iir#d] == I[iir#g];
  assume I[iir#h] == I[iir#g];
  assume M[iir#f][0][data#int] == 0;
  assume R[iir#e] == (C[iir#f] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[iir#f]) ==> (M[iir#f][idx$][data#int] == M[iir#e][idx$ - 1][data#int])
  );
  assume R[iir#a] == C[iir#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#b]) ==> (M[iir#b][idx$][data#int] == (85 * M[iir#a][idx$][data#int]))
  );
  assume R[iir#d] == C[iir#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#e]) ==> (M[iir#e][idx$][data#int] == (171 * M[iir#d][idx$][data#int]))
  );
  assume R[iir#c] == C[iir#g];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#g]) ==> (M[iir#g][idx$][data#int] == AT#RShift(M[iir#c][idx$][data#int], 8))
  );
  assume R[iir#b] == C[iir#c];
  assume R[iir#f] == C[iir#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#c]) ==> (M[iir#c][idx$][data#int] == (M[iir#b][idx$][data#int] + M[iir#f][idx$][data#int]))
  );
  assume R[iir#g] == C[iir#d];
  assume R[iir#g] == C[iir#h];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#d]) ==> (M[iir#d][idx$][data#int] == M[iir#g][idx$][data#int])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#h]) ==> (M[iir#h][idx$][data#int] == M[iir#g][idx$][data#int])
  );
  assume 1 <= (C[iir#c] - R[iir#c]);
  in#i := M[iir#c][R[iir#c]][data#int];
  R[iir#c] := R[iir#c] + 1;
  M[iir#g][C[iir#g]][data#int] := AT#RShift(in#i, 8);
  C[iir#g] := C[iir#g] + 1;
  assume M[iir#f][0][data#int] == 0;
  assume R[iir#e] == (C[iir#f] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[iir#f]) ==> (M[iir#f][idx$][data#int] == M[iir#e][idx$ - 1][data#int])
  );
  assume R[iir#a] == C[iir#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#b]) ==> (M[iir#b][idx$][data#int] == (85 * M[iir#a][idx$][data#int]))
  );
  assume R[iir#d] == C[iir#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#e]) ==> (M[iir#e][idx$][data#int] == (171 * M[iir#d][idx$][data#int]))
  );
  assume R[iir#c] == C[iir#g];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#g]) ==> (M[iir#g][idx$][data#int] == AT#RShift(M[iir#c][idx$][data#int], 8))
  );
  assume R[iir#b] == C[iir#c];
  assume R[iir#f] == C[iir#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#c]) ==> (M[iir#c][idx$][data#int] == (M[iir#b][idx$][data#int] + M[iir#f][idx$][data#int]))
  );
  assume R[iir#g] == C[iir#d];
  assume R[iir#g] == C[iir#h];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#d]) ==> (M[iir#d][idx$][data#int] == M[iir#g][idx$][data#int])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#h]) ==> (M[iir#h][idx$][data#int] == M[iir#g][idx$][data#int])
  );
  assert {:msg "Action at 16.3 ('anon$4') for actor instance 'rsh1' might not preserve the channel invariant (#68)"} I[iir#f] == I[iir#e];
  assert {:msg "Action at 16.3 ('anon$4') for actor instance 'rsh1' might not preserve the channel invariant (#69)"} I[iir#b] == I[iir#a];
  assert {:msg "Action at 16.3 ('anon$4') for actor instance 'rsh1' might not preserve the channel invariant (#70)"} I[iir#e] == I[iir#d];
  assert {:msg "Action at 16.3 ('anon$4') for actor instance 'rsh1' might not preserve the channel invariant (#71)"} I[iir#g] == I[iir#c];
  assert {:msg "Action at 16.3 ('anon$4') for actor instance 'rsh1' might not preserve the channel invariant (#72)"} I[iir#c] == I[iir#b];
  assert {:msg "Action at 16.3 ('anon$4') for actor instance 'rsh1' might not preserve the channel invariant (#73)"} I[iir#c] == I[iir#f];
  assert {:msg "Action at 16.3 ('anon$4') for actor instance 'rsh1' might not preserve the channel invariant (#74)"} I[iir#d] == I[iir#g];
  assert {:msg "Action at 16.3 ('anon$4') for actor instance 'rsh1' might not preserve the channel invariant (#75)"} I[iir#h] == I[iir#g];
}
procedure iir##add#anon$0#15()
  modifies C, R, M, I;
{
  var iir#del1: Actor;
  var iir#mul1: Actor;
  var iir#mul2: Actor;
  var iir#rsh1: Actor;
  var iir#add1: Actor;
  var iir#spl1: Actor;
  var iir#a: Chan;
  var iir#a#data: Field (int);
  var iir#b: Chan;
  var iir#b#data: Field (int);
  var iir#c: Chan;
  var iir#c#data: Field (int);
  var iir#d: Chan;
  var iir#d#data: Field (int);
  var iir#e: Chan;
  var iir#e#data: Field (int);
  var iir#f: Chan;
  var iir#f#data: Field (int);
  var iir#g: Chan;
  var iir#g#data: Field (int);
  var iir#h: Chan;
  var iir#h#data: Field (int);
  var in1#i: int;
  var in2#j: int;
  assume (iir#del1 != iir#mul1) && (iir#del1 != iir#mul2) && (iir#del1 != iir#rsh1) && (iir#del1 != iir#add1) && (iir#del1 != iir#spl1) && (iir#mul1 != iir#mul2) && (iir#mul1 != iir#rsh1) && (iir#mul1 != iir#add1) && (iir#mul1 != iir#spl1) && (iir#mul2 != iir#rsh1) && (iir#mul2 != iir#add1) && (iir#mul2 != iir#spl1) && (iir#rsh1 != iir#add1) && (iir#rsh1 != iir#spl1) && (iir#add1 != iir#spl1);
  assume (iir#a != iir#b) && (iir#a != iir#c) && (iir#a != iir#d) && (iir#a != iir#e) && (iir#a != iir#f) && (iir#a != iir#g) && (iir#a != iir#h) && (iir#a#data != iir#b#data) && (iir#a#data != iir#c#data) && (iir#a#data != iir#d#data) && (iir#a#data != iir#e#data) && (iir#a#data != iir#f#data) && (iir#a#data != iir#g#data) && (iir#a#data != iir#h#data) && (iir#b != iir#c) && (iir#b != iir#d) && (iir#b != iir#e) && (iir#b != iir#f) && (iir#b != iir#g) && (iir#b != iir#h) && (iir#b#data != iir#c#data) && (iir#b#data != iir#d#data) && (iir#b#data != iir#e#data) && (iir#b#data != iir#f#data) && (iir#b#data != iir#g#data) && (iir#b#data != iir#h#data) && (iir#c != iir#d) && (iir#c != iir#e) && (iir#c != iir#f) && (iir#c != iir#g) && (iir#c != iir#h) && (iir#c#data != iir#d#data) && (iir#c#data != iir#e#data) && (iir#c#data != iir#f#data) && (iir#c#data != iir#g#data) && (iir#c#data != iir#h#data) && (iir#d != iir#e) && (iir#d != iir#f) && (iir#d != iir#g) && (iir#d != iir#h) && (iir#d#data != iir#e#data) && (iir#d#data != iir#f#data) && (iir#d#data != iir#g#data) && (iir#d#data != iir#h#data) && (iir#e != iir#f) && (iir#e != iir#g) && (iir#e != iir#h) && (iir#e#data != iir#f#data) && (iir#e#data != iir#g#data) && (iir#e#data != iir#h#data) && (iir#f != iir#g) && (iir#f != iir#h) && (iir#f#data != iir#g#data) && (iir#f#data != iir#h#data) && (iir#g != iir#h) && (iir#g#data != iir#h#data);
  assume 0 <= I[iir#a];
  assume I[iir#a] <= R[iir#a];
  assume R[iir#a] <= C[iir#a];
  assume 0 <= I[iir#b];
  assume I[iir#b] <= R[iir#b];
  assume R[iir#b] <= C[iir#b];
  assume 0 <= I[iir#c];
  assume I[iir#c] <= R[iir#c];
  assume R[iir#c] <= C[iir#c];
  assume 0 <= I[iir#d];
  assume I[iir#d] <= R[iir#d];
  assume R[iir#d] <= C[iir#d];
  assume 0 <= I[iir#e];
  assume I[iir#e] <= R[iir#e];
  assume R[iir#e] <= C[iir#e];
  assume 0 <= I[iir#f];
  assume I[iir#f] <= R[iir#f];
  assume R[iir#f] <= C[iir#f];
  assume 0 <= I[iir#g];
  assume I[iir#g] <= R[iir#g];
  assume R[iir#g] <= C[iir#g];
  assume 0 <= I[iir#h];
  assume I[iir#h] <= R[iir#h];
  assume R[iir#h] <= C[iir#h];
  assume I[iir#h] == R[iir#h];
  assume I[iir#f] == I[iir#e];
  assume I[iir#b] == I[iir#a];
  assume I[iir#e] == I[iir#d];
  assume I[iir#g] == I[iir#c];
  assume I[iir#c] == I[iir#b];
  assume I[iir#c] == I[iir#f];
  assume I[iir#d] == I[iir#g];
  assume I[iir#h] == I[iir#g];
  assume M[iir#f][0][data#int] == 0;
  assume R[iir#e] == (C[iir#f] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[iir#f]) ==> (M[iir#f][idx$][data#int] == M[iir#e][idx$ - 1][data#int])
  );
  assume R[iir#a] == C[iir#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#b]) ==> (M[iir#b][idx$][data#int] == (85 * M[iir#a][idx$][data#int]))
  );
  assume R[iir#d] == C[iir#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#e]) ==> (M[iir#e][idx$][data#int] == (171 * M[iir#d][idx$][data#int]))
  );
  assume R[iir#c] == C[iir#g];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#g]) ==> (M[iir#g][idx$][data#int] == AT#RShift(M[iir#c][idx$][data#int], 8))
  );
  assume R[iir#b] == C[iir#c];
  assume R[iir#f] == C[iir#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#c]) ==> (M[iir#c][idx$][data#int] == (M[iir#b][idx$][data#int] + M[iir#f][idx$][data#int]))
  );
  assume R[iir#g] == C[iir#d];
  assume R[iir#g] == C[iir#h];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#d]) ==> (M[iir#d][idx$][data#int] == M[iir#g][idx$][data#int])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#h]) ==> (M[iir#h][idx$][data#int] == M[iir#g][idx$][data#int])
  );
  assume (1 <= (C[iir#b] - R[iir#b])) && (1 <= (C[iir#f] - R[iir#f]));
  in1#i := M[iir#b][R[iir#b]][data#int];
  R[iir#b] := R[iir#b] + 1;
  in2#j := M[iir#f][R[iir#f]][data#int];
  R[iir#f] := R[iir#f] + 1;
  M[iir#c][C[iir#c]][data#int] := in1#i + in2#j;
  C[iir#c] := C[iir#c] + 1;
  assume M[iir#f][0][data#int] == 0;
  assume R[iir#e] == (C[iir#f] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[iir#f]) ==> (M[iir#f][idx$][data#int] == M[iir#e][idx$ - 1][data#int])
  );
  assume R[iir#a] == C[iir#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#b]) ==> (M[iir#b][idx$][data#int] == (85 * M[iir#a][idx$][data#int]))
  );
  assume R[iir#d] == C[iir#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#e]) ==> (M[iir#e][idx$][data#int] == (171 * M[iir#d][idx$][data#int]))
  );
  assume R[iir#c] == C[iir#g];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#g]) ==> (M[iir#g][idx$][data#int] == AT#RShift(M[iir#c][idx$][data#int], 8))
  );
  assume R[iir#b] == C[iir#c];
  assume R[iir#f] == C[iir#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#c]) ==> (M[iir#c][idx$][data#int] == (M[iir#b][idx$][data#int] + M[iir#f][idx$][data#int]))
  );
  assume R[iir#g] == C[iir#d];
  assume R[iir#g] == C[iir#h];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#d]) ==> (M[iir#d][idx$][data#int] == M[iir#g][idx$][data#int])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#h]) ==> (M[iir#h][idx$][data#int] == M[iir#g][idx$][data#int])
  );
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add1' might not preserve the channel invariant (#76)"} I[iir#f] == I[iir#e];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add1' might not preserve the channel invariant (#77)"} I[iir#b] == I[iir#a];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add1' might not preserve the channel invariant (#78)"} I[iir#e] == I[iir#d];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add1' might not preserve the channel invariant (#79)"} I[iir#g] == I[iir#c];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add1' might not preserve the channel invariant (#80)"} I[iir#c] == I[iir#b];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add1' might not preserve the channel invariant (#81)"} I[iir#c] == I[iir#f];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add1' might not preserve the channel invariant (#82)"} I[iir#d] == I[iir#g];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add1' might not preserve the channel invariant (#83)"} I[iir#h] == I[iir#g];
}
procedure iir##split#anon$5#16()
  modifies C, R, M, I;
{
  var iir#del1: Actor;
  var iir#mul1: Actor;
  var iir#mul2: Actor;
  var iir#rsh1: Actor;
  var iir#add1: Actor;
  var iir#spl1: Actor;
  var iir#a: Chan;
  var iir#a#data: Field (int);
  var iir#b: Chan;
  var iir#b#data: Field (int);
  var iir#c: Chan;
  var iir#c#data: Field (int);
  var iir#d: Chan;
  var iir#d#data: Field (int);
  var iir#e: Chan;
  var iir#e#data: Field (int);
  var iir#f: Chan;
  var iir#f#data: Field (int);
  var iir#g: Chan;
  var iir#g#data: Field (int);
  var iir#h: Chan;
  var iir#h#data: Field (int);
  var in#i: int;
  assume (iir#del1 != iir#mul1) && (iir#del1 != iir#mul2) && (iir#del1 != iir#rsh1) && (iir#del1 != iir#add1) && (iir#del1 != iir#spl1) && (iir#mul1 != iir#mul2) && (iir#mul1 != iir#rsh1) && (iir#mul1 != iir#add1) && (iir#mul1 != iir#spl1) && (iir#mul2 != iir#rsh1) && (iir#mul2 != iir#add1) && (iir#mul2 != iir#spl1) && (iir#rsh1 != iir#add1) && (iir#rsh1 != iir#spl1) && (iir#add1 != iir#spl1);
  assume (iir#a != iir#b) && (iir#a != iir#c) && (iir#a != iir#d) && (iir#a != iir#e) && (iir#a != iir#f) && (iir#a != iir#g) && (iir#a != iir#h) && (iir#a#data != iir#b#data) && (iir#a#data != iir#c#data) && (iir#a#data != iir#d#data) && (iir#a#data != iir#e#data) && (iir#a#data != iir#f#data) && (iir#a#data != iir#g#data) && (iir#a#data != iir#h#data) && (iir#b != iir#c) && (iir#b != iir#d) && (iir#b != iir#e) && (iir#b != iir#f) && (iir#b != iir#g) && (iir#b != iir#h) && (iir#b#data != iir#c#data) && (iir#b#data != iir#d#data) && (iir#b#data != iir#e#data) && (iir#b#data != iir#f#data) && (iir#b#data != iir#g#data) && (iir#b#data != iir#h#data) && (iir#c != iir#d) && (iir#c != iir#e) && (iir#c != iir#f) && (iir#c != iir#g) && (iir#c != iir#h) && (iir#c#data != iir#d#data) && (iir#c#data != iir#e#data) && (iir#c#data != iir#f#data) && (iir#c#data != iir#g#data) && (iir#c#data != iir#h#data) && (iir#d != iir#e) && (iir#d != iir#f) && (iir#d != iir#g) && (iir#d != iir#h) && (iir#d#data != iir#e#data) && (iir#d#data != iir#f#data) && (iir#d#data != iir#g#data) && (iir#d#data != iir#h#data) && (iir#e != iir#f) && (iir#e != iir#g) && (iir#e != iir#h) && (iir#e#data != iir#f#data) && (iir#e#data != iir#g#data) && (iir#e#data != iir#h#data) && (iir#f != iir#g) && (iir#f != iir#h) && (iir#f#data != iir#g#data) && (iir#f#data != iir#h#data) && (iir#g != iir#h) && (iir#g#data != iir#h#data);
  assume 0 <= I[iir#a];
  assume I[iir#a] <= R[iir#a];
  assume R[iir#a] <= C[iir#a];
  assume 0 <= I[iir#b];
  assume I[iir#b] <= R[iir#b];
  assume R[iir#b] <= C[iir#b];
  assume 0 <= I[iir#c];
  assume I[iir#c] <= R[iir#c];
  assume R[iir#c] <= C[iir#c];
  assume 0 <= I[iir#d];
  assume I[iir#d] <= R[iir#d];
  assume R[iir#d] <= C[iir#d];
  assume 0 <= I[iir#e];
  assume I[iir#e] <= R[iir#e];
  assume R[iir#e] <= C[iir#e];
  assume 0 <= I[iir#f];
  assume I[iir#f] <= R[iir#f];
  assume R[iir#f] <= C[iir#f];
  assume 0 <= I[iir#g];
  assume I[iir#g] <= R[iir#g];
  assume R[iir#g] <= C[iir#g];
  assume 0 <= I[iir#h];
  assume I[iir#h] <= R[iir#h];
  assume R[iir#h] <= C[iir#h];
  assume I[iir#h] == R[iir#h];
  assume I[iir#f] == I[iir#e];
  assume I[iir#b] == I[iir#a];
  assume I[iir#e] == I[iir#d];
  assume I[iir#g] == I[iir#c];
  assume I[iir#c] == I[iir#b];
  assume I[iir#c] == I[iir#f];
  assume I[iir#d] == I[iir#g];
  assume I[iir#h] == I[iir#g];
  assume M[iir#f][0][data#int] == 0;
  assume R[iir#e] == (C[iir#f] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[iir#f]) ==> (M[iir#f][idx$][data#int] == M[iir#e][idx$ - 1][data#int])
  );
  assume R[iir#a] == C[iir#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#b]) ==> (M[iir#b][idx$][data#int] == (85 * M[iir#a][idx$][data#int]))
  );
  assume R[iir#d] == C[iir#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#e]) ==> (M[iir#e][idx$][data#int] == (171 * M[iir#d][idx$][data#int]))
  );
  assume R[iir#c] == C[iir#g];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#g]) ==> (M[iir#g][idx$][data#int] == AT#RShift(M[iir#c][idx$][data#int], 8))
  );
  assume R[iir#b] == C[iir#c];
  assume R[iir#f] == C[iir#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#c]) ==> (M[iir#c][idx$][data#int] == (M[iir#b][idx$][data#int] + M[iir#f][idx$][data#int]))
  );
  assume R[iir#g] == C[iir#d];
  assume R[iir#g] == C[iir#h];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#d]) ==> (M[iir#d][idx$][data#int] == M[iir#g][idx$][data#int])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#h]) ==> (M[iir#h][idx$][data#int] == M[iir#g][idx$][data#int])
  );
  assume 1 <= (C[iir#g] - R[iir#g]);
  in#i := M[iir#g][R[iir#g]][data#int];
  R[iir#g] := R[iir#g] + 1;
  M[iir#d][C[iir#d]][data#int] := in#i;
  C[iir#d] := C[iir#d] + 1;
  M[iir#h][C[iir#h]][data#int] := in#i;
  C[iir#h] := C[iir#h] + 1;
  assume M[iir#f][0][data#int] == 0;
  assume R[iir#e] == (C[iir#f] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[iir#f]) ==> (M[iir#f][idx$][data#int] == M[iir#e][idx$ - 1][data#int])
  );
  assume R[iir#a] == C[iir#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#b]) ==> (M[iir#b][idx$][data#int] == (85 * M[iir#a][idx$][data#int]))
  );
  assume R[iir#d] == C[iir#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#e]) ==> (M[iir#e][idx$][data#int] == (171 * M[iir#d][idx$][data#int]))
  );
  assume R[iir#c] == C[iir#g];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#g]) ==> (M[iir#g][idx$][data#int] == AT#RShift(M[iir#c][idx$][data#int], 8))
  );
  assume R[iir#b] == C[iir#c];
  assume R[iir#f] == C[iir#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#c]) ==> (M[iir#c][idx$][data#int] == (M[iir#b][idx$][data#int] + M[iir#f][idx$][data#int]))
  );
  assume R[iir#g] == C[iir#d];
  assume R[iir#g] == C[iir#h];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#d]) ==> (M[iir#d][idx$][data#int] == M[iir#g][idx$][data#int])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#h]) ==> (M[iir#h][idx$][data#int] == M[iir#g][idx$][data#int])
  );
  assert {:msg "Action at 20.3 ('anon$5') for actor instance 'spl1' might not preserve the channel invariant (#84)"} I[iir#f] == I[iir#e];
  assert {:msg "Action at 20.3 ('anon$5') for actor instance 'spl1' might not preserve the channel invariant (#85)"} I[iir#b] == I[iir#a];
  assert {:msg "Action at 20.3 ('anon$5') for actor instance 'spl1' might not preserve the channel invariant (#86)"} I[iir#e] == I[iir#d];
  assert {:msg "Action at 20.3 ('anon$5') for actor instance 'spl1' might not preserve the channel invariant (#87)"} I[iir#g] == I[iir#c];
  assert {:msg "Action at 20.3 ('anon$5') for actor instance 'spl1' might not preserve the channel invariant (#88)"} I[iir#c] == I[iir#b];
  assert {:msg "Action at 20.3 ('anon$5') for actor instance 'spl1' might not preserve the channel invariant (#89)"} I[iir#c] == I[iir#f];
  assert {:msg "Action at 20.3 ('anon$5') for actor instance 'spl1' might not preserve the channel invariant (#90)"} I[iir#d] == I[iir#g];
  assert {:msg "Action at 20.3 ('anon$5') for actor instance 'spl1' might not preserve the channel invariant (#91)"} I[iir#h] == I[iir#g];
}
procedure iir#anon$6#input#in#17()
  modifies C, R, M, I;
{
  var iir#del1: Actor;
  var iir#mul1: Actor;
  var iir#mul2: Actor;
  var iir#rsh1: Actor;
  var iir#add1: Actor;
  var iir#spl1: Actor;
  var iir#a: Chan;
  var iir#a#data: Field (int);
  var iir#b: Chan;
  var iir#b#data: Field (int);
  var iir#c: Chan;
  var iir#c#data: Field (int);
  var iir#d: Chan;
  var iir#d#data: Field (int);
  var iir#e: Chan;
  var iir#e#data: Field (int);
  var iir#f: Chan;
  var iir#f#data: Field (int);
  var iir#g: Chan;
  var iir#g#data: Field (int);
  var iir#h: Chan;
  var iir#h#data: Field (int);
  assume (iir#del1 != iir#mul1) && (iir#del1 != iir#mul2) && (iir#del1 != iir#rsh1) && (iir#del1 != iir#add1) && (iir#del1 != iir#spl1) && (iir#mul1 != iir#mul2) && (iir#mul1 != iir#rsh1) && (iir#mul1 != iir#add1) && (iir#mul1 != iir#spl1) && (iir#mul2 != iir#rsh1) && (iir#mul2 != iir#add1) && (iir#mul2 != iir#spl1) && (iir#rsh1 != iir#add1) && (iir#rsh1 != iir#spl1) && (iir#add1 != iir#spl1);
  assume (iir#a != iir#b) && (iir#a != iir#c) && (iir#a != iir#d) && (iir#a != iir#e) && (iir#a != iir#f) && (iir#a != iir#g) && (iir#a != iir#h) && (iir#a#data != iir#b#data) && (iir#a#data != iir#c#data) && (iir#a#data != iir#d#data) && (iir#a#data != iir#e#data) && (iir#a#data != iir#f#data) && (iir#a#data != iir#g#data) && (iir#a#data != iir#h#data) && (iir#b != iir#c) && (iir#b != iir#d) && (iir#b != iir#e) && (iir#b != iir#f) && (iir#b != iir#g) && (iir#b != iir#h) && (iir#b#data != iir#c#data) && (iir#b#data != iir#d#data) && (iir#b#data != iir#e#data) && (iir#b#data != iir#f#data) && (iir#b#data != iir#g#data) && (iir#b#data != iir#h#data) && (iir#c != iir#d) && (iir#c != iir#e) && (iir#c != iir#f) && (iir#c != iir#g) && (iir#c != iir#h) && (iir#c#data != iir#d#data) && (iir#c#data != iir#e#data) && (iir#c#data != iir#f#data) && (iir#c#data != iir#g#data) && (iir#c#data != iir#h#data) && (iir#d != iir#e) && (iir#d != iir#f) && (iir#d != iir#g) && (iir#d != iir#h) && (iir#d#data != iir#e#data) && (iir#d#data != iir#f#data) && (iir#d#data != iir#g#data) && (iir#d#data != iir#h#data) && (iir#e != iir#f) && (iir#e != iir#g) && (iir#e != iir#h) && (iir#e#data != iir#f#data) && (iir#e#data != iir#g#data) && (iir#e#data != iir#h#data) && (iir#f != iir#g) && (iir#f != iir#h) && (iir#f#data != iir#g#data) && (iir#f#data != iir#h#data) && (iir#g != iir#h) && (iir#g#data != iir#h#data);
  assume 0 <= I[iir#a];
  assume I[iir#a] <= R[iir#a];
  assume R[iir#a] <= C[iir#a];
  assume 0 <= I[iir#b];
  assume I[iir#b] <= R[iir#b];
  assume R[iir#b] <= C[iir#b];
  assume 0 <= I[iir#c];
  assume I[iir#c] <= R[iir#c];
  assume R[iir#c] <= C[iir#c];
  assume 0 <= I[iir#d];
  assume I[iir#d] <= R[iir#d];
  assume R[iir#d] <= C[iir#d];
  assume 0 <= I[iir#e];
  assume I[iir#e] <= R[iir#e];
  assume R[iir#e] <= C[iir#e];
  assume 0 <= I[iir#f];
  assume I[iir#f] <= R[iir#f];
  assume R[iir#f] <= C[iir#f];
  assume 0 <= I[iir#g];
  assume I[iir#g] <= R[iir#g];
  assume R[iir#g] <= C[iir#g];
  assume 0 <= I[iir#h];
  assume I[iir#h] <= R[iir#h];
  assume R[iir#h] <= C[iir#h];
  assume I[iir#h] == R[iir#h];
  assume (C[iir#a] - I[iir#a]) < 1;
  assume I[iir#f] == I[iir#e];
  assume I[iir#b] == I[iir#a];
  assume I[iir#e] == I[iir#d];
  assume I[iir#g] == I[iir#c];
  assume I[iir#c] == I[iir#b];
  assume I[iir#c] == I[iir#f];
  assume I[iir#d] == I[iir#g];
  assume I[iir#h] == I[iir#g];
  assume M[iir#f][0][data#int] == 0;
  assume R[iir#e] == (C[iir#f] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[iir#f]) ==> (M[iir#f][idx$][data#int] == M[iir#e][idx$ - 1][data#int])
  );
  assume R[iir#a] == C[iir#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#b]) ==> (M[iir#b][idx$][data#int] == (85 * M[iir#a][idx$][data#int]))
  );
  assume R[iir#d] == C[iir#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#e]) ==> (M[iir#e][idx$][data#int] == (171 * M[iir#d][idx$][data#int]))
  );
  assume R[iir#c] == C[iir#g];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#g]) ==> (M[iir#g][idx$][data#int] == AT#RShift(M[iir#c][idx$][data#int], 8))
  );
  assume R[iir#b] == C[iir#c];
  assume R[iir#f] == C[iir#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#c]) ==> (M[iir#c][idx$][data#int] == (M[iir#b][idx$][data#int] + M[iir#f][idx$][data#int]))
  );
  assume R[iir#g] == C[iir#d];
  assume R[iir#g] == C[iir#h];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#d]) ==> (M[iir#d][idx$][data#int] == M[iir#g][idx$][data#int])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#h]) ==> (M[iir#h][idx$][data#int] == M[iir#g][idx$][data#int])
  );
  C[iir#a] := C[iir#a] + 1;
  assert {:msg "Channel invariant might be falsified by network input (#92)"} I[iir#f] == I[iir#e];
  assert {:msg "Channel invariant might be falsified by network input (#93)"} I[iir#b] == I[iir#a];
  assert {:msg "Channel invariant might be falsified by network input (#94)"} I[iir#e] == I[iir#d];
  assert {:msg "Channel invariant might be falsified by network input (#95)"} I[iir#g] == I[iir#c];
  assert {:msg "Channel invariant might be falsified by network input (#96)"} I[iir#c] == I[iir#b];
  assert {:msg "Channel invariant might be falsified by network input (#97)"} I[iir#c] == I[iir#f];
  assert {:msg "Channel invariant might be falsified by network input (#98)"} I[iir#d] == I[iir#g];
  assert {:msg "Channel invariant might be falsified by network input (#99)"} I[iir#h] == I[iir#g];
}
procedure iir#anon$6#exit#18()
  modifies C, R, M, I;
{
  var iir#del1: Actor;
  var iir#mul1: Actor;
  var iir#mul2: Actor;
  var iir#rsh1: Actor;
  var iir#add1: Actor;
  var iir#spl1: Actor;
  var iir#a: Chan;
  var iir#a#data: Field (int);
  var iir#b: Chan;
  var iir#b#data: Field (int);
  var iir#c: Chan;
  var iir#c#data: Field (int);
  var iir#d: Chan;
  var iir#d#data: Field (int);
  var iir#e: Chan;
  var iir#e#data: Field (int);
  var iir#f: Chan;
  var iir#f#data: Field (int);
  var iir#g: Chan;
  var iir#g#data: Field (int);
  var iir#h: Chan;
  var iir#h#data: Field (int);
  assume (iir#del1 != iir#mul1) && (iir#del1 != iir#mul2) && (iir#del1 != iir#rsh1) && (iir#del1 != iir#add1) && (iir#del1 != iir#spl1) && (iir#mul1 != iir#mul2) && (iir#mul1 != iir#rsh1) && (iir#mul1 != iir#add1) && (iir#mul1 != iir#spl1) && (iir#mul2 != iir#rsh1) && (iir#mul2 != iir#add1) && (iir#mul2 != iir#spl1) && (iir#rsh1 != iir#add1) && (iir#rsh1 != iir#spl1) && (iir#add1 != iir#spl1);
  assume (iir#a != iir#b) && (iir#a != iir#c) && (iir#a != iir#d) && (iir#a != iir#e) && (iir#a != iir#f) && (iir#a != iir#g) && (iir#a != iir#h) && (iir#a#data != iir#b#data) && (iir#a#data != iir#c#data) && (iir#a#data != iir#d#data) && (iir#a#data != iir#e#data) && (iir#a#data != iir#f#data) && (iir#a#data != iir#g#data) && (iir#a#data != iir#h#data) && (iir#b != iir#c) && (iir#b != iir#d) && (iir#b != iir#e) && (iir#b != iir#f) && (iir#b != iir#g) && (iir#b != iir#h) && (iir#b#data != iir#c#data) && (iir#b#data != iir#d#data) && (iir#b#data != iir#e#data) && (iir#b#data != iir#f#data) && (iir#b#data != iir#g#data) && (iir#b#data != iir#h#data) && (iir#c != iir#d) && (iir#c != iir#e) && (iir#c != iir#f) && (iir#c != iir#g) && (iir#c != iir#h) && (iir#c#data != iir#d#data) && (iir#c#data != iir#e#data) && (iir#c#data != iir#f#data) && (iir#c#data != iir#g#data) && (iir#c#data != iir#h#data) && (iir#d != iir#e) && (iir#d != iir#f) && (iir#d != iir#g) && (iir#d != iir#h) && (iir#d#data != iir#e#data) && (iir#d#data != iir#f#data) && (iir#d#data != iir#g#data) && (iir#d#data != iir#h#data) && (iir#e != iir#f) && (iir#e != iir#g) && (iir#e != iir#h) && (iir#e#data != iir#f#data) && (iir#e#data != iir#g#data) && (iir#e#data != iir#h#data) && (iir#f != iir#g) && (iir#f != iir#h) && (iir#f#data != iir#g#data) && (iir#f#data != iir#h#data) && (iir#g != iir#h) && (iir#g#data != iir#h#data);
  assume 0 <= I[iir#a];
  assume I[iir#a] <= R[iir#a];
  assume R[iir#a] <= C[iir#a];
  assume 0 <= I[iir#b];
  assume I[iir#b] <= R[iir#b];
  assume R[iir#b] <= C[iir#b];
  assume 0 <= I[iir#c];
  assume I[iir#c] <= R[iir#c];
  assume R[iir#c] <= C[iir#c];
  assume 0 <= I[iir#d];
  assume I[iir#d] <= R[iir#d];
  assume R[iir#d] <= C[iir#d];
  assume 0 <= I[iir#e];
  assume I[iir#e] <= R[iir#e];
  assume R[iir#e] <= C[iir#e];
  assume 0 <= I[iir#f];
  assume I[iir#f] <= R[iir#f];
  assume R[iir#f] <= C[iir#f];
  assume 0 <= I[iir#g];
  assume I[iir#g] <= R[iir#g];
  assume R[iir#g] <= C[iir#g];
  assume 0 <= I[iir#h];
  assume I[iir#h] <= R[iir#h];
  assume R[iir#h] <= C[iir#h];
  assume I[iir#h] == R[iir#h];
  assume I[iir#f] == I[iir#e];
  assume I[iir#b] == I[iir#a];
  assume I[iir#e] == I[iir#d];
  assume I[iir#g] == I[iir#c];
  assume I[iir#c] == I[iir#b];
  assume I[iir#c] == I[iir#f];
  assume I[iir#d] == I[iir#g];
  assume I[iir#h] == I[iir#g];
  assume M[iir#f][0][data#int] == 0;
  assume R[iir#e] == (C[iir#f] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[iir#f]) ==> (M[iir#f][idx$][data#int] == M[iir#e][idx$ - 1][data#int])
  );
  assume R[iir#a] == C[iir#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#b]) ==> (M[iir#b][idx$][data#int] == (85 * M[iir#a][idx$][data#int]))
  );
  assume R[iir#d] == C[iir#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#e]) ==> (M[iir#e][idx$][data#int] == (171 * M[iir#d][idx$][data#int]))
  );
  assume R[iir#c] == C[iir#g];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#g]) ==> (M[iir#g][idx$][data#int] == AT#RShift(M[iir#c][idx$][data#int], 8))
  );
  assume R[iir#b] == C[iir#c];
  assume R[iir#f] == C[iir#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#c]) ==> (M[iir#c][idx$][data#int] == (M[iir#b][idx$][data#int] + M[iir#f][idx$][data#int]))
  );
  assume R[iir#g] == C[iir#d];
  assume R[iir#g] == C[iir#h];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#d]) ==> (M[iir#d][idx$][data#int] == M[iir#g][idx$][data#int])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#h]) ==> (M[iir#h][idx$][data#int] == M[iir#g][idx$][data#int])
  );
  assume (C[iir#a] - I[iir#a]) == 1;
  assume !(1 <= (C[iir#e] - R[iir#e]));
  assume !(1 <= (C[iir#a] - R[iir#a]));
  assume !(1 <= (C[iir#d] - R[iir#d]));
  assume !(1 <= (C[iir#c] - R[iir#c]));
  assume !((1 <= (C[iir#b] - R[iir#b])) && (1 <= (C[iir#f] - R[iir#f])));
  assume !(1 <= (C[iir#g] - R[iir#g]));
  assert {:msg "26.13: Network action postcondition might not hold (#100)"} M[iir#h][0][data#int] == AT#RShift(85 * M[iir#a][0][data#int], 8);
  assert {:msg "27.13: Network action postcondition might not hold (#101)"} (0 < I[iir#h]) ==> (M[iir#h][I[iir#h]][data#int] == AT#RShift((171 * M[iir#h][I[iir#h] - 1][data#int]) + (85 * M[iir#a][I[iir#a]][data#int]), 8));
  R[iir#h] := R[iir#h] + 1;
  I := R;
  assert {:msg "The network might not preserve the channel invariant (#102)"} I[iir#f] == I[iir#e];
  assert {:msg "The network might not preserve the channel invariant (#103)"} I[iir#b] == I[iir#a];
  assert {:msg "The network might not preserve the channel invariant (#104)"} I[iir#e] == I[iir#d];
  assert {:msg "The network might not preserve the channel invariant (#105)"} I[iir#g] == I[iir#c];
  assert {:msg "The network might not preserve the channel invariant (#106)"} I[iir#c] == I[iir#b];
  assert {:msg "The network might not preserve the channel invariant (#107)"} I[iir#c] == I[iir#f];
  assert {:msg "The network might not preserve the channel invariant (#108)"} I[iir#d] == I[iir#g];
  assert {:msg "The network might not preserve the channel invariant (#109)"} I[iir#h] == I[iir#g];
  assert {:msg "30.13: The network might not preserve the network invariant (#110)"} (C[iir#f] - R[iir#f]) == 1;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel a (#111)"} (C[iir#a] - R[iir#a]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel b (#112)"} (C[iir#b] - R[iir#b]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel c (#113)"} (C[iir#c] - R[iir#c]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel d (#114)"} (C[iir#d] - R[iir#d]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel e (#115)"} (C[iir#e] - R[iir#e]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel g (#116)"} (C[iir#g] - R[iir#g]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel h (#117)"} (C[iir#h] - R[iir#h]) == 0;
}

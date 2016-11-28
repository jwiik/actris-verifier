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

const unique this#: Actor;
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
  var in1: Chan (int);
  var in2: Chan (int);
  var out: Chan (int);
  assume (in1 != in2) && (in1 != out) && (in2 != out);
  assume R[in1] == 0;
  assume R[in2] == 0;
  assume C[out] == 0;
  assert {:msg "Initialization might not establish the invariant (#0)"} R[in1] == C[out];
  assert {:msg "Initialization might not establish the invariant (#1)"} R[in2] == C[out];
  assert {:msg "Initialization might not establish the invariant (#2)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == (M[in1][idx$] + M[in2][idx$]))
  );
}
procedure add#anon$0#1()
  modifies C, R, M, I;
{
  var in1: Chan (int);
  var in2: Chan (int);
  var out: Chan (int);
  var in1#0: int;
  var in2#0: int;
  assume (in1 != in2) && (in1 != out) && (in2 != out);
  assume 0 <= R[in1];
  assume 0 <= R[in2];
  assume 0 <= C[out];
  assume R[in1] == C[out];
  assume R[in2] == C[out];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == (M[in1][idx$] + M[in2][idx$]))
  );
  in1#0 := M[in1][R[in1]];
  R[in1] := R[in1] + 1;
  in2#0 := M[in2][R[in2]];
  R[in2] := R[in2] + 1;
  M[out][C[out]] := in1#0 + in2#0;
  C[out] := C[out] + 1;
  assert {:msg "Action at 2.3 might not preserve invariant (#3)"} R[in1] == C[out];
  assert {:msg "Action at 2.3 might not preserve invariant (#4)"} R[in2] == C[out];
  assert {:msg "Action at 2.3 might not preserve invariant (#5)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == (M[in1][idx$] + M[in2][idx$]))
  );
}
procedure delay#init#2()
  modifies C, R, M, I;
{
  var in: Chan (int);
  var out: Chan (int);
  var k: int;
  assume in != out;
  assume R[in] == 0;
  assume C[out] == 0;
  M[out][C[out]] := k;
  C[out] := C[out] + 1;
  assert {:msg "6.13: Initialization might not establish the invariant (#6)"} M[out][0] == k;
  assert {:msg "Initialization might not establish the invariant (#7)"} R[in] == (C[out] - 1);
  assert {:msg "Initialization might not establish the invariant (#8)"} (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == M[in][idx$ - 1])
  );
}
procedure delay#anon$2#3()
  modifies C, R, M, I;
{
  var in: Chan (int);
  var out: Chan (int);
  var k: int;
  var in#0: int;
  assume in != out;
  assume 0 <= R[in];
  assume 0 <= C[out];
  assume M[out][0] == k;
  assume R[in] == (C[out] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == M[in][idx$ - 1])
  );
  in#0 := M[in][R[in]];
  R[in] := R[in] + 1;
  M[out][C[out]] := in#0;
  C[out] := C[out] + 1;
  assert {:msg "6.13: Action at 8.3 might not preserve invariant (#9)"} M[out][0] == k;
  assert {:msg "Action at 8.3 might not preserve invariant (#10)"} R[in] == (C[out] - 1);
  assert {:msg "Action at 8.3 might not preserve invariant (#11)"} (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == M[in][idx$ - 1])
  );
}
procedure mulc#init#4()
  modifies C, R, M, I;
{
  var in: Chan (int);
  var out: Chan (int);
  var c: int;
  assume in != out;
  assume R[in] == 0;
  assume C[out] == 0;
  assert {:msg "Initialization might not establish the invariant (#12)"} R[in] == C[out];
  assert {:msg "Initialization might not establish the invariant (#13)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == (c * M[in][idx$]))
  );
}
procedure mulc#anon$3#5()
  modifies C, R, M, I;
{
  var in: Chan (int);
  var out: Chan (int);
  var c: int;
  var in#0: int;
  assume in != out;
  assume 0 <= R[in];
  assume 0 <= C[out];
  assume R[in] == C[out];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == (c * M[in][idx$]))
  );
  in#0 := M[in][R[in]];
  R[in] := R[in] + 1;
  M[out][C[out]] := c * in#0;
  C[out] := C[out] + 1;
  assert {:msg "Action at 12.3 might not preserve invariant (#14)"} R[in] == C[out];
  assert {:msg "Action at 12.3 might not preserve invariant (#15)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == (c * M[in][idx$]))
  );
}
procedure rshift#init#6()
  modifies C, R, M, I;
{
  var in: Chan (int);
  var out: Chan (int);
  var s: int;
  assume in != out;
  assume R[in] == 0;
  assume C[out] == 0;
  assert {:msg "Initialization might not establish the invariant (#16)"} R[in] == C[out];
  assert {:msg "Initialization might not establish the invariant (#17)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == AT#RShift(M[in][idx$], s))
  );
}
procedure rshift#anon$4#7()
  modifies C, R, M, I;
{
  var in: Chan (int);
  var out: Chan (int);
  var s: int;
  var in#0: int;
  assume in != out;
  assume 0 <= R[in];
  assume 0 <= C[out];
  assume R[in] == C[out];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == AT#RShift(M[in][idx$], s))
  );
  in#0 := M[in][R[in]];
  R[in] := R[in] + 1;
  M[out][C[out]] := AT#RShift(in#0, s);
  C[out] := C[out] + 1;
  assert {:msg "Action at 16.3 might not preserve invariant (#18)"} R[in] == C[out];
  assert {:msg "Action at 16.3 might not preserve invariant (#19)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == AT#RShift(M[in][idx$], s))
  );
}
procedure split#init#8()
  modifies C, R, M, I;
{
  var in: Chan (int);
  var out1: Chan (int);
  var out2: Chan (int);
  assume (in != out1) && (in != out2) && (out1 != out2);
  assume R[in] == 0;
  assume C[out1] == 0;
  assume C[out2] == 0;
  assert {:msg "Initialization might not establish the invariant (#20)"} R[in] == C[out1];
  assert {:msg "Initialization might not establish the invariant (#21)"} R[in] == C[out2];
  assert {:msg "Initialization might not establish the invariant (#22)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out1]) ==> (M[out1][idx$] == M[in][idx$])
  );
  assert {:msg "Initialization might not establish the invariant (#23)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out2]) ==> (M[out2][idx$] == M[in][idx$])
  );
}
procedure split#anon$5#9()
  modifies C, R, M, I;
{
  var in: Chan (int);
  var out1: Chan (int);
  var out2: Chan (int);
  var in#0: int;
  assume (in != out1) && (in != out2) && (out1 != out2);
  assume 0 <= R[in];
  assume 0 <= C[out1];
  assume 0 <= C[out2];
  assume R[in] == C[out1];
  assume R[in] == C[out2];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out1]) ==> (M[out1][idx$] == M[in][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out2]) ==> (M[out2][idx$] == M[in][idx$])
  );
  in#0 := M[in][R[in]];
  R[in] := R[in] + 1;
  M[out1][C[out1]] := in#0;
  C[out1] := C[out1] + 1;
  M[out2][C[out2]] := in#0;
  C[out2] := C[out2] + 1;
  assert {:msg "Action at 20.3 might not preserve invariant (#24)"} R[in] == C[out1];
  assert {:msg "Action at 20.3 might not preserve invariant (#25)"} R[in] == C[out2];
  assert {:msg "Action at 20.3 might not preserve invariant (#26)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out1]) ==> (M[out1][idx$] == M[in][idx$])
  );
  assert {:msg "Action at 20.3 might not preserve invariant (#27)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out2]) ==> (M[out2][idx$] == M[in][idx$])
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
  var iir#a: Chan (int);
  var iir#b: Chan (int);
  var iir#c: Chan (int);
  var iir#d: Chan (int);
  var iir#e: Chan (int);
  var iir#f: Chan (int);
  var iir#g: Chan (int);
  var iir#h: Chan (int);
  assume (iir#del1 != iir#mul1) && (iir#del1 != iir#mul2) && (iir#del1 != iir#rsh1) && (iir#del1 != iir#add1) && (iir#del1 != iir#spl1) && (iir#mul1 != iir#mul2) && (iir#mul1 != iir#rsh1) && (iir#mul1 != iir#add1) && (iir#mul1 != iir#spl1) && (iir#mul2 != iir#rsh1) && (iir#mul2 != iir#add1) && (iir#mul2 != iir#spl1) && (iir#rsh1 != iir#add1) && (iir#rsh1 != iir#spl1) && (iir#add1 != iir#spl1);
  assume (iir#a != iir#b) && (iir#a != iir#c) && (iir#a != iir#d) && (iir#a != iir#e) && (iir#a != iir#f) && (iir#a != iir#g) && (iir#a != iir#h) && (iir#b != iir#c) && (iir#b != iir#d) && (iir#b != iir#e) && (iir#b != iir#f) && (iir#b != iir#g) && (iir#b != iir#h) && (iir#c != iir#d) && (iir#c != iir#e) && (iir#c != iir#f) && (iir#c != iir#g) && (iir#c != iir#h) && (iir#d != iir#e) && (iir#d != iir#f) && (iir#d != iir#g) && (iir#d != iir#h) && (iir#e != iir#f) && (iir#e != iir#g) && (iir#e != iir#h) && (iir#f != iir#g) && (iir#f != iir#h) && (iir#g != iir#h);
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
  M[iir#f][C[iir#f]] := 0;
  C[iir#f] := C[iir#f] + 1;
  assume M[iir#f][0] == 0;
  assume R[iir#e] == (C[iir#f] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[iir#f]) ==> (M[iir#f][idx$] == M[iir#e][idx$ - 1])
  );
  assume 85 == 85;
  assume R[iir#a] == C[iir#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#b]) ==> (M[iir#b][idx$] == (85 * M[iir#a][idx$]))
  );
  assume 171 == 171;
  assume R[iir#d] == C[iir#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#e]) ==> (M[iir#e][idx$] == (171 * M[iir#d][idx$]))
  );
  assume 8 == 8;
  assume R[iir#c] == C[iir#g];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#g]) ==> (M[iir#g][idx$] == AT#RShift(M[iir#c][idx$], 8))
  );
  assume R[iir#b] == C[iir#c];
  assume R[iir#f] == C[iir#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#c]) ==> (M[iir#c][idx$] == (M[iir#b][idx$] + M[iir#f][idx$]))
  );
  assume R[iir#g] == C[iir#d];
  assume R[iir#g] == C[iir#h];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#d]) ==> (M[iir#d][idx$] == M[iir#g][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#h]) ==> (M[iir#h][idx$] == M[iir#g][idx$])
  );
  assert {:msg "Initialization of network 'iir' might not establish the channel invariant (#28)"} I[iir#f] == I[iir#e];
  assert {:msg "Initialization of network 'iir' might not establish the channel invariant (#29)"} I[iir#b] == I[iir#a];
  assert {:msg "Initialization of network 'iir' might not establish the channel invariant (#30)"} I[iir#e] == I[iir#d];
  assert {:msg "Initialization of network 'iir' might not establish the channel invariant (#31)"} I[iir#g] == I[iir#c];
  assert {:msg "Initialization of network 'iir' might not establish the channel invariant (#32)"} I[iir#c] == I[iir#b];
  assert {:msg "Initialization of network 'iir' might not establish the channel invariant (#33)"} I[iir#c] == I[iir#f];
  assert {:msg "Initialization of network 'iir' might not establish the channel invariant (#34)"} I[iir#d] == I[iir#g];
  assert {:msg "Initialization of network 'iir' might not establish the channel invariant (#35)"} I[iir#h] == I[iir#g];
  I := R;
  C[iir#f] := C[iir#f] - 1;
  assert {:msg "42.5: The initialization might produce unspecified tokens on channel a (#36)"} (C[iir#a] - R[iir#a]) == 0;
  assert {:msg "43.5: The initialization might produce unspecified tokens on channel b (#37)"} (C[iir#b] - R[iir#b]) == 0;
  assert {:msg "44.5: The initialization might produce unspecified tokens on channel c (#38)"} (C[iir#c] - R[iir#c]) == 0;
  assert {:msg "45.5: The initialization might produce unspecified tokens on channel d (#39)"} (C[iir#d] - R[iir#d]) == 0;
  assert {:msg "46.5: The initialization might produce unspecified tokens on channel e (#40)"} (C[iir#e] - R[iir#e]) == 0;
  assert {:msg "47.5: The initialization might produce unspecified tokens on channel f (#41)"} (C[iir#f] - R[iir#f]) == 0;
  assert {:msg "48.5: The initialization might produce unspecified tokens on channel g (#42)"} (C[iir#g] - R[iir#g]) == 0;
  assert {:msg "49.5: The initialization might produce unspecified tokens on channel h (#43)"} (C[iir#h] - R[iir#h]) == 0;
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
  var iir#a: Chan (int);
  var iir#b: Chan (int);
  var iir#c: Chan (int);
  var iir#d: Chan (int);
  var iir#e: Chan (int);
  var iir#f: Chan (int);
  var iir#g: Chan (int);
  var iir#h: Chan (int);
  var in#i: int;
  assume (iir#del1 != iir#mul1) && (iir#del1 != iir#mul2) && (iir#del1 != iir#rsh1) && (iir#del1 != iir#add1) && (iir#del1 != iir#spl1) && (iir#mul1 != iir#mul2) && (iir#mul1 != iir#rsh1) && (iir#mul1 != iir#add1) && (iir#mul1 != iir#spl1) && (iir#mul2 != iir#rsh1) && (iir#mul2 != iir#add1) && (iir#mul2 != iir#spl1) && (iir#rsh1 != iir#add1) && (iir#rsh1 != iir#spl1) && (iir#add1 != iir#spl1);
  assume (iir#a != iir#b) && (iir#a != iir#c) && (iir#a != iir#d) && (iir#a != iir#e) && (iir#a != iir#f) && (iir#a != iir#g) && (iir#a != iir#h) && (iir#b != iir#c) && (iir#b != iir#d) && (iir#b != iir#e) && (iir#b != iir#f) && (iir#b != iir#g) && (iir#b != iir#h) && (iir#c != iir#d) && (iir#c != iir#e) && (iir#c != iir#f) && (iir#c != iir#g) && (iir#c != iir#h) && (iir#d != iir#e) && (iir#d != iir#f) && (iir#d != iir#g) && (iir#d != iir#h) && (iir#e != iir#f) && (iir#e != iir#g) && (iir#e != iir#h) && (iir#f != iir#g) && (iir#f != iir#h) && (iir#g != iir#h);
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
  assume M[iir#f][0] == 0;
  assume R[iir#e] == (C[iir#f] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[iir#f]) ==> (M[iir#f][idx$] == M[iir#e][idx$ - 1])
  );
  assume R[iir#a] == C[iir#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#b]) ==> (M[iir#b][idx$] == (85 * M[iir#a][idx$]))
  );
  assume R[iir#d] == C[iir#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#e]) ==> (M[iir#e][idx$] == (171 * M[iir#d][idx$]))
  );
  assume R[iir#c] == C[iir#g];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#g]) ==> (M[iir#g][idx$] == AT#RShift(M[iir#c][idx$], 8))
  );
  assume R[iir#b] == C[iir#c];
  assume R[iir#f] == C[iir#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#c]) ==> (M[iir#c][idx$] == (M[iir#b][idx$] + M[iir#f][idx$]))
  );
  assume R[iir#g] == C[iir#d];
  assume R[iir#g] == C[iir#h];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#d]) ==> (M[iir#d][idx$] == M[iir#g][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#h]) ==> (M[iir#h][idx$] == M[iir#g][idx$])
  );
  assume 1 <= (C[iir#e] - R[iir#e]);
  assume M[iir#f][0] == 0;
  assume R[iir#e] == (C[iir#f] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[iir#f]) ==> (M[iir#f][idx$] == M[iir#e][idx$ - 1])
  );
  in#i := M[iir#e][R[iir#e]];
  R[iir#e] := R[iir#e] + 1;
  M[iir#f][C[iir#f]] := in#i;
  C[iir#f] := C[iir#f] + 1;
  assume M[iir#f][0] == 0;
  assume R[iir#e] == (C[iir#f] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[iir#f]) ==> (M[iir#f][idx$] == M[iir#e][idx$ - 1])
  );
  assume M[iir#f][0] == 0;
  assume R[iir#e] == (C[iir#f] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[iir#f]) ==> (M[iir#f][idx$] == M[iir#e][idx$ - 1])
  );
  assume R[iir#a] == C[iir#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#b]) ==> (M[iir#b][idx$] == (85 * M[iir#a][idx$]))
  );
  assume R[iir#d] == C[iir#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#e]) ==> (M[iir#e][idx$] == (171 * M[iir#d][idx$]))
  );
  assume R[iir#c] == C[iir#g];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#g]) ==> (M[iir#g][idx$] == AT#RShift(M[iir#c][idx$], 8))
  );
  assume R[iir#b] == C[iir#c];
  assume R[iir#f] == C[iir#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#c]) ==> (M[iir#c][idx$] == (M[iir#b][idx$] + M[iir#f][idx$]))
  );
  assume R[iir#g] == C[iir#d];
  assume R[iir#g] == C[iir#h];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#d]) ==> (M[iir#d][idx$] == M[iir#g][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#h]) ==> (M[iir#h][idx$] == M[iir#g][idx$])
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
  var iir#a: Chan (int);
  var iir#b: Chan (int);
  var iir#c: Chan (int);
  var iir#d: Chan (int);
  var iir#e: Chan (int);
  var iir#f: Chan (int);
  var iir#g: Chan (int);
  var iir#h: Chan (int);
  var in#i: int;
  assume (iir#del1 != iir#mul1) && (iir#del1 != iir#mul2) && (iir#del1 != iir#rsh1) && (iir#del1 != iir#add1) && (iir#del1 != iir#spl1) && (iir#mul1 != iir#mul2) && (iir#mul1 != iir#rsh1) && (iir#mul1 != iir#add1) && (iir#mul1 != iir#spl1) && (iir#mul2 != iir#rsh1) && (iir#mul2 != iir#add1) && (iir#mul2 != iir#spl1) && (iir#rsh1 != iir#add1) && (iir#rsh1 != iir#spl1) && (iir#add1 != iir#spl1);
  assume (iir#a != iir#b) && (iir#a != iir#c) && (iir#a != iir#d) && (iir#a != iir#e) && (iir#a != iir#f) && (iir#a != iir#g) && (iir#a != iir#h) && (iir#b != iir#c) && (iir#b != iir#d) && (iir#b != iir#e) && (iir#b != iir#f) && (iir#b != iir#g) && (iir#b != iir#h) && (iir#c != iir#d) && (iir#c != iir#e) && (iir#c != iir#f) && (iir#c != iir#g) && (iir#c != iir#h) && (iir#d != iir#e) && (iir#d != iir#f) && (iir#d != iir#g) && (iir#d != iir#h) && (iir#e != iir#f) && (iir#e != iir#g) && (iir#e != iir#h) && (iir#f != iir#g) && (iir#f != iir#h) && (iir#g != iir#h);
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
  assume M[iir#f][0] == 0;
  assume R[iir#e] == (C[iir#f] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[iir#f]) ==> (M[iir#f][idx$] == M[iir#e][idx$ - 1])
  );
  assume R[iir#a] == C[iir#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#b]) ==> (M[iir#b][idx$] == (85 * M[iir#a][idx$]))
  );
  assume R[iir#d] == C[iir#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#e]) ==> (M[iir#e][idx$] == (171 * M[iir#d][idx$]))
  );
  assume R[iir#c] == C[iir#g];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#g]) ==> (M[iir#g][idx$] == AT#RShift(M[iir#c][idx$], 8))
  );
  assume R[iir#b] == C[iir#c];
  assume R[iir#f] == C[iir#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#c]) ==> (M[iir#c][idx$] == (M[iir#b][idx$] + M[iir#f][idx$]))
  );
  assume R[iir#g] == C[iir#d];
  assume R[iir#g] == C[iir#h];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#d]) ==> (M[iir#d][idx$] == M[iir#g][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#h]) ==> (M[iir#h][idx$] == M[iir#g][idx$])
  );
  assume 1 <= (C[iir#a] - R[iir#a]);
  assume R[iir#a] == C[iir#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#b]) ==> (M[iir#b][idx$] == (85 * M[iir#a][idx$]))
  );
  in#i := M[iir#a][R[iir#a]];
  R[iir#a] := R[iir#a] + 1;
  M[iir#b][C[iir#b]] := 85 * in#i;
  C[iir#b] := C[iir#b] + 1;
  assume R[iir#a] == C[iir#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#b]) ==> (M[iir#b][idx$] == (85 * M[iir#a][idx$]))
  );
  assume M[iir#f][0] == 0;
  assume R[iir#e] == (C[iir#f] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[iir#f]) ==> (M[iir#f][idx$] == M[iir#e][idx$ - 1])
  );
  assume R[iir#a] == C[iir#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#b]) ==> (M[iir#b][idx$] == (85 * M[iir#a][idx$]))
  );
  assume R[iir#d] == C[iir#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#e]) ==> (M[iir#e][idx$] == (171 * M[iir#d][idx$]))
  );
  assume R[iir#c] == C[iir#g];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#g]) ==> (M[iir#g][idx$] == AT#RShift(M[iir#c][idx$], 8))
  );
  assume R[iir#b] == C[iir#c];
  assume R[iir#f] == C[iir#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#c]) ==> (M[iir#c][idx$] == (M[iir#b][idx$] + M[iir#f][idx$]))
  );
  assume R[iir#g] == C[iir#d];
  assume R[iir#g] == C[iir#h];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#d]) ==> (M[iir#d][idx$] == M[iir#g][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#h]) ==> (M[iir#h][idx$] == M[iir#g][idx$])
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
  var iir#a: Chan (int);
  var iir#b: Chan (int);
  var iir#c: Chan (int);
  var iir#d: Chan (int);
  var iir#e: Chan (int);
  var iir#f: Chan (int);
  var iir#g: Chan (int);
  var iir#h: Chan (int);
  var in#i: int;
  assume (iir#del1 != iir#mul1) && (iir#del1 != iir#mul2) && (iir#del1 != iir#rsh1) && (iir#del1 != iir#add1) && (iir#del1 != iir#spl1) && (iir#mul1 != iir#mul2) && (iir#mul1 != iir#rsh1) && (iir#mul1 != iir#add1) && (iir#mul1 != iir#spl1) && (iir#mul2 != iir#rsh1) && (iir#mul2 != iir#add1) && (iir#mul2 != iir#spl1) && (iir#rsh1 != iir#add1) && (iir#rsh1 != iir#spl1) && (iir#add1 != iir#spl1);
  assume (iir#a != iir#b) && (iir#a != iir#c) && (iir#a != iir#d) && (iir#a != iir#e) && (iir#a != iir#f) && (iir#a != iir#g) && (iir#a != iir#h) && (iir#b != iir#c) && (iir#b != iir#d) && (iir#b != iir#e) && (iir#b != iir#f) && (iir#b != iir#g) && (iir#b != iir#h) && (iir#c != iir#d) && (iir#c != iir#e) && (iir#c != iir#f) && (iir#c != iir#g) && (iir#c != iir#h) && (iir#d != iir#e) && (iir#d != iir#f) && (iir#d != iir#g) && (iir#d != iir#h) && (iir#e != iir#f) && (iir#e != iir#g) && (iir#e != iir#h) && (iir#f != iir#g) && (iir#f != iir#h) && (iir#g != iir#h);
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
  assume M[iir#f][0] == 0;
  assume R[iir#e] == (C[iir#f] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[iir#f]) ==> (M[iir#f][idx$] == M[iir#e][idx$ - 1])
  );
  assume R[iir#a] == C[iir#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#b]) ==> (M[iir#b][idx$] == (85 * M[iir#a][idx$]))
  );
  assume R[iir#d] == C[iir#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#e]) ==> (M[iir#e][idx$] == (171 * M[iir#d][idx$]))
  );
  assume R[iir#c] == C[iir#g];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#g]) ==> (M[iir#g][idx$] == AT#RShift(M[iir#c][idx$], 8))
  );
  assume R[iir#b] == C[iir#c];
  assume R[iir#f] == C[iir#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#c]) ==> (M[iir#c][idx$] == (M[iir#b][idx$] + M[iir#f][idx$]))
  );
  assume R[iir#g] == C[iir#d];
  assume R[iir#g] == C[iir#h];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#d]) ==> (M[iir#d][idx$] == M[iir#g][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#h]) ==> (M[iir#h][idx$] == M[iir#g][idx$])
  );
  assume 1 <= (C[iir#d] - R[iir#d]);
  assume R[iir#d] == C[iir#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#e]) ==> (M[iir#e][idx$] == (171 * M[iir#d][idx$]))
  );
  in#i := M[iir#d][R[iir#d]];
  R[iir#d] := R[iir#d] + 1;
  M[iir#e][C[iir#e]] := 171 * in#i;
  C[iir#e] := C[iir#e] + 1;
  assume R[iir#d] == C[iir#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#e]) ==> (M[iir#e][idx$] == (171 * M[iir#d][idx$]))
  );
  assume M[iir#f][0] == 0;
  assume R[iir#e] == (C[iir#f] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[iir#f]) ==> (M[iir#f][idx$] == M[iir#e][idx$ - 1])
  );
  assume R[iir#a] == C[iir#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#b]) ==> (M[iir#b][idx$] == (85 * M[iir#a][idx$]))
  );
  assume R[iir#d] == C[iir#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#e]) ==> (M[iir#e][idx$] == (171 * M[iir#d][idx$]))
  );
  assume R[iir#c] == C[iir#g];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#g]) ==> (M[iir#g][idx$] == AT#RShift(M[iir#c][idx$], 8))
  );
  assume R[iir#b] == C[iir#c];
  assume R[iir#f] == C[iir#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#c]) ==> (M[iir#c][idx$] == (M[iir#b][idx$] + M[iir#f][idx$]))
  );
  assume R[iir#g] == C[iir#d];
  assume R[iir#g] == C[iir#h];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#d]) ==> (M[iir#d][idx$] == M[iir#g][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#h]) ==> (M[iir#h][idx$] == M[iir#g][idx$])
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
  var iir#a: Chan (int);
  var iir#b: Chan (int);
  var iir#c: Chan (int);
  var iir#d: Chan (int);
  var iir#e: Chan (int);
  var iir#f: Chan (int);
  var iir#g: Chan (int);
  var iir#h: Chan (int);
  var in#i: int;
  assume (iir#del1 != iir#mul1) && (iir#del1 != iir#mul2) && (iir#del1 != iir#rsh1) && (iir#del1 != iir#add1) && (iir#del1 != iir#spl1) && (iir#mul1 != iir#mul2) && (iir#mul1 != iir#rsh1) && (iir#mul1 != iir#add1) && (iir#mul1 != iir#spl1) && (iir#mul2 != iir#rsh1) && (iir#mul2 != iir#add1) && (iir#mul2 != iir#spl1) && (iir#rsh1 != iir#add1) && (iir#rsh1 != iir#spl1) && (iir#add1 != iir#spl1);
  assume (iir#a != iir#b) && (iir#a != iir#c) && (iir#a != iir#d) && (iir#a != iir#e) && (iir#a != iir#f) && (iir#a != iir#g) && (iir#a != iir#h) && (iir#b != iir#c) && (iir#b != iir#d) && (iir#b != iir#e) && (iir#b != iir#f) && (iir#b != iir#g) && (iir#b != iir#h) && (iir#c != iir#d) && (iir#c != iir#e) && (iir#c != iir#f) && (iir#c != iir#g) && (iir#c != iir#h) && (iir#d != iir#e) && (iir#d != iir#f) && (iir#d != iir#g) && (iir#d != iir#h) && (iir#e != iir#f) && (iir#e != iir#g) && (iir#e != iir#h) && (iir#f != iir#g) && (iir#f != iir#h) && (iir#g != iir#h);
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
  assume M[iir#f][0] == 0;
  assume R[iir#e] == (C[iir#f] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[iir#f]) ==> (M[iir#f][idx$] == M[iir#e][idx$ - 1])
  );
  assume R[iir#a] == C[iir#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#b]) ==> (M[iir#b][idx$] == (85 * M[iir#a][idx$]))
  );
  assume R[iir#d] == C[iir#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#e]) ==> (M[iir#e][idx$] == (171 * M[iir#d][idx$]))
  );
  assume R[iir#c] == C[iir#g];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#g]) ==> (M[iir#g][idx$] == AT#RShift(M[iir#c][idx$], 8))
  );
  assume R[iir#b] == C[iir#c];
  assume R[iir#f] == C[iir#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#c]) ==> (M[iir#c][idx$] == (M[iir#b][idx$] + M[iir#f][idx$]))
  );
  assume R[iir#g] == C[iir#d];
  assume R[iir#g] == C[iir#h];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#d]) ==> (M[iir#d][idx$] == M[iir#g][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#h]) ==> (M[iir#h][idx$] == M[iir#g][idx$])
  );
  assume 1 <= (C[iir#c] - R[iir#c]);
  assume R[iir#c] == C[iir#g];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#g]) ==> (M[iir#g][idx$] == AT#RShift(M[iir#c][idx$], 8))
  );
  in#i := M[iir#c][R[iir#c]];
  R[iir#c] := R[iir#c] + 1;
  M[iir#g][C[iir#g]] := AT#RShift(in#i, 8);
  C[iir#g] := C[iir#g] + 1;
  assume R[iir#c] == C[iir#g];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#g]) ==> (M[iir#g][idx$] == AT#RShift(M[iir#c][idx$], 8))
  );
  assume M[iir#f][0] == 0;
  assume R[iir#e] == (C[iir#f] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[iir#f]) ==> (M[iir#f][idx$] == M[iir#e][idx$ - 1])
  );
  assume R[iir#a] == C[iir#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#b]) ==> (M[iir#b][idx$] == (85 * M[iir#a][idx$]))
  );
  assume R[iir#d] == C[iir#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#e]) ==> (M[iir#e][idx$] == (171 * M[iir#d][idx$]))
  );
  assume R[iir#c] == C[iir#g];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#g]) ==> (M[iir#g][idx$] == AT#RShift(M[iir#c][idx$], 8))
  );
  assume R[iir#b] == C[iir#c];
  assume R[iir#f] == C[iir#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#c]) ==> (M[iir#c][idx$] == (M[iir#b][idx$] + M[iir#f][idx$]))
  );
  assume R[iir#g] == C[iir#d];
  assume R[iir#g] == C[iir#h];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#d]) ==> (M[iir#d][idx$] == M[iir#g][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#h]) ==> (M[iir#h][idx$] == M[iir#g][idx$])
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
  var iir#a: Chan (int);
  var iir#b: Chan (int);
  var iir#c: Chan (int);
  var iir#d: Chan (int);
  var iir#e: Chan (int);
  var iir#f: Chan (int);
  var iir#g: Chan (int);
  var iir#h: Chan (int);
  var in1#i: int;
  var in2#j: int;
  assume (iir#del1 != iir#mul1) && (iir#del1 != iir#mul2) && (iir#del1 != iir#rsh1) && (iir#del1 != iir#add1) && (iir#del1 != iir#spl1) && (iir#mul1 != iir#mul2) && (iir#mul1 != iir#rsh1) && (iir#mul1 != iir#add1) && (iir#mul1 != iir#spl1) && (iir#mul2 != iir#rsh1) && (iir#mul2 != iir#add1) && (iir#mul2 != iir#spl1) && (iir#rsh1 != iir#add1) && (iir#rsh1 != iir#spl1) && (iir#add1 != iir#spl1);
  assume (iir#a != iir#b) && (iir#a != iir#c) && (iir#a != iir#d) && (iir#a != iir#e) && (iir#a != iir#f) && (iir#a != iir#g) && (iir#a != iir#h) && (iir#b != iir#c) && (iir#b != iir#d) && (iir#b != iir#e) && (iir#b != iir#f) && (iir#b != iir#g) && (iir#b != iir#h) && (iir#c != iir#d) && (iir#c != iir#e) && (iir#c != iir#f) && (iir#c != iir#g) && (iir#c != iir#h) && (iir#d != iir#e) && (iir#d != iir#f) && (iir#d != iir#g) && (iir#d != iir#h) && (iir#e != iir#f) && (iir#e != iir#g) && (iir#e != iir#h) && (iir#f != iir#g) && (iir#f != iir#h) && (iir#g != iir#h);
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
  assume M[iir#f][0] == 0;
  assume R[iir#e] == (C[iir#f] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[iir#f]) ==> (M[iir#f][idx$] == M[iir#e][idx$ - 1])
  );
  assume R[iir#a] == C[iir#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#b]) ==> (M[iir#b][idx$] == (85 * M[iir#a][idx$]))
  );
  assume R[iir#d] == C[iir#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#e]) ==> (M[iir#e][idx$] == (171 * M[iir#d][idx$]))
  );
  assume R[iir#c] == C[iir#g];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#g]) ==> (M[iir#g][idx$] == AT#RShift(M[iir#c][idx$], 8))
  );
  assume R[iir#b] == C[iir#c];
  assume R[iir#f] == C[iir#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#c]) ==> (M[iir#c][idx$] == (M[iir#b][idx$] + M[iir#f][idx$]))
  );
  assume R[iir#g] == C[iir#d];
  assume R[iir#g] == C[iir#h];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#d]) ==> (M[iir#d][idx$] == M[iir#g][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#h]) ==> (M[iir#h][idx$] == M[iir#g][idx$])
  );
  assume (1 <= (C[iir#b] - R[iir#b])) && (1 <= (C[iir#f] - R[iir#f]));
  assume R[iir#b] == C[iir#c];
  assume R[iir#f] == C[iir#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#c]) ==> (M[iir#c][idx$] == (M[iir#b][idx$] + M[iir#f][idx$]))
  );
  in1#i := M[iir#b][R[iir#b]];
  R[iir#b] := R[iir#b] + 1;
  in2#j := M[iir#f][R[iir#f]];
  R[iir#f] := R[iir#f] + 1;
  M[iir#c][C[iir#c]] := in1#i + in2#j;
  C[iir#c] := C[iir#c] + 1;
  assume R[iir#b] == C[iir#c];
  assume R[iir#f] == C[iir#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#c]) ==> (M[iir#c][idx$] == (M[iir#b][idx$] + M[iir#f][idx$]))
  );
  assume M[iir#f][0] == 0;
  assume R[iir#e] == (C[iir#f] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[iir#f]) ==> (M[iir#f][idx$] == M[iir#e][idx$ - 1])
  );
  assume R[iir#a] == C[iir#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#b]) ==> (M[iir#b][idx$] == (85 * M[iir#a][idx$]))
  );
  assume R[iir#d] == C[iir#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#e]) ==> (M[iir#e][idx$] == (171 * M[iir#d][idx$]))
  );
  assume R[iir#c] == C[iir#g];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#g]) ==> (M[iir#g][idx$] == AT#RShift(M[iir#c][idx$], 8))
  );
  assume R[iir#b] == C[iir#c];
  assume R[iir#f] == C[iir#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#c]) ==> (M[iir#c][idx$] == (M[iir#b][idx$] + M[iir#f][idx$]))
  );
  assume R[iir#g] == C[iir#d];
  assume R[iir#g] == C[iir#h];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#d]) ==> (M[iir#d][idx$] == M[iir#g][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#h]) ==> (M[iir#h][idx$] == M[iir#g][idx$])
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
  var iir#a: Chan (int);
  var iir#b: Chan (int);
  var iir#c: Chan (int);
  var iir#d: Chan (int);
  var iir#e: Chan (int);
  var iir#f: Chan (int);
  var iir#g: Chan (int);
  var iir#h: Chan (int);
  var in#i: int;
  assume (iir#del1 != iir#mul1) && (iir#del1 != iir#mul2) && (iir#del1 != iir#rsh1) && (iir#del1 != iir#add1) && (iir#del1 != iir#spl1) && (iir#mul1 != iir#mul2) && (iir#mul1 != iir#rsh1) && (iir#mul1 != iir#add1) && (iir#mul1 != iir#spl1) && (iir#mul2 != iir#rsh1) && (iir#mul2 != iir#add1) && (iir#mul2 != iir#spl1) && (iir#rsh1 != iir#add1) && (iir#rsh1 != iir#spl1) && (iir#add1 != iir#spl1);
  assume (iir#a != iir#b) && (iir#a != iir#c) && (iir#a != iir#d) && (iir#a != iir#e) && (iir#a != iir#f) && (iir#a != iir#g) && (iir#a != iir#h) && (iir#b != iir#c) && (iir#b != iir#d) && (iir#b != iir#e) && (iir#b != iir#f) && (iir#b != iir#g) && (iir#b != iir#h) && (iir#c != iir#d) && (iir#c != iir#e) && (iir#c != iir#f) && (iir#c != iir#g) && (iir#c != iir#h) && (iir#d != iir#e) && (iir#d != iir#f) && (iir#d != iir#g) && (iir#d != iir#h) && (iir#e != iir#f) && (iir#e != iir#g) && (iir#e != iir#h) && (iir#f != iir#g) && (iir#f != iir#h) && (iir#g != iir#h);
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
  assume M[iir#f][0] == 0;
  assume R[iir#e] == (C[iir#f] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[iir#f]) ==> (M[iir#f][idx$] == M[iir#e][idx$ - 1])
  );
  assume R[iir#a] == C[iir#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#b]) ==> (M[iir#b][idx$] == (85 * M[iir#a][idx$]))
  );
  assume R[iir#d] == C[iir#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#e]) ==> (M[iir#e][idx$] == (171 * M[iir#d][idx$]))
  );
  assume R[iir#c] == C[iir#g];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#g]) ==> (M[iir#g][idx$] == AT#RShift(M[iir#c][idx$], 8))
  );
  assume R[iir#b] == C[iir#c];
  assume R[iir#f] == C[iir#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#c]) ==> (M[iir#c][idx$] == (M[iir#b][idx$] + M[iir#f][idx$]))
  );
  assume R[iir#g] == C[iir#d];
  assume R[iir#g] == C[iir#h];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#d]) ==> (M[iir#d][idx$] == M[iir#g][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#h]) ==> (M[iir#h][idx$] == M[iir#g][idx$])
  );
  assume 1 <= (C[iir#g] - R[iir#g]);
  assume R[iir#g] == C[iir#d];
  assume R[iir#g] == C[iir#h];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#d]) ==> (M[iir#d][idx$] == M[iir#g][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#h]) ==> (M[iir#h][idx$] == M[iir#g][idx$])
  );
  in#i := M[iir#g][R[iir#g]];
  R[iir#g] := R[iir#g] + 1;
  M[iir#d][C[iir#d]] := in#i;
  C[iir#d] := C[iir#d] + 1;
  M[iir#h][C[iir#h]] := in#i;
  C[iir#h] := C[iir#h] + 1;
  assume R[iir#g] == C[iir#d];
  assume R[iir#g] == C[iir#h];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#d]) ==> (M[iir#d][idx$] == M[iir#g][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#h]) ==> (M[iir#h][idx$] == M[iir#g][idx$])
  );
  assume M[iir#f][0] == 0;
  assume R[iir#e] == (C[iir#f] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[iir#f]) ==> (M[iir#f][idx$] == M[iir#e][idx$ - 1])
  );
  assume R[iir#a] == C[iir#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#b]) ==> (M[iir#b][idx$] == (85 * M[iir#a][idx$]))
  );
  assume R[iir#d] == C[iir#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#e]) ==> (M[iir#e][idx$] == (171 * M[iir#d][idx$]))
  );
  assume R[iir#c] == C[iir#g];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#g]) ==> (M[iir#g][idx$] == AT#RShift(M[iir#c][idx$], 8))
  );
  assume R[iir#b] == C[iir#c];
  assume R[iir#f] == C[iir#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#c]) ==> (M[iir#c][idx$] == (M[iir#b][idx$] + M[iir#f][idx$]))
  );
  assume R[iir#g] == C[iir#d];
  assume R[iir#g] == C[iir#h];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#d]) ==> (M[iir#d][idx$] == M[iir#g][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#h]) ==> (M[iir#h][idx$] == M[iir#g][idx$])
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
procedure iir#entry()
  modifies C, R, M, I;
{
  var iir#del1: Actor;
  var iir#mul1: Actor;
  var iir#mul2: Actor;
  var iir#rsh1: Actor;
  var iir#add1: Actor;
  var iir#spl1: Actor;
  var iir#a: Chan (int);
  var iir#b: Chan (int);
  var iir#c: Chan (int);
  var iir#d: Chan (int);
  var iir#e: Chan (int);
  var iir#f: Chan (int);
  var iir#g: Chan (int);
  var iir#h: Chan (int);
  assume (iir#del1 != iir#mul1) && (iir#del1 != iir#mul2) && (iir#del1 != iir#rsh1) && (iir#del1 != iir#add1) && (iir#del1 != iir#spl1) && (iir#mul1 != iir#mul2) && (iir#mul1 != iir#rsh1) && (iir#mul1 != iir#add1) && (iir#mul1 != iir#spl1) && (iir#mul2 != iir#rsh1) && (iir#mul2 != iir#add1) && (iir#mul2 != iir#spl1) && (iir#rsh1 != iir#add1) && (iir#rsh1 != iir#spl1) && (iir#add1 != iir#spl1);
  assume (iir#a != iir#b) && (iir#a != iir#c) && (iir#a != iir#d) && (iir#a != iir#e) && (iir#a != iir#f) && (iir#a != iir#g) && (iir#a != iir#h) && (iir#b != iir#c) && (iir#b != iir#d) && (iir#b != iir#e) && (iir#b != iir#f) && (iir#b != iir#g) && (iir#b != iir#h) && (iir#c != iir#d) && (iir#c != iir#e) && (iir#c != iir#f) && (iir#c != iir#g) && (iir#c != iir#h) && (iir#d != iir#e) && (iir#d != iir#f) && (iir#d != iir#g) && (iir#d != iir#h) && (iir#e != iir#f) && (iir#e != iir#g) && (iir#e != iir#h) && (iir#f != iir#g) && (iir#f != iir#h) && (iir#g != iir#h);
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
  assume C[iir#a] == R[iir#a];
  assume C[iir#b] == R[iir#b];
  assume C[iir#c] == R[iir#c];
  assume C[iir#d] == R[iir#d];
  assume C[iir#e] == R[iir#e];
  assume C[iir#f] == R[iir#f];
  assume C[iir#g] == R[iir#g];
  assume C[iir#h] == R[iir#h];
  C[iir#f] := C[iir#f] + 1;
  assume I[iir#f] == I[iir#e];
  assume I[iir#b] == I[iir#a];
  assume I[iir#e] == I[iir#d];
  assume I[iir#g] == I[iir#c];
  assume I[iir#c] == I[iir#b];
  assume I[iir#c] == I[iir#f];
  assume I[iir#d] == I[iir#g];
  assume I[iir#h] == I[iir#g];
  assume M[iir#f][0] == 0;
  assume R[iir#e] == (C[iir#f] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[iir#f]) ==> (M[iir#f][idx$] == M[iir#e][idx$ - 1])
  );
  assume R[iir#a] == C[iir#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#b]) ==> (M[iir#b][idx$] == (85 * M[iir#a][idx$]))
  );
  assume R[iir#d] == C[iir#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#e]) ==> (M[iir#e][idx$] == (171 * M[iir#d][idx$]))
  );
  assume R[iir#c] == C[iir#g];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#g]) ==> (M[iir#g][idx$] == AT#RShift(M[iir#c][idx$], 8))
  );
  assume R[iir#b] == C[iir#c];
  assume R[iir#f] == C[iir#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#c]) ==> (M[iir#c][idx$] == (M[iir#b][idx$] + M[iir#f][idx$]))
  );
  assume R[iir#g] == C[iir#d];
  assume R[iir#g] == C[iir#h];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#d]) ==> (M[iir#d][idx$] == M[iir#g][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#h]) ==> (M[iir#h][idx$] == M[iir#g][idx$])
  );
  assert {:msg "23.1: Sub-actors in the network might fire without network input. This is not permitted. (#92)"} !(1 <= (C[iir#e] - R[iir#e]));
  assert {:msg "23.1: Sub-actors in the network might fire without network input. This is not permitted. (#93)"} !(1 <= (C[iir#a] - R[iir#a]));
  assert {:msg "23.1: Sub-actors in the network might fire without network input. This is not permitted. (#94)"} !(1 <= (C[iir#d] - R[iir#d]));
  assert {:msg "23.1: Sub-actors in the network might fire without network input. This is not permitted. (#95)"} !(1 <= (C[iir#c] - R[iir#c]));
  assert {:msg "23.1: Sub-actors in the network might fire without network input. This is not permitted. (#96)"} !((1 <= (C[iir#b] - R[iir#b])) && (1 <= (C[iir#f] - R[iir#f])));
  assert {:msg "23.1: Sub-actors in the network might fire without network input. This is not permitted. (#97)"} !(1 <= (C[iir#g] - R[iir#g]));
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
  var iir#a: Chan (int);
  var iir#b: Chan (int);
  var iir#c: Chan (int);
  var iir#d: Chan (int);
  var iir#e: Chan (int);
  var iir#f: Chan (int);
  var iir#g: Chan (int);
  var iir#h: Chan (int);
  var x: int;
  assume (iir#del1 != iir#mul1) && (iir#del1 != iir#mul2) && (iir#del1 != iir#rsh1) && (iir#del1 != iir#add1) && (iir#del1 != iir#spl1) && (iir#mul1 != iir#mul2) && (iir#mul1 != iir#rsh1) && (iir#mul1 != iir#add1) && (iir#mul1 != iir#spl1) && (iir#mul2 != iir#rsh1) && (iir#mul2 != iir#add1) && (iir#mul2 != iir#spl1) && (iir#rsh1 != iir#add1) && (iir#rsh1 != iir#spl1) && (iir#add1 != iir#spl1);
  assume (iir#a != iir#b) && (iir#a != iir#c) && (iir#a != iir#d) && (iir#a != iir#e) && (iir#a != iir#f) && (iir#a != iir#g) && (iir#a != iir#h) && (iir#b != iir#c) && (iir#b != iir#d) && (iir#b != iir#e) && (iir#b != iir#f) && (iir#b != iir#g) && (iir#b != iir#h) && (iir#c != iir#d) && (iir#c != iir#e) && (iir#c != iir#f) && (iir#c != iir#g) && (iir#c != iir#h) && (iir#d != iir#e) && (iir#d != iir#f) && (iir#d != iir#g) && (iir#d != iir#h) && (iir#e != iir#f) && (iir#e != iir#g) && (iir#e != iir#h) && (iir#f != iir#g) && (iir#f != iir#h) && (iir#g != iir#h);
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
  assume M[iir#f][0] == 0;
  assume R[iir#e] == (C[iir#f] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[iir#f]) ==> (M[iir#f][idx$] == M[iir#e][idx$ - 1])
  );
  assume R[iir#a] == C[iir#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#b]) ==> (M[iir#b][idx$] == (85 * M[iir#a][idx$]))
  );
  assume R[iir#d] == C[iir#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#e]) ==> (M[iir#e][idx$] == (171 * M[iir#d][idx$]))
  );
  assume R[iir#c] == C[iir#g];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#g]) ==> (M[iir#g][idx$] == AT#RShift(M[iir#c][idx$], 8))
  );
  assume R[iir#b] == C[iir#c];
  assume R[iir#f] == C[iir#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#c]) ==> (M[iir#c][idx$] == (M[iir#b][idx$] + M[iir#f][idx$]))
  );
  assume R[iir#g] == C[iir#d];
  assume R[iir#g] == C[iir#h];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#d]) ==> (M[iir#d][idx$] == M[iir#g][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#h]) ==> (M[iir#h][idx$] == M[iir#g][idx$])
  );
  assume 0 <= x;
  C[iir#a] := C[iir#a] + x;
  assert {:msg "Channel invariant might be falsified by network input (#98)"} I[iir#f] == I[iir#e];
  assert {:msg "Channel invariant might be falsified by network input (#99)"} I[iir#b] == I[iir#a];
  assert {:msg "Channel invariant might be falsified by network input (#100)"} I[iir#e] == I[iir#d];
  assert {:msg "Channel invariant might be falsified by network input (#101)"} I[iir#g] == I[iir#c];
  assert {:msg "Channel invariant might be falsified by network input (#102)"} I[iir#c] == I[iir#b];
  assert {:msg "Channel invariant might be falsified by network input (#103)"} I[iir#c] == I[iir#f];
  assert {:msg "Channel invariant might be falsified by network input (#104)"} I[iir#d] == I[iir#g];
  assert {:msg "Channel invariant might be falsified by network input (#105)"} I[iir#h] == I[iir#g];
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
  var iir#a: Chan (int);
  var iir#b: Chan (int);
  var iir#c: Chan (int);
  var iir#d: Chan (int);
  var iir#e: Chan (int);
  var iir#f: Chan (int);
  var iir#g: Chan (int);
  var iir#h: Chan (int);
  assume (iir#del1 != iir#mul1) && (iir#del1 != iir#mul2) && (iir#del1 != iir#rsh1) && (iir#del1 != iir#add1) && (iir#del1 != iir#spl1) && (iir#mul1 != iir#mul2) && (iir#mul1 != iir#rsh1) && (iir#mul1 != iir#add1) && (iir#mul1 != iir#spl1) && (iir#mul2 != iir#rsh1) && (iir#mul2 != iir#add1) && (iir#mul2 != iir#spl1) && (iir#rsh1 != iir#add1) && (iir#rsh1 != iir#spl1) && (iir#add1 != iir#spl1);
  assume (iir#a != iir#b) && (iir#a != iir#c) && (iir#a != iir#d) && (iir#a != iir#e) && (iir#a != iir#f) && (iir#a != iir#g) && (iir#a != iir#h) && (iir#b != iir#c) && (iir#b != iir#d) && (iir#b != iir#e) && (iir#b != iir#f) && (iir#b != iir#g) && (iir#b != iir#h) && (iir#c != iir#d) && (iir#c != iir#e) && (iir#c != iir#f) && (iir#c != iir#g) && (iir#c != iir#h) && (iir#d != iir#e) && (iir#d != iir#f) && (iir#d != iir#g) && (iir#d != iir#h) && (iir#e != iir#f) && (iir#e != iir#g) && (iir#e != iir#h) && (iir#f != iir#g) && (iir#f != iir#h) && (iir#g != iir#h);
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
  assume M[iir#f][0] == 0;
  assume R[iir#e] == (C[iir#f] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[iir#f]) ==> (M[iir#f][idx$] == M[iir#e][idx$ - 1])
  );
  assume R[iir#a] == C[iir#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#b]) ==> (M[iir#b][idx$] == (85 * M[iir#a][idx$]))
  );
  assume R[iir#d] == C[iir#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#e]) ==> (M[iir#e][idx$] == (171 * M[iir#d][idx$]))
  );
  assume R[iir#c] == C[iir#g];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#g]) ==> (M[iir#g][idx$] == AT#RShift(M[iir#c][idx$], 8))
  );
  assume R[iir#b] == C[iir#c];
  assume R[iir#f] == C[iir#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#c]) ==> (M[iir#c][idx$] == (M[iir#b][idx$] + M[iir#f][idx$]))
  );
  assume R[iir#g] == C[iir#d];
  assume R[iir#g] == C[iir#h];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#d]) ==> (M[iir#d][idx$] == M[iir#g][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#h]) ==> (M[iir#h][idx$] == M[iir#g][idx$])
  );
  assume (C[iir#a] - I[iir#a]) == 1;
  assume !(1 <= (C[iir#e] - R[iir#e]));
  assume !(1 <= (C[iir#a] - R[iir#a]));
  assume !(1 <= (C[iir#d] - R[iir#d]));
  assume !(1 <= (C[iir#c] - R[iir#c]));
  assume !((1 <= (C[iir#b] - R[iir#b])) && (1 <= (C[iir#f] - R[iir#f])));
  assume !(1 <= (C[iir#g] - R[iir#g]));
  assert {:msg "26.13: Network action postcondition might not hold (#106)"} M[iir#h][0] == AT#RShift(85 * M[iir#a][0], 8);
  assert {:msg "27.13: Network action postcondition might not hold (#107)"} (0 < I[iir#h]) ==> (M[iir#h][I[iir#h]] == AT#RShift((171 * M[iir#h][I[iir#h] - 1]) + (85 * M[iir#a][I[iir#a]]), 8));
  R[iir#h] := R[iir#h] + 1;
  I := R;
  assert {:msg "The network might not preserve the channel invariant (#108)"} I[iir#f] == I[iir#e];
  assert {:msg "The network might not preserve the channel invariant (#109)"} I[iir#b] == I[iir#a];
  assert {:msg "The network might not preserve the channel invariant (#110)"} I[iir#e] == I[iir#d];
  assert {:msg "The network might not preserve the channel invariant (#111)"} I[iir#g] == I[iir#c];
  assert {:msg "The network might not preserve the channel invariant (#112)"} I[iir#c] == I[iir#b];
  assert {:msg "The network might not preserve the channel invariant (#113)"} I[iir#c] == I[iir#f];
  assert {:msg "The network might not preserve the channel invariant (#114)"} I[iir#d] == I[iir#g];
  assert {:msg "The network might not preserve the channel invariant (#115)"} I[iir#h] == I[iir#g];
  C[iir#f] := C[iir#f] - 1;
  assert {:msg "25.3: The network might leave unread tokens on channel a (#116)"} C[iir#a] == R[iir#a];
  assert {:msg "25.3: The network might leave unread tokens on channel b (#117)"} C[iir#b] == R[iir#b];
  assert {:msg "25.3: The network might leave unread tokens on channel c (#118)"} C[iir#c] == R[iir#c];
  assert {:msg "25.3: The network might leave unread tokens on channel d (#119)"} C[iir#d] == R[iir#d];
  assert {:msg "25.3: The network might leave unread tokens on channel e (#120)"} C[iir#e] == R[iir#e];
  assert {:msg "25.3: The network might leave unread tokens on channel f (#121)"} C[iir#f] == R[iir#f];
  assert {:msg "25.3: The network might leave unread tokens on channel g (#122)"} C[iir#g] == R[iir#g];
  assert {:msg "25.3: The network might not produce the specified number of tokens on output out (#123)"} C[iir#h] == R[iir#h];
}

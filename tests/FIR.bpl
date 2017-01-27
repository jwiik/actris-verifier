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

var M: MType;
var C: CType;
var R: CType;
var I: CType;

var H: HType;

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
  modifies C, R, M, I, H;
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
  modifies C, R, M, I, H;
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
  modifies C, R, M, I, H;
{
  var in: Chan (int);
  var out: Chan (int);
  var data: int;
  var y: int;
  var k: int;
  assume in != out;
  assume R[in] == 0;
  assume C[out] == 0;
  data := k;
  assert {:msg "9.20: Initialization might not establish the invariant (#6)"} (C[out] == 0) ==> (data == k);
  assert {:msg "10.20: Initialization might not establish the invariant (#7)"} (C[out] > 0) ==> (data == M[in][R[in] - 1]);
  assert {:msg "11.20: Initialization might not establish the invariant (#8)"} R[in] == C[out];
  assert {:msg "12.20: Initialization might not establish the invariant (#9)"} (C[out] > 0) ==> (M[out][0] == k);
  assert {:msg "13.21: Initialization might not establish the invariant (#10)"} (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[out] - 0)) ==> (M[out][idx] == M[in][idx - 1])
  );
}
procedure delay#anon$2#3()
  modifies C, R, M, I, H;
{
  var in: Chan (int);
  var out: Chan (int);
  var data: int;
  var y: int;
  var k: int;
  var in#0: int;
  assume in != out;
  assume 0 <= R[in];
  assume 0 <= C[out];
  assume (C[out] == 0) ==> (data == k);
  assume (C[out] > 0) ==> (data == M[in][R[in] - 1]);
  assume R[in] == C[out];
  assume (C[out] > 0) ==> (M[out][0] == k);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[out] - 0)) ==> (M[out][idx] == M[in][idx - 1])
  );
  in#0 := M[in][R[in]];
  R[in] := R[in] + 1;
  y := data;
  data := in#0;
  M[out][C[out]] := y;
  C[out] := C[out] + 1;
  assert {:msg "9.20: Action at 16.3 might not preserve invariant (#11)"} (C[out] == 0) ==> (data == k);
  assert {:msg "10.20: Action at 16.3 might not preserve invariant (#12)"} (C[out] > 0) ==> (data == M[in][R[in] - 1]);
  assert {:msg "11.20: Action at 16.3 might not preserve invariant (#13)"} R[in] == C[out];
  assert {:msg "12.20: Action at 16.3 might not preserve invariant (#14)"} (C[out] > 0) ==> (M[out][0] == k);
  assert {:msg "13.21: Action at 16.3 might not preserve invariant (#15)"} (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[out] - 0)) ==> (M[out][idx] == M[in][idx - 1])
  );
}
procedure mulc#init#4()
  modifies C, R, M, I, H;
{
  var in: Chan (int);
  var out: Chan (int);
  var c: int;
  assume in != out;
  assume R[in] == 0;
  assume C[out] == 0;
  assert {:msg "Initialization might not establish the invariant (#16)"} R[in] == C[out];
  assert {:msg "Initialization might not establish the invariant (#17)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == (c * M[in][idx$]))
  );
}
procedure mulc#anon$3#5()
  modifies C, R, M, I, H;
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
  assert {:msg "Action at 24.3 might not preserve invariant (#18)"} R[in] == C[out];
  assert {:msg "Action at 24.3 might not preserve invariant (#19)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == (c * M[in][idx$]))
  );
}
procedure rshiftc#init#6()
  modifies C, R, M, I, H;
{
  var in: Chan (int);
  var out: Chan (int);
  var s: int;
  assume in != out;
  assume R[in] == 0;
  assume C[out] == 0;
  assert {:msg "Initialization might not establish the invariant (#20)"} R[in] == C[out];
  assert {:msg "Initialization might not establish the invariant (#21)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == AT#RShift(M[in][idx$], s))
  );
}
procedure rshiftc#anon$4#7()
  modifies C, R, M, I, H;
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
  assert {:msg "Action at 28.3 might not preserve invariant (#22)"} R[in] == C[out];
  assert {:msg "Action at 28.3 might not preserve invariant (#23)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == AT#RShift(M[in][idx$], s))
  );
}
procedure split#init#8()
  modifies C, R, M, I, H;
{
  var in: Chan (int);
  var out1: Chan (int);
  var out2: Chan (int);
  assume (in != out1) && (in != out2) && (out1 != out2);
  assume R[in] == 0;
  assume C[out1] == 0;
  assume C[out2] == 0;
  assert {:msg "Initialization might not establish the invariant (#24)"} R[in] == C[out1];
  assert {:msg "Initialization might not establish the invariant (#25)"} R[in] == C[out2];
  assert {:msg "Initialization might not establish the invariant (#26)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out1]) ==> (M[out1][idx$] == M[in][idx$])
  );
  assert {:msg "Initialization might not establish the invariant (#27)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out2]) ==> (M[out2][idx$] == M[in][idx$])
  );
}
procedure split#anon$5#9()
  modifies C, R, M, I, H;
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
  assert {:msg "Action at 32.3 might not preserve invariant (#28)"} R[in] == C[out1];
  assert {:msg "Action at 32.3 might not preserve invariant (#29)"} R[in] == C[out2];
  assert {:msg "Action at 32.3 might not preserve invariant (#30)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out1]) ==> (M[out1][idx$] == M[in][idx$])
  );
  assert {:msg "Action at 32.3 might not preserve invariant (#31)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out2]) ==> (M[out2][idx$] == M[in][idx$])
  );
}
procedure iir#init#10()
  modifies C, R, M, I, H;
{
  var iir#delay_1: Actor;
  var iir#delay_2: Actor;
  var iir#delay_3: Actor;
  var iir#mul_1: Actor;
  var iir#mul_2: Actor;
  var iir#mul_3: Actor;
  var iir#mul_4: Actor;
  var iir#add_1: Actor;
  var iir#add_2: Actor;
  var iir#add_3: Actor;
  var iir#spl_1: Actor;
  var iir#spl_2: Actor;
  var iir#spl_3: Actor;
  var iir#anon$7: Chan (int);
  var iir#anon$8: Chan (int);
  var iir#anon$9: Chan (int);
  var iir#anon$10: Chan (int);
  var iir#anon$11: Chan (int);
  var iir#anon$12: Chan (int);
  var iir#anon$13: Chan (int);
  var iir#anon$14: Chan (int);
  var iir#anon$15: Chan (int);
  var iir#anon$16: Chan (int);
  var iir#anon$17: Chan (int);
  var iir#anon$18: Chan (int);
  var iir#anon$19: Chan (int);
  var iir#anon$20: Chan (int);
  var iir#anon$21: Chan (int);
  var iir#anon$22: Chan (int);
  var iir#anon$23: Chan (int);
  var AV#delay_1#data: int;
  var AV#delay_1#y: int;
  var AV#delay_2#data: int;
  var AV#delay_2#y: int;
  var AV#delay_3#data: int;
  var AV#delay_3#y: int;
  assume (iir#delay_1 != iir#delay_2) && (iir#delay_1 != iir#delay_3) && (iir#delay_1 != iir#mul_1) && (iir#delay_1 != iir#mul_2) && (iir#delay_1 != iir#mul_3) && (iir#delay_1 != iir#mul_4) && (iir#delay_1 != iir#add_1) && (iir#delay_1 != iir#add_2) && (iir#delay_1 != iir#add_3) && (iir#delay_1 != iir#spl_1) && (iir#delay_1 != iir#spl_2) && (iir#delay_1 != iir#spl_3) && (iir#delay_2 != iir#delay_3) && (iir#delay_2 != iir#mul_1) && (iir#delay_2 != iir#mul_2) && (iir#delay_2 != iir#mul_3) && (iir#delay_2 != iir#mul_4) && (iir#delay_2 != iir#add_1) && (iir#delay_2 != iir#add_2) && (iir#delay_2 != iir#add_3) && (iir#delay_2 != iir#spl_1) && (iir#delay_2 != iir#spl_2) && (iir#delay_2 != iir#spl_3) && (iir#delay_3 != iir#mul_1) && (iir#delay_3 != iir#mul_2) && (iir#delay_3 != iir#mul_3) && (iir#delay_3 != iir#mul_4) && (iir#delay_3 != iir#add_1) && (iir#delay_3 != iir#add_2) && (iir#delay_3 != iir#add_3) && (iir#delay_3 != iir#spl_1) && (iir#delay_3 != iir#spl_2) && (iir#delay_3 != iir#spl_3) && (iir#mul_1 != iir#mul_2) && (iir#mul_1 != iir#mul_3) && (iir#mul_1 != iir#mul_4) && (iir#mul_1 != iir#add_1) && (iir#mul_1 != iir#add_2) && (iir#mul_1 != iir#add_3) && (iir#mul_1 != iir#spl_1) && (iir#mul_1 != iir#spl_2) && (iir#mul_1 != iir#spl_3) && (iir#mul_2 != iir#mul_3) && (iir#mul_2 != iir#mul_4) && (iir#mul_2 != iir#add_1) && (iir#mul_2 != iir#add_2) && (iir#mul_2 != iir#add_3) && (iir#mul_2 != iir#spl_1) && (iir#mul_2 != iir#spl_2) && (iir#mul_2 != iir#spl_3) && (iir#mul_3 != iir#mul_4) && (iir#mul_3 != iir#add_1) && (iir#mul_3 != iir#add_2) && (iir#mul_3 != iir#add_3) && (iir#mul_3 != iir#spl_1) && (iir#mul_3 != iir#spl_2) && (iir#mul_3 != iir#spl_3) && (iir#mul_4 != iir#add_1) && (iir#mul_4 != iir#add_2) && (iir#mul_4 != iir#add_3) && (iir#mul_4 != iir#spl_1) && (iir#mul_4 != iir#spl_2) && (iir#mul_4 != iir#spl_3) && (iir#add_1 != iir#add_2) && (iir#add_1 != iir#add_3) && (iir#add_1 != iir#spl_1) && (iir#add_1 != iir#spl_2) && (iir#add_1 != iir#spl_3) && (iir#add_2 != iir#add_3) && (iir#add_2 != iir#spl_1) && (iir#add_2 != iir#spl_2) && (iir#add_2 != iir#spl_3) && (iir#add_3 != iir#spl_1) && (iir#add_3 != iir#spl_2) && (iir#add_3 != iir#spl_3) && (iir#spl_1 != iir#spl_2) && (iir#spl_1 != iir#spl_3) && (iir#spl_2 != iir#spl_3);
  assume (iir#anon$7 != iir#anon$8) && (iir#anon$7 != iir#anon$9) && (iir#anon$7 != iir#anon$10) && (iir#anon$7 != iir#anon$11) && (iir#anon$7 != iir#anon$12) && (iir#anon$7 != iir#anon$13) && (iir#anon$7 != iir#anon$14) && (iir#anon$7 != iir#anon$15) && (iir#anon$7 != iir#anon$16) && (iir#anon$7 != iir#anon$17) && (iir#anon$7 != iir#anon$18) && (iir#anon$7 != iir#anon$19) && (iir#anon$7 != iir#anon$20) && (iir#anon$7 != iir#anon$21) && (iir#anon$7 != iir#anon$22) && (iir#anon$7 != iir#anon$23) && (iir#anon$8 != iir#anon$9) && (iir#anon$8 != iir#anon$10) && (iir#anon$8 != iir#anon$11) && (iir#anon$8 != iir#anon$12) && (iir#anon$8 != iir#anon$13) && (iir#anon$8 != iir#anon$14) && (iir#anon$8 != iir#anon$15) && (iir#anon$8 != iir#anon$16) && (iir#anon$8 != iir#anon$17) && (iir#anon$8 != iir#anon$18) && (iir#anon$8 != iir#anon$19) && (iir#anon$8 != iir#anon$20) && (iir#anon$8 != iir#anon$21) && (iir#anon$8 != iir#anon$22) && (iir#anon$8 != iir#anon$23) && (iir#anon$9 != iir#anon$10) && (iir#anon$9 != iir#anon$11) && (iir#anon$9 != iir#anon$12) && (iir#anon$9 != iir#anon$13) && (iir#anon$9 != iir#anon$14) && (iir#anon$9 != iir#anon$15) && (iir#anon$9 != iir#anon$16) && (iir#anon$9 != iir#anon$17) && (iir#anon$9 != iir#anon$18) && (iir#anon$9 != iir#anon$19) && (iir#anon$9 != iir#anon$20) && (iir#anon$9 != iir#anon$21) && (iir#anon$9 != iir#anon$22) && (iir#anon$9 != iir#anon$23) && (iir#anon$10 != iir#anon$11) && (iir#anon$10 != iir#anon$12) && (iir#anon$10 != iir#anon$13) && (iir#anon$10 != iir#anon$14) && (iir#anon$10 != iir#anon$15) && (iir#anon$10 != iir#anon$16) && (iir#anon$10 != iir#anon$17) && (iir#anon$10 != iir#anon$18) && (iir#anon$10 != iir#anon$19) && (iir#anon$10 != iir#anon$20) && (iir#anon$10 != iir#anon$21) && (iir#anon$10 != iir#anon$22) && (iir#anon$10 != iir#anon$23) && (iir#anon$11 != iir#anon$12) && (iir#anon$11 != iir#anon$13) && (iir#anon$11 != iir#anon$14) && (iir#anon$11 != iir#anon$15) && (iir#anon$11 != iir#anon$16) && (iir#anon$11 != iir#anon$17) && (iir#anon$11 != iir#anon$18) && (iir#anon$11 != iir#anon$19) && (iir#anon$11 != iir#anon$20) && (iir#anon$11 != iir#anon$21) && (iir#anon$11 != iir#anon$22) && (iir#anon$11 != iir#anon$23) && (iir#anon$12 != iir#anon$13) && (iir#anon$12 != iir#anon$14) && (iir#anon$12 != iir#anon$15) && (iir#anon$12 != iir#anon$16) && (iir#anon$12 != iir#anon$17) && (iir#anon$12 != iir#anon$18) && (iir#anon$12 != iir#anon$19) && (iir#anon$12 != iir#anon$20) && (iir#anon$12 != iir#anon$21) && (iir#anon$12 != iir#anon$22) && (iir#anon$12 != iir#anon$23) && (iir#anon$13 != iir#anon$14) && (iir#anon$13 != iir#anon$15) && (iir#anon$13 != iir#anon$16) && (iir#anon$13 != iir#anon$17) && (iir#anon$13 != iir#anon$18) && (iir#anon$13 != iir#anon$19) && (iir#anon$13 != iir#anon$20) && (iir#anon$13 != iir#anon$21) && (iir#anon$13 != iir#anon$22) && (iir#anon$13 != iir#anon$23) && (iir#anon$14 != iir#anon$15) && (iir#anon$14 != iir#anon$16) && (iir#anon$14 != iir#anon$17) && (iir#anon$14 != iir#anon$18) && (iir#anon$14 != iir#anon$19) && (iir#anon$14 != iir#anon$20) && (iir#anon$14 != iir#anon$21) && (iir#anon$14 != iir#anon$22) && (iir#anon$14 != iir#anon$23) && (iir#anon$15 != iir#anon$16) && (iir#anon$15 != iir#anon$17) && (iir#anon$15 != iir#anon$18) && (iir#anon$15 != iir#anon$19) && (iir#anon$15 != iir#anon$20) && (iir#anon$15 != iir#anon$21) && (iir#anon$15 != iir#anon$22) && (iir#anon$15 != iir#anon$23) && (iir#anon$16 != iir#anon$17) && (iir#anon$16 != iir#anon$18) && (iir#anon$16 != iir#anon$19) && (iir#anon$16 != iir#anon$20) && (iir#anon$16 != iir#anon$21) && (iir#anon$16 != iir#anon$22) && (iir#anon$16 != iir#anon$23) && (iir#anon$17 != iir#anon$18) && (iir#anon$17 != iir#anon$19) && (iir#anon$17 != iir#anon$20) && (iir#anon$17 != iir#anon$21) && (iir#anon$17 != iir#anon$22) && (iir#anon$17 != iir#anon$23) && (iir#anon$18 != iir#anon$19) && (iir#anon$18 != iir#anon$20) && (iir#anon$18 != iir#anon$21) && (iir#anon$18 != iir#anon$22) && (iir#anon$18 != iir#anon$23) && (iir#anon$19 != iir#anon$20) && (iir#anon$19 != iir#anon$21) && (iir#anon$19 != iir#anon$22) && (iir#anon$19 != iir#anon$23) && (iir#anon$20 != iir#anon$21) && (iir#anon$20 != iir#anon$22) && (iir#anon$20 != iir#anon$23) && (iir#anon$21 != iir#anon$22) && (iir#anon$21 != iir#anon$23) && (iir#anon$22 != iir#anon$23);
  assume 0 <= I[iir#anon$7];
  assume I[iir#anon$7] <= R[iir#anon$7];
  assume R[iir#anon$7] <= C[iir#anon$7];
  assume 0 <= I[iir#anon$8];
  assume I[iir#anon$8] <= R[iir#anon$8];
  assume R[iir#anon$8] <= C[iir#anon$8];
  assume 0 <= I[iir#anon$9];
  assume I[iir#anon$9] <= R[iir#anon$9];
  assume R[iir#anon$9] <= C[iir#anon$9];
  assume 0 <= I[iir#anon$10];
  assume I[iir#anon$10] <= R[iir#anon$10];
  assume R[iir#anon$10] <= C[iir#anon$10];
  assume 0 <= I[iir#anon$11];
  assume I[iir#anon$11] <= R[iir#anon$11];
  assume R[iir#anon$11] <= C[iir#anon$11];
  assume 0 <= I[iir#anon$12];
  assume I[iir#anon$12] <= R[iir#anon$12];
  assume R[iir#anon$12] <= C[iir#anon$12];
  assume 0 <= I[iir#anon$13];
  assume I[iir#anon$13] <= R[iir#anon$13];
  assume R[iir#anon$13] <= C[iir#anon$13];
  assume 0 <= I[iir#anon$14];
  assume I[iir#anon$14] <= R[iir#anon$14];
  assume R[iir#anon$14] <= C[iir#anon$14];
  assume 0 <= I[iir#anon$15];
  assume I[iir#anon$15] <= R[iir#anon$15];
  assume R[iir#anon$15] <= C[iir#anon$15];
  assume 0 <= I[iir#anon$16];
  assume I[iir#anon$16] <= R[iir#anon$16];
  assume R[iir#anon$16] <= C[iir#anon$16];
  assume 0 <= I[iir#anon$17];
  assume I[iir#anon$17] <= R[iir#anon$17];
  assume R[iir#anon$17] <= C[iir#anon$17];
  assume 0 <= I[iir#anon$18];
  assume I[iir#anon$18] <= R[iir#anon$18];
  assume R[iir#anon$18] <= C[iir#anon$18];
  assume 0 <= I[iir#anon$19];
  assume I[iir#anon$19] <= R[iir#anon$19];
  assume R[iir#anon$19] <= C[iir#anon$19];
  assume 0 <= I[iir#anon$20];
  assume I[iir#anon$20] <= R[iir#anon$20];
  assume R[iir#anon$20] <= C[iir#anon$20];
  assume 0 <= I[iir#anon$21];
  assume I[iir#anon$21] <= R[iir#anon$21];
  assume R[iir#anon$21] <= C[iir#anon$21];
  assume 0 <= I[iir#anon$22];
  assume I[iir#anon$22] <= R[iir#anon$22];
  assume R[iir#anon$22] <= C[iir#anon$22];
  assume 0 <= I[iir#anon$23];
  assume I[iir#anon$23] <= R[iir#anon$23];
  assume R[iir#anon$23] <= C[iir#anon$23];
  assume I[iir#anon$23] == R[iir#anon$23];
  assume C[iir#anon$7] == 0;
  assume R[iir#anon$7] == 0;
  assume C[iir#anon$8] == 0;
  assume R[iir#anon$8] == 0;
  assume C[iir#anon$9] == 0;
  assume R[iir#anon$9] == 0;
  assume C[iir#anon$10] == 0;
  assume R[iir#anon$10] == 0;
  assume C[iir#anon$11] == 0;
  assume R[iir#anon$11] == 0;
  assume C[iir#anon$12] == 0;
  assume R[iir#anon$12] == 0;
  assume C[iir#anon$13] == 0;
  assume R[iir#anon$13] == 0;
  assume C[iir#anon$14] == 0;
  assume R[iir#anon$14] == 0;
  assume C[iir#anon$15] == 0;
  assume R[iir#anon$15] == 0;
  assume C[iir#anon$16] == 0;
  assume R[iir#anon$16] == 0;
  assume C[iir#anon$17] == 0;
  assume R[iir#anon$17] == 0;
  assume C[iir#anon$18] == 0;
  assume R[iir#anon$18] == 0;
  assume C[iir#anon$19] == 0;
  assume R[iir#anon$19] == 0;
  assume C[iir#anon$20] == 0;
  assume R[iir#anon$20] == 0;
  assume C[iir#anon$21] == 0;
  assume R[iir#anon$21] == 0;
  assume C[iir#anon$22] == 0;
  assume R[iir#anon$22] == 0;
  assume C[iir#anon$23] == 0;
  assume R[iir#anon$23] == 0;
  assume 0 == 0;
  assume 0 == 0;
  assume 0 == 0;
  assume 37 == 37;
  assume 109 == 109;
  assume 109 == 109;
  assume 37 == 37;
  assert {:msg "Initialization of network 'iir' might not establish the channel invariant (#32)"} I[iir#anon$17] == I[iir#anon$8];
  assert {:msg "Initialization of network 'iir' might not establish the channel invariant (#33)"} I[iir#anon$18] == I[iir#anon$11];
  assert {:msg "Initialization of network 'iir' might not establish the channel invariant (#34)"} I[iir#anon$19] == I[iir#anon$14];
  assert {:msg "Initialization of network 'iir' might not establish the channel invariant (#35)"} I[iir#anon$20] == I[iir#anon$16];
  assert {:msg "Initialization of network 'iir' might not establish the channel invariant (#36)"} I[iir#anon$21] == I[iir#anon$17];
  assert {:msg "Initialization of network 'iir' might not establish the channel invariant (#37)"} I[iir#anon$21] == I[iir#anon$18];
  assert {:msg "Initialization of network 'iir' might not establish the channel invariant (#38)"} I[iir#anon$22] == I[iir#anon$19];
  assert {:msg "Initialization of network 'iir' might not establish the channel invariant (#39)"} I[iir#anon$22] == I[iir#anon$20];
  assert {:msg "Initialization of network 'iir' might not establish the channel invariant (#40)"} I[iir#anon$23] == I[iir#anon$21];
  assert {:msg "Initialization of network 'iir' might not establish the channel invariant (#41)"} I[iir#anon$23] == I[iir#anon$22];
  assert {:msg "Initialization of network 'iir' might not establish the channel invariant (#42)"} I[iir#anon$8] == I[iir#anon$7];
  assert {:msg "Initialization of network 'iir' might not establish the channel invariant (#43)"} I[iir#anon$9] == I[iir#anon$7];
  assert {:msg "Initialization of network 'iir' might not establish the channel invariant (#44)"} I[iir#anon$11] == I[iir#anon$10];
  assert {:msg "Initialization of network 'iir' might not establish the channel invariant (#45)"} I[iir#anon$12] == I[iir#anon$10];
  assert {:msg "Initialization of network 'iir' might not establish the channel invariant (#46)"} I[iir#anon$14] == I[iir#anon$13];
  assert {:msg "Initialization of network 'iir' might not establish the channel invariant (#47)"} I[iir#anon$15] == I[iir#anon$13];
  I := R;
  assert {:msg "Initialization of network 'iir' might not establish the network invariant: Unread tokens might be left on channel anon$7 (#48)"} (C[iir#anon$7] - R[iir#anon$7]) == 0;
  assert {:msg "Initialization of network 'iir' might not establish the network invariant: Unread tokens might be left on channel anon$8 (#49)"} (C[iir#anon$8] - R[iir#anon$8]) == 0;
  assert {:msg "Initialization of network 'iir' might not establish the network invariant: Unread tokens might be left on channel anon$9 (#50)"} (C[iir#anon$9] - R[iir#anon$9]) == 0;
  assert {:msg "Initialization of network 'iir' might not establish the network invariant: Unread tokens might be left on channel anon$10 (#51)"} (C[iir#anon$10] - R[iir#anon$10]) == 0;
  assert {:msg "Initialization of network 'iir' might not establish the network invariant: Unread tokens might be left on channel anon$11 (#52)"} (C[iir#anon$11] - R[iir#anon$11]) == 0;
  assert {:msg "Initialization of network 'iir' might not establish the network invariant: Unread tokens might be left on channel anon$12 (#53)"} (C[iir#anon$12] - R[iir#anon$12]) == 0;
  assert {:msg "Initialization of network 'iir' might not establish the network invariant: Unread tokens might be left on channel anon$13 (#54)"} (C[iir#anon$13] - R[iir#anon$13]) == 0;
  assert {:msg "Initialization of network 'iir' might not establish the network invariant: Unread tokens might be left on channel anon$14 (#55)"} (C[iir#anon$14] - R[iir#anon$14]) == 0;
  assert {:msg "Initialization of network 'iir' might not establish the network invariant: Unread tokens might be left on channel anon$15 (#56)"} (C[iir#anon$15] - R[iir#anon$15]) == 0;
  assert {:msg "Initialization of network 'iir' might not establish the network invariant: Unread tokens might be left on channel anon$16 (#57)"} (C[iir#anon$16] - R[iir#anon$16]) == 0;
  assert {:msg "Initialization of network 'iir' might not establish the network invariant: Unread tokens might be left on channel anon$17 (#58)"} (C[iir#anon$17] - R[iir#anon$17]) == 0;
  assert {:msg "Initialization of network 'iir' might not establish the network invariant: Unread tokens might be left on channel anon$18 (#59)"} (C[iir#anon$18] - R[iir#anon$18]) == 0;
  assert {:msg "Initialization of network 'iir' might not establish the network invariant: Unread tokens might be left on channel anon$19 (#60)"} (C[iir#anon$19] - R[iir#anon$19]) == 0;
  assert {:msg "Initialization of network 'iir' might not establish the network invariant: Unread tokens might be left on channel anon$20 (#61)"} (C[iir#anon$20] - R[iir#anon$20]) == 0;
  assert {:msg "Initialization of network 'iir' might not establish the network invariant: Unread tokens might be left on channel anon$21 (#62)"} (C[iir#anon$21] - R[iir#anon$21]) == 0;
  assert {:msg "Initialization of network 'iir' might not establish the network invariant: Unread tokens might be left on channel anon$22 (#63)"} (C[iir#anon$22] - R[iir#anon$22]) == 0;
  assert {:msg "Initialization of network 'iir' might not establish the network invariant: Unread tokens might be left on channel anon$23 (#64)"} (C[iir#anon$23] - R[iir#anon$23]) == 0;
}
procedure iir##delay#anon$2#11()
  modifies C, R, M, I, H;
{
  var iir#delay_1: Actor;
  var iir#delay_2: Actor;
  var iir#delay_3: Actor;
  var iir#mul_1: Actor;
  var iir#mul_2: Actor;
  var iir#mul_3: Actor;
  var iir#mul_4: Actor;
  var iir#add_1: Actor;
  var iir#add_2: Actor;
  var iir#add_3: Actor;
  var iir#spl_1: Actor;
  var iir#spl_2: Actor;
  var iir#spl_3: Actor;
  var iir#anon$7: Chan (int);
  var iir#anon$8: Chan (int);
  var iir#anon$9: Chan (int);
  var iir#anon$10: Chan (int);
  var iir#anon$11: Chan (int);
  var iir#anon$12: Chan (int);
  var iir#anon$13: Chan (int);
  var iir#anon$14: Chan (int);
  var iir#anon$15: Chan (int);
  var iir#anon$16: Chan (int);
  var iir#anon$17: Chan (int);
  var iir#anon$18: Chan (int);
  var iir#anon$19: Chan (int);
  var iir#anon$20: Chan (int);
  var iir#anon$21: Chan (int);
  var iir#anon$22: Chan (int);
  var iir#anon$23: Chan (int);
  var AV#delay_1#data: int;
  var AV#delay_1#y: int;
  var AV#delay_2#data: int;
  var AV#delay_2#y: int;
  var AV#delay_3#data: int;
  var AV#delay_3#y: int;
  var in#i: int;
  assume (iir#delay_1 != iir#delay_2) && (iir#delay_1 != iir#delay_3) && (iir#delay_1 != iir#mul_1) && (iir#delay_1 != iir#mul_2) && (iir#delay_1 != iir#mul_3) && (iir#delay_1 != iir#mul_4) && (iir#delay_1 != iir#add_1) && (iir#delay_1 != iir#add_2) && (iir#delay_1 != iir#add_3) && (iir#delay_1 != iir#spl_1) && (iir#delay_1 != iir#spl_2) && (iir#delay_1 != iir#spl_3) && (iir#delay_2 != iir#delay_3) && (iir#delay_2 != iir#mul_1) && (iir#delay_2 != iir#mul_2) && (iir#delay_2 != iir#mul_3) && (iir#delay_2 != iir#mul_4) && (iir#delay_2 != iir#add_1) && (iir#delay_2 != iir#add_2) && (iir#delay_2 != iir#add_3) && (iir#delay_2 != iir#spl_1) && (iir#delay_2 != iir#spl_2) && (iir#delay_2 != iir#spl_3) && (iir#delay_3 != iir#mul_1) && (iir#delay_3 != iir#mul_2) && (iir#delay_3 != iir#mul_3) && (iir#delay_3 != iir#mul_4) && (iir#delay_3 != iir#add_1) && (iir#delay_3 != iir#add_2) && (iir#delay_3 != iir#add_3) && (iir#delay_3 != iir#spl_1) && (iir#delay_3 != iir#spl_2) && (iir#delay_3 != iir#spl_3) && (iir#mul_1 != iir#mul_2) && (iir#mul_1 != iir#mul_3) && (iir#mul_1 != iir#mul_4) && (iir#mul_1 != iir#add_1) && (iir#mul_1 != iir#add_2) && (iir#mul_1 != iir#add_3) && (iir#mul_1 != iir#spl_1) && (iir#mul_1 != iir#spl_2) && (iir#mul_1 != iir#spl_3) && (iir#mul_2 != iir#mul_3) && (iir#mul_2 != iir#mul_4) && (iir#mul_2 != iir#add_1) && (iir#mul_2 != iir#add_2) && (iir#mul_2 != iir#add_3) && (iir#mul_2 != iir#spl_1) && (iir#mul_2 != iir#spl_2) && (iir#mul_2 != iir#spl_3) && (iir#mul_3 != iir#mul_4) && (iir#mul_3 != iir#add_1) && (iir#mul_3 != iir#add_2) && (iir#mul_3 != iir#add_3) && (iir#mul_3 != iir#spl_1) && (iir#mul_3 != iir#spl_2) && (iir#mul_3 != iir#spl_3) && (iir#mul_4 != iir#add_1) && (iir#mul_4 != iir#add_2) && (iir#mul_4 != iir#add_3) && (iir#mul_4 != iir#spl_1) && (iir#mul_4 != iir#spl_2) && (iir#mul_4 != iir#spl_3) && (iir#add_1 != iir#add_2) && (iir#add_1 != iir#add_3) && (iir#add_1 != iir#spl_1) && (iir#add_1 != iir#spl_2) && (iir#add_1 != iir#spl_3) && (iir#add_2 != iir#add_3) && (iir#add_2 != iir#spl_1) && (iir#add_2 != iir#spl_2) && (iir#add_2 != iir#spl_3) && (iir#add_3 != iir#spl_1) && (iir#add_3 != iir#spl_2) && (iir#add_3 != iir#spl_3) && (iir#spl_1 != iir#spl_2) && (iir#spl_1 != iir#spl_3) && (iir#spl_2 != iir#spl_3);
  assume (iir#anon$7 != iir#anon$8) && (iir#anon$7 != iir#anon$9) && (iir#anon$7 != iir#anon$10) && (iir#anon$7 != iir#anon$11) && (iir#anon$7 != iir#anon$12) && (iir#anon$7 != iir#anon$13) && (iir#anon$7 != iir#anon$14) && (iir#anon$7 != iir#anon$15) && (iir#anon$7 != iir#anon$16) && (iir#anon$7 != iir#anon$17) && (iir#anon$7 != iir#anon$18) && (iir#anon$7 != iir#anon$19) && (iir#anon$7 != iir#anon$20) && (iir#anon$7 != iir#anon$21) && (iir#anon$7 != iir#anon$22) && (iir#anon$7 != iir#anon$23) && (iir#anon$8 != iir#anon$9) && (iir#anon$8 != iir#anon$10) && (iir#anon$8 != iir#anon$11) && (iir#anon$8 != iir#anon$12) && (iir#anon$8 != iir#anon$13) && (iir#anon$8 != iir#anon$14) && (iir#anon$8 != iir#anon$15) && (iir#anon$8 != iir#anon$16) && (iir#anon$8 != iir#anon$17) && (iir#anon$8 != iir#anon$18) && (iir#anon$8 != iir#anon$19) && (iir#anon$8 != iir#anon$20) && (iir#anon$8 != iir#anon$21) && (iir#anon$8 != iir#anon$22) && (iir#anon$8 != iir#anon$23) && (iir#anon$9 != iir#anon$10) && (iir#anon$9 != iir#anon$11) && (iir#anon$9 != iir#anon$12) && (iir#anon$9 != iir#anon$13) && (iir#anon$9 != iir#anon$14) && (iir#anon$9 != iir#anon$15) && (iir#anon$9 != iir#anon$16) && (iir#anon$9 != iir#anon$17) && (iir#anon$9 != iir#anon$18) && (iir#anon$9 != iir#anon$19) && (iir#anon$9 != iir#anon$20) && (iir#anon$9 != iir#anon$21) && (iir#anon$9 != iir#anon$22) && (iir#anon$9 != iir#anon$23) && (iir#anon$10 != iir#anon$11) && (iir#anon$10 != iir#anon$12) && (iir#anon$10 != iir#anon$13) && (iir#anon$10 != iir#anon$14) && (iir#anon$10 != iir#anon$15) && (iir#anon$10 != iir#anon$16) && (iir#anon$10 != iir#anon$17) && (iir#anon$10 != iir#anon$18) && (iir#anon$10 != iir#anon$19) && (iir#anon$10 != iir#anon$20) && (iir#anon$10 != iir#anon$21) && (iir#anon$10 != iir#anon$22) && (iir#anon$10 != iir#anon$23) && (iir#anon$11 != iir#anon$12) && (iir#anon$11 != iir#anon$13) && (iir#anon$11 != iir#anon$14) && (iir#anon$11 != iir#anon$15) && (iir#anon$11 != iir#anon$16) && (iir#anon$11 != iir#anon$17) && (iir#anon$11 != iir#anon$18) && (iir#anon$11 != iir#anon$19) && (iir#anon$11 != iir#anon$20) && (iir#anon$11 != iir#anon$21) && (iir#anon$11 != iir#anon$22) && (iir#anon$11 != iir#anon$23) && (iir#anon$12 != iir#anon$13) && (iir#anon$12 != iir#anon$14) && (iir#anon$12 != iir#anon$15) && (iir#anon$12 != iir#anon$16) && (iir#anon$12 != iir#anon$17) && (iir#anon$12 != iir#anon$18) && (iir#anon$12 != iir#anon$19) && (iir#anon$12 != iir#anon$20) && (iir#anon$12 != iir#anon$21) && (iir#anon$12 != iir#anon$22) && (iir#anon$12 != iir#anon$23) && (iir#anon$13 != iir#anon$14) && (iir#anon$13 != iir#anon$15) && (iir#anon$13 != iir#anon$16) && (iir#anon$13 != iir#anon$17) && (iir#anon$13 != iir#anon$18) && (iir#anon$13 != iir#anon$19) && (iir#anon$13 != iir#anon$20) && (iir#anon$13 != iir#anon$21) && (iir#anon$13 != iir#anon$22) && (iir#anon$13 != iir#anon$23) && (iir#anon$14 != iir#anon$15) && (iir#anon$14 != iir#anon$16) && (iir#anon$14 != iir#anon$17) && (iir#anon$14 != iir#anon$18) && (iir#anon$14 != iir#anon$19) && (iir#anon$14 != iir#anon$20) && (iir#anon$14 != iir#anon$21) && (iir#anon$14 != iir#anon$22) && (iir#anon$14 != iir#anon$23) && (iir#anon$15 != iir#anon$16) && (iir#anon$15 != iir#anon$17) && (iir#anon$15 != iir#anon$18) && (iir#anon$15 != iir#anon$19) && (iir#anon$15 != iir#anon$20) && (iir#anon$15 != iir#anon$21) && (iir#anon$15 != iir#anon$22) && (iir#anon$15 != iir#anon$23) && (iir#anon$16 != iir#anon$17) && (iir#anon$16 != iir#anon$18) && (iir#anon$16 != iir#anon$19) && (iir#anon$16 != iir#anon$20) && (iir#anon$16 != iir#anon$21) && (iir#anon$16 != iir#anon$22) && (iir#anon$16 != iir#anon$23) && (iir#anon$17 != iir#anon$18) && (iir#anon$17 != iir#anon$19) && (iir#anon$17 != iir#anon$20) && (iir#anon$17 != iir#anon$21) && (iir#anon$17 != iir#anon$22) && (iir#anon$17 != iir#anon$23) && (iir#anon$18 != iir#anon$19) && (iir#anon$18 != iir#anon$20) && (iir#anon$18 != iir#anon$21) && (iir#anon$18 != iir#anon$22) && (iir#anon$18 != iir#anon$23) && (iir#anon$19 != iir#anon$20) && (iir#anon$19 != iir#anon$21) && (iir#anon$19 != iir#anon$22) && (iir#anon$19 != iir#anon$23) && (iir#anon$20 != iir#anon$21) && (iir#anon$20 != iir#anon$22) && (iir#anon$20 != iir#anon$23) && (iir#anon$21 != iir#anon$22) && (iir#anon$21 != iir#anon$23) && (iir#anon$22 != iir#anon$23);
  assume 0 <= I[iir#anon$7];
  assume I[iir#anon$7] <= R[iir#anon$7];
  assume R[iir#anon$7] <= C[iir#anon$7];
  assume 0 <= I[iir#anon$8];
  assume I[iir#anon$8] <= R[iir#anon$8];
  assume R[iir#anon$8] <= C[iir#anon$8];
  assume 0 <= I[iir#anon$9];
  assume I[iir#anon$9] <= R[iir#anon$9];
  assume R[iir#anon$9] <= C[iir#anon$9];
  assume 0 <= I[iir#anon$10];
  assume I[iir#anon$10] <= R[iir#anon$10];
  assume R[iir#anon$10] <= C[iir#anon$10];
  assume 0 <= I[iir#anon$11];
  assume I[iir#anon$11] <= R[iir#anon$11];
  assume R[iir#anon$11] <= C[iir#anon$11];
  assume 0 <= I[iir#anon$12];
  assume I[iir#anon$12] <= R[iir#anon$12];
  assume R[iir#anon$12] <= C[iir#anon$12];
  assume 0 <= I[iir#anon$13];
  assume I[iir#anon$13] <= R[iir#anon$13];
  assume R[iir#anon$13] <= C[iir#anon$13];
  assume 0 <= I[iir#anon$14];
  assume I[iir#anon$14] <= R[iir#anon$14];
  assume R[iir#anon$14] <= C[iir#anon$14];
  assume 0 <= I[iir#anon$15];
  assume I[iir#anon$15] <= R[iir#anon$15];
  assume R[iir#anon$15] <= C[iir#anon$15];
  assume 0 <= I[iir#anon$16];
  assume I[iir#anon$16] <= R[iir#anon$16];
  assume R[iir#anon$16] <= C[iir#anon$16];
  assume 0 <= I[iir#anon$17];
  assume I[iir#anon$17] <= R[iir#anon$17];
  assume R[iir#anon$17] <= C[iir#anon$17];
  assume 0 <= I[iir#anon$18];
  assume I[iir#anon$18] <= R[iir#anon$18];
  assume R[iir#anon$18] <= C[iir#anon$18];
  assume 0 <= I[iir#anon$19];
  assume I[iir#anon$19] <= R[iir#anon$19];
  assume R[iir#anon$19] <= C[iir#anon$19];
  assume 0 <= I[iir#anon$20];
  assume I[iir#anon$20] <= R[iir#anon$20];
  assume R[iir#anon$20] <= C[iir#anon$20];
  assume 0 <= I[iir#anon$21];
  assume I[iir#anon$21] <= R[iir#anon$21];
  assume R[iir#anon$21] <= C[iir#anon$21];
  assume 0 <= I[iir#anon$22];
  assume I[iir#anon$22] <= R[iir#anon$22];
  assume R[iir#anon$22] <= C[iir#anon$22];
  assume 0 <= I[iir#anon$23];
  assume I[iir#anon$23] <= R[iir#anon$23];
  assume R[iir#anon$23] <= C[iir#anon$23];
  assume I[iir#anon$23] == R[iir#anon$23];
  assume I[iir#anon$17] == I[iir#anon$8];
  assume I[iir#anon$18] == I[iir#anon$11];
  assume I[iir#anon$19] == I[iir#anon$14];
  assume I[iir#anon$20] == I[iir#anon$16];
  assume I[iir#anon$21] == I[iir#anon$17];
  assume I[iir#anon$21] == I[iir#anon$18];
  assume I[iir#anon$22] == I[iir#anon$19];
  assume I[iir#anon$22] == I[iir#anon$20];
  assume I[iir#anon$23] == I[iir#anon$21];
  assume I[iir#anon$23] == I[iir#anon$22];
  assume I[iir#anon$8] == I[iir#anon$7];
  assume I[iir#anon$9] == I[iir#anon$7];
  assume I[iir#anon$11] == I[iir#anon$10];
  assume I[iir#anon$12] == I[iir#anon$10];
  assume I[iir#anon$14] == I[iir#anon$13];
  assume I[iir#anon$15] == I[iir#anon$13];
  assume (C[iir#anon$10] == 0) ==> (AV#delay_1#data == 0);
  assume (C[iir#anon$10] > 0) ==> (AV#delay_1#data == M[iir#anon$9][R[iir#anon$9] - 1]);
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$10] > 0) ==> (M[iir#anon$10][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$10] - 0)) ==> (M[iir#anon$10][idx] == M[iir#anon$9][idx - 1])
  );
  assume (C[iir#anon$13] == 0) ==> (AV#delay_2#data == 0);
  assume (C[iir#anon$13] > 0) ==> (AV#delay_2#data == M[iir#anon$12][R[iir#anon$12] - 1]);
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$13] > 0) ==> (M[iir#anon$13][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$13] - 0)) ==> (M[iir#anon$13][idx] == M[iir#anon$12][idx - 1])
  );
  assume (C[iir#anon$16] == 0) ==> (AV#delay_3#data == 0);
  assume (C[iir#anon$16] > 0) ==> (AV#delay_3#data == M[iir#anon$15][R[iir#anon$15] - 1]);
  assume R[iir#anon$15] == C[iir#anon$16];
  assume (C[iir#anon$16] > 0) ==> (M[iir#anon$16][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$16] - 0)) ==> (M[iir#anon$16][idx] == M[iir#anon$15][idx - 1])
  );
  assume R[iir#anon$8] == C[iir#anon$17];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$17]) ==> (M[iir#anon$17][idx$] == (37 * M[iir#anon$8][idx$]))
  );
  assume R[iir#anon$11] == C[iir#anon$18];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$18]) ==> (M[iir#anon$18][idx$] == (109 * M[iir#anon$11][idx$]))
  );
  assume R[iir#anon$14] == C[iir#anon$19];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$19]) ==> (M[iir#anon$19][idx$] == (109 * M[iir#anon$14][idx$]))
  );
  assume R[iir#anon$16] == C[iir#anon$20];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$20]) ==> (M[iir#anon$20][idx$] == (37 * M[iir#anon$16][idx$]))
  );
  assume R[iir#anon$17] == C[iir#anon$21];
  assume R[iir#anon$18] == C[iir#anon$21];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$21]) ==> (M[iir#anon$21][idx$] == (M[iir#anon$17][idx$] + M[iir#anon$18][idx$]))
  );
  assume R[iir#anon$19] == C[iir#anon$22];
  assume R[iir#anon$20] == C[iir#anon$22];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$22]) ==> (M[iir#anon$22][idx$] == (M[iir#anon$19][idx$] + M[iir#anon$20][idx$]))
  );
  assume R[iir#anon$21] == C[iir#anon$23];
  assume R[iir#anon$22] == C[iir#anon$23];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$23]) ==> (M[iir#anon$23][idx$] == (M[iir#anon$21][idx$] + M[iir#anon$22][idx$]))
  );
  assume R[iir#anon$7] == C[iir#anon$8];
  assume R[iir#anon$7] == C[iir#anon$9];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$8]) ==> (M[iir#anon$8][idx$] == M[iir#anon$7][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$9]) ==> (M[iir#anon$9][idx$] == M[iir#anon$7][idx$])
  );
  assume R[iir#anon$10] == C[iir#anon$11];
  assume R[iir#anon$10] == C[iir#anon$12];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$11]) ==> (M[iir#anon$11][idx$] == M[iir#anon$10][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$12]) ==> (M[iir#anon$12][idx$] == M[iir#anon$10][idx$])
  );
  assume R[iir#anon$13] == C[iir#anon$14];
  assume R[iir#anon$13] == C[iir#anon$15];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$14]) ==> (M[iir#anon$14][idx$] == M[iir#anon$13][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$15]) ==> (M[iir#anon$15][idx$] == M[iir#anon$13][idx$])
  );
  assume 1 <= (C[iir#anon$9] - R[iir#anon$9]);
  in#i := M[iir#anon$9][R[iir#anon$9]];
  R[iir#anon$9] := R[iir#anon$9] + 1;
  havoc AV#delay_1#y;
  havoc AV#delay_1#data;
  M[iir#anon$10][C[iir#anon$10]] := AV#delay_1#y;
  C[iir#anon$10] := C[iir#anon$10] + 1;
  assume (C[iir#anon$10] == 0) ==> (AV#delay_1#data == 0);
  assume (C[iir#anon$10] > 0) ==> (AV#delay_1#data == M[iir#anon$9][R[iir#anon$9] - 1]);
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$10] > 0) ==> (M[iir#anon$10][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$10] - 0)) ==> (M[iir#anon$10][idx] == M[iir#anon$9][idx - 1])
  );
  assume (C[iir#anon$13] == 0) ==> (AV#delay_2#data == 0);
  assume (C[iir#anon$13] > 0) ==> (AV#delay_2#data == M[iir#anon$12][R[iir#anon$12] - 1]);
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$13] > 0) ==> (M[iir#anon$13][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$13] - 0)) ==> (M[iir#anon$13][idx] == M[iir#anon$12][idx - 1])
  );
  assume (C[iir#anon$16] == 0) ==> (AV#delay_3#data == 0);
  assume (C[iir#anon$16] > 0) ==> (AV#delay_3#data == M[iir#anon$15][R[iir#anon$15] - 1]);
  assume R[iir#anon$15] == C[iir#anon$16];
  assume (C[iir#anon$16] > 0) ==> (M[iir#anon$16][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$16] - 0)) ==> (M[iir#anon$16][idx] == M[iir#anon$15][idx - 1])
  );
  assume R[iir#anon$8] == C[iir#anon$17];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$17]) ==> (M[iir#anon$17][idx$] == (37 * M[iir#anon$8][idx$]))
  );
  assume R[iir#anon$11] == C[iir#anon$18];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$18]) ==> (M[iir#anon$18][idx$] == (109 * M[iir#anon$11][idx$]))
  );
  assume R[iir#anon$14] == C[iir#anon$19];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$19]) ==> (M[iir#anon$19][idx$] == (109 * M[iir#anon$14][idx$]))
  );
  assume R[iir#anon$16] == C[iir#anon$20];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$20]) ==> (M[iir#anon$20][idx$] == (37 * M[iir#anon$16][idx$]))
  );
  assume R[iir#anon$17] == C[iir#anon$21];
  assume R[iir#anon$18] == C[iir#anon$21];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$21]) ==> (M[iir#anon$21][idx$] == (M[iir#anon$17][idx$] + M[iir#anon$18][idx$]))
  );
  assume R[iir#anon$19] == C[iir#anon$22];
  assume R[iir#anon$20] == C[iir#anon$22];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$22]) ==> (M[iir#anon$22][idx$] == (M[iir#anon$19][idx$] + M[iir#anon$20][idx$]))
  );
  assume R[iir#anon$21] == C[iir#anon$23];
  assume R[iir#anon$22] == C[iir#anon$23];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$23]) ==> (M[iir#anon$23][idx$] == (M[iir#anon$21][idx$] + M[iir#anon$22][idx$]))
  );
  assume R[iir#anon$7] == C[iir#anon$8];
  assume R[iir#anon$7] == C[iir#anon$9];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$8]) ==> (M[iir#anon$8][idx$] == M[iir#anon$7][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$9]) ==> (M[iir#anon$9][idx$] == M[iir#anon$7][idx$])
  );
  assume R[iir#anon$10] == C[iir#anon$11];
  assume R[iir#anon$10] == C[iir#anon$12];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$11]) ==> (M[iir#anon$11][idx$] == M[iir#anon$10][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$12]) ==> (M[iir#anon$12][idx$] == M[iir#anon$10][idx$])
  );
  assume R[iir#anon$13] == C[iir#anon$14];
  assume R[iir#anon$13] == C[iir#anon$15];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$14]) ==> (M[iir#anon$14][idx$] == M[iir#anon$13][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$15]) ==> (M[iir#anon$15][idx$] == M[iir#anon$13][idx$])
  );
  assert {:msg "Action at 16.3 ('anon$2') for actor instance 'delay_1' might not preserve the channel invariant (#65)"} I[iir#anon$17] == I[iir#anon$8];
  assert {:msg "Action at 16.3 ('anon$2') for actor instance 'delay_1' might not preserve the channel invariant (#66)"} I[iir#anon$18] == I[iir#anon$11];
  assert {:msg "Action at 16.3 ('anon$2') for actor instance 'delay_1' might not preserve the channel invariant (#67)"} I[iir#anon$19] == I[iir#anon$14];
  assert {:msg "Action at 16.3 ('anon$2') for actor instance 'delay_1' might not preserve the channel invariant (#68)"} I[iir#anon$20] == I[iir#anon$16];
  assert {:msg "Action at 16.3 ('anon$2') for actor instance 'delay_1' might not preserve the channel invariant (#69)"} I[iir#anon$21] == I[iir#anon$17];
  assert {:msg "Action at 16.3 ('anon$2') for actor instance 'delay_1' might not preserve the channel invariant (#70)"} I[iir#anon$21] == I[iir#anon$18];
  assert {:msg "Action at 16.3 ('anon$2') for actor instance 'delay_1' might not preserve the channel invariant (#71)"} I[iir#anon$22] == I[iir#anon$19];
  assert {:msg "Action at 16.3 ('anon$2') for actor instance 'delay_1' might not preserve the channel invariant (#72)"} I[iir#anon$22] == I[iir#anon$20];
  assert {:msg "Action at 16.3 ('anon$2') for actor instance 'delay_1' might not preserve the channel invariant (#73)"} I[iir#anon$23] == I[iir#anon$21];
  assert {:msg "Action at 16.3 ('anon$2') for actor instance 'delay_1' might not preserve the channel invariant (#74)"} I[iir#anon$23] == I[iir#anon$22];
  assert {:msg "Action at 16.3 ('anon$2') for actor instance 'delay_1' might not preserve the channel invariant (#75)"} I[iir#anon$8] == I[iir#anon$7];
  assert {:msg "Action at 16.3 ('anon$2') for actor instance 'delay_1' might not preserve the channel invariant (#76)"} I[iir#anon$9] == I[iir#anon$7];
  assert {:msg "Action at 16.3 ('anon$2') for actor instance 'delay_1' might not preserve the channel invariant (#77)"} I[iir#anon$11] == I[iir#anon$10];
  assert {:msg "Action at 16.3 ('anon$2') for actor instance 'delay_1' might not preserve the channel invariant (#78)"} I[iir#anon$12] == I[iir#anon$10];
  assert {:msg "Action at 16.3 ('anon$2') for actor instance 'delay_1' might not preserve the channel invariant (#79)"} I[iir#anon$14] == I[iir#anon$13];
  assert {:msg "Action at 16.3 ('anon$2') for actor instance 'delay_1' might not preserve the channel invariant (#80)"} I[iir#anon$15] == I[iir#anon$13];
}
procedure iir##delay#anon$2#12()
  modifies C, R, M, I, H;
{
  var iir#delay_1: Actor;
  var iir#delay_2: Actor;
  var iir#delay_3: Actor;
  var iir#mul_1: Actor;
  var iir#mul_2: Actor;
  var iir#mul_3: Actor;
  var iir#mul_4: Actor;
  var iir#add_1: Actor;
  var iir#add_2: Actor;
  var iir#add_3: Actor;
  var iir#spl_1: Actor;
  var iir#spl_2: Actor;
  var iir#spl_3: Actor;
  var iir#anon$7: Chan (int);
  var iir#anon$8: Chan (int);
  var iir#anon$9: Chan (int);
  var iir#anon$10: Chan (int);
  var iir#anon$11: Chan (int);
  var iir#anon$12: Chan (int);
  var iir#anon$13: Chan (int);
  var iir#anon$14: Chan (int);
  var iir#anon$15: Chan (int);
  var iir#anon$16: Chan (int);
  var iir#anon$17: Chan (int);
  var iir#anon$18: Chan (int);
  var iir#anon$19: Chan (int);
  var iir#anon$20: Chan (int);
  var iir#anon$21: Chan (int);
  var iir#anon$22: Chan (int);
  var iir#anon$23: Chan (int);
  var AV#delay_1#data: int;
  var AV#delay_1#y: int;
  var AV#delay_2#data: int;
  var AV#delay_2#y: int;
  var AV#delay_3#data: int;
  var AV#delay_3#y: int;
  var in#i: int;
  assume (iir#delay_1 != iir#delay_2) && (iir#delay_1 != iir#delay_3) && (iir#delay_1 != iir#mul_1) && (iir#delay_1 != iir#mul_2) && (iir#delay_1 != iir#mul_3) && (iir#delay_1 != iir#mul_4) && (iir#delay_1 != iir#add_1) && (iir#delay_1 != iir#add_2) && (iir#delay_1 != iir#add_3) && (iir#delay_1 != iir#spl_1) && (iir#delay_1 != iir#spl_2) && (iir#delay_1 != iir#spl_3) && (iir#delay_2 != iir#delay_3) && (iir#delay_2 != iir#mul_1) && (iir#delay_2 != iir#mul_2) && (iir#delay_2 != iir#mul_3) && (iir#delay_2 != iir#mul_4) && (iir#delay_2 != iir#add_1) && (iir#delay_2 != iir#add_2) && (iir#delay_2 != iir#add_3) && (iir#delay_2 != iir#spl_1) && (iir#delay_2 != iir#spl_2) && (iir#delay_2 != iir#spl_3) && (iir#delay_3 != iir#mul_1) && (iir#delay_3 != iir#mul_2) && (iir#delay_3 != iir#mul_3) && (iir#delay_3 != iir#mul_4) && (iir#delay_3 != iir#add_1) && (iir#delay_3 != iir#add_2) && (iir#delay_3 != iir#add_3) && (iir#delay_3 != iir#spl_1) && (iir#delay_3 != iir#spl_2) && (iir#delay_3 != iir#spl_3) && (iir#mul_1 != iir#mul_2) && (iir#mul_1 != iir#mul_3) && (iir#mul_1 != iir#mul_4) && (iir#mul_1 != iir#add_1) && (iir#mul_1 != iir#add_2) && (iir#mul_1 != iir#add_3) && (iir#mul_1 != iir#spl_1) && (iir#mul_1 != iir#spl_2) && (iir#mul_1 != iir#spl_3) && (iir#mul_2 != iir#mul_3) && (iir#mul_2 != iir#mul_4) && (iir#mul_2 != iir#add_1) && (iir#mul_2 != iir#add_2) && (iir#mul_2 != iir#add_3) && (iir#mul_2 != iir#spl_1) && (iir#mul_2 != iir#spl_2) && (iir#mul_2 != iir#spl_3) && (iir#mul_3 != iir#mul_4) && (iir#mul_3 != iir#add_1) && (iir#mul_3 != iir#add_2) && (iir#mul_3 != iir#add_3) && (iir#mul_3 != iir#spl_1) && (iir#mul_3 != iir#spl_2) && (iir#mul_3 != iir#spl_3) && (iir#mul_4 != iir#add_1) && (iir#mul_4 != iir#add_2) && (iir#mul_4 != iir#add_3) && (iir#mul_4 != iir#spl_1) && (iir#mul_4 != iir#spl_2) && (iir#mul_4 != iir#spl_3) && (iir#add_1 != iir#add_2) && (iir#add_1 != iir#add_3) && (iir#add_1 != iir#spl_1) && (iir#add_1 != iir#spl_2) && (iir#add_1 != iir#spl_3) && (iir#add_2 != iir#add_3) && (iir#add_2 != iir#spl_1) && (iir#add_2 != iir#spl_2) && (iir#add_2 != iir#spl_3) && (iir#add_3 != iir#spl_1) && (iir#add_3 != iir#spl_2) && (iir#add_3 != iir#spl_3) && (iir#spl_1 != iir#spl_2) && (iir#spl_1 != iir#spl_3) && (iir#spl_2 != iir#spl_3);
  assume (iir#anon$7 != iir#anon$8) && (iir#anon$7 != iir#anon$9) && (iir#anon$7 != iir#anon$10) && (iir#anon$7 != iir#anon$11) && (iir#anon$7 != iir#anon$12) && (iir#anon$7 != iir#anon$13) && (iir#anon$7 != iir#anon$14) && (iir#anon$7 != iir#anon$15) && (iir#anon$7 != iir#anon$16) && (iir#anon$7 != iir#anon$17) && (iir#anon$7 != iir#anon$18) && (iir#anon$7 != iir#anon$19) && (iir#anon$7 != iir#anon$20) && (iir#anon$7 != iir#anon$21) && (iir#anon$7 != iir#anon$22) && (iir#anon$7 != iir#anon$23) && (iir#anon$8 != iir#anon$9) && (iir#anon$8 != iir#anon$10) && (iir#anon$8 != iir#anon$11) && (iir#anon$8 != iir#anon$12) && (iir#anon$8 != iir#anon$13) && (iir#anon$8 != iir#anon$14) && (iir#anon$8 != iir#anon$15) && (iir#anon$8 != iir#anon$16) && (iir#anon$8 != iir#anon$17) && (iir#anon$8 != iir#anon$18) && (iir#anon$8 != iir#anon$19) && (iir#anon$8 != iir#anon$20) && (iir#anon$8 != iir#anon$21) && (iir#anon$8 != iir#anon$22) && (iir#anon$8 != iir#anon$23) && (iir#anon$9 != iir#anon$10) && (iir#anon$9 != iir#anon$11) && (iir#anon$9 != iir#anon$12) && (iir#anon$9 != iir#anon$13) && (iir#anon$9 != iir#anon$14) && (iir#anon$9 != iir#anon$15) && (iir#anon$9 != iir#anon$16) && (iir#anon$9 != iir#anon$17) && (iir#anon$9 != iir#anon$18) && (iir#anon$9 != iir#anon$19) && (iir#anon$9 != iir#anon$20) && (iir#anon$9 != iir#anon$21) && (iir#anon$9 != iir#anon$22) && (iir#anon$9 != iir#anon$23) && (iir#anon$10 != iir#anon$11) && (iir#anon$10 != iir#anon$12) && (iir#anon$10 != iir#anon$13) && (iir#anon$10 != iir#anon$14) && (iir#anon$10 != iir#anon$15) && (iir#anon$10 != iir#anon$16) && (iir#anon$10 != iir#anon$17) && (iir#anon$10 != iir#anon$18) && (iir#anon$10 != iir#anon$19) && (iir#anon$10 != iir#anon$20) && (iir#anon$10 != iir#anon$21) && (iir#anon$10 != iir#anon$22) && (iir#anon$10 != iir#anon$23) && (iir#anon$11 != iir#anon$12) && (iir#anon$11 != iir#anon$13) && (iir#anon$11 != iir#anon$14) && (iir#anon$11 != iir#anon$15) && (iir#anon$11 != iir#anon$16) && (iir#anon$11 != iir#anon$17) && (iir#anon$11 != iir#anon$18) && (iir#anon$11 != iir#anon$19) && (iir#anon$11 != iir#anon$20) && (iir#anon$11 != iir#anon$21) && (iir#anon$11 != iir#anon$22) && (iir#anon$11 != iir#anon$23) && (iir#anon$12 != iir#anon$13) && (iir#anon$12 != iir#anon$14) && (iir#anon$12 != iir#anon$15) && (iir#anon$12 != iir#anon$16) && (iir#anon$12 != iir#anon$17) && (iir#anon$12 != iir#anon$18) && (iir#anon$12 != iir#anon$19) && (iir#anon$12 != iir#anon$20) && (iir#anon$12 != iir#anon$21) && (iir#anon$12 != iir#anon$22) && (iir#anon$12 != iir#anon$23) && (iir#anon$13 != iir#anon$14) && (iir#anon$13 != iir#anon$15) && (iir#anon$13 != iir#anon$16) && (iir#anon$13 != iir#anon$17) && (iir#anon$13 != iir#anon$18) && (iir#anon$13 != iir#anon$19) && (iir#anon$13 != iir#anon$20) && (iir#anon$13 != iir#anon$21) && (iir#anon$13 != iir#anon$22) && (iir#anon$13 != iir#anon$23) && (iir#anon$14 != iir#anon$15) && (iir#anon$14 != iir#anon$16) && (iir#anon$14 != iir#anon$17) && (iir#anon$14 != iir#anon$18) && (iir#anon$14 != iir#anon$19) && (iir#anon$14 != iir#anon$20) && (iir#anon$14 != iir#anon$21) && (iir#anon$14 != iir#anon$22) && (iir#anon$14 != iir#anon$23) && (iir#anon$15 != iir#anon$16) && (iir#anon$15 != iir#anon$17) && (iir#anon$15 != iir#anon$18) && (iir#anon$15 != iir#anon$19) && (iir#anon$15 != iir#anon$20) && (iir#anon$15 != iir#anon$21) && (iir#anon$15 != iir#anon$22) && (iir#anon$15 != iir#anon$23) && (iir#anon$16 != iir#anon$17) && (iir#anon$16 != iir#anon$18) && (iir#anon$16 != iir#anon$19) && (iir#anon$16 != iir#anon$20) && (iir#anon$16 != iir#anon$21) && (iir#anon$16 != iir#anon$22) && (iir#anon$16 != iir#anon$23) && (iir#anon$17 != iir#anon$18) && (iir#anon$17 != iir#anon$19) && (iir#anon$17 != iir#anon$20) && (iir#anon$17 != iir#anon$21) && (iir#anon$17 != iir#anon$22) && (iir#anon$17 != iir#anon$23) && (iir#anon$18 != iir#anon$19) && (iir#anon$18 != iir#anon$20) && (iir#anon$18 != iir#anon$21) && (iir#anon$18 != iir#anon$22) && (iir#anon$18 != iir#anon$23) && (iir#anon$19 != iir#anon$20) && (iir#anon$19 != iir#anon$21) && (iir#anon$19 != iir#anon$22) && (iir#anon$19 != iir#anon$23) && (iir#anon$20 != iir#anon$21) && (iir#anon$20 != iir#anon$22) && (iir#anon$20 != iir#anon$23) && (iir#anon$21 != iir#anon$22) && (iir#anon$21 != iir#anon$23) && (iir#anon$22 != iir#anon$23);
  assume 0 <= I[iir#anon$7];
  assume I[iir#anon$7] <= R[iir#anon$7];
  assume R[iir#anon$7] <= C[iir#anon$7];
  assume 0 <= I[iir#anon$8];
  assume I[iir#anon$8] <= R[iir#anon$8];
  assume R[iir#anon$8] <= C[iir#anon$8];
  assume 0 <= I[iir#anon$9];
  assume I[iir#anon$9] <= R[iir#anon$9];
  assume R[iir#anon$9] <= C[iir#anon$9];
  assume 0 <= I[iir#anon$10];
  assume I[iir#anon$10] <= R[iir#anon$10];
  assume R[iir#anon$10] <= C[iir#anon$10];
  assume 0 <= I[iir#anon$11];
  assume I[iir#anon$11] <= R[iir#anon$11];
  assume R[iir#anon$11] <= C[iir#anon$11];
  assume 0 <= I[iir#anon$12];
  assume I[iir#anon$12] <= R[iir#anon$12];
  assume R[iir#anon$12] <= C[iir#anon$12];
  assume 0 <= I[iir#anon$13];
  assume I[iir#anon$13] <= R[iir#anon$13];
  assume R[iir#anon$13] <= C[iir#anon$13];
  assume 0 <= I[iir#anon$14];
  assume I[iir#anon$14] <= R[iir#anon$14];
  assume R[iir#anon$14] <= C[iir#anon$14];
  assume 0 <= I[iir#anon$15];
  assume I[iir#anon$15] <= R[iir#anon$15];
  assume R[iir#anon$15] <= C[iir#anon$15];
  assume 0 <= I[iir#anon$16];
  assume I[iir#anon$16] <= R[iir#anon$16];
  assume R[iir#anon$16] <= C[iir#anon$16];
  assume 0 <= I[iir#anon$17];
  assume I[iir#anon$17] <= R[iir#anon$17];
  assume R[iir#anon$17] <= C[iir#anon$17];
  assume 0 <= I[iir#anon$18];
  assume I[iir#anon$18] <= R[iir#anon$18];
  assume R[iir#anon$18] <= C[iir#anon$18];
  assume 0 <= I[iir#anon$19];
  assume I[iir#anon$19] <= R[iir#anon$19];
  assume R[iir#anon$19] <= C[iir#anon$19];
  assume 0 <= I[iir#anon$20];
  assume I[iir#anon$20] <= R[iir#anon$20];
  assume R[iir#anon$20] <= C[iir#anon$20];
  assume 0 <= I[iir#anon$21];
  assume I[iir#anon$21] <= R[iir#anon$21];
  assume R[iir#anon$21] <= C[iir#anon$21];
  assume 0 <= I[iir#anon$22];
  assume I[iir#anon$22] <= R[iir#anon$22];
  assume R[iir#anon$22] <= C[iir#anon$22];
  assume 0 <= I[iir#anon$23];
  assume I[iir#anon$23] <= R[iir#anon$23];
  assume R[iir#anon$23] <= C[iir#anon$23];
  assume I[iir#anon$23] == R[iir#anon$23];
  assume I[iir#anon$17] == I[iir#anon$8];
  assume I[iir#anon$18] == I[iir#anon$11];
  assume I[iir#anon$19] == I[iir#anon$14];
  assume I[iir#anon$20] == I[iir#anon$16];
  assume I[iir#anon$21] == I[iir#anon$17];
  assume I[iir#anon$21] == I[iir#anon$18];
  assume I[iir#anon$22] == I[iir#anon$19];
  assume I[iir#anon$22] == I[iir#anon$20];
  assume I[iir#anon$23] == I[iir#anon$21];
  assume I[iir#anon$23] == I[iir#anon$22];
  assume I[iir#anon$8] == I[iir#anon$7];
  assume I[iir#anon$9] == I[iir#anon$7];
  assume I[iir#anon$11] == I[iir#anon$10];
  assume I[iir#anon$12] == I[iir#anon$10];
  assume I[iir#anon$14] == I[iir#anon$13];
  assume I[iir#anon$15] == I[iir#anon$13];
  assume (C[iir#anon$10] == 0) ==> (AV#delay_1#data == 0);
  assume (C[iir#anon$10] > 0) ==> (AV#delay_1#data == M[iir#anon$9][R[iir#anon$9] - 1]);
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$10] > 0) ==> (M[iir#anon$10][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$10] - 0)) ==> (M[iir#anon$10][idx] == M[iir#anon$9][idx - 1])
  );
  assume (C[iir#anon$13] == 0) ==> (AV#delay_2#data == 0);
  assume (C[iir#anon$13] > 0) ==> (AV#delay_2#data == M[iir#anon$12][R[iir#anon$12] - 1]);
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$13] > 0) ==> (M[iir#anon$13][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$13] - 0)) ==> (M[iir#anon$13][idx] == M[iir#anon$12][idx - 1])
  );
  assume (C[iir#anon$16] == 0) ==> (AV#delay_3#data == 0);
  assume (C[iir#anon$16] > 0) ==> (AV#delay_3#data == M[iir#anon$15][R[iir#anon$15] - 1]);
  assume R[iir#anon$15] == C[iir#anon$16];
  assume (C[iir#anon$16] > 0) ==> (M[iir#anon$16][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$16] - 0)) ==> (M[iir#anon$16][idx] == M[iir#anon$15][idx - 1])
  );
  assume R[iir#anon$8] == C[iir#anon$17];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$17]) ==> (M[iir#anon$17][idx$] == (37 * M[iir#anon$8][idx$]))
  );
  assume R[iir#anon$11] == C[iir#anon$18];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$18]) ==> (M[iir#anon$18][idx$] == (109 * M[iir#anon$11][idx$]))
  );
  assume R[iir#anon$14] == C[iir#anon$19];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$19]) ==> (M[iir#anon$19][idx$] == (109 * M[iir#anon$14][idx$]))
  );
  assume R[iir#anon$16] == C[iir#anon$20];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$20]) ==> (M[iir#anon$20][idx$] == (37 * M[iir#anon$16][idx$]))
  );
  assume R[iir#anon$17] == C[iir#anon$21];
  assume R[iir#anon$18] == C[iir#anon$21];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$21]) ==> (M[iir#anon$21][idx$] == (M[iir#anon$17][idx$] + M[iir#anon$18][idx$]))
  );
  assume R[iir#anon$19] == C[iir#anon$22];
  assume R[iir#anon$20] == C[iir#anon$22];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$22]) ==> (M[iir#anon$22][idx$] == (M[iir#anon$19][idx$] + M[iir#anon$20][idx$]))
  );
  assume R[iir#anon$21] == C[iir#anon$23];
  assume R[iir#anon$22] == C[iir#anon$23];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$23]) ==> (M[iir#anon$23][idx$] == (M[iir#anon$21][idx$] + M[iir#anon$22][idx$]))
  );
  assume R[iir#anon$7] == C[iir#anon$8];
  assume R[iir#anon$7] == C[iir#anon$9];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$8]) ==> (M[iir#anon$8][idx$] == M[iir#anon$7][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$9]) ==> (M[iir#anon$9][idx$] == M[iir#anon$7][idx$])
  );
  assume R[iir#anon$10] == C[iir#anon$11];
  assume R[iir#anon$10] == C[iir#anon$12];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$11]) ==> (M[iir#anon$11][idx$] == M[iir#anon$10][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$12]) ==> (M[iir#anon$12][idx$] == M[iir#anon$10][idx$])
  );
  assume R[iir#anon$13] == C[iir#anon$14];
  assume R[iir#anon$13] == C[iir#anon$15];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$14]) ==> (M[iir#anon$14][idx$] == M[iir#anon$13][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$15]) ==> (M[iir#anon$15][idx$] == M[iir#anon$13][idx$])
  );
  assume 1 <= (C[iir#anon$12] - R[iir#anon$12]);
  in#i := M[iir#anon$12][R[iir#anon$12]];
  R[iir#anon$12] := R[iir#anon$12] + 1;
  havoc AV#delay_2#y;
  havoc AV#delay_2#data;
  M[iir#anon$13][C[iir#anon$13]] := AV#delay_2#y;
  C[iir#anon$13] := C[iir#anon$13] + 1;
  assume (C[iir#anon$10] == 0) ==> (AV#delay_1#data == 0);
  assume (C[iir#anon$10] > 0) ==> (AV#delay_1#data == M[iir#anon$9][R[iir#anon$9] - 1]);
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$10] > 0) ==> (M[iir#anon$10][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$10] - 0)) ==> (M[iir#anon$10][idx] == M[iir#anon$9][idx - 1])
  );
  assume (C[iir#anon$13] == 0) ==> (AV#delay_2#data == 0);
  assume (C[iir#anon$13] > 0) ==> (AV#delay_2#data == M[iir#anon$12][R[iir#anon$12] - 1]);
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$13] > 0) ==> (M[iir#anon$13][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$13] - 0)) ==> (M[iir#anon$13][idx] == M[iir#anon$12][idx - 1])
  );
  assume (C[iir#anon$16] == 0) ==> (AV#delay_3#data == 0);
  assume (C[iir#anon$16] > 0) ==> (AV#delay_3#data == M[iir#anon$15][R[iir#anon$15] - 1]);
  assume R[iir#anon$15] == C[iir#anon$16];
  assume (C[iir#anon$16] > 0) ==> (M[iir#anon$16][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$16] - 0)) ==> (M[iir#anon$16][idx] == M[iir#anon$15][idx - 1])
  );
  assume R[iir#anon$8] == C[iir#anon$17];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$17]) ==> (M[iir#anon$17][idx$] == (37 * M[iir#anon$8][idx$]))
  );
  assume R[iir#anon$11] == C[iir#anon$18];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$18]) ==> (M[iir#anon$18][idx$] == (109 * M[iir#anon$11][idx$]))
  );
  assume R[iir#anon$14] == C[iir#anon$19];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$19]) ==> (M[iir#anon$19][idx$] == (109 * M[iir#anon$14][idx$]))
  );
  assume R[iir#anon$16] == C[iir#anon$20];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$20]) ==> (M[iir#anon$20][idx$] == (37 * M[iir#anon$16][idx$]))
  );
  assume R[iir#anon$17] == C[iir#anon$21];
  assume R[iir#anon$18] == C[iir#anon$21];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$21]) ==> (M[iir#anon$21][idx$] == (M[iir#anon$17][idx$] + M[iir#anon$18][idx$]))
  );
  assume R[iir#anon$19] == C[iir#anon$22];
  assume R[iir#anon$20] == C[iir#anon$22];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$22]) ==> (M[iir#anon$22][idx$] == (M[iir#anon$19][idx$] + M[iir#anon$20][idx$]))
  );
  assume R[iir#anon$21] == C[iir#anon$23];
  assume R[iir#anon$22] == C[iir#anon$23];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$23]) ==> (M[iir#anon$23][idx$] == (M[iir#anon$21][idx$] + M[iir#anon$22][idx$]))
  );
  assume R[iir#anon$7] == C[iir#anon$8];
  assume R[iir#anon$7] == C[iir#anon$9];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$8]) ==> (M[iir#anon$8][idx$] == M[iir#anon$7][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$9]) ==> (M[iir#anon$9][idx$] == M[iir#anon$7][idx$])
  );
  assume R[iir#anon$10] == C[iir#anon$11];
  assume R[iir#anon$10] == C[iir#anon$12];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$11]) ==> (M[iir#anon$11][idx$] == M[iir#anon$10][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$12]) ==> (M[iir#anon$12][idx$] == M[iir#anon$10][idx$])
  );
  assume R[iir#anon$13] == C[iir#anon$14];
  assume R[iir#anon$13] == C[iir#anon$15];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$14]) ==> (M[iir#anon$14][idx$] == M[iir#anon$13][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$15]) ==> (M[iir#anon$15][idx$] == M[iir#anon$13][idx$])
  );
  assert {:msg "Action at 16.3 ('anon$2') for actor instance 'delay_2' might not preserve the channel invariant (#81)"} I[iir#anon$17] == I[iir#anon$8];
  assert {:msg "Action at 16.3 ('anon$2') for actor instance 'delay_2' might not preserve the channel invariant (#82)"} I[iir#anon$18] == I[iir#anon$11];
  assert {:msg "Action at 16.3 ('anon$2') for actor instance 'delay_2' might not preserve the channel invariant (#83)"} I[iir#anon$19] == I[iir#anon$14];
  assert {:msg "Action at 16.3 ('anon$2') for actor instance 'delay_2' might not preserve the channel invariant (#84)"} I[iir#anon$20] == I[iir#anon$16];
  assert {:msg "Action at 16.3 ('anon$2') for actor instance 'delay_2' might not preserve the channel invariant (#85)"} I[iir#anon$21] == I[iir#anon$17];
  assert {:msg "Action at 16.3 ('anon$2') for actor instance 'delay_2' might not preserve the channel invariant (#86)"} I[iir#anon$21] == I[iir#anon$18];
  assert {:msg "Action at 16.3 ('anon$2') for actor instance 'delay_2' might not preserve the channel invariant (#87)"} I[iir#anon$22] == I[iir#anon$19];
  assert {:msg "Action at 16.3 ('anon$2') for actor instance 'delay_2' might not preserve the channel invariant (#88)"} I[iir#anon$22] == I[iir#anon$20];
  assert {:msg "Action at 16.3 ('anon$2') for actor instance 'delay_2' might not preserve the channel invariant (#89)"} I[iir#anon$23] == I[iir#anon$21];
  assert {:msg "Action at 16.3 ('anon$2') for actor instance 'delay_2' might not preserve the channel invariant (#90)"} I[iir#anon$23] == I[iir#anon$22];
  assert {:msg "Action at 16.3 ('anon$2') for actor instance 'delay_2' might not preserve the channel invariant (#91)"} I[iir#anon$8] == I[iir#anon$7];
  assert {:msg "Action at 16.3 ('anon$2') for actor instance 'delay_2' might not preserve the channel invariant (#92)"} I[iir#anon$9] == I[iir#anon$7];
  assert {:msg "Action at 16.3 ('anon$2') for actor instance 'delay_2' might not preserve the channel invariant (#93)"} I[iir#anon$11] == I[iir#anon$10];
  assert {:msg "Action at 16.3 ('anon$2') for actor instance 'delay_2' might not preserve the channel invariant (#94)"} I[iir#anon$12] == I[iir#anon$10];
  assert {:msg "Action at 16.3 ('anon$2') for actor instance 'delay_2' might not preserve the channel invariant (#95)"} I[iir#anon$14] == I[iir#anon$13];
  assert {:msg "Action at 16.3 ('anon$2') for actor instance 'delay_2' might not preserve the channel invariant (#96)"} I[iir#anon$15] == I[iir#anon$13];
}
procedure iir##delay#anon$2#13()
  modifies C, R, M, I, H;
{
  var iir#delay_1: Actor;
  var iir#delay_2: Actor;
  var iir#delay_3: Actor;
  var iir#mul_1: Actor;
  var iir#mul_2: Actor;
  var iir#mul_3: Actor;
  var iir#mul_4: Actor;
  var iir#add_1: Actor;
  var iir#add_2: Actor;
  var iir#add_3: Actor;
  var iir#spl_1: Actor;
  var iir#spl_2: Actor;
  var iir#spl_3: Actor;
  var iir#anon$7: Chan (int);
  var iir#anon$8: Chan (int);
  var iir#anon$9: Chan (int);
  var iir#anon$10: Chan (int);
  var iir#anon$11: Chan (int);
  var iir#anon$12: Chan (int);
  var iir#anon$13: Chan (int);
  var iir#anon$14: Chan (int);
  var iir#anon$15: Chan (int);
  var iir#anon$16: Chan (int);
  var iir#anon$17: Chan (int);
  var iir#anon$18: Chan (int);
  var iir#anon$19: Chan (int);
  var iir#anon$20: Chan (int);
  var iir#anon$21: Chan (int);
  var iir#anon$22: Chan (int);
  var iir#anon$23: Chan (int);
  var AV#delay_1#data: int;
  var AV#delay_1#y: int;
  var AV#delay_2#data: int;
  var AV#delay_2#y: int;
  var AV#delay_3#data: int;
  var AV#delay_3#y: int;
  var in#i: int;
  assume (iir#delay_1 != iir#delay_2) && (iir#delay_1 != iir#delay_3) && (iir#delay_1 != iir#mul_1) && (iir#delay_1 != iir#mul_2) && (iir#delay_1 != iir#mul_3) && (iir#delay_1 != iir#mul_4) && (iir#delay_1 != iir#add_1) && (iir#delay_1 != iir#add_2) && (iir#delay_1 != iir#add_3) && (iir#delay_1 != iir#spl_1) && (iir#delay_1 != iir#spl_2) && (iir#delay_1 != iir#spl_3) && (iir#delay_2 != iir#delay_3) && (iir#delay_2 != iir#mul_1) && (iir#delay_2 != iir#mul_2) && (iir#delay_2 != iir#mul_3) && (iir#delay_2 != iir#mul_4) && (iir#delay_2 != iir#add_1) && (iir#delay_2 != iir#add_2) && (iir#delay_2 != iir#add_3) && (iir#delay_2 != iir#spl_1) && (iir#delay_2 != iir#spl_2) && (iir#delay_2 != iir#spl_3) && (iir#delay_3 != iir#mul_1) && (iir#delay_3 != iir#mul_2) && (iir#delay_3 != iir#mul_3) && (iir#delay_3 != iir#mul_4) && (iir#delay_3 != iir#add_1) && (iir#delay_3 != iir#add_2) && (iir#delay_3 != iir#add_3) && (iir#delay_3 != iir#spl_1) && (iir#delay_3 != iir#spl_2) && (iir#delay_3 != iir#spl_3) && (iir#mul_1 != iir#mul_2) && (iir#mul_1 != iir#mul_3) && (iir#mul_1 != iir#mul_4) && (iir#mul_1 != iir#add_1) && (iir#mul_1 != iir#add_2) && (iir#mul_1 != iir#add_3) && (iir#mul_1 != iir#spl_1) && (iir#mul_1 != iir#spl_2) && (iir#mul_1 != iir#spl_3) && (iir#mul_2 != iir#mul_3) && (iir#mul_2 != iir#mul_4) && (iir#mul_2 != iir#add_1) && (iir#mul_2 != iir#add_2) && (iir#mul_2 != iir#add_3) && (iir#mul_2 != iir#spl_1) && (iir#mul_2 != iir#spl_2) && (iir#mul_2 != iir#spl_3) && (iir#mul_3 != iir#mul_4) && (iir#mul_3 != iir#add_1) && (iir#mul_3 != iir#add_2) && (iir#mul_3 != iir#add_3) && (iir#mul_3 != iir#spl_1) && (iir#mul_3 != iir#spl_2) && (iir#mul_3 != iir#spl_3) && (iir#mul_4 != iir#add_1) && (iir#mul_4 != iir#add_2) && (iir#mul_4 != iir#add_3) && (iir#mul_4 != iir#spl_1) && (iir#mul_4 != iir#spl_2) && (iir#mul_4 != iir#spl_3) && (iir#add_1 != iir#add_2) && (iir#add_1 != iir#add_3) && (iir#add_1 != iir#spl_1) && (iir#add_1 != iir#spl_2) && (iir#add_1 != iir#spl_3) && (iir#add_2 != iir#add_3) && (iir#add_2 != iir#spl_1) && (iir#add_2 != iir#spl_2) && (iir#add_2 != iir#spl_3) && (iir#add_3 != iir#spl_1) && (iir#add_3 != iir#spl_2) && (iir#add_3 != iir#spl_3) && (iir#spl_1 != iir#spl_2) && (iir#spl_1 != iir#spl_3) && (iir#spl_2 != iir#spl_3);
  assume (iir#anon$7 != iir#anon$8) && (iir#anon$7 != iir#anon$9) && (iir#anon$7 != iir#anon$10) && (iir#anon$7 != iir#anon$11) && (iir#anon$7 != iir#anon$12) && (iir#anon$7 != iir#anon$13) && (iir#anon$7 != iir#anon$14) && (iir#anon$7 != iir#anon$15) && (iir#anon$7 != iir#anon$16) && (iir#anon$7 != iir#anon$17) && (iir#anon$7 != iir#anon$18) && (iir#anon$7 != iir#anon$19) && (iir#anon$7 != iir#anon$20) && (iir#anon$7 != iir#anon$21) && (iir#anon$7 != iir#anon$22) && (iir#anon$7 != iir#anon$23) && (iir#anon$8 != iir#anon$9) && (iir#anon$8 != iir#anon$10) && (iir#anon$8 != iir#anon$11) && (iir#anon$8 != iir#anon$12) && (iir#anon$8 != iir#anon$13) && (iir#anon$8 != iir#anon$14) && (iir#anon$8 != iir#anon$15) && (iir#anon$8 != iir#anon$16) && (iir#anon$8 != iir#anon$17) && (iir#anon$8 != iir#anon$18) && (iir#anon$8 != iir#anon$19) && (iir#anon$8 != iir#anon$20) && (iir#anon$8 != iir#anon$21) && (iir#anon$8 != iir#anon$22) && (iir#anon$8 != iir#anon$23) && (iir#anon$9 != iir#anon$10) && (iir#anon$9 != iir#anon$11) && (iir#anon$9 != iir#anon$12) && (iir#anon$9 != iir#anon$13) && (iir#anon$9 != iir#anon$14) && (iir#anon$9 != iir#anon$15) && (iir#anon$9 != iir#anon$16) && (iir#anon$9 != iir#anon$17) && (iir#anon$9 != iir#anon$18) && (iir#anon$9 != iir#anon$19) && (iir#anon$9 != iir#anon$20) && (iir#anon$9 != iir#anon$21) && (iir#anon$9 != iir#anon$22) && (iir#anon$9 != iir#anon$23) && (iir#anon$10 != iir#anon$11) && (iir#anon$10 != iir#anon$12) && (iir#anon$10 != iir#anon$13) && (iir#anon$10 != iir#anon$14) && (iir#anon$10 != iir#anon$15) && (iir#anon$10 != iir#anon$16) && (iir#anon$10 != iir#anon$17) && (iir#anon$10 != iir#anon$18) && (iir#anon$10 != iir#anon$19) && (iir#anon$10 != iir#anon$20) && (iir#anon$10 != iir#anon$21) && (iir#anon$10 != iir#anon$22) && (iir#anon$10 != iir#anon$23) && (iir#anon$11 != iir#anon$12) && (iir#anon$11 != iir#anon$13) && (iir#anon$11 != iir#anon$14) && (iir#anon$11 != iir#anon$15) && (iir#anon$11 != iir#anon$16) && (iir#anon$11 != iir#anon$17) && (iir#anon$11 != iir#anon$18) && (iir#anon$11 != iir#anon$19) && (iir#anon$11 != iir#anon$20) && (iir#anon$11 != iir#anon$21) && (iir#anon$11 != iir#anon$22) && (iir#anon$11 != iir#anon$23) && (iir#anon$12 != iir#anon$13) && (iir#anon$12 != iir#anon$14) && (iir#anon$12 != iir#anon$15) && (iir#anon$12 != iir#anon$16) && (iir#anon$12 != iir#anon$17) && (iir#anon$12 != iir#anon$18) && (iir#anon$12 != iir#anon$19) && (iir#anon$12 != iir#anon$20) && (iir#anon$12 != iir#anon$21) && (iir#anon$12 != iir#anon$22) && (iir#anon$12 != iir#anon$23) && (iir#anon$13 != iir#anon$14) && (iir#anon$13 != iir#anon$15) && (iir#anon$13 != iir#anon$16) && (iir#anon$13 != iir#anon$17) && (iir#anon$13 != iir#anon$18) && (iir#anon$13 != iir#anon$19) && (iir#anon$13 != iir#anon$20) && (iir#anon$13 != iir#anon$21) && (iir#anon$13 != iir#anon$22) && (iir#anon$13 != iir#anon$23) && (iir#anon$14 != iir#anon$15) && (iir#anon$14 != iir#anon$16) && (iir#anon$14 != iir#anon$17) && (iir#anon$14 != iir#anon$18) && (iir#anon$14 != iir#anon$19) && (iir#anon$14 != iir#anon$20) && (iir#anon$14 != iir#anon$21) && (iir#anon$14 != iir#anon$22) && (iir#anon$14 != iir#anon$23) && (iir#anon$15 != iir#anon$16) && (iir#anon$15 != iir#anon$17) && (iir#anon$15 != iir#anon$18) && (iir#anon$15 != iir#anon$19) && (iir#anon$15 != iir#anon$20) && (iir#anon$15 != iir#anon$21) && (iir#anon$15 != iir#anon$22) && (iir#anon$15 != iir#anon$23) && (iir#anon$16 != iir#anon$17) && (iir#anon$16 != iir#anon$18) && (iir#anon$16 != iir#anon$19) && (iir#anon$16 != iir#anon$20) && (iir#anon$16 != iir#anon$21) && (iir#anon$16 != iir#anon$22) && (iir#anon$16 != iir#anon$23) && (iir#anon$17 != iir#anon$18) && (iir#anon$17 != iir#anon$19) && (iir#anon$17 != iir#anon$20) && (iir#anon$17 != iir#anon$21) && (iir#anon$17 != iir#anon$22) && (iir#anon$17 != iir#anon$23) && (iir#anon$18 != iir#anon$19) && (iir#anon$18 != iir#anon$20) && (iir#anon$18 != iir#anon$21) && (iir#anon$18 != iir#anon$22) && (iir#anon$18 != iir#anon$23) && (iir#anon$19 != iir#anon$20) && (iir#anon$19 != iir#anon$21) && (iir#anon$19 != iir#anon$22) && (iir#anon$19 != iir#anon$23) && (iir#anon$20 != iir#anon$21) && (iir#anon$20 != iir#anon$22) && (iir#anon$20 != iir#anon$23) && (iir#anon$21 != iir#anon$22) && (iir#anon$21 != iir#anon$23) && (iir#anon$22 != iir#anon$23);
  assume 0 <= I[iir#anon$7];
  assume I[iir#anon$7] <= R[iir#anon$7];
  assume R[iir#anon$7] <= C[iir#anon$7];
  assume 0 <= I[iir#anon$8];
  assume I[iir#anon$8] <= R[iir#anon$8];
  assume R[iir#anon$8] <= C[iir#anon$8];
  assume 0 <= I[iir#anon$9];
  assume I[iir#anon$9] <= R[iir#anon$9];
  assume R[iir#anon$9] <= C[iir#anon$9];
  assume 0 <= I[iir#anon$10];
  assume I[iir#anon$10] <= R[iir#anon$10];
  assume R[iir#anon$10] <= C[iir#anon$10];
  assume 0 <= I[iir#anon$11];
  assume I[iir#anon$11] <= R[iir#anon$11];
  assume R[iir#anon$11] <= C[iir#anon$11];
  assume 0 <= I[iir#anon$12];
  assume I[iir#anon$12] <= R[iir#anon$12];
  assume R[iir#anon$12] <= C[iir#anon$12];
  assume 0 <= I[iir#anon$13];
  assume I[iir#anon$13] <= R[iir#anon$13];
  assume R[iir#anon$13] <= C[iir#anon$13];
  assume 0 <= I[iir#anon$14];
  assume I[iir#anon$14] <= R[iir#anon$14];
  assume R[iir#anon$14] <= C[iir#anon$14];
  assume 0 <= I[iir#anon$15];
  assume I[iir#anon$15] <= R[iir#anon$15];
  assume R[iir#anon$15] <= C[iir#anon$15];
  assume 0 <= I[iir#anon$16];
  assume I[iir#anon$16] <= R[iir#anon$16];
  assume R[iir#anon$16] <= C[iir#anon$16];
  assume 0 <= I[iir#anon$17];
  assume I[iir#anon$17] <= R[iir#anon$17];
  assume R[iir#anon$17] <= C[iir#anon$17];
  assume 0 <= I[iir#anon$18];
  assume I[iir#anon$18] <= R[iir#anon$18];
  assume R[iir#anon$18] <= C[iir#anon$18];
  assume 0 <= I[iir#anon$19];
  assume I[iir#anon$19] <= R[iir#anon$19];
  assume R[iir#anon$19] <= C[iir#anon$19];
  assume 0 <= I[iir#anon$20];
  assume I[iir#anon$20] <= R[iir#anon$20];
  assume R[iir#anon$20] <= C[iir#anon$20];
  assume 0 <= I[iir#anon$21];
  assume I[iir#anon$21] <= R[iir#anon$21];
  assume R[iir#anon$21] <= C[iir#anon$21];
  assume 0 <= I[iir#anon$22];
  assume I[iir#anon$22] <= R[iir#anon$22];
  assume R[iir#anon$22] <= C[iir#anon$22];
  assume 0 <= I[iir#anon$23];
  assume I[iir#anon$23] <= R[iir#anon$23];
  assume R[iir#anon$23] <= C[iir#anon$23];
  assume I[iir#anon$23] == R[iir#anon$23];
  assume I[iir#anon$17] == I[iir#anon$8];
  assume I[iir#anon$18] == I[iir#anon$11];
  assume I[iir#anon$19] == I[iir#anon$14];
  assume I[iir#anon$20] == I[iir#anon$16];
  assume I[iir#anon$21] == I[iir#anon$17];
  assume I[iir#anon$21] == I[iir#anon$18];
  assume I[iir#anon$22] == I[iir#anon$19];
  assume I[iir#anon$22] == I[iir#anon$20];
  assume I[iir#anon$23] == I[iir#anon$21];
  assume I[iir#anon$23] == I[iir#anon$22];
  assume I[iir#anon$8] == I[iir#anon$7];
  assume I[iir#anon$9] == I[iir#anon$7];
  assume I[iir#anon$11] == I[iir#anon$10];
  assume I[iir#anon$12] == I[iir#anon$10];
  assume I[iir#anon$14] == I[iir#anon$13];
  assume I[iir#anon$15] == I[iir#anon$13];
  assume (C[iir#anon$10] == 0) ==> (AV#delay_1#data == 0);
  assume (C[iir#anon$10] > 0) ==> (AV#delay_1#data == M[iir#anon$9][R[iir#anon$9] - 1]);
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$10] > 0) ==> (M[iir#anon$10][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$10] - 0)) ==> (M[iir#anon$10][idx] == M[iir#anon$9][idx - 1])
  );
  assume (C[iir#anon$13] == 0) ==> (AV#delay_2#data == 0);
  assume (C[iir#anon$13] > 0) ==> (AV#delay_2#data == M[iir#anon$12][R[iir#anon$12] - 1]);
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$13] > 0) ==> (M[iir#anon$13][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$13] - 0)) ==> (M[iir#anon$13][idx] == M[iir#anon$12][idx - 1])
  );
  assume (C[iir#anon$16] == 0) ==> (AV#delay_3#data == 0);
  assume (C[iir#anon$16] > 0) ==> (AV#delay_3#data == M[iir#anon$15][R[iir#anon$15] - 1]);
  assume R[iir#anon$15] == C[iir#anon$16];
  assume (C[iir#anon$16] > 0) ==> (M[iir#anon$16][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$16] - 0)) ==> (M[iir#anon$16][idx] == M[iir#anon$15][idx - 1])
  );
  assume R[iir#anon$8] == C[iir#anon$17];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$17]) ==> (M[iir#anon$17][idx$] == (37 * M[iir#anon$8][idx$]))
  );
  assume R[iir#anon$11] == C[iir#anon$18];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$18]) ==> (M[iir#anon$18][idx$] == (109 * M[iir#anon$11][idx$]))
  );
  assume R[iir#anon$14] == C[iir#anon$19];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$19]) ==> (M[iir#anon$19][idx$] == (109 * M[iir#anon$14][idx$]))
  );
  assume R[iir#anon$16] == C[iir#anon$20];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$20]) ==> (M[iir#anon$20][idx$] == (37 * M[iir#anon$16][idx$]))
  );
  assume R[iir#anon$17] == C[iir#anon$21];
  assume R[iir#anon$18] == C[iir#anon$21];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$21]) ==> (M[iir#anon$21][idx$] == (M[iir#anon$17][idx$] + M[iir#anon$18][idx$]))
  );
  assume R[iir#anon$19] == C[iir#anon$22];
  assume R[iir#anon$20] == C[iir#anon$22];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$22]) ==> (M[iir#anon$22][idx$] == (M[iir#anon$19][idx$] + M[iir#anon$20][idx$]))
  );
  assume R[iir#anon$21] == C[iir#anon$23];
  assume R[iir#anon$22] == C[iir#anon$23];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$23]) ==> (M[iir#anon$23][idx$] == (M[iir#anon$21][idx$] + M[iir#anon$22][idx$]))
  );
  assume R[iir#anon$7] == C[iir#anon$8];
  assume R[iir#anon$7] == C[iir#anon$9];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$8]) ==> (M[iir#anon$8][idx$] == M[iir#anon$7][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$9]) ==> (M[iir#anon$9][idx$] == M[iir#anon$7][idx$])
  );
  assume R[iir#anon$10] == C[iir#anon$11];
  assume R[iir#anon$10] == C[iir#anon$12];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$11]) ==> (M[iir#anon$11][idx$] == M[iir#anon$10][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$12]) ==> (M[iir#anon$12][idx$] == M[iir#anon$10][idx$])
  );
  assume R[iir#anon$13] == C[iir#anon$14];
  assume R[iir#anon$13] == C[iir#anon$15];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$14]) ==> (M[iir#anon$14][idx$] == M[iir#anon$13][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$15]) ==> (M[iir#anon$15][idx$] == M[iir#anon$13][idx$])
  );
  assume 1 <= (C[iir#anon$15] - R[iir#anon$15]);
  in#i := M[iir#anon$15][R[iir#anon$15]];
  R[iir#anon$15] := R[iir#anon$15] + 1;
  havoc AV#delay_3#y;
  havoc AV#delay_3#data;
  M[iir#anon$16][C[iir#anon$16]] := AV#delay_3#y;
  C[iir#anon$16] := C[iir#anon$16] + 1;
  assume (C[iir#anon$10] == 0) ==> (AV#delay_1#data == 0);
  assume (C[iir#anon$10] > 0) ==> (AV#delay_1#data == M[iir#anon$9][R[iir#anon$9] - 1]);
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$10] > 0) ==> (M[iir#anon$10][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$10] - 0)) ==> (M[iir#anon$10][idx] == M[iir#anon$9][idx - 1])
  );
  assume (C[iir#anon$13] == 0) ==> (AV#delay_2#data == 0);
  assume (C[iir#anon$13] > 0) ==> (AV#delay_2#data == M[iir#anon$12][R[iir#anon$12] - 1]);
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$13] > 0) ==> (M[iir#anon$13][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$13] - 0)) ==> (M[iir#anon$13][idx] == M[iir#anon$12][idx - 1])
  );
  assume (C[iir#anon$16] == 0) ==> (AV#delay_3#data == 0);
  assume (C[iir#anon$16] > 0) ==> (AV#delay_3#data == M[iir#anon$15][R[iir#anon$15] - 1]);
  assume R[iir#anon$15] == C[iir#anon$16];
  assume (C[iir#anon$16] > 0) ==> (M[iir#anon$16][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$16] - 0)) ==> (M[iir#anon$16][idx] == M[iir#anon$15][idx - 1])
  );
  assume R[iir#anon$8] == C[iir#anon$17];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$17]) ==> (M[iir#anon$17][idx$] == (37 * M[iir#anon$8][idx$]))
  );
  assume R[iir#anon$11] == C[iir#anon$18];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$18]) ==> (M[iir#anon$18][idx$] == (109 * M[iir#anon$11][idx$]))
  );
  assume R[iir#anon$14] == C[iir#anon$19];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$19]) ==> (M[iir#anon$19][idx$] == (109 * M[iir#anon$14][idx$]))
  );
  assume R[iir#anon$16] == C[iir#anon$20];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$20]) ==> (M[iir#anon$20][idx$] == (37 * M[iir#anon$16][idx$]))
  );
  assume R[iir#anon$17] == C[iir#anon$21];
  assume R[iir#anon$18] == C[iir#anon$21];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$21]) ==> (M[iir#anon$21][idx$] == (M[iir#anon$17][idx$] + M[iir#anon$18][idx$]))
  );
  assume R[iir#anon$19] == C[iir#anon$22];
  assume R[iir#anon$20] == C[iir#anon$22];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$22]) ==> (M[iir#anon$22][idx$] == (M[iir#anon$19][idx$] + M[iir#anon$20][idx$]))
  );
  assume R[iir#anon$21] == C[iir#anon$23];
  assume R[iir#anon$22] == C[iir#anon$23];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$23]) ==> (M[iir#anon$23][idx$] == (M[iir#anon$21][idx$] + M[iir#anon$22][idx$]))
  );
  assume R[iir#anon$7] == C[iir#anon$8];
  assume R[iir#anon$7] == C[iir#anon$9];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$8]) ==> (M[iir#anon$8][idx$] == M[iir#anon$7][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$9]) ==> (M[iir#anon$9][idx$] == M[iir#anon$7][idx$])
  );
  assume R[iir#anon$10] == C[iir#anon$11];
  assume R[iir#anon$10] == C[iir#anon$12];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$11]) ==> (M[iir#anon$11][idx$] == M[iir#anon$10][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$12]) ==> (M[iir#anon$12][idx$] == M[iir#anon$10][idx$])
  );
  assume R[iir#anon$13] == C[iir#anon$14];
  assume R[iir#anon$13] == C[iir#anon$15];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$14]) ==> (M[iir#anon$14][idx$] == M[iir#anon$13][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$15]) ==> (M[iir#anon$15][idx$] == M[iir#anon$13][idx$])
  );
  assert {:msg "Action at 16.3 ('anon$2') for actor instance 'delay_3' might not preserve the channel invariant (#97)"} I[iir#anon$17] == I[iir#anon$8];
  assert {:msg "Action at 16.3 ('anon$2') for actor instance 'delay_3' might not preserve the channel invariant (#98)"} I[iir#anon$18] == I[iir#anon$11];
  assert {:msg "Action at 16.3 ('anon$2') for actor instance 'delay_3' might not preserve the channel invariant (#99)"} I[iir#anon$19] == I[iir#anon$14];
  assert {:msg "Action at 16.3 ('anon$2') for actor instance 'delay_3' might not preserve the channel invariant (#100)"} I[iir#anon$20] == I[iir#anon$16];
  assert {:msg "Action at 16.3 ('anon$2') for actor instance 'delay_3' might not preserve the channel invariant (#101)"} I[iir#anon$21] == I[iir#anon$17];
  assert {:msg "Action at 16.3 ('anon$2') for actor instance 'delay_3' might not preserve the channel invariant (#102)"} I[iir#anon$21] == I[iir#anon$18];
  assert {:msg "Action at 16.3 ('anon$2') for actor instance 'delay_3' might not preserve the channel invariant (#103)"} I[iir#anon$22] == I[iir#anon$19];
  assert {:msg "Action at 16.3 ('anon$2') for actor instance 'delay_3' might not preserve the channel invariant (#104)"} I[iir#anon$22] == I[iir#anon$20];
  assert {:msg "Action at 16.3 ('anon$2') for actor instance 'delay_3' might not preserve the channel invariant (#105)"} I[iir#anon$23] == I[iir#anon$21];
  assert {:msg "Action at 16.3 ('anon$2') for actor instance 'delay_3' might not preserve the channel invariant (#106)"} I[iir#anon$23] == I[iir#anon$22];
  assert {:msg "Action at 16.3 ('anon$2') for actor instance 'delay_3' might not preserve the channel invariant (#107)"} I[iir#anon$8] == I[iir#anon$7];
  assert {:msg "Action at 16.3 ('anon$2') for actor instance 'delay_3' might not preserve the channel invariant (#108)"} I[iir#anon$9] == I[iir#anon$7];
  assert {:msg "Action at 16.3 ('anon$2') for actor instance 'delay_3' might not preserve the channel invariant (#109)"} I[iir#anon$11] == I[iir#anon$10];
  assert {:msg "Action at 16.3 ('anon$2') for actor instance 'delay_3' might not preserve the channel invariant (#110)"} I[iir#anon$12] == I[iir#anon$10];
  assert {:msg "Action at 16.3 ('anon$2') for actor instance 'delay_3' might not preserve the channel invariant (#111)"} I[iir#anon$14] == I[iir#anon$13];
  assert {:msg "Action at 16.3 ('anon$2') for actor instance 'delay_3' might not preserve the channel invariant (#112)"} I[iir#anon$15] == I[iir#anon$13];
}
procedure iir##mulc#anon$3#14()
  modifies C, R, M, I, H;
{
  var iir#delay_1: Actor;
  var iir#delay_2: Actor;
  var iir#delay_3: Actor;
  var iir#mul_1: Actor;
  var iir#mul_2: Actor;
  var iir#mul_3: Actor;
  var iir#mul_4: Actor;
  var iir#add_1: Actor;
  var iir#add_2: Actor;
  var iir#add_3: Actor;
  var iir#spl_1: Actor;
  var iir#spl_2: Actor;
  var iir#spl_3: Actor;
  var iir#anon$7: Chan (int);
  var iir#anon$8: Chan (int);
  var iir#anon$9: Chan (int);
  var iir#anon$10: Chan (int);
  var iir#anon$11: Chan (int);
  var iir#anon$12: Chan (int);
  var iir#anon$13: Chan (int);
  var iir#anon$14: Chan (int);
  var iir#anon$15: Chan (int);
  var iir#anon$16: Chan (int);
  var iir#anon$17: Chan (int);
  var iir#anon$18: Chan (int);
  var iir#anon$19: Chan (int);
  var iir#anon$20: Chan (int);
  var iir#anon$21: Chan (int);
  var iir#anon$22: Chan (int);
  var iir#anon$23: Chan (int);
  var AV#delay_1#data: int;
  var AV#delay_1#y: int;
  var AV#delay_2#data: int;
  var AV#delay_2#y: int;
  var AV#delay_3#data: int;
  var AV#delay_3#y: int;
  var in#i: int;
  assume (iir#delay_1 != iir#delay_2) && (iir#delay_1 != iir#delay_3) && (iir#delay_1 != iir#mul_1) && (iir#delay_1 != iir#mul_2) && (iir#delay_1 != iir#mul_3) && (iir#delay_1 != iir#mul_4) && (iir#delay_1 != iir#add_1) && (iir#delay_1 != iir#add_2) && (iir#delay_1 != iir#add_3) && (iir#delay_1 != iir#spl_1) && (iir#delay_1 != iir#spl_2) && (iir#delay_1 != iir#spl_3) && (iir#delay_2 != iir#delay_3) && (iir#delay_2 != iir#mul_1) && (iir#delay_2 != iir#mul_2) && (iir#delay_2 != iir#mul_3) && (iir#delay_2 != iir#mul_4) && (iir#delay_2 != iir#add_1) && (iir#delay_2 != iir#add_2) && (iir#delay_2 != iir#add_3) && (iir#delay_2 != iir#spl_1) && (iir#delay_2 != iir#spl_2) && (iir#delay_2 != iir#spl_3) && (iir#delay_3 != iir#mul_1) && (iir#delay_3 != iir#mul_2) && (iir#delay_3 != iir#mul_3) && (iir#delay_3 != iir#mul_4) && (iir#delay_3 != iir#add_1) && (iir#delay_3 != iir#add_2) && (iir#delay_3 != iir#add_3) && (iir#delay_3 != iir#spl_1) && (iir#delay_3 != iir#spl_2) && (iir#delay_3 != iir#spl_3) && (iir#mul_1 != iir#mul_2) && (iir#mul_1 != iir#mul_3) && (iir#mul_1 != iir#mul_4) && (iir#mul_1 != iir#add_1) && (iir#mul_1 != iir#add_2) && (iir#mul_1 != iir#add_3) && (iir#mul_1 != iir#spl_1) && (iir#mul_1 != iir#spl_2) && (iir#mul_1 != iir#spl_3) && (iir#mul_2 != iir#mul_3) && (iir#mul_2 != iir#mul_4) && (iir#mul_2 != iir#add_1) && (iir#mul_2 != iir#add_2) && (iir#mul_2 != iir#add_3) && (iir#mul_2 != iir#spl_1) && (iir#mul_2 != iir#spl_2) && (iir#mul_2 != iir#spl_3) && (iir#mul_3 != iir#mul_4) && (iir#mul_3 != iir#add_1) && (iir#mul_3 != iir#add_2) && (iir#mul_3 != iir#add_3) && (iir#mul_3 != iir#spl_1) && (iir#mul_3 != iir#spl_2) && (iir#mul_3 != iir#spl_3) && (iir#mul_4 != iir#add_1) && (iir#mul_4 != iir#add_2) && (iir#mul_4 != iir#add_3) && (iir#mul_4 != iir#spl_1) && (iir#mul_4 != iir#spl_2) && (iir#mul_4 != iir#spl_3) && (iir#add_1 != iir#add_2) && (iir#add_1 != iir#add_3) && (iir#add_1 != iir#spl_1) && (iir#add_1 != iir#spl_2) && (iir#add_1 != iir#spl_3) && (iir#add_2 != iir#add_3) && (iir#add_2 != iir#spl_1) && (iir#add_2 != iir#spl_2) && (iir#add_2 != iir#spl_3) && (iir#add_3 != iir#spl_1) && (iir#add_3 != iir#spl_2) && (iir#add_3 != iir#spl_3) && (iir#spl_1 != iir#spl_2) && (iir#spl_1 != iir#spl_3) && (iir#spl_2 != iir#spl_3);
  assume (iir#anon$7 != iir#anon$8) && (iir#anon$7 != iir#anon$9) && (iir#anon$7 != iir#anon$10) && (iir#anon$7 != iir#anon$11) && (iir#anon$7 != iir#anon$12) && (iir#anon$7 != iir#anon$13) && (iir#anon$7 != iir#anon$14) && (iir#anon$7 != iir#anon$15) && (iir#anon$7 != iir#anon$16) && (iir#anon$7 != iir#anon$17) && (iir#anon$7 != iir#anon$18) && (iir#anon$7 != iir#anon$19) && (iir#anon$7 != iir#anon$20) && (iir#anon$7 != iir#anon$21) && (iir#anon$7 != iir#anon$22) && (iir#anon$7 != iir#anon$23) && (iir#anon$8 != iir#anon$9) && (iir#anon$8 != iir#anon$10) && (iir#anon$8 != iir#anon$11) && (iir#anon$8 != iir#anon$12) && (iir#anon$8 != iir#anon$13) && (iir#anon$8 != iir#anon$14) && (iir#anon$8 != iir#anon$15) && (iir#anon$8 != iir#anon$16) && (iir#anon$8 != iir#anon$17) && (iir#anon$8 != iir#anon$18) && (iir#anon$8 != iir#anon$19) && (iir#anon$8 != iir#anon$20) && (iir#anon$8 != iir#anon$21) && (iir#anon$8 != iir#anon$22) && (iir#anon$8 != iir#anon$23) && (iir#anon$9 != iir#anon$10) && (iir#anon$9 != iir#anon$11) && (iir#anon$9 != iir#anon$12) && (iir#anon$9 != iir#anon$13) && (iir#anon$9 != iir#anon$14) && (iir#anon$9 != iir#anon$15) && (iir#anon$9 != iir#anon$16) && (iir#anon$9 != iir#anon$17) && (iir#anon$9 != iir#anon$18) && (iir#anon$9 != iir#anon$19) && (iir#anon$9 != iir#anon$20) && (iir#anon$9 != iir#anon$21) && (iir#anon$9 != iir#anon$22) && (iir#anon$9 != iir#anon$23) && (iir#anon$10 != iir#anon$11) && (iir#anon$10 != iir#anon$12) && (iir#anon$10 != iir#anon$13) && (iir#anon$10 != iir#anon$14) && (iir#anon$10 != iir#anon$15) && (iir#anon$10 != iir#anon$16) && (iir#anon$10 != iir#anon$17) && (iir#anon$10 != iir#anon$18) && (iir#anon$10 != iir#anon$19) && (iir#anon$10 != iir#anon$20) && (iir#anon$10 != iir#anon$21) && (iir#anon$10 != iir#anon$22) && (iir#anon$10 != iir#anon$23) && (iir#anon$11 != iir#anon$12) && (iir#anon$11 != iir#anon$13) && (iir#anon$11 != iir#anon$14) && (iir#anon$11 != iir#anon$15) && (iir#anon$11 != iir#anon$16) && (iir#anon$11 != iir#anon$17) && (iir#anon$11 != iir#anon$18) && (iir#anon$11 != iir#anon$19) && (iir#anon$11 != iir#anon$20) && (iir#anon$11 != iir#anon$21) && (iir#anon$11 != iir#anon$22) && (iir#anon$11 != iir#anon$23) && (iir#anon$12 != iir#anon$13) && (iir#anon$12 != iir#anon$14) && (iir#anon$12 != iir#anon$15) && (iir#anon$12 != iir#anon$16) && (iir#anon$12 != iir#anon$17) && (iir#anon$12 != iir#anon$18) && (iir#anon$12 != iir#anon$19) && (iir#anon$12 != iir#anon$20) && (iir#anon$12 != iir#anon$21) && (iir#anon$12 != iir#anon$22) && (iir#anon$12 != iir#anon$23) && (iir#anon$13 != iir#anon$14) && (iir#anon$13 != iir#anon$15) && (iir#anon$13 != iir#anon$16) && (iir#anon$13 != iir#anon$17) && (iir#anon$13 != iir#anon$18) && (iir#anon$13 != iir#anon$19) && (iir#anon$13 != iir#anon$20) && (iir#anon$13 != iir#anon$21) && (iir#anon$13 != iir#anon$22) && (iir#anon$13 != iir#anon$23) && (iir#anon$14 != iir#anon$15) && (iir#anon$14 != iir#anon$16) && (iir#anon$14 != iir#anon$17) && (iir#anon$14 != iir#anon$18) && (iir#anon$14 != iir#anon$19) && (iir#anon$14 != iir#anon$20) && (iir#anon$14 != iir#anon$21) && (iir#anon$14 != iir#anon$22) && (iir#anon$14 != iir#anon$23) && (iir#anon$15 != iir#anon$16) && (iir#anon$15 != iir#anon$17) && (iir#anon$15 != iir#anon$18) && (iir#anon$15 != iir#anon$19) && (iir#anon$15 != iir#anon$20) && (iir#anon$15 != iir#anon$21) && (iir#anon$15 != iir#anon$22) && (iir#anon$15 != iir#anon$23) && (iir#anon$16 != iir#anon$17) && (iir#anon$16 != iir#anon$18) && (iir#anon$16 != iir#anon$19) && (iir#anon$16 != iir#anon$20) && (iir#anon$16 != iir#anon$21) && (iir#anon$16 != iir#anon$22) && (iir#anon$16 != iir#anon$23) && (iir#anon$17 != iir#anon$18) && (iir#anon$17 != iir#anon$19) && (iir#anon$17 != iir#anon$20) && (iir#anon$17 != iir#anon$21) && (iir#anon$17 != iir#anon$22) && (iir#anon$17 != iir#anon$23) && (iir#anon$18 != iir#anon$19) && (iir#anon$18 != iir#anon$20) && (iir#anon$18 != iir#anon$21) && (iir#anon$18 != iir#anon$22) && (iir#anon$18 != iir#anon$23) && (iir#anon$19 != iir#anon$20) && (iir#anon$19 != iir#anon$21) && (iir#anon$19 != iir#anon$22) && (iir#anon$19 != iir#anon$23) && (iir#anon$20 != iir#anon$21) && (iir#anon$20 != iir#anon$22) && (iir#anon$20 != iir#anon$23) && (iir#anon$21 != iir#anon$22) && (iir#anon$21 != iir#anon$23) && (iir#anon$22 != iir#anon$23);
  assume 0 <= I[iir#anon$7];
  assume I[iir#anon$7] <= R[iir#anon$7];
  assume R[iir#anon$7] <= C[iir#anon$7];
  assume 0 <= I[iir#anon$8];
  assume I[iir#anon$8] <= R[iir#anon$8];
  assume R[iir#anon$8] <= C[iir#anon$8];
  assume 0 <= I[iir#anon$9];
  assume I[iir#anon$9] <= R[iir#anon$9];
  assume R[iir#anon$9] <= C[iir#anon$9];
  assume 0 <= I[iir#anon$10];
  assume I[iir#anon$10] <= R[iir#anon$10];
  assume R[iir#anon$10] <= C[iir#anon$10];
  assume 0 <= I[iir#anon$11];
  assume I[iir#anon$11] <= R[iir#anon$11];
  assume R[iir#anon$11] <= C[iir#anon$11];
  assume 0 <= I[iir#anon$12];
  assume I[iir#anon$12] <= R[iir#anon$12];
  assume R[iir#anon$12] <= C[iir#anon$12];
  assume 0 <= I[iir#anon$13];
  assume I[iir#anon$13] <= R[iir#anon$13];
  assume R[iir#anon$13] <= C[iir#anon$13];
  assume 0 <= I[iir#anon$14];
  assume I[iir#anon$14] <= R[iir#anon$14];
  assume R[iir#anon$14] <= C[iir#anon$14];
  assume 0 <= I[iir#anon$15];
  assume I[iir#anon$15] <= R[iir#anon$15];
  assume R[iir#anon$15] <= C[iir#anon$15];
  assume 0 <= I[iir#anon$16];
  assume I[iir#anon$16] <= R[iir#anon$16];
  assume R[iir#anon$16] <= C[iir#anon$16];
  assume 0 <= I[iir#anon$17];
  assume I[iir#anon$17] <= R[iir#anon$17];
  assume R[iir#anon$17] <= C[iir#anon$17];
  assume 0 <= I[iir#anon$18];
  assume I[iir#anon$18] <= R[iir#anon$18];
  assume R[iir#anon$18] <= C[iir#anon$18];
  assume 0 <= I[iir#anon$19];
  assume I[iir#anon$19] <= R[iir#anon$19];
  assume R[iir#anon$19] <= C[iir#anon$19];
  assume 0 <= I[iir#anon$20];
  assume I[iir#anon$20] <= R[iir#anon$20];
  assume R[iir#anon$20] <= C[iir#anon$20];
  assume 0 <= I[iir#anon$21];
  assume I[iir#anon$21] <= R[iir#anon$21];
  assume R[iir#anon$21] <= C[iir#anon$21];
  assume 0 <= I[iir#anon$22];
  assume I[iir#anon$22] <= R[iir#anon$22];
  assume R[iir#anon$22] <= C[iir#anon$22];
  assume 0 <= I[iir#anon$23];
  assume I[iir#anon$23] <= R[iir#anon$23];
  assume R[iir#anon$23] <= C[iir#anon$23];
  assume I[iir#anon$23] == R[iir#anon$23];
  assume I[iir#anon$17] == I[iir#anon$8];
  assume I[iir#anon$18] == I[iir#anon$11];
  assume I[iir#anon$19] == I[iir#anon$14];
  assume I[iir#anon$20] == I[iir#anon$16];
  assume I[iir#anon$21] == I[iir#anon$17];
  assume I[iir#anon$21] == I[iir#anon$18];
  assume I[iir#anon$22] == I[iir#anon$19];
  assume I[iir#anon$22] == I[iir#anon$20];
  assume I[iir#anon$23] == I[iir#anon$21];
  assume I[iir#anon$23] == I[iir#anon$22];
  assume I[iir#anon$8] == I[iir#anon$7];
  assume I[iir#anon$9] == I[iir#anon$7];
  assume I[iir#anon$11] == I[iir#anon$10];
  assume I[iir#anon$12] == I[iir#anon$10];
  assume I[iir#anon$14] == I[iir#anon$13];
  assume I[iir#anon$15] == I[iir#anon$13];
  assume (C[iir#anon$10] == 0) ==> (AV#delay_1#data == 0);
  assume (C[iir#anon$10] > 0) ==> (AV#delay_1#data == M[iir#anon$9][R[iir#anon$9] - 1]);
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$10] > 0) ==> (M[iir#anon$10][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$10] - 0)) ==> (M[iir#anon$10][idx] == M[iir#anon$9][idx - 1])
  );
  assume (C[iir#anon$13] == 0) ==> (AV#delay_2#data == 0);
  assume (C[iir#anon$13] > 0) ==> (AV#delay_2#data == M[iir#anon$12][R[iir#anon$12] - 1]);
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$13] > 0) ==> (M[iir#anon$13][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$13] - 0)) ==> (M[iir#anon$13][idx] == M[iir#anon$12][idx - 1])
  );
  assume (C[iir#anon$16] == 0) ==> (AV#delay_3#data == 0);
  assume (C[iir#anon$16] > 0) ==> (AV#delay_3#data == M[iir#anon$15][R[iir#anon$15] - 1]);
  assume R[iir#anon$15] == C[iir#anon$16];
  assume (C[iir#anon$16] > 0) ==> (M[iir#anon$16][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$16] - 0)) ==> (M[iir#anon$16][idx] == M[iir#anon$15][idx - 1])
  );
  assume R[iir#anon$8] == C[iir#anon$17];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$17]) ==> (M[iir#anon$17][idx$] == (37 * M[iir#anon$8][idx$]))
  );
  assume R[iir#anon$11] == C[iir#anon$18];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$18]) ==> (M[iir#anon$18][idx$] == (109 * M[iir#anon$11][idx$]))
  );
  assume R[iir#anon$14] == C[iir#anon$19];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$19]) ==> (M[iir#anon$19][idx$] == (109 * M[iir#anon$14][idx$]))
  );
  assume R[iir#anon$16] == C[iir#anon$20];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$20]) ==> (M[iir#anon$20][idx$] == (37 * M[iir#anon$16][idx$]))
  );
  assume R[iir#anon$17] == C[iir#anon$21];
  assume R[iir#anon$18] == C[iir#anon$21];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$21]) ==> (M[iir#anon$21][idx$] == (M[iir#anon$17][idx$] + M[iir#anon$18][idx$]))
  );
  assume R[iir#anon$19] == C[iir#anon$22];
  assume R[iir#anon$20] == C[iir#anon$22];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$22]) ==> (M[iir#anon$22][idx$] == (M[iir#anon$19][idx$] + M[iir#anon$20][idx$]))
  );
  assume R[iir#anon$21] == C[iir#anon$23];
  assume R[iir#anon$22] == C[iir#anon$23];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$23]) ==> (M[iir#anon$23][idx$] == (M[iir#anon$21][idx$] + M[iir#anon$22][idx$]))
  );
  assume R[iir#anon$7] == C[iir#anon$8];
  assume R[iir#anon$7] == C[iir#anon$9];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$8]) ==> (M[iir#anon$8][idx$] == M[iir#anon$7][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$9]) ==> (M[iir#anon$9][idx$] == M[iir#anon$7][idx$])
  );
  assume R[iir#anon$10] == C[iir#anon$11];
  assume R[iir#anon$10] == C[iir#anon$12];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$11]) ==> (M[iir#anon$11][idx$] == M[iir#anon$10][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$12]) ==> (M[iir#anon$12][idx$] == M[iir#anon$10][idx$])
  );
  assume R[iir#anon$13] == C[iir#anon$14];
  assume R[iir#anon$13] == C[iir#anon$15];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$14]) ==> (M[iir#anon$14][idx$] == M[iir#anon$13][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$15]) ==> (M[iir#anon$15][idx$] == M[iir#anon$13][idx$])
  );
  assume 1 <= (C[iir#anon$8] - R[iir#anon$8]);
  in#i := M[iir#anon$8][R[iir#anon$8]];
  R[iir#anon$8] := R[iir#anon$8] + 1;
  M[iir#anon$17][C[iir#anon$17]] := 37 * in#i;
  C[iir#anon$17] := C[iir#anon$17] + 1;
  assume (C[iir#anon$10] == 0) ==> (AV#delay_1#data == 0);
  assume (C[iir#anon$10] > 0) ==> (AV#delay_1#data == M[iir#anon$9][R[iir#anon$9] - 1]);
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$10] > 0) ==> (M[iir#anon$10][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$10] - 0)) ==> (M[iir#anon$10][idx] == M[iir#anon$9][idx - 1])
  );
  assume (C[iir#anon$13] == 0) ==> (AV#delay_2#data == 0);
  assume (C[iir#anon$13] > 0) ==> (AV#delay_2#data == M[iir#anon$12][R[iir#anon$12] - 1]);
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$13] > 0) ==> (M[iir#anon$13][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$13] - 0)) ==> (M[iir#anon$13][idx] == M[iir#anon$12][idx - 1])
  );
  assume (C[iir#anon$16] == 0) ==> (AV#delay_3#data == 0);
  assume (C[iir#anon$16] > 0) ==> (AV#delay_3#data == M[iir#anon$15][R[iir#anon$15] - 1]);
  assume R[iir#anon$15] == C[iir#anon$16];
  assume (C[iir#anon$16] > 0) ==> (M[iir#anon$16][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$16] - 0)) ==> (M[iir#anon$16][idx] == M[iir#anon$15][idx - 1])
  );
  assume R[iir#anon$8] == C[iir#anon$17];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$17]) ==> (M[iir#anon$17][idx$] == (37 * M[iir#anon$8][idx$]))
  );
  assume R[iir#anon$11] == C[iir#anon$18];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$18]) ==> (M[iir#anon$18][idx$] == (109 * M[iir#anon$11][idx$]))
  );
  assume R[iir#anon$14] == C[iir#anon$19];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$19]) ==> (M[iir#anon$19][idx$] == (109 * M[iir#anon$14][idx$]))
  );
  assume R[iir#anon$16] == C[iir#anon$20];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$20]) ==> (M[iir#anon$20][idx$] == (37 * M[iir#anon$16][idx$]))
  );
  assume R[iir#anon$17] == C[iir#anon$21];
  assume R[iir#anon$18] == C[iir#anon$21];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$21]) ==> (M[iir#anon$21][idx$] == (M[iir#anon$17][idx$] + M[iir#anon$18][idx$]))
  );
  assume R[iir#anon$19] == C[iir#anon$22];
  assume R[iir#anon$20] == C[iir#anon$22];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$22]) ==> (M[iir#anon$22][idx$] == (M[iir#anon$19][idx$] + M[iir#anon$20][idx$]))
  );
  assume R[iir#anon$21] == C[iir#anon$23];
  assume R[iir#anon$22] == C[iir#anon$23];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$23]) ==> (M[iir#anon$23][idx$] == (M[iir#anon$21][idx$] + M[iir#anon$22][idx$]))
  );
  assume R[iir#anon$7] == C[iir#anon$8];
  assume R[iir#anon$7] == C[iir#anon$9];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$8]) ==> (M[iir#anon$8][idx$] == M[iir#anon$7][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$9]) ==> (M[iir#anon$9][idx$] == M[iir#anon$7][idx$])
  );
  assume R[iir#anon$10] == C[iir#anon$11];
  assume R[iir#anon$10] == C[iir#anon$12];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$11]) ==> (M[iir#anon$11][idx$] == M[iir#anon$10][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$12]) ==> (M[iir#anon$12][idx$] == M[iir#anon$10][idx$])
  );
  assume R[iir#anon$13] == C[iir#anon$14];
  assume R[iir#anon$13] == C[iir#anon$15];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$14]) ==> (M[iir#anon$14][idx$] == M[iir#anon$13][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$15]) ==> (M[iir#anon$15][idx$] == M[iir#anon$13][idx$])
  );
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_1' might not preserve the channel invariant (#113)"} I[iir#anon$17] == I[iir#anon$8];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_1' might not preserve the channel invariant (#114)"} I[iir#anon$18] == I[iir#anon$11];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_1' might not preserve the channel invariant (#115)"} I[iir#anon$19] == I[iir#anon$14];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_1' might not preserve the channel invariant (#116)"} I[iir#anon$20] == I[iir#anon$16];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_1' might not preserve the channel invariant (#117)"} I[iir#anon$21] == I[iir#anon$17];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_1' might not preserve the channel invariant (#118)"} I[iir#anon$21] == I[iir#anon$18];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_1' might not preserve the channel invariant (#119)"} I[iir#anon$22] == I[iir#anon$19];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_1' might not preserve the channel invariant (#120)"} I[iir#anon$22] == I[iir#anon$20];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_1' might not preserve the channel invariant (#121)"} I[iir#anon$23] == I[iir#anon$21];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_1' might not preserve the channel invariant (#122)"} I[iir#anon$23] == I[iir#anon$22];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_1' might not preserve the channel invariant (#123)"} I[iir#anon$8] == I[iir#anon$7];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_1' might not preserve the channel invariant (#124)"} I[iir#anon$9] == I[iir#anon$7];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_1' might not preserve the channel invariant (#125)"} I[iir#anon$11] == I[iir#anon$10];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_1' might not preserve the channel invariant (#126)"} I[iir#anon$12] == I[iir#anon$10];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_1' might not preserve the channel invariant (#127)"} I[iir#anon$14] == I[iir#anon$13];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_1' might not preserve the channel invariant (#128)"} I[iir#anon$15] == I[iir#anon$13];
}
procedure iir##mulc#anon$3#15()
  modifies C, R, M, I, H;
{
  var iir#delay_1: Actor;
  var iir#delay_2: Actor;
  var iir#delay_3: Actor;
  var iir#mul_1: Actor;
  var iir#mul_2: Actor;
  var iir#mul_3: Actor;
  var iir#mul_4: Actor;
  var iir#add_1: Actor;
  var iir#add_2: Actor;
  var iir#add_3: Actor;
  var iir#spl_1: Actor;
  var iir#spl_2: Actor;
  var iir#spl_3: Actor;
  var iir#anon$7: Chan (int);
  var iir#anon$8: Chan (int);
  var iir#anon$9: Chan (int);
  var iir#anon$10: Chan (int);
  var iir#anon$11: Chan (int);
  var iir#anon$12: Chan (int);
  var iir#anon$13: Chan (int);
  var iir#anon$14: Chan (int);
  var iir#anon$15: Chan (int);
  var iir#anon$16: Chan (int);
  var iir#anon$17: Chan (int);
  var iir#anon$18: Chan (int);
  var iir#anon$19: Chan (int);
  var iir#anon$20: Chan (int);
  var iir#anon$21: Chan (int);
  var iir#anon$22: Chan (int);
  var iir#anon$23: Chan (int);
  var AV#delay_1#data: int;
  var AV#delay_1#y: int;
  var AV#delay_2#data: int;
  var AV#delay_2#y: int;
  var AV#delay_3#data: int;
  var AV#delay_3#y: int;
  var in#i: int;
  assume (iir#delay_1 != iir#delay_2) && (iir#delay_1 != iir#delay_3) && (iir#delay_1 != iir#mul_1) && (iir#delay_1 != iir#mul_2) && (iir#delay_1 != iir#mul_3) && (iir#delay_1 != iir#mul_4) && (iir#delay_1 != iir#add_1) && (iir#delay_1 != iir#add_2) && (iir#delay_1 != iir#add_3) && (iir#delay_1 != iir#spl_1) && (iir#delay_1 != iir#spl_2) && (iir#delay_1 != iir#spl_3) && (iir#delay_2 != iir#delay_3) && (iir#delay_2 != iir#mul_1) && (iir#delay_2 != iir#mul_2) && (iir#delay_2 != iir#mul_3) && (iir#delay_2 != iir#mul_4) && (iir#delay_2 != iir#add_1) && (iir#delay_2 != iir#add_2) && (iir#delay_2 != iir#add_3) && (iir#delay_2 != iir#spl_1) && (iir#delay_2 != iir#spl_2) && (iir#delay_2 != iir#spl_3) && (iir#delay_3 != iir#mul_1) && (iir#delay_3 != iir#mul_2) && (iir#delay_3 != iir#mul_3) && (iir#delay_3 != iir#mul_4) && (iir#delay_3 != iir#add_1) && (iir#delay_3 != iir#add_2) && (iir#delay_3 != iir#add_3) && (iir#delay_3 != iir#spl_1) && (iir#delay_3 != iir#spl_2) && (iir#delay_3 != iir#spl_3) && (iir#mul_1 != iir#mul_2) && (iir#mul_1 != iir#mul_3) && (iir#mul_1 != iir#mul_4) && (iir#mul_1 != iir#add_1) && (iir#mul_1 != iir#add_2) && (iir#mul_1 != iir#add_3) && (iir#mul_1 != iir#spl_1) && (iir#mul_1 != iir#spl_2) && (iir#mul_1 != iir#spl_3) && (iir#mul_2 != iir#mul_3) && (iir#mul_2 != iir#mul_4) && (iir#mul_2 != iir#add_1) && (iir#mul_2 != iir#add_2) && (iir#mul_2 != iir#add_3) && (iir#mul_2 != iir#spl_1) && (iir#mul_2 != iir#spl_2) && (iir#mul_2 != iir#spl_3) && (iir#mul_3 != iir#mul_4) && (iir#mul_3 != iir#add_1) && (iir#mul_3 != iir#add_2) && (iir#mul_3 != iir#add_3) && (iir#mul_3 != iir#spl_1) && (iir#mul_3 != iir#spl_2) && (iir#mul_3 != iir#spl_3) && (iir#mul_4 != iir#add_1) && (iir#mul_4 != iir#add_2) && (iir#mul_4 != iir#add_3) && (iir#mul_4 != iir#spl_1) && (iir#mul_4 != iir#spl_2) && (iir#mul_4 != iir#spl_3) && (iir#add_1 != iir#add_2) && (iir#add_1 != iir#add_3) && (iir#add_1 != iir#spl_1) && (iir#add_1 != iir#spl_2) && (iir#add_1 != iir#spl_3) && (iir#add_2 != iir#add_3) && (iir#add_2 != iir#spl_1) && (iir#add_2 != iir#spl_2) && (iir#add_2 != iir#spl_3) && (iir#add_3 != iir#spl_1) && (iir#add_3 != iir#spl_2) && (iir#add_3 != iir#spl_3) && (iir#spl_1 != iir#spl_2) && (iir#spl_1 != iir#spl_3) && (iir#spl_2 != iir#spl_3);
  assume (iir#anon$7 != iir#anon$8) && (iir#anon$7 != iir#anon$9) && (iir#anon$7 != iir#anon$10) && (iir#anon$7 != iir#anon$11) && (iir#anon$7 != iir#anon$12) && (iir#anon$7 != iir#anon$13) && (iir#anon$7 != iir#anon$14) && (iir#anon$7 != iir#anon$15) && (iir#anon$7 != iir#anon$16) && (iir#anon$7 != iir#anon$17) && (iir#anon$7 != iir#anon$18) && (iir#anon$7 != iir#anon$19) && (iir#anon$7 != iir#anon$20) && (iir#anon$7 != iir#anon$21) && (iir#anon$7 != iir#anon$22) && (iir#anon$7 != iir#anon$23) && (iir#anon$8 != iir#anon$9) && (iir#anon$8 != iir#anon$10) && (iir#anon$8 != iir#anon$11) && (iir#anon$8 != iir#anon$12) && (iir#anon$8 != iir#anon$13) && (iir#anon$8 != iir#anon$14) && (iir#anon$8 != iir#anon$15) && (iir#anon$8 != iir#anon$16) && (iir#anon$8 != iir#anon$17) && (iir#anon$8 != iir#anon$18) && (iir#anon$8 != iir#anon$19) && (iir#anon$8 != iir#anon$20) && (iir#anon$8 != iir#anon$21) && (iir#anon$8 != iir#anon$22) && (iir#anon$8 != iir#anon$23) && (iir#anon$9 != iir#anon$10) && (iir#anon$9 != iir#anon$11) && (iir#anon$9 != iir#anon$12) && (iir#anon$9 != iir#anon$13) && (iir#anon$9 != iir#anon$14) && (iir#anon$9 != iir#anon$15) && (iir#anon$9 != iir#anon$16) && (iir#anon$9 != iir#anon$17) && (iir#anon$9 != iir#anon$18) && (iir#anon$9 != iir#anon$19) && (iir#anon$9 != iir#anon$20) && (iir#anon$9 != iir#anon$21) && (iir#anon$9 != iir#anon$22) && (iir#anon$9 != iir#anon$23) && (iir#anon$10 != iir#anon$11) && (iir#anon$10 != iir#anon$12) && (iir#anon$10 != iir#anon$13) && (iir#anon$10 != iir#anon$14) && (iir#anon$10 != iir#anon$15) && (iir#anon$10 != iir#anon$16) && (iir#anon$10 != iir#anon$17) && (iir#anon$10 != iir#anon$18) && (iir#anon$10 != iir#anon$19) && (iir#anon$10 != iir#anon$20) && (iir#anon$10 != iir#anon$21) && (iir#anon$10 != iir#anon$22) && (iir#anon$10 != iir#anon$23) && (iir#anon$11 != iir#anon$12) && (iir#anon$11 != iir#anon$13) && (iir#anon$11 != iir#anon$14) && (iir#anon$11 != iir#anon$15) && (iir#anon$11 != iir#anon$16) && (iir#anon$11 != iir#anon$17) && (iir#anon$11 != iir#anon$18) && (iir#anon$11 != iir#anon$19) && (iir#anon$11 != iir#anon$20) && (iir#anon$11 != iir#anon$21) && (iir#anon$11 != iir#anon$22) && (iir#anon$11 != iir#anon$23) && (iir#anon$12 != iir#anon$13) && (iir#anon$12 != iir#anon$14) && (iir#anon$12 != iir#anon$15) && (iir#anon$12 != iir#anon$16) && (iir#anon$12 != iir#anon$17) && (iir#anon$12 != iir#anon$18) && (iir#anon$12 != iir#anon$19) && (iir#anon$12 != iir#anon$20) && (iir#anon$12 != iir#anon$21) && (iir#anon$12 != iir#anon$22) && (iir#anon$12 != iir#anon$23) && (iir#anon$13 != iir#anon$14) && (iir#anon$13 != iir#anon$15) && (iir#anon$13 != iir#anon$16) && (iir#anon$13 != iir#anon$17) && (iir#anon$13 != iir#anon$18) && (iir#anon$13 != iir#anon$19) && (iir#anon$13 != iir#anon$20) && (iir#anon$13 != iir#anon$21) && (iir#anon$13 != iir#anon$22) && (iir#anon$13 != iir#anon$23) && (iir#anon$14 != iir#anon$15) && (iir#anon$14 != iir#anon$16) && (iir#anon$14 != iir#anon$17) && (iir#anon$14 != iir#anon$18) && (iir#anon$14 != iir#anon$19) && (iir#anon$14 != iir#anon$20) && (iir#anon$14 != iir#anon$21) && (iir#anon$14 != iir#anon$22) && (iir#anon$14 != iir#anon$23) && (iir#anon$15 != iir#anon$16) && (iir#anon$15 != iir#anon$17) && (iir#anon$15 != iir#anon$18) && (iir#anon$15 != iir#anon$19) && (iir#anon$15 != iir#anon$20) && (iir#anon$15 != iir#anon$21) && (iir#anon$15 != iir#anon$22) && (iir#anon$15 != iir#anon$23) && (iir#anon$16 != iir#anon$17) && (iir#anon$16 != iir#anon$18) && (iir#anon$16 != iir#anon$19) && (iir#anon$16 != iir#anon$20) && (iir#anon$16 != iir#anon$21) && (iir#anon$16 != iir#anon$22) && (iir#anon$16 != iir#anon$23) && (iir#anon$17 != iir#anon$18) && (iir#anon$17 != iir#anon$19) && (iir#anon$17 != iir#anon$20) && (iir#anon$17 != iir#anon$21) && (iir#anon$17 != iir#anon$22) && (iir#anon$17 != iir#anon$23) && (iir#anon$18 != iir#anon$19) && (iir#anon$18 != iir#anon$20) && (iir#anon$18 != iir#anon$21) && (iir#anon$18 != iir#anon$22) && (iir#anon$18 != iir#anon$23) && (iir#anon$19 != iir#anon$20) && (iir#anon$19 != iir#anon$21) && (iir#anon$19 != iir#anon$22) && (iir#anon$19 != iir#anon$23) && (iir#anon$20 != iir#anon$21) && (iir#anon$20 != iir#anon$22) && (iir#anon$20 != iir#anon$23) && (iir#anon$21 != iir#anon$22) && (iir#anon$21 != iir#anon$23) && (iir#anon$22 != iir#anon$23);
  assume 0 <= I[iir#anon$7];
  assume I[iir#anon$7] <= R[iir#anon$7];
  assume R[iir#anon$7] <= C[iir#anon$7];
  assume 0 <= I[iir#anon$8];
  assume I[iir#anon$8] <= R[iir#anon$8];
  assume R[iir#anon$8] <= C[iir#anon$8];
  assume 0 <= I[iir#anon$9];
  assume I[iir#anon$9] <= R[iir#anon$9];
  assume R[iir#anon$9] <= C[iir#anon$9];
  assume 0 <= I[iir#anon$10];
  assume I[iir#anon$10] <= R[iir#anon$10];
  assume R[iir#anon$10] <= C[iir#anon$10];
  assume 0 <= I[iir#anon$11];
  assume I[iir#anon$11] <= R[iir#anon$11];
  assume R[iir#anon$11] <= C[iir#anon$11];
  assume 0 <= I[iir#anon$12];
  assume I[iir#anon$12] <= R[iir#anon$12];
  assume R[iir#anon$12] <= C[iir#anon$12];
  assume 0 <= I[iir#anon$13];
  assume I[iir#anon$13] <= R[iir#anon$13];
  assume R[iir#anon$13] <= C[iir#anon$13];
  assume 0 <= I[iir#anon$14];
  assume I[iir#anon$14] <= R[iir#anon$14];
  assume R[iir#anon$14] <= C[iir#anon$14];
  assume 0 <= I[iir#anon$15];
  assume I[iir#anon$15] <= R[iir#anon$15];
  assume R[iir#anon$15] <= C[iir#anon$15];
  assume 0 <= I[iir#anon$16];
  assume I[iir#anon$16] <= R[iir#anon$16];
  assume R[iir#anon$16] <= C[iir#anon$16];
  assume 0 <= I[iir#anon$17];
  assume I[iir#anon$17] <= R[iir#anon$17];
  assume R[iir#anon$17] <= C[iir#anon$17];
  assume 0 <= I[iir#anon$18];
  assume I[iir#anon$18] <= R[iir#anon$18];
  assume R[iir#anon$18] <= C[iir#anon$18];
  assume 0 <= I[iir#anon$19];
  assume I[iir#anon$19] <= R[iir#anon$19];
  assume R[iir#anon$19] <= C[iir#anon$19];
  assume 0 <= I[iir#anon$20];
  assume I[iir#anon$20] <= R[iir#anon$20];
  assume R[iir#anon$20] <= C[iir#anon$20];
  assume 0 <= I[iir#anon$21];
  assume I[iir#anon$21] <= R[iir#anon$21];
  assume R[iir#anon$21] <= C[iir#anon$21];
  assume 0 <= I[iir#anon$22];
  assume I[iir#anon$22] <= R[iir#anon$22];
  assume R[iir#anon$22] <= C[iir#anon$22];
  assume 0 <= I[iir#anon$23];
  assume I[iir#anon$23] <= R[iir#anon$23];
  assume R[iir#anon$23] <= C[iir#anon$23];
  assume I[iir#anon$23] == R[iir#anon$23];
  assume I[iir#anon$17] == I[iir#anon$8];
  assume I[iir#anon$18] == I[iir#anon$11];
  assume I[iir#anon$19] == I[iir#anon$14];
  assume I[iir#anon$20] == I[iir#anon$16];
  assume I[iir#anon$21] == I[iir#anon$17];
  assume I[iir#anon$21] == I[iir#anon$18];
  assume I[iir#anon$22] == I[iir#anon$19];
  assume I[iir#anon$22] == I[iir#anon$20];
  assume I[iir#anon$23] == I[iir#anon$21];
  assume I[iir#anon$23] == I[iir#anon$22];
  assume I[iir#anon$8] == I[iir#anon$7];
  assume I[iir#anon$9] == I[iir#anon$7];
  assume I[iir#anon$11] == I[iir#anon$10];
  assume I[iir#anon$12] == I[iir#anon$10];
  assume I[iir#anon$14] == I[iir#anon$13];
  assume I[iir#anon$15] == I[iir#anon$13];
  assume (C[iir#anon$10] == 0) ==> (AV#delay_1#data == 0);
  assume (C[iir#anon$10] > 0) ==> (AV#delay_1#data == M[iir#anon$9][R[iir#anon$9] - 1]);
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$10] > 0) ==> (M[iir#anon$10][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$10] - 0)) ==> (M[iir#anon$10][idx] == M[iir#anon$9][idx - 1])
  );
  assume (C[iir#anon$13] == 0) ==> (AV#delay_2#data == 0);
  assume (C[iir#anon$13] > 0) ==> (AV#delay_2#data == M[iir#anon$12][R[iir#anon$12] - 1]);
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$13] > 0) ==> (M[iir#anon$13][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$13] - 0)) ==> (M[iir#anon$13][idx] == M[iir#anon$12][idx - 1])
  );
  assume (C[iir#anon$16] == 0) ==> (AV#delay_3#data == 0);
  assume (C[iir#anon$16] > 0) ==> (AV#delay_3#data == M[iir#anon$15][R[iir#anon$15] - 1]);
  assume R[iir#anon$15] == C[iir#anon$16];
  assume (C[iir#anon$16] > 0) ==> (M[iir#anon$16][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$16] - 0)) ==> (M[iir#anon$16][idx] == M[iir#anon$15][idx - 1])
  );
  assume R[iir#anon$8] == C[iir#anon$17];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$17]) ==> (M[iir#anon$17][idx$] == (37 * M[iir#anon$8][idx$]))
  );
  assume R[iir#anon$11] == C[iir#anon$18];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$18]) ==> (M[iir#anon$18][idx$] == (109 * M[iir#anon$11][idx$]))
  );
  assume R[iir#anon$14] == C[iir#anon$19];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$19]) ==> (M[iir#anon$19][idx$] == (109 * M[iir#anon$14][idx$]))
  );
  assume R[iir#anon$16] == C[iir#anon$20];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$20]) ==> (M[iir#anon$20][idx$] == (37 * M[iir#anon$16][idx$]))
  );
  assume R[iir#anon$17] == C[iir#anon$21];
  assume R[iir#anon$18] == C[iir#anon$21];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$21]) ==> (M[iir#anon$21][idx$] == (M[iir#anon$17][idx$] + M[iir#anon$18][idx$]))
  );
  assume R[iir#anon$19] == C[iir#anon$22];
  assume R[iir#anon$20] == C[iir#anon$22];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$22]) ==> (M[iir#anon$22][idx$] == (M[iir#anon$19][idx$] + M[iir#anon$20][idx$]))
  );
  assume R[iir#anon$21] == C[iir#anon$23];
  assume R[iir#anon$22] == C[iir#anon$23];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$23]) ==> (M[iir#anon$23][idx$] == (M[iir#anon$21][idx$] + M[iir#anon$22][idx$]))
  );
  assume R[iir#anon$7] == C[iir#anon$8];
  assume R[iir#anon$7] == C[iir#anon$9];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$8]) ==> (M[iir#anon$8][idx$] == M[iir#anon$7][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$9]) ==> (M[iir#anon$9][idx$] == M[iir#anon$7][idx$])
  );
  assume R[iir#anon$10] == C[iir#anon$11];
  assume R[iir#anon$10] == C[iir#anon$12];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$11]) ==> (M[iir#anon$11][idx$] == M[iir#anon$10][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$12]) ==> (M[iir#anon$12][idx$] == M[iir#anon$10][idx$])
  );
  assume R[iir#anon$13] == C[iir#anon$14];
  assume R[iir#anon$13] == C[iir#anon$15];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$14]) ==> (M[iir#anon$14][idx$] == M[iir#anon$13][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$15]) ==> (M[iir#anon$15][idx$] == M[iir#anon$13][idx$])
  );
  assume 1 <= (C[iir#anon$11] - R[iir#anon$11]);
  in#i := M[iir#anon$11][R[iir#anon$11]];
  R[iir#anon$11] := R[iir#anon$11] + 1;
  M[iir#anon$18][C[iir#anon$18]] := 109 * in#i;
  C[iir#anon$18] := C[iir#anon$18] + 1;
  assume (C[iir#anon$10] == 0) ==> (AV#delay_1#data == 0);
  assume (C[iir#anon$10] > 0) ==> (AV#delay_1#data == M[iir#anon$9][R[iir#anon$9] - 1]);
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$10] > 0) ==> (M[iir#anon$10][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$10] - 0)) ==> (M[iir#anon$10][idx] == M[iir#anon$9][idx - 1])
  );
  assume (C[iir#anon$13] == 0) ==> (AV#delay_2#data == 0);
  assume (C[iir#anon$13] > 0) ==> (AV#delay_2#data == M[iir#anon$12][R[iir#anon$12] - 1]);
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$13] > 0) ==> (M[iir#anon$13][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$13] - 0)) ==> (M[iir#anon$13][idx] == M[iir#anon$12][idx - 1])
  );
  assume (C[iir#anon$16] == 0) ==> (AV#delay_3#data == 0);
  assume (C[iir#anon$16] > 0) ==> (AV#delay_3#data == M[iir#anon$15][R[iir#anon$15] - 1]);
  assume R[iir#anon$15] == C[iir#anon$16];
  assume (C[iir#anon$16] > 0) ==> (M[iir#anon$16][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$16] - 0)) ==> (M[iir#anon$16][idx] == M[iir#anon$15][idx - 1])
  );
  assume R[iir#anon$8] == C[iir#anon$17];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$17]) ==> (M[iir#anon$17][idx$] == (37 * M[iir#anon$8][idx$]))
  );
  assume R[iir#anon$11] == C[iir#anon$18];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$18]) ==> (M[iir#anon$18][idx$] == (109 * M[iir#anon$11][idx$]))
  );
  assume R[iir#anon$14] == C[iir#anon$19];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$19]) ==> (M[iir#anon$19][idx$] == (109 * M[iir#anon$14][idx$]))
  );
  assume R[iir#anon$16] == C[iir#anon$20];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$20]) ==> (M[iir#anon$20][idx$] == (37 * M[iir#anon$16][idx$]))
  );
  assume R[iir#anon$17] == C[iir#anon$21];
  assume R[iir#anon$18] == C[iir#anon$21];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$21]) ==> (M[iir#anon$21][idx$] == (M[iir#anon$17][idx$] + M[iir#anon$18][idx$]))
  );
  assume R[iir#anon$19] == C[iir#anon$22];
  assume R[iir#anon$20] == C[iir#anon$22];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$22]) ==> (M[iir#anon$22][idx$] == (M[iir#anon$19][idx$] + M[iir#anon$20][idx$]))
  );
  assume R[iir#anon$21] == C[iir#anon$23];
  assume R[iir#anon$22] == C[iir#anon$23];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$23]) ==> (M[iir#anon$23][idx$] == (M[iir#anon$21][idx$] + M[iir#anon$22][idx$]))
  );
  assume R[iir#anon$7] == C[iir#anon$8];
  assume R[iir#anon$7] == C[iir#anon$9];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$8]) ==> (M[iir#anon$8][idx$] == M[iir#anon$7][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$9]) ==> (M[iir#anon$9][idx$] == M[iir#anon$7][idx$])
  );
  assume R[iir#anon$10] == C[iir#anon$11];
  assume R[iir#anon$10] == C[iir#anon$12];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$11]) ==> (M[iir#anon$11][idx$] == M[iir#anon$10][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$12]) ==> (M[iir#anon$12][idx$] == M[iir#anon$10][idx$])
  );
  assume R[iir#anon$13] == C[iir#anon$14];
  assume R[iir#anon$13] == C[iir#anon$15];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$14]) ==> (M[iir#anon$14][idx$] == M[iir#anon$13][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$15]) ==> (M[iir#anon$15][idx$] == M[iir#anon$13][idx$])
  );
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_2' might not preserve the channel invariant (#129)"} I[iir#anon$17] == I[iir#anon$8];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_2' might not preserve the channel invariant (#130)"} I[iir#anon$18] == I[iir#anon$11];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_2' might not preserve the channel invariant (#131)"} I[iir#anon$19] == I[iir#anon$14];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_2' might not preserve the channel invariant (#132)"} I[iir#anon$20] == I[iir#anon$16];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_2' might not preserve the channel invariant (#133)"} I[iir#anon$21] == I[iir#anon$17];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_2' might not preserve the channel invariant (#134)"} I[iir#anon$21] == I[iir#anon$18];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_2' might not preserve the channel invariant (#135)"} I[iir#anon$22] == I[iir#anon$19];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_2' might not preserve the channel invariant (#136)"} I[iir#anon$22] == I[iir#anon$20];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_2' might not preserve the channel invariant (#137)"} I[iir#anon$23] == I[iir#anon$21];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_2' might not preserve the channel invariant (#138)"} I[iir#anon$23] == I[iir#anon$22];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_2' might not preserve the channel invariant (#139)"} I[iir#anon$8] == I[iir#anon$7];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_2' might not preserve the channel invariant (#140)"} I[iir#anon$9] == I[iir#anon$7];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_2' might not preserve the channel invariant (#141)"} I[iir#anon$11] == I[iir#anon$10];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_2' might not preserve the channel invariant (#142)"} I[iir#anon$12] == I[iir#anon$10];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_2' might not preserve the channel invariant (#143)"} I[iir#anon$14] == I[iir#anon$13];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_2' might not preserve the channel invariant (#144)"} I[iir#anon$15] == I[iir#anon$13];
}
procedure iir##mulc#anon$3#16()
  modifies C, R, M, I, H;
{
  var iir#delay_1: Actor;
  var iir#delay_2: Actor;
  var iir#delay_3: Actor;
  var iir#mul_1: Actor;
  var iir#mul_2: Actor;
  var iir#mul_3: Actor;
  var iir#mul_4: Actor;
  var iir#add_1: Actor;
  var iir#add_2: Actor;
  var iir#add_3: Actor;
  var iir#spl_1: Actor;
  var iir#spl_2: Actor;
  var iir#spl_3: Actor;
  var iir#anon$7: Chan (int);
  var iir#anon$8: Chan (int);
  var iir#anon$9: Chan (int);
  var iir#anon$10: Chan (int);
  var iir#anon$11: Chan (int);
  var iir#anon$12: Chan (int);
  var iir#anon$13: Chan (int);
  var iir#anon$14: Chan (int);
  var iir#anon$15: Chan (int);
  var iir#anon$16: Chan (int);
  var iir#anon$17: Chan (int);
  var iir#anon$18: Chan (int);
  var iir#anon$19: Chan (int);
  var iir#anon$20: Chan (int);
  var iir#anon$21: Chan (int);
  var iir#anon$22: Chan (int);
  var iir#anon$23: Chan (int);
  var AV#delay_1#data: int;
  var AV#delay_1#y: int;
  var AV#delay_2#data: int;
  var AV#delay_2#y: int;
  var AV#delay_3#data: int;
  var AV#delay_3#y: int;
  var in#i: int;
  assume (iir#delay_1 != iir#delay_2) && (iir#delay_1 != iir#delay_3) && (iir#delay_1 != iir#mul_1) && (iir#delay_1 != iir#mul_2) && (iir#delay_1 != iir#mul_3) && (iir#delay_1 != iir#mul_4) && (iir#delay_1 != iir#add_1) && (iir#delay_1 != iir#add_2) && (iir#delay_1 != iir#add_3) && (iir#delay_1 != iir#spl_1) && (iir#delay_1 != iir#spl_2) && (iir#delay_1 != iir#spl_3) && (iir#delay_2 != iir#delay_3) && (iir#delay_2 != iir#mul_1) && (iir#delay_2 != iir#mul_2) && (iir#delay_2 != iir#mul_3) && (iir#delay_2 != iir#mul_4) && (iir#delay_2 != iir#add_1) && (iir#delay_2 != iir#add_2) && (iir#delay_2 != iir#add_3) && (iir#delay_2 != iir#spl_1) && (iir#delay_2 != iir#spl_2) && (iir#delay_2 != iir#spl_3) && (iir#delay_3 != iir#mul_1) && (iir#delay_3 != iir#mul_2) && (iir#delay_3 != iir#mul_3) && (iir#delay_3 != iir#mul_4) && (iir#delay_3 != iir#add_1) && (iir#delay_3 != iir#add_2) && (iir#delay_3 != iir#add_3) && (iir#delay_3 != iir#spl_1) && (iir#delay_3 != iir#spl_2) && (iir#delay_3 != iir#spl_3) && (iir#mul_1 != iir#mul_2) && (iir#mul_1 != iir#mul_3) && (iir#mul_1 != iir#mul_4) && (iir#mul_1 != iir#add_1) && (iir#mul_1 != iir#add_2) && (iir#mul_1 != iir#add_3) && (iir#mul_1 != iir#spl_1) && (iir#mul_1 != iir#spl_2) && (iir#mul_1 != iir#spl_3) && (iir#mul_2 != iir#mul_3) && (iir#mul_2 != iir#mul_4) && (iir#mul_2 != iir#add_1) && (iir#mul_2 != iir#add_2) && (iir#mul_2 != iir#add_3) && (iir#mul_2 != iir#spl_1) && (iir#mul_2 != iir#spl_2) && (iir#mul_2 != iir#spl_3) && (iir#mul_3 != iir#mul_4) && (iir#mul_3 != iir#add_1) && (iir#mul_3 != iir#add_2) && (iir#mul_3 != iir#add_3) && (iir#mul_3 != iir#spl_1) && (iir#mul_3 != iir#spl_2) && (iir#mul_3 != iir#spl_3) && (iir#mul_4 != iir#add_1) && (iir#mul_4 != iir#add_2) && (iir#mul_4 != iir#add_3) && (iir#mul_4 != iir#spl_1) && (iir#mul_4 != iir#spl_2) && (iir#mul_4 != iir#spl_3) && (iir#add_1 != iir#add_2) && (iir#add_1 != iir#add_3) && (iir#add_1 != iir#spl_1) && (iir#add_1 != iir#spl_2) && (iir#add_1 != iir#spl_3) && (iir#add_2 != iir#add_3) && (iir#add_2 != iir#spl_1) && (iir#add_2 != iir#spl_2) && (iir#add_2 != iir#spl_3) && (iir#add_3 != iir#spl_1) && (iir#add_3 != iir#spl_2) && (iir#add_3 != iir#spl_3) && (iir#spl_1 != iir#spl_2) && (iir#spl_1 != iir#spl_3) && (iir#spl_2 != iir#spl_3);
  assume (iir#anon$7 != iir#anon$8) && (iir#anon$7 != iir#anon$9) && (iir#anon$7 != iir#anon$10) && (iir#anon$7 != iir#anon$11) && (iir#anon$7 != iir#anon$12) && (iir#anon$7 != iir#anon$13) && (iir#anon$7 != iir#anon$14) && (iir#anon$7 != iir#anon$15) && (iir#anon$7 != iir#anon$16) && (iir#anon$7 != iir#anon$17) && (iir#anon$7 != iir#anon$18) && (iir#anon$7 != iir#anon$19) && (iir#anon$7 != iir#anon$20) && (iir#anon$7 != iir#anon$21) && (iir#anon$7 != iir#anon$22) && (iir#anon$7 != iir#anon$23) && (iir#anon$8 != iir#anon$9) && (iir#anon$8 != iir#anon$10) && (iir#anon$8 != iir#anon$11) && (iir#anon$8 != iir#anon$12) && (iir#anon$8 != iir#anon$13) && (iir#anon$8 != iir#anon$14) && (iir#anon$8 != iir#anon$15) && (iir#anon$8 != iir#anon$16) && (iir#anon$8 != iir#anon$17) && (iir#anon$8 != iir#anon$18) && (iir#anon$8 != iir#anon$19) && (iir#anon$8 != iir#anon$20) && (iir#anon$8 != iir#anon$21) && (iir#anon$8 != iir#anon$22) && (iir#anon$8 != iir#anon$23) && (iir#anon$9 != iir#anon$10) && (iir#anon$9 != iir#anon$11) && (iir#anon$9 != iir#anon$12) && (iir#anon$9 != iir#anon$13) && (iir#anon$9 != iir#anon$14) && (iir#anon$9 != iir#anon$15) && (iir#anon$9 != iir#anon$16) && (iir#anon$9 != iir#anon$17) && (iir#anon$9 != iir#anon$18) && (iir#anon$9 != iir#anon$19) && (iir#anon$9 != iir#anon$20) && (iir#anon$9 != iir#anon$21) && (iir#anon$9 != iir#anon$22) && (iir#anon$9 != iir#anon$23) && (iir#anon$10 != iir#anon$11) && (iir#anon$10 != iir#anon$12) && (iir#anon$10 != iir#anon$13) && (iir#anon$10 != iir#anon$14) && (iir#anon$10 != iir#anon$15) && (iir#anon$10 != iir#anon$16) && (iir#anon$10 != iir#anon$17) && (iir#anon$10 != iir#anon$18) && (iir#anon$10 != iir#anon$19) && (iir#anon$10 != iir#anon$20) && (iir#anon$10 != iir#anon$21) && (iir#anon$10 != iir#anon$22) && (iir#anon$10 != iir#anon$23) && (iir#anon$11 != iir#anon$12) && (iir#anon$11 != iir#anon$13) && (iir#anon$11 != iir#anon$14) && (iir#anon$11 != iir#anon$15) && (iir#anon$11 != iir#anon$16) && (iir#anon$11 != iir#anon$17) && (iir#anon$11 != iir#anon$18) && (iir#anon$11 != iir#anon$19) && (iir#anon$11 != iir#anon$20) && (iir#anon$11 != iir#anon$21) && (iir#anon$11 != iir#anon$22) && (iir#anon$11 != iir#anon$23) && (iir#anon$12 != iir#anon$13) && (iir#anon$12 != iir#anon$14) && (iir#anon$12 != iir#anon$15) && (iir#anon$12 != iir#anon$16) && (iir#anon$12 != iir#anon$17) && (iir#anon$12 != iir#anon$18) && (iir#anon$12 != iir#anon$19) && (iir#anon$12 != iir#anon$20) && (iir#anon$12 != iir#anon$21) && (iir#anon$12 != iir#anon$22) && (iir#anon$12 != iir#anon$23) && (iir#anon$13 != iir#anon$14) && (iir#anon$13 != iir#anon$15) && (iir#anon$13 != iir#anon$16) && (iir#anon$13 != iir#anon$17) && (iir#anon$13 != iir#anon$18) && (iir#anon$13 != iir#anon$19) && (iir#anon$13 != iir#anon$20) && (iir#anon$13 != iir#anon$21) && (iir#anon$13 != iir#anon$22) && (iir#anon$13 != iir#anon$23) && (iir#anon$14 != iir#anon$15) && (iir#anon$14 != iir#anon$16) && (iir#anon$14 != iir#anon$17) && (iir#anon$14 != iir#anon$18) && (iir#anon$14 != iir#anon$19) && (iir#anon$14 != iir#anon$20) && (iir#anon$14 != iir#anon$21) && (iir#anon$14 != iir#anon$22) && (iir#anon$14 != iir#anon$23) && (iir#anon$15 != iir#anon$16) && (iir#anon$15 != iir#anon$17) && (iir#anon$15 != iir#anon$18) && (iir#anon$15 != iir#anon$19) && (iir#anon$15 != iir#anon$20) && (iir#anon$15 != iir#anon$21) && (iir#anon$15 != iir#anon$22) && (iir#anon$15 != iir#anon$23) && (iir#anon$16 != iir#anon$17) && (iir#anon$16 != iir#anon$18) && (iir#anon$16 != iir#anon$19) && (iir#anon$16 != iir#anon$20) && (iir#anon$16 != iir#anon$21) && (iir#anon$16 != iir#anon$22) && (iir#anon$16 != iir#anon$23) && (iir#anon$17 != iir#anon$18) && (iir#anon$17 != iir#anon$19) && (iir#anon$17 != iir#anon$20) && (iir#anon$17 != iir#anon$21) && (iir#anon$17 != iir#anon$22) && (iir#anon$17 != iir#anon$23) && (iir#anon$18 != iir#anon$19) && (iir#anon$18 != iir#anon$20) && (iir#anon$18 != iir#anon$21) && (iir#anon$18 != iir#anon$22) && (iir#anon$18 != iir#anon$23) && (iir#anon$19 != iir#anon$20) && (iir#anon$19 != iir#anon$21) && (iir#anon$19 != iir#anon$22) && (iir#anon$19 != iir#anon$23) && (iir#anon$20 != iir#anon$21) && (iir#anon$20 != iir#anon$22) && (iir#anon$20 != iir#anon$23) && (iir#anon$21 != iir#anon$22) && (iir#anon$21 != iir#anon$23) && (iir#anon$22 != iir#anon$23);
  assume 0 <= I[iir#anon$7];
  assume I[iir#anon$7] <= R[iir#anon$7];
  assume R[iir#anon$7] <= C[iir#anon$7];
  assume 0 <= I[iir#anon$8];
  assume I[iir#anon$8] <= R[iir#anon$8];
  assume R[iir#anon$8] <= C[iir#anon$8];
  assume 0 <= I[iir#anon$9];
  assume I[iir#anon$9] <= R[iir#anon$9];
  assume R[iir#anon$9] <= C[iir#anon$9];
  assume 0 <= I[iir#anon$10];
  assume I[iir#anon$10] <= R[iir#anon$10];
  assume R[iir#anon$10] <= C[iir#anon$10];
  assume 0 <= I[iir#anon$11];
  assume I[iir#anon$11] <= R[iir#anon$11];
  assume R[iir#anon$11] <= C[iir#anon$11];
  assume 0 <= I[iir#anon$12];
  assume I[iir#anon$12] <= R[iir#anon$12];
  assume R[iir#anon$12] <= C[iir#anon$12];
  assume 0 <= I[iir#anon$13];
  assume I[iir#anon$13] <= R[iir#anon$13];
  assume R[iir#anon$13] <= C[iir#anon$13];
  assume 0 <= I[iir#anon$14];
  assume I[iir#anon$14] <= R[iir#anon$14];
  assume R[iir#anon$14] <= C[iir#anon$14];
  assume 0 <= I[iir#anon$15];
  assume I[iir#anon$15] <= R[iir#anon$15];
  assume R[iir#anon$15] <= C[iir#anon$15];
  assume 0 <= I[iir#anon$16];
  assume I[iir#anon$16] <= R[iir#anon$16];
  assume R[iir#anon$16] <= C[iir#anon$16];
  assume 0 <= I[iir#anon$17];
  assume I[iir#anon$17] <= R[iir#anon$17];
  assume R[iir#anon$17] <= C[iir#anon$17];
  assume 0 <= I[iir#anon$18];
  assume I[iir#anon$18] <= R[iir#anon$18];
  assume R[iir#anon$18] <= C[iir#anon$18];
  assume 0 <= I[iir#anon$19];
  assume I[iir#anon$19] <= R[iir#anon$19];
  assume R[iir#anon$19] <= C[iir#anon$19];
  assume 0 <= I[iir#anon$20];
  assume I[iir#anon$20] <= R[iir#anon$20];
  assume R[iir#anon$20] <= C[iir#anon$20];
  assume 0 <= I[iir#anon$21];
  assume I[iir#anon$21] <= R[iir#anon$21];
  assume R[iir#anon$21] <= C[iir#anon$21];
  assume 0 <= I[iir#anon$22];
  assume I[iir#anon$22] <= R[iir#anon$22];
  assume R[iir#anon$22] <= C[iir#anon$22];
  assume 0 <= I[iir#anon$23];
  assume I[iir#anon$23] <= R[iir#anon$23];
  assume R[iir#anon$23] <= C[iir#anon$23];
  assume I[iir#anon$23] == R[iir#anon$23];
  assume I[iir#anon$17] == I[iir#anon$8];
  assume I[iir#anon$18] == I[iir#anon$11];
  assume I[iir#anon$19] == I[iir#anon$14];
  assume I[iir#anon$20] == I[iir#anon$16];
  assume I[iir#anon$21] == I[iir#anon$17];
  assume I[iir#anon$21] == I[iir#anon$18];
  assume I[iir#anon$22] == I[iir#anon$19];
  assume I[iir#anon$22] == I[iir#anon$20];
  assume I[iir#anon$23] == I[iir#anon$21];
  assume I[iir#anon$23] == I[iir#anon$22];
  assume I[iir#anon$8] == I[iir#anon$7];
  assume I[iir#anon$9] == I[iir#anon$7];
  assume I[iir#anon$11] == I[iir#anon$10];
  assume I[iir#anon$12] == I[iir#anon$10];
  assume I[iir#anon$14] == I[iir#anon$13];
  assume I[iir#anon$15] == I[iir#anon$13];
  assume (C[iir#anon$10] == 0) ==> (AV#delay_1#data == 0);
  assume (C[iir#anon$10] > 0) ==> (AV#delay_1#data == M[iir#anon$9][R[iir#anon$9] - 1]);
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$10] > 0) ==> (M[iir#anon$10][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$10] - 0)) ==> (M[iir#anon$10][idx] == M[iir#anon$9][idx - 1])
  );
  assume (C[iir#anon$13] == 0) ==> (AV#delay_2#data == 0);
  assume (C[iir#anon$13] > 0) ==> (AV#delay_2#data == M[iir#anon$12][R[iir#anon$12] - 1]);
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$13] > 0) ==> (M[iir#anon$13][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$13] - 0)) ==> (M[iir#anon$13][idx] == M[iir#anon$12][idx - 1])
  );
  assume (C[iir#anon$16] == 0) ==> (AV#delay_3#data == 0);
  assume (C[iir#anon$16] > 0) ==> (AV#delay_3#data == M[iir#anon$15][R[iir#anon$15] - 1]);
  assume R[iir#anon$15] == C[iir#anon$16];
  assume (C[iir#anon$16] > 0) ==> (M[iir#anon$16][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$16] - 0)) ==> (M[iir#anon$16][idx] == M[iir#anon$15][idx - 1])
  );
  assume R[iir#anon$8] == C[iir#anon$17];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$17]) ==> (M[iir#anon$17][idx$] == (37 * M[iir#anon$8][idx$]))
  );
  assume R[iir#anon$11] == C[iir#anon$18];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$18]) ==> (M[iir#anon$18][idx$] == (109 * M[iir#anon$11][idx$]))
  );
  assume R[iir#anon$14] == C[iir#anon$19];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$19]) ==> (M[iir#anon$19][idx$] == (109 * M[iir#anon$14][idx$]))
  );
  assume R[iir#anon$16] == C[iir#anon$20];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$20]) ==> (M[iir#anon$20][idx$] == (37 * M[iir#anon$16][idx$]))
  );
  assume R[iir#anon$17] == C[iir#anon$21];
  assume R[iir#anon$18] == C[iir#anon$21];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$21]) ==> (M[iir#anon$21][idx$] == (M[iir#anon$17][idx$] + M[iir#anon$18][idx$]))
  );
  assume R[iir#anon$19] == C[iir#anon$22];
  assume R[iir#anon$20] == C[iir#anon$22];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$22]) ==> (M[iir#anon$22][idx$] == (M[iir#anon$19][idx$] + M[iir#anon$20][idx$]))
  );
  assume R[iir#anon$21] == C[iir#anon$23];
  assume R[iir#anon$22] == C[iir#anon$23];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$23]) ==> (M[iir#anon$23][idx$] == (M[iir#anon$21][idx$] + M[iir#anon$22][idx$]))
  );
  assume R[iir#anon$7] == C[iir#anon$8];
  assume R[iir#anon$7] == C[iir#anon$9];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$8]) ==> (M[iir#anon$8][idx$] == M[iir#anon$7][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$9]) ==> (M[iir#anon$9][idx$] == M[iir#anon$7][idx$])
  );
  assume R[iir#anon$10] == C[iir#anon$11];
  assume R[iir#anon$10] == C[iir#anon$12];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$11]) ==> (M[iir#anon$11][idx$] == M[iir#anon$10][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$12]) ==> (M[iir#anon$12][idx$] == M[iir#anon$10][idx$])
  );
  assume R[iir#anon$13] == C[iir#anon$14];
  assume R[iir#anon$13] == C[iir#anon$15];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$14]) ==> (M[iir#anon$14][idx$] == M[iir#anon$13][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$15]) ==> (M[iir#anon$15][idx$] == M[iir#anon$13][idx$])
  );
  assume 1 <= (C[iir#anon$14] - R[iir#anon$14]);
  in#i := M[iir#anon$14][R[iir#anon$14]];
  R[iir#anon$14] := R[iir#anon$14] + 1;
  M[iir#anon$19][C[iir#anon$19]] := 109 * in#i;
  C[iir#anon$19] := C[iir#anon$19] + 1;
  assume (C[iir#anon$10] == 0) ==> (AV#delay_1#data == 0);
  assume (C[iir#anon$10] > 0) ==> (AV#delay_1#data == M[iir#anon$9][R[iir#anon$9] - 1]);
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$10] > 0) ==> (M[iir#anon$10][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$10] - 0)) ==> (M[iir#anon$10][idx] == M[iir#anon$9][idx - 1])
  );
  assume (C[iir#anon$13] == 0) ==> (AV#delay_2#data == 0);
  assume (C[iir#anon$13] > 0) ==> (AV#delay_2#data == M[iir#anon$12][R[iir#anon$12] - 1]);
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$13] > 0) ==> (M[iir#anon$13][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$13] - 0)) ==> (M[iir#anon$13][idx] == M[iir#anon$12][idx - 1])
  );
  assume (C[iir#anon$16] == 0) ==> (AV#delay_3#data == 0);
  assume (C[iir#anon$16] > 0) ==> (AV#delay_3#data == M[iir#anon$15][R[iir#anon$15] - 1]);
  assume R[iir#anon$15] == C[iir#anon$16];
  assume (C[iir#anon$16] > 0) ==> (M[iir#anon$16][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$16] - 0)) ==> (M[iir#anon$16][idx] == M[iir#anon$15][idx - 1])
  );
  assume R[iir#anon$8] == C[iir#anon$17];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$17]) ==> (M[iir#anon$17][idx$] == (37 * M[iir#anon$8][idx$]))
  );
  assume R[iir#anon$11] == C[iir#anon$18];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$18]) ==> (M[iir#anon$18][idx$] == (109 * M[iir#anon$11][idx$]))
  );
  assume R[iir#anon$14] == C[iir#anon$19];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$19]) ==> (M[iir#anon$19][idx$] == (109 * M[iir#anon$14][idx$]))
  );
  assume R[iir#anon$16] == C[iir#anon$20];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$20]) ==> (M[iir#anon$20][idx$] == (37 * M[iir#anon$16][idx$]))
  );
  assume R[iir#anon$17] == C[iir#anon$21];
  assume R[iir#anon$18] == C[iir#anon$21];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$21]) ==> (M[iir#anon$21][idx$] == (M[iir#anon$17][idx$] + M[iir#anon$18][idx$]))
  );
  assume R[iir#anon$19] == C[iir#anon$22];
  assume R[iir#anon$20] == C[iir#anon$22];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$22]) ==> (M[iir#anon$22][idx$] == (M[iir#anon$19][idx$] + M[iir#anon$20][idx$]))
  );
  assume R[iir#anon$21] == C[iir#anon$23];
  assume R[iir#anon$22] == C[iir#anon$23];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$23]) ==> (M[iir#anon$23][idx$] == (M[iir#anon$21][idx$] + M[iir#anon$22][idx$]))
  );
  assume R[iir#anon$7] == C[iir#anon$8];
  assume R[iir#anon$7] == C[iir#anon$9];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$8]) ==> (M[iir#anon$8][idx$] == M[iir#anon$7][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$9]) ==> (M[iir#anon$9][idx$] == M[iir#anon$7][idx$])
  );
  assume R[iir#anon$10] == C[iir#anon$11];
  assume R[iir#anon$10] == C[iir#anon$12];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$11]) ==> (M[iir#anon$11][idx$] == M[iir#anon$10][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$12]) ==> (M[iir#anon$12][idx$] == M[iir#anon$10][idx$])
  );
  assume R[iir#anon$13] == C[iir#anon$14];
  assume R[iir#anon$13] == C[iir#anon$15];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$14]) ==> (M[iir#anon$14][idx$] == M[iir#anon$13][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$15]) ==> (M[iir#anon$15][idx$] == M[iir#anon$13][idx$])
  );
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_3' might not preserve the channel invariant (#145)"} I[iir#anon$17] == I[iir#anon$8];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_3' might not preserve the channel invariant (#146)"} I[iir#anon$18] == I[iir#anon$11];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_3' might not preserve the channel invariant (#147)"} I[iir#anon$19] == I[iir#anon$14];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_3' might not preserve the channel invariant (#148)"} I[iir#anon$20] == I[iir#anon$16];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_3' might not preserve the channel invariant (#149)"} I[iir#anon$21] == I[iir#anon$17];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_3' might not preserve the channel invariant (#150)"} I[iir#anon$21] == I[iir#anon$18];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_3' might not preserve the channel invariant (#151)"} I[iir#anon$22] == I[iir#anon$19];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_3' might not preserve the channel invariant (#152)"} I[iir#anon$22] == I[iir#anon$20];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_3' might not preserve the channel invariant (#153)"} I[iir#anon$23] == I[iir#anon$21];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_3' might not preserve the channel invariant (#154)"} I[iir#anon$23] == I[iir#anon$22];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_3' might not preserve the channel invariant (#155)"} I[iir#anon$8] == I[iir#anon$7];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_3' might not preserve the channel invariant (#156)"} I[iir#anon$9] == I[iir#anon$7];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_3' might not preserve the channel invariant (#157)"} I[iir#anon$11] == I[iir#anon$10];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_3' might not preserve the channel invariant (#158)"} I[iir#anon$12] == I[iir#anon$10];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_3' might not preserve the channel invariant (#159)"} I[iir#anon$14] == I[iir#anon$13];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_3' might not preserve the channel invariant (#160)"} I[iir#anon$15] == I[iir#anon$13];
}
procedure iir##mulc#anon$3#17()
  modifies C, R, M, I, H;
{
  var iir#delay_1: Actor;
  var iir#delay_2: Actor;
  var iir#delay_3: Actor;
  var iir#mul_1: Actor;
  var iir#mul_2: Actor;
  var iir#mul_3: Actor;
  var iir#mul_4: Actor;
  var iir#add_1: Actor;
  var iir#add_2: Actor;
  var iir#add_3: Actor;
  var iir#spl_1: Actor;
  var iir#spl_2: Actor;
  var iir#spl_3: Actor;
  var iir#anon$7: Chan (int);
  var iir#anon$8: Chan (int);
  var iir#anon$9: Chan (int);
  var iir#anon$10: Chan (int);
  var iir#anon$11: Chan (int);
  var iir#anon$12: Chan (int);
  var iir#anon$13: Chan (int);
  var iir#anon$14: Chan (int);
  var iir#anon$15: Chan (int);
  var iir#anon$16: Chan (int);
  var iir#anon$17: Chan (int);
  var iir#anon$18: Chan (int);
  var iir#anon$19: Chan (int);
  var iir#anon$20: Chan (int);
  var iir#anon$21: Chan (int);
  var iir#anon$22: Chan (int);
  var iir#anon$23: Chan (int);
  var AV#delay_1#data: int;
  var AV#delay_1#y: int;
  var AV#delay_2#data: int;
  var AV#delay_2#y: int;
  var AV#delay_3#data: int;
  var AV#delay_3#y: int;
  var in#i: int;
  assume (iir#delay_1 != iir#delay_2) && (iir#delay_1 != iir#delay_3) && (iir#delay_1 != iir#mul_1) && (iir#delay_1 != iir#mul_2) && (iir#delay_1 != iir#mul_3) && (iir#delay_1 != iir#mul_4) && (iir#delay_1 != iir#add_1) && (iir#delay_1 != iir#add_2) && (iir#delay_1 != iir#add_3) && (iir#delay_1 != iir#spl_1) && (iir#delay_1 != iir#spl_2) && (iir#delay_1 != iir#spl_3) && (iir#delay_2 != iir#delay_3) && (iir#delay_2 != iir#mul_1) && (iir#delay_2 != iir#mul_2) && (iir#delay_2 != iir#mul_3) && (iir#delay_2 != iir#mul_4) && (iir#delay_2 != iir#add_1) && (iir#delay_2 != iir#add_2) && (iir#delay_2 != iir#add_3) && (iir#delay_2 != iir#spl_1) && (iir#delay_2 != iir#spl_2) && (iir#delay_2 != iir#spl_3) && (iir#delay_3 != iir#mul_1) && (iir#delay_3 != iir#mul_2) && (iir#delay_3 != iir#mul_3) && (iir#delay_3 != iir#mul_4) && (iir#delay_3 != iir#add_1) && (iir#delay_3 != iir#add_2) && (iir#delay_3 != iir#add_3) && (iir#delay_3 != iir#spl_1) && (iir#delay_3 != iir#spl_2) && (iir#delay_3 != iir#spl_3) && (iir#mul_1 != iir#mul_2) && (iir#mul_1 != iir#mul_3) && (iir#mul_1 != iir#mul_4) && (iir#mul_1 != iir#add_1) && (iir#mul_1 != iir#add_2) && (iir#mul_1 != iir#add_3) && (iir#mul_1 != iir#spl_1) && (iir#mul_1 != iir#spl_2) && (iir#mul_1 != iir#spl_3) && (iir#mul_2 != iir#mul_3) && (iir#mul_2 != iir#mul_4) && (iir#mul_2 != iir#add_1) && (iir#mul_2 != iir#add_2) && (iir#mul_2 != iir#add_3) && (iir#mul_2 != iir#spl_1) && (iir#mul_2 != iir#spl_2) && (iir#mul_2 != iir#spl_3) && (iir#mul_3 != iir#mul_4) && (iir#mul_3 != iir#add_1) && (iir#mul_3 != iir#add_2) && (iir#mul_3 != iir#add_3) && (iir#mul_3 != iir#spl_1) && (iir#mul_3 != iir#spl_2) && (iir#mul_3 != iir#spl_3) && (iir#mul_4 != iir#add_1) && (iir#mul_4 != iir#add_2) && (iir#mul_4 != iir#add_3) && (iir#mul_4 != iir#spl_1) && (iir#mul_4 != iir#spl_2) && (iir#mul_4 != iir#spl_3) && (iir#add_1 != iir#add_2) && (iir#add_1 != iir#add_3) && (iir#add_1 != iir#spl_1) && (iir#add_1 != iir#spl_2) && (iir#add_1 != iir#spl_3) && (iir#add_2 != iir#add_3) && (iir#add_2 != iir#spl_1) && (iir#add_2 != iir#spl_2) && (iir#add_2 != iir#spl_3) && (iir#add_3 != iir#spl_1) && (iir#add_3 != iir#spl_2) && (iir#add_3 != iir#spl_3) && (iir#spl_1 != iir#spl_2) && (iir#spl_1 != iir#spl_3) && (iir#spl_2 != iir#spl_3);
  assume (iir#anon$7 != iir#anon$8) && (iir#anon$7 != iir#anon$9) && (iir#anon$7 != iir#anon$10) && (iir#anon$7 != iir#anon$11) && (iir#anon$7 != iir#anon$12) && (iir#anon$7 != iir#anon$13) && (iir#anon$7 != iir#anon$14) && (iir#anon$7 != iir#anon$15) && (iir#anon$7 != iir#anon$16) && (iir#anon$7 != iir#anon$17) && (iir#anon$7 != iir#anon$18) && (iir#anon$7 != iir#anon$19) && (iir#anon$7 != iir#anon$20) && (iir#anon$7 != iir#anon$21) && (iir#anon$7 != iir#anon$22) && (iir#anon$7 != iir#anon$23) && (iir#anon$8 != iir#anon$9) && (iir#anon$8 != iir#anon$10) && (iir#anon$8 != iir#anon$11) && (iir#anon$8 != iir#anon$12) && (iir#anon$8 != iir#anon$13) && (iir#anon$8 != iir#anon$14) && (iir#anon$8 != iir#anon$15) && (iir#anon$8 != iir#anon$16) && (iir#anon$8 != iir#anon$17) && (iir#anon$8 != iir#anon$18) && (iir#anon$8 != iir#anon$19) && (iir#anon$8 != iir#anon$20) && (iir#anon$8 != iir#anon$21) && (iir#anon$8 != iir#anon$22) && (iir#anon$8 != iir#anon$23) && (iir#anon$9 != iir#anon$10) && (iir#anon$9 != iir#anon$11) && (iir#anon$9 != iir#anon$12) && (iir#anon$9 != iir#anon$13) && (iir#anon$9 != iir#anon$14) && (iir#anon$9 != iir#anon$15) && (iir#anon$9 != iir#anon$16) && (iir#anon$9 != iir#anon$17) && (iir#anon$9 != iir#anon$18) && (iir#anon$9 != iir#anon$19) && (iir#anon$9 != iir#anon$20) && (iir#anon$9 != iir#anon$21) && (iir#anon$9 != iir#anon$22) && (iir#anon$9 != iir#anon$23) && (iir#anon$10 != iir#anon$11) && (iir#anon$10 != iir#anon$12) && (iir#anon$10 != iir#anon$13) && (iir#anon$10 != iir#anon$14) && (iir#anon$10 != iir#anon$15) && (iir#anon$10 != iir#anon$16) && (iir#anon$10 != iir#anon$17) && (iir#anon$10 != iir#anon$18) && (iir#anon$10 != iir#anon$19) && (iir#anon$10 != iir#anon$20) && (iir#anon$10 != iir#anon$21) && (iir#anon$10 != iir#anon$22) && (iir#anon$10 != iir#anon$23) && (iir#anon$11 != iir#anon$12) && (iir#anon$11 != iir#anon$13) && (iir#anon$11 != iir#anon$14) && (iir#anon$11 != iir#anon$15) && (iir#anon$11 != iir#anon$16) && (iir#anon$11 != iir#anon$17) && (iir#anon$11 != iir#anon$18) && (iir#anon$11 != iir#anon$19) && (iir#anon$11 != iir#anon$20) && (iir#anon$11 != iir#anon$21) && (iir#anon$11 != iir#anon$22) && (iir#anon$11 != iir#anon$23) && (iir#anon$12 != iir#anon$13) && (iir#anon$12 != iir#anon$14) && (iir#anon$12 != iir#anon$15) && (iir#anon$12 != iir#anon$16) && (iir#anon$12 != iir#anon$17) && (iir#anon$12 != iir#anon$18) && (iir#anon$12 != iir#anon$19) && (iir#anon$12 != iir#anon$20) && (iir#anon$12 != iir#anon$21) && (iir#anon$12 != iir#anon$22) && (iir#anon$12 != iir#anon$23) && (iir#anon$13 != iir#anon$14) && (iir#anon$13 != iir#anon$15) && (iir#anon$13 != iir#anon$16) && (iir#anon$13 != iir#anon$17) && (iir#anon$13 != iir#anon$18) && (iir#anon$13 != iir#anon$19) && (iir#anon$13 != iir#anon$20) && (iir#anon$13 != iir#anon$21) && (iir#anon$13 != iir#anon$22) && (iir#anon$13 != iir#anon$23) && (iir#anon$14 != iir#anon$15) && (iir#anon$14 != iir#anon$16) && (iir#anon$14 != iir#anon$17) && (iir#anon$14 != iir#anon$18) && (iir#anon$14 != iir#anon$19) && (iir#anon$14 != iir#anon$20) && (iir#anon$14 != iir#anon$21) && (iir#anon$14 != iir#anon$22) && (iir#anon$14 != iir#anon$23) && (iir#anon$15 != iir#anon$16) && (iir#anon$15 != iir#anon$17) && (iir#anon$15 != iir#anon$18) && (iir#anon$15 != iir#anon$19) && (iir#anon$15 != iir#anon$20) && (iir#anon$15 != iir#anon$21) && (iir#anon$15 != iir#anon$22) && (iir#anon$15 != iir#anon$23) && (iir#anon$16 != iir#anon$17) && (iir#anon$16 != iir#anon$18) && (iir#anon$16 != iir#anon$19) && (iir#anon$16 != iir#anon$20) && (iir#anon$16 != iir#anon$21) && (iir#anon$16 != iir#anon$22) && (iir#anon$16 != iir#anon$23) && (iir#anon$17 != iir#anon$18) && (iir#anon$17 != iir#anon$19) && (iir#anon$17 != iir#anon$20) && (iir#anon$17 != iir#anon$21) && (iir#anon$17 != iir#anon$22) && (iir#anon$17 != iir#anon$23) && (iir#anon$18 != iir#anon$19) && (iir#anon$18 != iir#anon$20) && (iir#anon$18 != iir#anon$21) && (iir#anon$18 != iir#anon$22) && (iir#anon$18 != iir#anon$23) && (iir#anon$19 != iir#anon$20) && (iir#anon$19 != iir#anon$21) && (iir#anon$19 != iir#anon$22) && (iir#anon$19 != iir#anon$23) && (iir#anon$20 != iir#anon$21) && (iir#anon$20 != iir#anon$22) && (iir#anon$20 != iir#anon$23) && (iir#anon$21 != iir#anon$22) && (iir#anon$21 != iir#anon$23) && (iir#anon$22 != iir#anon$23);
  assume 0 <= I[iir#anon$7];
  assume I[iir#anon$7] <= R[iir#anon$7];
  assume R[iir#anon$7] <= C[iir#anon$7];
  assume 0 <= I[iir#anon$8];
  assume I[iir#anon$8] <= R[iir#anon$8];
  assume R[iir#anon$8] <= C[iir#anon$8];
  assume 0 <= I[iir#anon$9];
  assume I[iir#anon$9] <= R[iir#anon$9];
  assume R[iir#anon$9] <= C[iir#anon$9];
  assume 0 <= I[iir#anon$10];
  assume I[iir#anon$10] <= R[iir#anon$10];
  assume R[iir#anon$10] <= C[iir#anon$10];
  assume 0 <= I[iir#anon$11];
  assume I[iir#anon$11] <= R[iir#anon$11];
  assume R[iir#anon$11] <= C[iir#anon$11];
  assume 0 <= I[iir#anon$12];
  assume I[iir#anon$12] <= R[iir#anon$12];
  assume R[iir#anon$12] <= C[iir#anon$12];
  assume 0 <= I[iir#anon$13];
  assume I[iir#anon$13] <= R[iir#anon$13];
  assume R[iir#anon$13] <= C[iir#anon$13];
  assume 0 <= I[iir#anon$14];
  assume I[iir#anon$14] <= R[iir#anon$14];
  assume R[iir#anon$14] <= C[iir#anon$14];
  assume 0 <= I[iir#anon$15];
  assume I[iir#anon$15] <= R[iir#anon$15];
  assume R[iir#anon$15] <= C[iir#anon$15];
  assume 0 <= I[iir#anon$16];
  assume I[iir#anon$16] <= R[iir#anon$16];
  assume R[iir#anon$16] <= C[iir#anon$16];
  assume 0 <= I[iir#anon$17];
  assume I[iir#anon$17] <= R[iir#anon$17];
  assume R[iir#anon$17] <= C[iir#anon$17];
  assume 0 <= I[iir#anon$18];
  assume I[iir#anon$18] <= R[iir#anon$18];
  assume R[iir#anon$18] <= C[iir#anon$18];
  assume 0 <= I[iir#anon$19];
  assume I[iir#anon$19] <= R[iir#anon$19];
  assume R[iir#anon$19] <= C[iir#anon$19];
  assume 0 <= I[iir#anon$20];
  assume I[iir#anon$20] <= R[iir#anon$20];
  assume R[iir#anon$20] <= C[iir#anon$20];
  assume 0 <= I[iir#anon$21];
  assume I[iir#anon$21] <= R[iir#anon$21];
  assume R[iir#anon$21] <= C[iir#anon$21];
  assume 0 <= I[iir#anon$22];
  assume I[iir#anon$22] <= R[iir#anon$22];
  assume R[iir#anon$22] <= C[iir#anon$22];
  assume 0 <= I[iir#anon$23];
  assume I[iir#anon$23] <= R[iir#anon$23];
  assume R[iir#anon$23] <= C[iir#anon$23];
  assume I[iir#anon$23] == R[iir#anon$23];
  assume I[iir#anon$17] == I[iir#anon$8];
  assume I[iir#anon$18] == I[iir#anon$11];
  assume I[iir#anon$19] == I[iir#anon$14];
  assume I[iir#anon$20] == I[iir#anon$16];
  assume I[iir#anon$21] == I[iir#anon$17];
  assume I[iir#anon$21] == I[iir#anon$18];
  assume I[iir#anon$22] == I[iir#anon$19];
  assume I[iir#anon$22] == I[iir#anon$20];
  assume I[iir#anon$23] == I[iir#anon$21];
  assume I[iir#anon$23] == I[iir#anon$22];
  assume I[iir#anon$8] == I[iir#anon$7];
  assume I[iir#anon$9] == I[iir#anon$7];
  assume I[iir#anon$11] == I[iir#anon$10];
  assume I[iir#anon$12] == I[iir#anon$10];
  assume I[iir#anon$14] == I[iir#anon$13];
  assume I[iir#anon$15] == I[iir#anon$13];
  assume (C[iir#anon$10] == 0) ==> (AV#delay_1#data == 0);
  assume (C[iir#anon$10] > 0) ==> (AV#delay_1#data == M[iir#anon$9][R[iir#anon$9] - 1]);
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$10] > 0) ==> (M[iir#anon$10][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$10] - 0)) ==> (M[iir#anon$10][idx] == M[iir#anon$9][idx - 1])
  );
  assume (C[iir#anon$13] == 0) ==> (AV#delay_2#data == 0);
  assume (C[iir#anon$13] > 0) ==> (AV#delay_2#data == M[iir#anon$12][R[iir#anon$12] - 1]);
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$13] > 0) ==> (M[iir#anon$13][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$13] - 0)) ==> (M[iir#anon$13][idx] == M[iir#anon$12][idx - 1])
  );
  assume (C[iir#anon$16] == 0) ==> (AV#delay_3#data == 0);
  assume (C[iir#anon$16] > 0) ==> (AV#delay_3#data == M[iir#anon$15][R[iir#anon$15] - 1]);
  assume R[iir#anon$15] == C[iir#anon$16];
  assume (C[iir#anon$16] > 0) ==> (M[iir#anon$16][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$16] - 0)) ==> (M[iir#anon$16][idx] == M[iir#anon$15][idx - 1])
  );
  assume R[iir#anon$8] == C[iir#anon$17];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$17]) ==> (M[iir#anon$17][idx$] == (37 * M[iir#anon$8][idx$]))
  );
  assume R[iir#anon$11] == C[iir#anon$18];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$18]) ==> (M[iir#anon$18][idx$] == (109 * M[iir#anon$11][idx$]))
  );
  assume R[iir#anon$14] == C[iir#anon$19];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$19]) ==> (M[iir#anon$19][idx$] == (109 * M[iir#anon$14][idx$]))
  );
  assume R[iir#anon$16] == C[iir#anon$20];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$20]) ==> (M[iir#anon$20][idx$] == (37 * M[iir#anon$16][idx$]))
  );
  assume R[iir#anon$17] == C[iir#anon$21];
  assume R[iir#anon$18] == C[iir#anon$21];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$21]) ==> (M[iir#anon$21][idx$] == (M[iir#anon$17][idx$] + M[iir#anon$18][idx$]))
  );
  assume R[iir#anon$19] == C[iir#anon$22];
  assume R[iir#anon$20] == C[iir#anon$22];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$22]) ==> (M[iir#anon$22][idx$] == (M[iir#anon$19][idx$] + M[iir#anon$20][idx$]))
  );
  assume R[iir#anon$21] == C[iir#anon$23];
  assume R[iir#anon$22] == C[iir#anon$23];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$23]) ==> (M[iir#anon$23][idx$] == (M[iir#anon$21][idx$] + M[iir#anon$22][idx$]))
  );
  assume R[iir#anon$7] == C[iir#anon$8];
  assume R[iir#anon$7] == C[iir#anon$9];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$8]) ==> (M[iir#anon$8][idx$] == M[iir#anon$7][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$9]) ==> (M[iir#anon$9][idx$] == M[iir#anon$7][idx$])
  );
  assume R[iir#anon$10] == C[iir#anon$11];
  assume R[iir#anon$10] == C[iir#anon$12];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$11]) ==> (M[iir#anon$11][idx$] == M[iir#anon$10][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$12]) ==> (M[iir#anon$12][idx$] == M[iir#anon$10][idx$])
  );
  assume R[iir#anon$13] == C[iir#anon$14];
  assume R[iir#anon$13] == C[iir#anon$15];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$14]) ==> (M[iir#anon$14][idx$] == M[iir#anon$13][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$15]) ==> (M[iir#anon$15][idx$] == M[iir#anon$13][idx$])
  );
  assume 1 <= (C[iir#anon$16] - R[iir#anon$16]);
  in#i := M[iir#anon$16][R[iir#anon$16]];
  R[iir#anon$16] := R[iir#anon$16] + 1;
  M[iir#anon$20][C[iir#anon$20]] := 37 * in#i;
  C[iir#anon$20] := C[iir#anon$20] + 1;
  assume (C[iir#anon$10] == 0) ==> (AV#delay_1#data == 0);
  assume (C[iir#anon$10] > 0) ==> (AV#delay_1#data == M[iir#anon$9][R[iir#anon$9] - 1]);
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$10] > 0) ==> (M[iir#anon$10][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$10] - 0)) ==> (M[iir#anon$10][idx] == M[iir#anon$9][idx - 1])
  );
  assume (C[iir#anon$13] == 0) ==> (AV#delay_2#data == 0);
  assume (C[iir#anon$13] > 0) ==> (AV#delay_2#data == M[iir#anon$12][R[iir#anon$12] - 1]);
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$13] > 0) ==> (M[iir#anon$13][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$13] - 0)) ==> (M[iir#anon$13][idx] == M[iir#anon$12][idx - 1])
  );
  assume (C[iir#anon$16] == 0) ==> (AV#delay_3#data == 0);
  assume (C[iir#anon$16] > 0) ==> (AV#delay_3#data == M[iir#anon$15][R[iir#anon$15] - 1]);
  assume R[iir#anon$15] == C[iir#anon$16];
  assume (C[iir#anon$16] > 0) ==> (M[iir#anon$16][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$16] - 0)) ==> (M[iir#anon$16][idx] == M[iir#anon$15][idx - 1])
  );
  assume R[iir#anon$8] == C[iir#anon$17];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$17]) ==> (M[iir#anon$17][idx$] == (37 * M[iir#anon$8][idx$]))
  );
  assume R[iir#anon$11] == C[iir#anon$18];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$18]) ==> (M[iir#anon$18][idx$] == (109 * M[iir#anon$11][idx$]))
  );
  assume R[iir#anon$14] == C[iir#anon$19];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$19]) ==> (M[iir#anon$19][idx$] == (109 * M[iir#anon$14][idx$]))
  );
  assume R[iir#anon$16] == C[iir#anon$20];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$20]) ==> (M[iir#anon$20][idx$] == (37 * M[iir#anon$16][idx$]))
  );
  assume R[iir#anon$17] == C[iir#anon$21];
  assume R[iir#anon$18] == C[iir#anon$21];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$21]) ==> (M[iir#anon$21][idx$] == (M[iir#anon$17][idx$] + M[iir#anon$18][idx$]))
  );
  assume R[iir#anon$19] == C[iir#anon$22];
  assume R[iir#anon$20] == C[iir#anon$22];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$22]) ==> (M[iir#anon$22][idx$] == (M[iir#anon$19][idx$] + M[iir#anon$20][idx$]))
  );
  assume R[iir#anon$21] == C[iir#anon$23];
  assume R[iir#anon$22] == C[iir#anon$23];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$23]) ==> (M[iir#anon$23][idx$] == (M[iir#anon$21][idx$] + M[iir#anon$22][idx$]))
  );
  assume R[iir#anon$7] == C[iir#anon$8];
  assume R[iir#anon$7] == C[iir#anon$9];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$8]) ==> (M[iir#anon$8][idx$] == M[iir#anon$7][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$9]) ==> (M[iir#anon$9][idx$] == M[iir#anon$7][idx$])
  );
  assume R[iir#anon$10] == C[iir#anon$11];
  assume R[iir#anon$10] == C[iir#anon$12];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$11]) ==> (M[iir#anon$11][idx$] == M[iir#anon$10][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$12]) ==> (M[iir#anon$12][idx$] == M[iir#anon$10][idx$])
  );
  assume R[iir#anon$13] == C[iir#anon$14];
  assume R[iir#anon$13] == C[iir#anon$15];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$14]) ==> (M[iir#anon$14][idx$] == M[iir#anon$13][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$15]) ==> (M[iir#anon$15][idx$] == M[iir#anon$13][idx$])
  );
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_4' might not preserve the channel invariant (#161)"} I[iir#anon$17] == I[iir#anon$8];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_4' might not preserve the channel invariant (#162)"} I[iir#anon$18] == I[iir#anon$11];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_4' might not preserve the channel invariant (#163)"} I[iir#anon$19] == I[iir#anon$14];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_4' might not preserve the channel invariant (#164)"} I[iir#anon$20] == I[iir#anon$16];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_4' might not preserve the channel invariant (#165)"} I[iir#anon$21] == I[iir#anon$17];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_4' might not preserve the channel invariant (#166)"} I[iir#anon$21] == I[iir#anon$18];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_4' might not preserve the channel invariant (#167)"} I[iir#anon$22] == I[iir#anon$19];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_4' might not preserve the channel invariant (#168)"} I[iir#anon$22] == I[iir#anon$20];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_4' might not preserve the channel invariant (#169)"} I[iir#anon$23] == I[iir#anon$21];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_4' might not preserve the channel invariant (#170)"} I[iir#anon$23] == I[iir#anon$22];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_4' might not preserve the channel invariant (#171)"} I[iir#anon$8] == I[iir#anon$7];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_4' might not preserve the channel invariant (#172)"} I[iir#anon$9] == I[iir#anon$7];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_4' might not preserve the channel invariant (#173)"} I[iir#anon$11] == I[iir#anon$10];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_4' might not preserve the channel invariant (#174)"} I[iir#anon$12] == I[iir#anon$10];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_4' might not preserve the channel invariant (#175)"} I[iir#anon$14] == I[iir#anon$13];
  assert {:msg "Action at 24.3 ('anon$3') for actor instance 'mul_4' might not preserve the channel invariant (#176)"} I[iir#anon$15] == I[iir#anon$13];
}
procedure iir##add#anon$0#18()
  modifies C, R, M, I, H;
{
  var iir#delay_1: Actor;
  var iir#delay_2: Actor;
  var iir#delay_3: Actor;
  var iir#mul_1: Actor;
  var iir#mul_2: Actor;
  var iir#mul_3: Actor;
  var iir#mul_4: Actor;
  var iir#add_1: Actor;
  var iir#add_2: Actor;
  var iir#add_3: Actor;
  var iir#spl_1: Actor;
  var iir#spl_2: Actor;
  var iir#spl_3: Actor;
  var iir#anon$7: Chan (int);
  var iir#anon$8: Chan (int);
  var iir#anon$9: Chan (int);
  var iir#anon$10: Chan (int);
  var iir#anon$11: Chan (int);
  var iir#anon$12: Chan (int);
  var iir#anon$13: Chan (int);
  var iir#anon$14: Chan (int);
  var iir#anon$15: Chan (int);
  var iir#anon$16: Chan (int);
  var iir#anon$17: Chan (int);
  var iir#anon$18: Chan (int);
  var iir#anon$19: Chan (int);
  var iir#anon$20: Chan (int);
  var iir#anon$21: Chan (int);
  var iir#anon$22: Chan (int);
  var iir#anon$23: Chan (int);
  var AV#delay_1#data: int;
  var AV#delay_1#y: int;
  var AV#delay_2#data: int;
  var AV#delay_2#y: int;
  var AV#delay_3#data: int;
  var AV#delay_3#y: int;
  var in1#i: int;
  var in2#j: int;
  assume (iir#delay_1 != iir#delay_2) && (iir#delay_1 != iir#delay_3) && (iir#delay_1 != iir#mul_1) && (iir#delay_1 != iir#mul_2) && (iir#delay_1 != iir#mul_3) && (iir#delay_1 != iir#mul_4) && (iir#delay_1 != iir#add_1) && (iir#delay_1 != iir#add_2) && (iir#delay_1 != iir#add_3) && (iir#delay_1 != iir#spl_1) && (iir#delay_1 != iir#spl_2) && (iir#delay_1 != iir#spl_3) && (iir#delay_2 != iir#delay_3) && (iir#delay_2 != iir#mul_1) && (iir#delay_2 != iir#mul_2) && (iir#delay_2 != iir#mul_3) && (iir#delay_2 != iir#mul_4) && (iir#delay_2 != iir#add_1) && (iir#delay_2 != iir#add_2) && (iir#delay_2 != iir#add_3) && (iir#delay_2 != iir#spl_1) && (iir#delay_2 != iir#spl_2) && (iir#delay_2 != iir#spl_3) && (iir#delay_3 != iir#mul_1) && (iir#delay_3 != iir#mul_2) && (iir#delay_3 != iir#mul_3) && (iir#delay_3 != iir#mul_4) && (iir#delay_3 != iir#add_1) && (iir#delay_3 != iir#add_2) && (iir#delay_3 != iir#add_3) && (iir#delay_3 != iir#spl_1) && (iir#delay_3 != iir#spl_2) && (iir#delay_3 != iir#spl_3) && (iir#mul_1 != iir#mul_2) && (iir#mul_1 != iir#mul_3) && (iir#mul_1 != iir#mul_4) && (iir#mul_1 != iir#add_1) && (iir#mul_1 != iir#add_2) && (iir#mul_1 != iir#add_3) && (iir#mul_1 != iir#spl_1) && (iir#mul_1 != iir#spl_2) && (iir#mul_1 != iir#spl_3) && (iir#mul_2 != iir#mul_3) && (iir#mul_2 != iir#mul_4) && (iir#mul_2 != iir#add_1) && (iir#mul_2 != iir#add_2) && (iir#mul_2 != iir#add_3) && (iir#mul_2 != iir#spl_1) && (iir#mul_2 != iir#spl_2) && (iir#mul_2 != iir#spl_3) && (iir#mul_3 != iir#mul_4) && (iir#mul_3 != iir#add_1) && (iir#mul_3 != iir#add_2) && (iir#mul_3 != iir#add_3) && (iir#mul_3 != iir#spl_1) && (iir#mul_3 != iir#spl_2) && (iir#mul_3 != iir#spl_3) && (iir#mul_4 != iir#add_1) && (iir#mul_4 != iir#add_2) && (iir#mul_4 != iir#add_3) && (iir#mul_4 != iir#spl_1) && (iir#mul_4 != iir#spl_2) && (iir#mul_4 != iir#spl_3) && (iir#add_1 != iir#add_2) && (iir#add_1 != iir#add_3) && (iir#add_1 != iir#spl_1) && (iir#add_1 != iir#spl_2) && (iir#add_1 != iir#spl_3) && (iir#add_2 != iir#add_3) && (iir#add_2 != iir#spl_1) && (iir#add_2 != iir#spl_2) && (iir#add_2 != iir#spl_3) && (iir#add_3 != iir#spl_1) && (iir#add_3 != iir#spl_2) && (iir#add_3 != iir#spl_3) && (iir#spl_1 != iir#spl_2) && (iir#spl_1 != iir#spl_3) && (iir#spl_2 != iir#spl_3);
  assume (iir#anon$7 != iir#anon$8) && (iir#anon$7 != iir#anon$9) && (iir#anon$7 != iir#anon$10) && (iir#anon$7 != iir#anon$11) && (iir#anon$7 != iir#anon$12) && (iir#anon$7 != iir#anon$13) && (iir#anon$7 != iir#anon$14) && (iir#anon$7 != iir#anon$15) && (iir#anon$7 != iir#anon$16) && (iir#anon$7 != iir#anon$17) && (iir#anon$7 != iir#anon$18) && (iir#anon$7 != iir#anon$19) && (iir#anon$7 != iir#anon$20) && (iir#anon$7 != iir#anon$21) && (iir#anon$7 != iir#anon$22) && (iir#anon$7 != iir#anon$23) && (iir#anon$8 != iir#anon$9) && (iir#anon$8 != iir#anon$10) && (iir#anon$8 != iir#anon$11) && (iir#anon$8 != iir#anon$12) && (iir#anon$8 != iir#anon$13) && (iir#anon$8 != iir#anon$14) && (iir#anon$8 != iir#anon$15) && (iir#anon$8 != iir#anon$16) && (iir#anon$8 != iir#anon$17) && (iir#anon$8 != iir#anon$18) && (iir#anon$8 != iir#anon$19) && (iir#anon$8 != iir#anon$20) && (iir#anon$8 != iir#anon$21) && (iir#anon$8 != iir#anon$22) && (iir#anon$8 != iir#anon$23) && (iir#anon$9 != iir#anon$10) && (iir#anon$9 != iir#anon$11) && (iir#anon$9 != iir#anon$12) && (iir#anon$9 != iir#anon$13) && (iir#anon$9 != iir#anon$14) && (iir#anon$9 != iir#anon$15) && (iir#anon$9 != iir#anon$16) && (iir#anon$9 != iir#anon$17) && (iir#anon$9 != iir#anon$18) && (iir#anon$9 != iir#anon$19) && (iir#anon$9 != iir#anon$20) && (iir#anon$9 != iir#anon$21) && (iir#anon$9 != iir#anon$22) && (iir#anon$9 != iir#anon$23) && (iir#anon$10 != iir#anon$11) && (iir#anon$10 != iir#anon$12) && (iir#anon$10 != iir#anon$13) && (iir#anon$10 != iir#anon$14) && (iir#anon$10 != iir#anon$15) && (iir#anon$10 != iir#anon$16) && (iir#anon$10 != iir#anon$17) && (iir#anon$10 != iir#anon$18) && (iir#anon$10 != iir#anon$19) && (iir#anon$10 != iir#anon$20) && (iir#anon$10 != iir#anon$21) && (iir#anon$10 != iir#anon$22) && (iir#anon$10 != iir#anon$23) && (iir#anon$11 != iir#anon$12) && (iir#anon$11 != iir#anon$13) && (iir#anon$11 != iir#anon$14) && (iir#anon$11 != iir#anon$15) && (iir#anon$11 != iir#anon$16) && (iir#anon$11 != iir#anon$17) && (iir#anon$11 != iir#anon$18) && (iir#anon$11 != iir#anon$19) && (iir#anon$11 != iir#anon$20) && (iir#anon$11 != iir#anon$21) && (iir#anon$11 != iir#anon$22) && (iir#anon$11 != iir#anon$23) && (iir#anon$12 != iir#anon$13) && (iir#anon$12 != iir#anon$14) && (iir#anon$12 != iir#anon$15) && (iir#anon$12 != iir#anon$16) && (iir#anon$12 != iir#anon$17) && (iir#anon$12 != iir#anon$18) && (iir#anon$12 != iir#anon$19) && (iir#anon$12 != iir#anon$20) && (iir#anon$12 != iir#anon$21) && (iir#anon$12 != iir#anon$22) && (iir#anon$12 != iir#anon$23) && (iir#anon$13 != iir#anon$14) && (iir#anon$13 != iir#anon$15) && (iir#anon$13 != iir#anon$16) && (iir#anon$13 != iir#anon$17) && (iir#anon$13 != iir#anon$18) && (iir#anon$13 != iir#anon$19) && (iir#anon$13 != iir#anon$20) && (iir#anon$13 != iir#anon$21) && (iir#anon$13 != iir#anon$22) && (iir#anon$13 != iir#anon$23) && (iir#anon$14 != iir#anon$15) && (iir#anon$14 != iir#anon$16) && (iir#anon$14 != iir#anon$17) && (iir#anon$14 != iir#anon$18) && (iir#anon$14 != iir#anon$19) && (iir#anon$14 != iir#anon$20) && (iir#anon$14 != iir#anon$21) && (iir#anon$14 != iir#anon$22) && (iir#anon$14 != iir#anon$23) && (iir#anon$15 != iir#anon$16) && (iir#anon$15 != iir#anon$17) && (iir#anon$15 != iir#anon$18) && (iir#anon$15 != iir#anon$19) && (iir#anon$15 != iir#anon$20) && (iir#anon$15 != iir#anon$21) && (iir#anon$15 != iir#anon$22) && (iir#anon$15 != iir#anon$23) && (iir#anon$16 != iir#anon$17) && (iir#anon$16 != iir#anon$18) && (iir#anon$16 != iir#anon$19) && (iir#anon$16 != iir#anon$20) && (iir#anon$16 != iir#anon$21) && (iir#anon$16 != iir#anon$22) && (iir#anon$16 != iir#anon$23) && (iir#anon$17 != iir#anon$18) && (iir#anon$17 != iir#anon$19) && (iir#anon$17 != iir#anon$20) && (iir#anon$17 != iir#anon$21) && (iir#anon$17 != iir#anon$22) && (iir#anon$17 != iir#anon$23) && (iir#anon$18 != iir#anon$19) && (iir#anon$18 != iir#anon$20) && (iir#anon$18 != iir#anon$21) && (iir#anon$18 != iir#anon$22) && (iir#anon$18 != iir#anon$23) && (iir#anon$19 != iir#anon$20) && (iir#anon$19 != iir#anon$21) && (iir#anon$19 != iir#anon$22) && (iir#anon$19 != iir#anon$23) && (iir#anon$20 != iir#anon$21) && (iir#anon$20 != iir#anon$22) && (iir#anon$20 != iir#anon$23) && (iir#anon$21 != iir#anon$22) && (iir#anon$21 != iir#anon$23) && (iir#anon$22 != iir#anon$23);
  assume 0 <= I[iir#anon$7];
  assume I[iir#anon$7] <= R[iir#anon$7];
  assume R[iir#anon$7] <= C[iir#anon$7];
  assume 0 <= I[iir#anon$8];
  assume I[iir#anon$8] <= R[iir#anon$8];
  assume R[iir#anon$8] <= C[iir#anon$8];
  assume 0 <= I[iir#anon$9];
  assume I[iir#anon$9] <= R[iir#anon$9];
  assume R[iir#anon$9] <= C[iir#anon$9];
  assume 0 <= I[iir#anon$10];
  assume I[iir#anon$10] <= R[iir#anon$10];
  assume R[iir#anon$10] <= C[iir#anon$10];
  assume 0 <= I[iir#anon$11];
  assume I[iir#anon$11] <= R[iir#anon$11];
  assume R[iir#anon$11] <= C[iir#anon$11];
  assume 0 <= I[iir#anon$12];
  assume I[iir#anon$12] <= R[iir#anon$12];
  assume R[iir#anon$12] <= C[iir#anon$12];
  assume 0 <= I[iir#anon$13];
  assume I[iir#anon$13] <= R[iir#anon$13];
  assume R[iir#anon$13] <= C[iir#anon$13];
  assume 0 <= I[iir#anon$14];
  assume I[iir#anon$14] <= R[iir#anon$14];
  assume R[iir#anon$14] <= C[iir#anon$14];
  assume 0 <= I[iir#anon$15];
  assume I[iir#anon$15] <= R[iir#anon$15];
  assume R[iir#anon$15] <= C[iir#anon$15];
  assume 0 <= I[iir#anon$16];
  assume I[iir#anon$16] <= R[iir#anon$16];
  assume R[iir#anon$16] <= C[iir#anon$16];
  assume 0 <= I[iir#anon$17];
  assume I[iir#anon$17] <= R[iir#anon$17];
  assume R[iir#anon$17] <= C[iir#anon$17];
  assume 0 <= I[iir#anon$18];
  assume I[iir#anon$18] <= R[iir#anon$18];
  assume R[iir#anon$18] <= C[iir#anon$18];
  assume 0 <= I[iir#anon$19];
  assume I[iir#anon$19] <= R[iir#anon$19];
  assume R[iir#anon$19] <= C[iir#anon$19];
  assume 0 <= I[iir#anon$20];
  assume I[iir#anon$20] <= R[iir#anon$20];
  assume R[iir#anon$20] <= C[iir#anon$20];
  assume 0 <= I[iir#anon$21];
  assume I[iir#anon$21] <= R[iir#anon$21];
  assume R[iir#anon$21] <= C[iir#anon$21];
  assume 0 <= I[iir#anon$22];
  assume I[iir#anon$22] <= R[iir#anon$22];
  assume R[iir#anon$22] <= C[iir#anon$22];
  assume 0 <= I[iir#anon$23];
  assume I[iir#anon$23] <= R[iir#anon$23];
  assume R[iir#anon$23] <= C[iir#anon$23];
  assume I[iir#anon$23] == R[iir#anon$23];
  assume I[iir#anon$17] == I[iir#anon$8];
  assume I[iir#anon$18] == I[iir#anon$11];
  assume I[iir#anon$19] == I[iir#anon$14];
  assume I[iir#anon$20] == I[iir#anon$16];
  assume I[iir#anon$21] == I[iir#anon$17];
  assume I[iir#anon$21] == I[iir#anon$18];
  assume I[iir#anon$22] == I[iir#anon$19];
  assume I[iir#anon$22] == I[iir#anon$20];
  assume I[iir#anon$23] == I[iir#anon$21];
  assume I[iir#anon$23] == I[iir#anon$22];
  assume I[iir#anon$8] == I[iir#anon$7];
  assume I[iir#anon$9] == I[iir#anon$7];
  assume I[iir#anon$11] == I[iir#anon$10];
  assume I[iir#anon$12] == I[iir#anon$10];
  assume I[iir#anon$14] == I[iir#anon$13];
  assume I[iir#anon$15] == I[iir#anon$13];
  assume (C[iir#anon$10] == 0) ==> (AV#delay_1#data == 0);
  assume (C[iir#anon$10] > 0) ==> (AV#delay_1#data == M[iir#anon$9][R[iir#anon$9] - 1]);
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$10] > 0) ==> (M[iir#anon$10][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$10] - 0)) ==> (M[iir#anon$10][idx] == M[iir#anon$9][idx - 1])
  );
  assume (C[iir#anon$13] == 0) ==> (AV#delay_2#data == 0);
  assume (C[iir#anon$13] > 0) ==> (AV#delay_2#data == M[iir#anon$12][R[iir#anon$12] - 1]);
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$13] > 0) ==> (M[iir#anon$13][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$13] - 0)) ==> (M[iir#anon$13][idx] == M[iir#anon$12][idx - 1])
  );
  assume (C[iir#anon$16] == 0) ==> (AV#delay_3#data == 0);
  assume (C[iir#anon$16] > 0) ==> (AV#delay_3#data == M[iir#anon$15][R[iir#anon$15] - 1]);
  assume R[iir#anon$15] == C[iir#anon$16];
  assume (C[iir#anon$16] > 0) ==> (M[iir#anon$16][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$16] - 0)) ==> (M[iir#anon$16][idx] == M[iir#anon$15][idx - 1])
  );
  assume R[iir#anon$8] == C[iir#anon$17];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$17]) ==> (M[iir#anon$17][idx$] == (37 * M[iir#anon$8][idx$]))
  );
  assume R[iir#anon$11] == C[iir#anon$18];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$18]) ==> (M[iir#anon$18][idx$] == (109 * M[iir#anon$11][idx$]))
  );
  assume R[iir#anon$14] == C[iir#anon$19];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$19]) ==> (M[iir#anon$19][idx$] == (109 * M[iir#anon$14][idx$]))
  );
  assume R[iir#anon$16] == C[iir#anon$20];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$20]) ==> (M[iir#anon$20][idx$] == (37 * M[iir#anon$16][idx$]))
  );
  assume R[iir#anon$17] == C[iir#anon$21];
  assume R[iir#anon$18] == C[iir#anon$21];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$21]) ==> (M[iir#anon$21][idx$] == (M[iir#anon$17][idx$] + M[iir#anon$18][idx$]))
  );
  assume R[iir#anon$19] == C[iir#anon$22];
  assume R[iir#anon$20] == C[iir#anon$22];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$22]) ==> (M[iir#anon$22][idx$] == (M[iir#anon$19][idx$] + M[iir#anon$20][idx$]))
  );
  assume R[iir#anon$21] == C[iir#anon$23];
  assume R[iir#anon$22] == C[iir#anon$23];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$23]) ==> (M[iir#anon$23][idx$] == (M[iir#anon$21][idx$] + M[iir#anon$22][idx$]))
  );
  assume R[iir#anon$7] == C[iir#anon$8];
  assume R[iir#anon$7] == C[iir#anon$9];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$8]) ==> (M[iir#anon$8][idx$] == M[iir#anon$7][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$9]) ==> (M[iir#anon$9][idx$] == M[iir#anon$7][idx$])
  );
  assume R[iir#anon$10] == C[iir#anon$11];
  assume R[iir#anon$10] == C[iir#anon$12];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$11]) ==> (M[iir#anon$11][idx$] == M[iir#anon$10][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$12]) ==> (M[iir#anon$12][idx$] == M[iir#anon$10][idx$])
  );
  assume R[iir#anon$13] == C[iir#anon$14];
  assume R[iir#anon$13] == C[iir#anon$15];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$14]) ==> (M[iir#anon$14][idx$] == M[iir#anon$13][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$15]) ==> (M[iir#anon$15][idx$] == M[iir#anon$13][idx$])
  );
  assume (1 <= (C[iir#anon$17] - R[iir#anon$17])) && (1 <= (C[iir#anon$18] - R[iir#anon$18]));
  in1#i := M[iir#anon$17][R[iir#anon$17]];
  R[iir#anon$17] := R[iir#anon$17] + 1;
  in2#j := M[iir#anon$18][R[iir#anon$18]];
  R[iir#anon$18] := R[iir#anon$18] + 1;
  M[iir#anon$21][C[iir#anon$21]] := in1#i + in2#j;
  C[iir#anon$21] := C[iir#anon$21] + 1;
  assume (C[iir#anon$10] == 0) ==> (AV#delay_1#data == 0);
  assume (C[iir#anon$10] > 0) ==> (AV#delay_1#data == M[iir#anon$9][R[iir#anon$9] - 1]);
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$10] > 0) ==> (M[iir#anon$10][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$10] - 0)) ==> (M[iir#anon$10][idx] == M[iir#anon$9][idx - 1])
  );
  assume (C[iir#anon$13] == 0) ==> (AV#delay_2#data == 0);
  assume (C[iir#anon$13] > 0) ==> (AV#delay_2#data == M[iir#anon$12][R[iir#anon$12] - 1]);
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$13] > 0) ==> (M[iir#anon$13][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$13] - 0)) ==> (M[iir#anon$13][idx] == M[iir#anon$12][idx - 1])
  );
  assume (C[iir#anon$16] == 0) ==> (AV#delay_3#data == 0);
  assume (C[iir#anon$16] > 0) ==> (AV#delay_3#data == M[iir#anon$15][R[iir#anon$15] - 1]);
  assume R[iir#anon$15] == C[iir#anon$16];
  assume (C[iir#anon$16] > 0) ==> (M[iir#anon$16][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$16] - 0)) ==> (M[iir#anon$16][idx] == M[iir#anon$15][idx - 1])
  );
  assume R[iir#anon$8] == C[iir#anon$17];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$17]) ==> (M[iir#anon$17][idx$] == (37 * M[iir#anon$8][idx$]))
  );
  assume R[iir#anon$11] == C[iir#anon$18];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$18]) ==> (M[iir#anon$18][idx$] == (109 * M[iir#anon$11][idx$]))
  );
  assume R[iir#anon$14] == C[iir#anon$19];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$19]) ==> (M[iir#anon$19][idx$] == (109 * M[iir#anon$14][idx$]))
  );
  assume R[iir#anon$16] == C[iir#anon$20];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$20]) ==> (M[iir#anon$20][idx$] == (37 * M[iir#anon$16][idx$]))
  );
  assume R[iir#anon$17] == C[iir#anon$21];
  assume R[iir#anon$18] == C[iir#anon$21];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$21]) ==> (M[iir#anon$21][idx$] == (M[iir#anon$17][idx$] + M[iir#anon$18][idx$]))
  );
  assume R[iir#anon$19] == C[iir#anon$22];
  assume R[iir#anon$20] == C[iir#anon$22];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$22]) ==> (M[iir#anon$22][idx$] == (M[iir#anon$19][idx$] + M[iir#anon$20][idx$]))
  );
  assume R[iir#anon$21] == C[iir#anon$23];
  assume R[iir#anon$22] == C[iir#anon$23];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$23]) ==> (M[iir#anon$23][idx$] == (M[iir#anon$21][idx$] + M[iir#anon$22][idx$]))
  );
  assume R[iir#anon$7] == C[iir#anon$8];
  assume R[iir#anon$7] == C[iir#anon$9];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$8]) ==> (M[iir#anon$8][idx$] == M[iir#anon$7][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$9]) ==> (M[iir#anon$9][idx$] == M[iir#anon$7][idx$])
  );
  assume R[iir#anon$10] == C[iir#anon$11];
  assume R[iir#anon$10] == C[iir#anon$12];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$11]) ==> (M[iir#anon$11][idx$] == M[iir#anon$10][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$12]) ==> (M[iir#anon$12][idx$] == M[iir#anon$10][idx$])
  );
  assume R[iir#anon$13] == C[iir#anon$14];
  assume R[iir#anon$13] == C[iir#anon$15];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$14]) ==> (M[iir#anon$14][idx$] == M[iir#anon$13][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$15]) ==> (M[iir#anon$15][idx$] == M[iir#anon$13][idx$])
  );
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add_1' might not preserve the channel invariant (#177)"} I[iir#anon$17] == I[iir#anon$8];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add_1' might not preserve the channel invariant (#178)"} I[iir#anon$18] == I[iir#anon$11];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add_1' might not preserve the channel invariant (#179)"} I[iir#anon$19] == I[iir#anon$14];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add_1' might not preserve the channel invariant (#180)"} I[iir#anon$20] == I[iir#anon$16];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add_1' might not preserve the channel invariant (#181)"} I[iir#anon$21] == I[iir#anon$17];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add_1' might not preserve the channel invariant (#182)"} I[iir#anon$21] == I[iir#anon$18];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add_1' might not preserve the channel invariant (#183)"} I[iir#anon$22] == I[iir#anon$19];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add_1' might not preserve the channel invariant (#184)"} I[iir#anon$22] == I[iir#anon$20];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add_1' might not preserve the channel invariant (#185)"} I[iir#anon$23] == I[iir#anon$21];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add_1' might not preserve the channel invariant (#186)"} I[iir#anon$23] == I[iir#anon$22];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add_1' might not preserve the channel invariant (#187)"} I[iir#anon$8] == I[iir#anon$7];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add_1' might not preserve the channel invariant (#188)"} I[iir#anon$9] == I[iir#anon$7];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add_1' might not preserve the channel invariant (#189)"} I[iir#anon$11] == I[iir#anon$10];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add_1' might not preserve the channel invariant (#190)"} I[iir#anon$12] == I[iir#anon$10];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add_1' might not preserve the channel invariant (#191)"} I[iir#anon$14] == I[iir#anon$13];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add_1' might not preserve the channel invariant (#192)"} I[iir#anon$15] == I[iir#anon$13];
}
procedure iir##add#anon$0#19()
  modifies C, R, M, I, H;
{
  var iir#delay_1: Actor;
  var iir#delay_2: Actor;
  var iir#delay_3: Actor;
  var iir#mul_1: Actor;
  var iir#mul_2: Actor;
  var iir#mul_3: Actor;
  var iir#mul_4: Actor;
  var iir#add_1: Actor;
  var iir#add_2: Actor;
  var iir#add_3: Actor;
  var iir#spl_1: Actor;
  var iir#spl_2: Actor;
  var iir#spl_3: Actor;
  var iir#anon$7: Chan (int);
  var iir#anon$8: Chan (int);
  var iir#anon$9: Chan (int);
  var iir#anon$10: Chan (int);
  var iir#anon$11: Chan (int);
  var iir#anon$12: Chan (int);
  var iir#anon$13: Chan (int);
  var iir#anon$14: Chan (int);
  var iir#anon$15: Chan (int);
  var iir#anon$16: Chan (int);
  var iir#anon$17: Chan (int);
  var iir#anon$18: Chan (int);
  var iir#anon$19: Chan (int);
  var iir#anon$20: Chan (int);
  var iir#anon$21: Chan (int);
  var iir#anon$22: Chan (int);
  var iir#anon$23: Chan (int);
  var AV#delay_1#data: int;
  var AV#delay_1#y: int;
  var AV#delay_2#data: int;
  var AV#delay_2#y: int;
  var AV#delay_3#data: int;
  var AV#delay_3#y: int;
  var in1#i: int;
  var in2#j: int;
  assume (iir#delay_1 != iir#delay_2) && (iir#delay_1 != iir#delay_3) && (iir#delay_1 != iir#mul_1) && (iir#delay_1 != iir#mul_2) && (iir#delay_1 != iir#mul_3) && (iir#delay_1 != iir#mul_4) && (iir#delay_1 != iir#add_1) && (iir#delay_1 != iir#add_2) && (iir#delay_1 != iir#add_3) && (iir#delay_1 != iir#spl_1) && (iir#delay_1 != iir#spl_2) && (iir#delay_1 != iir#spl_3) && (iir#delay_2 != iir#delay_3) && (iir#delay_2 != iir#mul_1) && (iir#delay_2 != iir#mul_2) && (iir#delay_2 != iir#mul_3) && (iir#delay_2 != iir#mul_4) && (iir#delay_2 != iir#add_1) && (iir#delay_2 != iir#add_2) && (iir#delay_2 != iir#add_3) && (iir#delay_2 != iir#spl_1) && (iir#delay_2 != iir#spl_2) && (iir#delay_2 != iir#spl_3) && (iir#delay_3 != iir#mul_1) && (iir#delay_3 != iir#mul_2) && (iir#delay_3 != iir#mul_3) && (iir#delay_3 != iir#mul_4) && (iir#delay_3 != iir#add_1) && (iir#delay_3 != iir#add_2) && (iir#delay_3 != iir#add_3) && (iir#delay_3 != iir#spl_1) && (iir#delay_3 != iir#spl_2) && (iir#delay_3 != iir#spl_3) && (iir#mul_1 != iir#mul_2) && (iir#mul_1 != iir#mul_3) && (iir#mul_1 != iir#mul_4) && (iir#mul_1 != iir#add_1) && (iir#mul_1 != iir#add_2) && (iir#mul_1 != iir#add_3) && (iir#mul_1 != iir#spl_1) && (iir#mul_1 != iir#spl_2) && (iir#mul_1 != iir#spl_3) && (iir#mul_2 != iir#mul_3) && (iir#mul_2 != iir#mul_4) && (iir#mul_2 != iir#add_1) && (iir#mul_2 != iir#add_2) && (iir#mul_2 != iir#add_3) && (iir#mul_2 != iir#spl_1) && (iir#mul_2 != iir#spl_2) && (iir#mul_2 != iir#spl_3) && (iir#mul_3 != iir#mul_4) && (iir#mul_3 != iir#add_1) && (iir#mul_3 != iir#add_2) && (iir#mul_3 != iir#add_3) && (iir#mul_3 != iir#spl_1) && (iir#mul_3 != iir#spl_2) && (iir#mul_3 != iir#spl_3) && (iir#mul_4 != iir#add_1) && (iir#mul_4 != iir#add_2) && (iir#mul_4 != iir#add_3) && (iir#mul_4 != iir#spl_1) && (iir#mul_4 != iir#spl_2) && (iir#mul_4 != iir#spl_3) && (iir#add_1 != iir#add_2) && (iir#add_1 != iir#add_3) && (iir#add_1 != iir#spl_1) && (iir#add_1 != iir#spl_2) && (iir#add_1 != iir#spl_3) && (iir#add_2 != iir#add_3) && (iir#add_2 != iir#spl_1) && (iir#add_2 != iir#spl_2) && (iir#add_2 != iir#spl_3) && (iir#add_3 != iir#spl_1) && (iir#add_3 != iir#spl_2) && (iir#add_3 != iir#spl_3) && (iir#spl_1 != iir#spl_2) && (iir#spl_1 != iir#spl_3) && (iir#spl_2 != iir#spl_3);
  assume (iir#anon$7 != iir#anon$8) && (iir#anon$7 != iir#anon$9) && (iir#anon$7 != iir#anon$10) && (iir#anon$7 != iir#anon$11) && (iir#anon$7 != iir#anon$12) && (iir#anon$7 != iir#anon$13) && (iir#anon$7 != iir#anon$14) && (iir#anon$7 != iir#anon$15) && (iir#anon$7 != iir#anon$16) && (iir#anon$7 != iir#anon$17) && (iir#anon$7 != iir#anon$18) && (iir#anon$7 != iir#anon$19) && (iir#anon$7 != iir#anon$20) && (iir#anon$7 != iir#anon$21) && (iir#anon$7 != iir#anon$22) && (iir#anon$7 != iir#anon$23) && (iir#anon$8 != iir#anon$9) && (iir#anon$8 != iir#anon$10) && (iir#anon$8 != iir#anon$11) && (iir#anon$8 != iir#anon$12) && (iir#anon$8 != iir#anon$13) && (iir#anon$8 != iir#anon$14) && (iir#anon$8 != iir#anon$15) && (iir#anon$8 != iir#anon$16) && (iir#anon$8 != iir#anon$17) && (iir#anon$8 != iir#anon$18) && (iir#anon$8 != iir#anon$19) && (iir#anon$8 != iir#anon$20) && (iir#anon$8 != iir#anon$21) && (iir#anon$8 != iir#anon$22) && (iir#anon$8 != iir#anon$23) && (iir#anon$9 != iir#anon$10) && (iir#anon$9 != iir#anon$11) && (iir#anon$9 != iir#anon$12) && (iir#anon$9 != iir#anon$13) && (iir#anon$9 != iir#anon$14) && (iir#anon$9 != iir#anon$15) && (iir#anon$9 != iir#anon$16) && (iir#anon$9 != iir#anon$17) && (iir#anon$9 != iir#anon$18) && (iir#anon$9 != iir#anon$19) && (iir#anon$9 != iir#anon$20) && (iir#anon$9 != iir#anon$21) && (iir#anon$9 != iir#anon$22) && (iir#anon$9 != iir#anon$23) && (iir#anon$10 != iir#anon$11) && (iir#anon$10 != iir#anon$12) && (iir#anon$10 != iir#anon$13) && (iir#anon$10 != iir#anon$14) && (iir#anon$10 != iir#anon$15) && (iir#anon$10 != iir#anon$16) && (iir#anon$10 != iir#anon$17) && (iir#anon$10 != iir#anon$18) && (iir#anon$10 != iir#anon$19) && (iir#anon$10 != iir#anon$20) && (iir#anon$10 != iir#anon$21) && (iir#anon$10 != iir#anon$22) && (iir#anon$10 != iir#anon$23) && (iir#anon$11 != iir#anon$12) && (iir#anon$11 != iir#anon$13) && (iir#anon$11 != iir#anon$14) && (iir#anon$11 != iir#anon$15) && (iir#anon$11 != iir#anon$16) && (iir#anon$11 != iir#anon$17) && (iir#anon$11 != iir#anon$18) && (iir#anon$11 != iir#anon$19) && (iir#anon$11 != iir#anon$20) && (iir#anon$11 != iir#anon$21) && (iir#anon$11 != iir#anon$22) && (iir#anon$11 != iir#anon$23) && (iir#anon$12 != iir#anon$13) && (iir#anon$12 != iir#anon$14) && (iir#anon$12 != iir#anon$15) && (iir#anon$12 != iir#anon$16) && (iir#anon$12 != iir#anon$17) && (iir#anon$12 != iir#anon$18) && (iir#anon$12 != iir#anon$19) && (iir#anon$12 != iir#anon$20) && (iir#anon$12 != iir#anon$21) && (iir#anon$12 != iir#anon$22) && (iir#anon$12 != iir#anon$23) && (iir#anon$13 != iir#anon$14) && (iir#anon$13 != iir#anon$15) && (iir#anon$13 != iir#anon$16) && (iir#anon$13 != iir#anon$17) && (iir#anon$13 != iir#anon$18) && (iir#anon$13 != iir#anon$19) && (iir#anon$13 != iir#anon$20) && (iir#anon$13 != iir#anon$21) && (iir#anon$13 != iir#anon$22) && (iir#anon$13 != iir#anon$23) && (iir#anon$14 != iir#anon$15) && (iir#anon$14 != iir#anon$16) && (iir#anon$14 != iir#anon$17) && (iir#anon$14 != iir#anon$18) && (iir#anon$14 != iir#anon$19) && (iir#anon$14 != iir#anon$20) && (iir#anon$14 != iir#anon$21) && (iir#anon$14 != iir#anon$22) && (iir#anon$14 != iir#anon$23) && (iir#anon$15 != iir#anon$16) && (iir#anon$15 != iir#anon$17) && (iir#anon$15 != iir#anon$18) && (iir#anon$15 != iir#anon$19) && (iir#anon$15 != iir#anon$20) && (iir#anon$15 != iir#anon$21) && (iir#anon$15 != iir#anon$22) && (iir#anon$15 != iir#anon$23) && (iir#anon$16 != iir#anon$17) && (iir#anon$16 != iir#anon$18) && (iir#anon$16 != iir#anon$19) && (iir#anon$16 != iir#anon$20) && (iir#anon$16 != iir#anon$21) && (iir#anon$16 != iir#anon$22) && (iir#anon$16 != iir#anon$23) && (iir#anon$17 != iir#anon$18) && (iir#anon$17 != iir#anon$19) && (iir#anon$17 != iir#anon$20) && (iir#anon$17 != iir#anon$21) && (iir#anon$17 != iir#anon$22) && (iir#anon$17 != iir#anon$23) && (iir#anon$18 != iir#anon$19) && (iir#anon$18 != iir#anon$20) && (iir#anon$18 != iir#anon$21) && (iir#anon$18 != iir#anon$22) && (iir#anon$18 != iir#anon$23) && (iir#anon$19 != iir#anon$20) && (iir#anon$19 != iir#anon$21) && (iir#anon$19 != iir#anon$22) && (iir#anon$19 != iir#anon$23) && (iir#anon$20 != iir#anon$21) && (iir#anon$20 != iir#anon$22) && (iir#anon$20 != iir#anon$23) && (iir#anon$21 != iir#anon$22) && (iir#anon$21 != iir#anon$23) && (iir#anon$22 != iir#anon$23);
  assume 0 <= I[iir#anon$7];
  assume I[iir#anon$7] <= R[iir#anon$7];
  assume R[iir#anon$7] <= C[iir#anon$7];
  assume 0 <= I[iir#anon$8];
  assume I[iir#anon$8] <= R[iir#anon$8];
  assume R[iir#anon$8] <= C[iir#anon$8];
  assume 0 <= I[iir#anon$9];
  assume I[iir#anon$9] <= R[iir#anon$9];
  assume R[iir#anon$9] <= C[iir#anon$9];
  assume 0 <= I[iir#anon$10];
  assume I[iir#anon$10] <= R[iir#anon$10];
  assume R[iir#anon$10] <= C[iir#anon$10];
  assume 0 <= I[iir#anon$11];
  assume I[iir#anon$11] <= R[iir#anon$11];
  assume R[iir#anon$11] <= C[iir#anon$11];
  assume 0 <= I[iir#anon$12];
  assume I[iir#anon$12] <= R[iir#anon$12];
  assume R[iir#anon$12] <= C[iir#anon$12];
  assume 0 <= I[iir#anon$13];
  assume I[iir#anon$13] <= R[iir#anon$13];
  assume R[iir#anon$13] <= C[iir#anon$13];
  assume 0 <= I[iir#anon$14];
  assume I[iir#anon$14] <= R[iir#anon$14];
  assume R[iir#anon$14] <= C[iir#anon$14];
  assume 0 <= I[iir#anon$15];
  assume I[iir#anon$15] <= R[iir#anon$15];
  assume R[iir#anon$15] <= C[iir#anon$15];
  assume 0 <= I[iir#anon$16];
  assume I[iir#anon$16] <= R[iir#anon$16];
  assume R[iir#anon$16] <= C[iir#anon$16];
  assume 0 <= I[iir#anon$17];
  assume I[iir#anon$17] <= R[iir#anon$17];
  assume R[iir#anon$17] <= C[iir#anon$17];
  assume 0 <= I[iir#anon$18];
  assume I[iir#anon$18] <= R[iir#anon$18];
  assume R[iir#anon$18] <= C[iir#anon$18];
  assume 0 <= I[iir#anon$19];
  assume I[iir#anon$19] <= R[iir#anon$19];
  assume R[iir#anon$19] <= C[iir#anon$19];
  assume 0 <= I[iir#anon$20];
  assume I[iir#anon$20] <= R[iir#anon$20];
  assume R[iir#anon$20] <= C[iir#anon$20];
  assume 0 <= I[iir#anon$21];
  assume I[iir#anon$21] <= R[iir#anon$21];
  assume R[iir#anon$21] <= C[iir#anon$21];
  assume 0 <= I[iir#anon$22];
  assume I[iir#anon$22] <= R[iir#anon$22];
  assume R[iir#anon$22] <= C[iir#anon$22];
  assume 0 <= I[iir#anon$23];
  assume I[iir#anon$23] <= R[iir#anon$23];
  assume R[iir#anon$23] <= C[iir#anon$23];
  assume I[iir#anon$23] == R[iir#anon$23];
  assume I[iir#anon$17] == I[iir#anon$8];
  assume I[iir#anon$18] == I[iir#anon$11];
  assume I[iir#anon$19] == I[iir#anon$14];
  assume I[iir#anon$20] == I[iir#anon$16];
  assume I[iir#anon$21] == I[iir#anon$17];
  assume I[iir#anon$21] == I[iir#anon$18];
  assume I[iir#anon$22] == I[iir#anon$19];
  assume I[iir#anon$22] == I[iir#anon$20];
  assume I[iir#anon$23] == I[iir#anon$21];
  assume I[iir#anon$23] == I[iir#anon$22];
  assume I[iir#anon$8] == I[iir#anon$7];
  assume I[iir#anon$9] == I[iir#anon$7];
  assume I[iir#anon$11] == I[iir#anon$10];
  assume I[iir#anon$12] == I[iir#anon$10];
  assume I[iir#anon$14] == I[iir#anon$13];
  assume I[iir#anon$15] == I[iir#anon$13];
  assume (C[iir#anon$10] == 0) ==> (AV#delay_1#data == 0);
  assume (C[iir#anon$10] > 0) ==> (AV#delay_1#data == M[iir#anon$9][R[iir#anon$9] - 1]);
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$10] > 0) ==> (M[iir#anon$10][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$10] - 0)) ==> (M[iir#anon$10][idx] == M[iir#anon$9][idx - 1])
  );
  assume (C[iir#anon$13] == 0) ==> (AV#delay_2#data == 0);
  assume (C[iir#anon$13] > 0) ==> (AV#delay_2#data == M[iir#anon$12][R[iir#anon$12] - 1]);
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$13] > 0) ==> (M[iir#anon$13][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$13] - 0)) ==> (M[iir#anon$13][idx] == M[iir#anon$12][idx - 1])
  );
  assume (C[iir#anon$16] == 0) ==> (AV#delay_3#data == 0);
  assume (C[iir#anon$16] > 0) ==> (AV#delay_3#data == M[iir#anon$15][R[iir#anon$15] - 1]);
  assume R[iir#anon$15] == C[iir#anon$16];
  assume (C[iir#anon$16] > 0) ==> (M[iir#anon$16][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$16] - 0)) ==> (M[iir#anon$16][idx] == M[iir#anon$15][idx - 1])
  );
  assume R[iir#anon$8] == C[iir#anon$17];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$17]) ==> (M[iir#anon$17][idx$] == (37 * M[iir#anon$8][idx$]))
  );
  assume R[iir#anon$11] == C[iir#anon$18];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$18]) ==> (M[iir#anon$18][idx$] == (109 * M[iir#anon$11][idx$]))
  );
  assume R[iir#anon$14] == C[iir#anon$19];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$19]) ==> (M[iir#anon$19][idx$] == (109 * M[iir#anon$14][idx$]))
  );
  assume R[iir#anon$16] == C[iir#anon$20];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$20]) ==> (M[iir#anon$20][idx$] == (37 * M[iir#anon$16][idx$]))
  );
  assume R[iir#anon$17] == C[iir#anon$21];
  assume R[iir#anon$18] == C[iir#anon$21];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$21]) ==> (M[iir#anon$21][idx$] == (M[iir#anon$17][idx$] + M[iir#anon$18][idx$]))
  );
  assume R[iir#anon$19] == C[iir#anon$22];
  assume R[iir#anon$20] == C[iir#anon$22];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$22]) ==> (M[iir#anon$22][idx$] == (M[iir#anon$19][idx$] + M[iir#anon$20][idx$]))
  );
  assume R[iir#anon$21] == C[iir#anon$23];
  assume R[iir#anon$22] == C[iir#anon$23];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$23]) ==> (M[iir#anon$23][idx$] == (M[iir#anon$21][idx$] + M[iir#anon$22][idx$]))
  );
  assume R[iir#anon$7] == C[iir#anon$8];
  assume R[iir#anon$7] == C[iir#anon$9];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$8]) ==> (M[iir#anon$8][idx$] == M[iir#anon$7][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$9]) ==> (M[iir#anon$9][idx$] == M[iir#anon$7][idx$])
  );
  assume R[iir#anon$10] == C[iir#anon$11];
  assume R[iir#anon$10] == C[iir#anon$12];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$11]) ==> (M[iir#anon$11][idx$] == M[iir#anon$10][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$12]) ==> (M[iir#anon$12][idx$] == M[iir#anon$10][idx$])
  );
  assume R[iir#anon$13] == C[iir#anon$14];
  assume R[iir#anon$13] == C[iir#anon$15];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$14]) ==> (M[iir#anon$14][idx$] == M[iir#anon$13][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$15]) ==> (M[iir#anon$15][idx$] == M[iir#anon$13][idx$])
  );
  assume (1 <= (C[iir#anon$19] - R[iir#anon$19])) && (1 <= (C[iir#anon$20] - R[iir#anon$20]));
  in1#i := M[iir#anon$19][R[iir#anon$19]];
  R[iir#anon$19] := R[iir#anon$19] + 1;
  in2#j := M[iir#anon$20][R[iir#anon$20]];
  R[iir#anon$20] := R[iir#anon$20] + 1;
  M[iir#anon$22][C[iir#anon$22]] := in1#i + in2#j;
  C[iir#anon$22] := C[iir#anon$22] + 1;
  assume (C[iir#anon$10] == 0) ==> (AV#delay_1#data == 0);
  assume (C[iir#anon$10] > 0) ==> (AV#delay_1#data == M[iir#anon$9][R[iir#anon$9] - 1]);
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$10] > 0) ==> (M[iir#anon$10][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$10] - 0)) ==> (M[iir#anon$10][idx] == M[iir#anon$9][idx - 1])
  );
  assume (C[iir#anon$13] == 0) ==> (AV#delay_2#data == 0);
  assume (C[iir#anon$13] > 0) ==> (AV#delay_2#data == M[iir#anon$12][R[iir#anon$12] - 1]);
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$13] > 0) ==> (M[iir#anon$13][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$13] - 0)) ==> (M[iir#anon$13][idx] == M[iir#anon$12][idx - 1])
  );
  assume (C[iir#anon$16] == 0) ==> (AV#delay_3#data == 0);
  assume (C[iir#anon$16] > 0) ==> (AV#delay_3#data == M[iir#anon$15][R[iir#anon$15] - 1]);
  assume R[iir#anon$15] == C[iir#anon$16];
  assume (C[iir#anon$16] > 0) ==> (M[iir#anon$16][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$16] - 0)) ==> (M[iir#anon$16][idx] == M[iir#anon$15][idx - 1])
  );
  assume R[iir#anon$8] == C[iir#anon$17];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$17]) ==> (M[iir#anon$17][idx$] == (37 * M[iir#anon$8][idx$]))
  );
  assume R[iir#anon$11] == C[iir#anon$18];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$18]) ==> (M[iir#anon$18][idx$] == (109 * M[iir#anon$11][idx$]))
  );
  assume R[iir#anon$14] == C[iir#anon$19];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$19]) ==> (M[iir#anon$19][idx$] == (109 * M[iir#anon$14][idx$]))
  );
  assume R[iir#anon$16] == C[iir#anon$20];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$20]) ==> (M[iir#anon$20][idx$] == (37 * M[iir#anon$16][idx$]))
  );
  assume R[iir#anon$17] == C[iir#anon$21];
  assume R[iir#anon$18] == C[iir#anon$21];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$21]) ==> (M[iir#anon$21][idx$] == (M[iir#anon$17][idx$] + M[iir#anon$18][idx$]))
  );
  assume R[iir#anon$19] == C[iir#anon$22];
  assume R[iir#anon$20] == C[iir#anon$22];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$22]) ==> (M[iir#anon$22][idx$] == (M[iir#anon$19][idx$] + M[iir#anon$20][idx$]))
  );
  assume R[iir#anon$21] == C[iir#anon$23];
  assume R[iir#anon$22] == C[iir#anon$23];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$23]) ==> (M[iir#anon$23][idx$] == (M[iir#anon$21][idx$] + M[iir#anon$22][idx$]))
  );
  assume R[iir#anon$7] == C[iir#anon$8];
  assume R[iir#anon$7] == C[iir#anon$9];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$8]) ==> (M[iir#anon$8][idx$] == M[iir#anon$7][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$9]) ==> (M[iir#anon$9][idx$] == M[iir#anon$7][idx$])
  );
  assume R[iir#anon$10] == C[iir#anon$11];
  assume R[iir#anon$10] == C[iir#anon$12];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$11]) ==> (M[iir#anon$11][idx$] == M[iir#anon$10][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$12]) ==> (M[iir#anon$12][idx$] == M[iir#anon$10][idx$])
  );
  assume R[iir#anon$13] == C[iir#anon$14];
  assume R[iir#anon$13] == C[iir#anon$15];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$14]) ==> (M[iir#anon$14][idx$] == M[iir#anon$13][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$15]) ==> (M[iir#anon$15][idx$] == M[iir#anon$13][idx$])
  );
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add_2' might not preserve the channel invariant (#193)"} I[iir#anon$17] == I[iir#anon$8];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add_2' might not preserve the channel invariant (#194)"} I[iir#anon$18] == I[iir#anon$11];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add_2' might not preserve the channel invariant (#195)"} I[iir#anon$19] == I[iir#anon$14];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add_2' might not preserve the channel invariant (#196)"} I[iir#anon$20] == I[iir#anon$16];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add_2' might not preserve the channel invariant (#197)"} I[iir#anon$21] == I[iir#anon$17];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add_2' might not preserve the channel invariant (#198)"} I[iir#anon$21] == I[iir#anon$18];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add_2' might not preserve the channel invariant (#199)"} I[iir#anon$22] == I[iir#anon$19];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add_2' might not preserve the channel invariant (#200)"} I[iir#anon$22] == I[iir#anon$20];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add_2' might not preserve the channel invariant (#201)"} I[iir#anon$23] == I[iir#anon$21];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add_2' might not preserve the channel invariant (#202)"} I[iir#anon$23] == I[iir#anon$22];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add_2' might not preserve the channel invariant (#203)"} I[iir#anon$8] == I[iir#anon$7];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add_2' might not preserve the channel invariant (#204)"} I[iir#anon$9] == I[iir#anon$7];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add_2' might not preserve the channel invariant (#205)"} I[iir#anon$11] == I[iir#anon$10];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add_2' might not preserve the channel invariant (#206)"} I[iir#anon$12] == I[iir#anon$10];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add_2' might not preserve the channel invariant (#207)"} I[iir#anon$14] == I[iir#anon$13];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add_2' might not preserve the channel invariant (#208)"} I[iir#anon$15] == I[iir#anon$13];
}
procedure iir##add#anon$0#20()
  modifies C, R, M, I, H;
{
  var iir#delay_1: Actor;
  var iir#delay_2: Actor;
  var iir#delay_3: Actor;
  var iir#mul_1: Actor;
  var iir#mul_2: Actor;
  var iir#mul_3: Actor;
  var iir#mul_4: Actor;
  var iir#add_1: Actor;
  var iir#add_2: Actor;
  var iir#add_3: Actor;
  var iir#spl_1: Actor;
  var iir#spl_2: Actor;
  var iir#spl_3: Actor;
  var iir#anon$7: Chan (int);
  var iir#anon$8: Chan (int);
  var iir#anon$9: Chan (int);
  var iir#anon$10: Chan (int);
  var iir#anon$11: Chan (int);
  var iir#anon$12: Chan (int);
  var iir#anon$13: Chan (int);
  var iir#anon$14: Chan (int);
  var iir#anon$15: Chan (int);
  var iir#anon$16: Chan (int);
  var iir#anon$17: Chan (int);
  var iir#anon$18: Chan (int);
  var iir#anon$19: Chan (int);
  var iir#anon$20: Chan (int);
  var iir#anon$21: Chan (int);
  var iir#anon$22: Chan (int);
  var iir#anon$23: Chan (int);
  var AV#delay_1#data: int;
  var AV#delay_1#y: int;
  var AV#delay_2#data: int;
  var AV#delay_2#y: int;
  var AV#delay_3#data: int;
  var AV#delay_3#y: int;
  var in1#i: int;
  var in2#j: int;
  assume (iir#delay_1 != iir#delay_2) && (iir#delay_1 != iir#delay_3) && (iir#delay_1 != iir#mul_1) && (iir#delay_1 != iir#mul_2) && (iir#delay_1 != iir#mul_3) && (iir#delay_1 != iir#mul_4) && (iir#delay_1 != iir#add_1) && (iir#delay_1 != iir#add_2) && (iir#delay_1 != iir#add_3) && (iir#delay_1 != iir#spl_1) && (iir#delay_1 != iir#spl_2) && (iir#delay_1 != iir#spl_3) && (iir#delay_2 != iir#delay_3) && (iir#delay_2 != iir#mul_1) && (iir#delay_2 != iir#mul_2) && (iir#delay_2 != iir#mul_3) && (iir#delay_2 != iir#mul_4) && (iir#delay_2 != iir#add_1) && (iir#delay_2 != iir#add_2) && (iir#delay_2 != iir#add_3) && (iir#delay_2 != iir#spl_1) && (iir#delay_2 != iir#spl_2) && (iir#delay_2 != iir#spl_3) && (iir#delay_3 != iir#mul_1) && (iir#delay_3 != iir#mul_2) && (iir#delay_3 != iir#mul_3) && (iir#delay_3 != iir#mul_4) && (iir#delay_3 != iir#add_1) && (iir#delay_3 != iir#add_2) && (iir#delay_3 != iir#add_3) && (iir#delay_3 != iir#spl_1) && (iir#delay_3 != iir#spl_2) && (iir#delay_3 != iir#spl_3) && (iir#mul_1 != iir#mul_2) && (iir#mul_1 != iir#mul_3) && (iir#mul_1 != iir#mul_4) && (iir#mul_1 != iir#add_1) && (iir#mul_1 != iir#add_2) && (iir#mul_1 != iir#add_3) && (iir#mul_1 != iir#spl_1) && (iir#mul_1 != iir#spl_2) && (iir#mul_1 != iir#spl_3) && (iir#mul_2 != iir#mul_3) && (iir#mul_2 != iir#mul_4) && (iir#mul_2 != iir#add_1) && (iir#mul_2 != iir#add_2) && (iir#mul_2 != iir#add_3) && (iir#mul_2 != iir#spl_1) && (iir#mul_2 != iir#spl_2) && (iir#mul_2 != iir#spl_3) && (iir#mul_3 != iir#mul_4) && (iir#mul_3 != iir#add_1) && (iir#mul_3 != iir#add_2) && (iir#mul_3 != iir#add_3) && (iir#mul_3 != iir#spl_1) && (iir#mul_3 != iir#spl_2) && (iir#mul_3 != iir#spl_3) && (iir#mul_4 != iir#add_1) && (iir#mul_4 != iir#add_2) && (iir#mul_4 != iir#add_3) && (iir#mul_4 != iir#spl_1) && (iir#mul_4 != iir#spl_2) && (iir#mul_4 != iir#spl_3) && (iir#add_1 != iir#add_2) && (iir#add_1 != iir#add_3) && (iir#add_1 != iir#spl_1) && (iir#add_1 != iir#spl_2) && (iir#add_1 != iir#spl_3) && (iir#add_2 != iir#add_3) && (iir#add_2 != iir#spl_1) && (iir#add_2 != iir#spl_2) && (iir#add_2 != iir#spl_3) && (iir#add_3 != iir#spl_1) && (iir#add_3 != iir#spl_2) && (iir#add_3 != iir#spl_3) && (iir#spl_1 != iir#spl_2) && (iir#spl_1 != iir#spl_3) && (iir#spl_2 != iir#spl_3);
  assume (iir#anon$7 != iir#anon$8) && (iir#anon$7 != iir#anon$9) && (iir#anon$7 != iir#anon$10) && (iir#anon$7 != iir#anon$11) && (iir#anon$7 != iir#anon$12) && (iir#anon$7 != iir#anon$13) && (iir#anon$7 != iir#anon$14) && (iir#anon$7 != iir#anon$15) && (iir#anon$7 != iir#anon$16) && (iir#anon$7 != iir#anon$17) && (iir#anon$7 != iir#anon$18) && (iir#anon$7 != iir#anon$19) && (iir#anon$7 != iir#anon$20) && (iir#anon$7 != iir#anon$21) && (iir#anon$7 != iir#anon$22) && (iir#anon$7 != iir#anon$23) && (iir#anon$8 != iir#anon$9) && (iir#anon$8 != iir#anon$10) && (iir#anon$8 != iir#anon$11) && (iir#anon$8 != iir#anon$12) && (iir#anon$8 != iir#anon$13) && (iir#anon$8 != iir#anon$14) && (iir#anon$8 != iir#anon$15) && (iir#anon$8 != iir#anon$16) && (iir#anon$8 != iir#anon$17) && (iir#anon$8 != iir#anon$18) && (iir#anon$8 != iir#anon$19) && (iir#anon$8 != iir#anon$20) && (iir#anon$8 != iir#anon$21) && (iir#anon$8 != iir#anon$22) && (iir#anon$8 != iir#anon$23) && (iir#anon$9 != iir#anon$10) && (iir#anon$9 != iir#anon$11) && (iir#anon$9 != iir#anon$12) && (iir#anon$9 != iir#anon$13) && (iir#anon$9 != iir#anon$14) && (iir#anon$9 != iir#anon$15) && (iir#anon$9 != iir#anon$16) && (iir#anon$9 != iir#anon$17) && (iir#anon$9 != iir#anon$18) && (iir#anon$9 != iir#anon$19) && (iir#anon$9 != iir#anon$20) && (iir#anon$9 != iir#anon$21) && (iir#anon$9 != iir#anon$22) && (iir#anon$9 != iir#anon$23) && (iir#anon$10 != iir#anon$11) && (iir#anon$10 != iir#anon$12) && (iir#anon$10 != iir#anon$13) && (iir#anon$10 != iir#anon$14) && (iir#anon$10 != iir#anon$15) && (iir#anon$10 != iir#anon$16) && (iir#anon$10 != iir#anon$17) && (iir#anon$10 != iir#anon$18) && (iir#anon$10 != iir#anon$19) && (iir#anon$10 != iir#anon$20) && (iir#anon$10 != iir#anon$21) && (iir#anon$10 != iir#anon$22) && (iir#anon$10 != iir#anon$23) && (iir#anon$11 != iir#anon$12) && (iir#anon$11 != iir#anon$13) && (iir#anon$11 != iir#anon$14) && (iir#anon$11 != iir#anon$15) && (iir#anon$11 != iir#anon$16) && (iir#anon$11 != iir#anon$17) && (iir#anon$11 != iir#anon$18) && (iir#anon$11 != iir#anon$19) && (iir#anon$11 != iir#anon$20) && (iir#anon$11 != iir#anon$21) && (iir#anon$11 != iir#anon$22) && (iir#anon$11 != iir#anon$23) && (iir#anon$12 != iir#anon$13) && (iir#anon$12 != iir#anon$14) && (iir#anon$12 != iir#anon$15) && (iir#anon$12 != iir#anon$16) && (iir#anon$12 != iir#anon$17) && (iir#anon$12 != iir#anon$18) && (iir#anon$12 != iir#anon$19) && (iir#anon$12 != iir#anon$20) && (iir#anon$12 != iir#anon$21) && (iir#anon$12 != iir#anon$22) && (iir#anon$12 != iir#anon$23) && (iir#anon$13 != iir#anon$14) && (iir#anon$13 != iir#anon$15) && (iir#anon$13 != iir#anon$16) && (iir#anon$13 != iir#anon$17) && (iir#anon$13 != iir#anon$18) && (iir#anon$13 != iir#anon$19) && (iir#anon$13 != iir#anon$20) && (iir#anon$13 != iir#anon$21) && (iir#anon$13 != iir#anon$22) && (iir#anon$13 != iir#anon$23) && (iir#anon$14 != iir#anon$15) && (iir#anon$14 != iir#anon$16) && (iir#anon$14 != iir#anon$17) && (iir#anon$14 != iir#anon$18) && (iir#anon$14 != iir#anon$19) && (iir#anon$14 != iir#anon$20) && (iir#anon$14 != iir#anon$21) && (iir#anon$14 != iir#anon$22) && (iir#anon$14 != iir#anon$23) && (iir#anon$15 != iir#anon$16) && (iir#anon$15 != iir#anon$17) && (iir#anon$15 != iir#anon$18) && (iir#anon$15 != iir#anon$19) && (iir#anon$15 != iir#anon$20) && (iir#anon$15 != iir#anon$21) && (iir#anon$15 != iir#anon$22) && (iir#anon$15 != iir#anon$23) && (iir#anon$16 != iir#anon$17) && (iir#anon$16 != iir#anon$18) && (iir#anon$16 != iir#anon$19) && (iir#anon$16 != iir#anon$20) && (iir#anon$16 != iir#anon$21) && (iir#anon$16 != iir#anon$22) && (iir#anon$16 != iir#anon$23) && (iir#anon$17 != iir#anon$18) && (iir#anon$17 != iir#anon$19) && (iir#anon$17 != iir#anon$20) && (iir#anon$17 != iir#anon$21) && (iir#anon$17 != iir#anon$22) && (iir#anon$17 != iir#anon$23) && (iir#anon$18 != iir#anon$19) && (iir#anon$18 != iir#anon$20) && (iir#anon$18 != iir#anon$21) && (iir#anon$18 != iir#anon$22) && (iir#anon$18 != iir#anon$23) && (iir#anon$19 != iir#anon$20) && (iir#anon$19 != iir#anon$21) && (iir#anon$19 != iir#anon$22) && (iir#anon$19 != iir#anon$23) && (iir#anon$20 != iir#anon$21) && (iir#anon$20 != iir#anon$22) && (iir#anon$20 != iir#anon$23) && (iir#anon$21 != iir#anon$22) && (iir#anon$21 != iir#anon$23) && (iir#anon$22 != iir#anon$23);
  assume 0 <= I[iir#anon$7];
  assume I[iir#anon$7] <= R[iir#anon$7];
  assume R[iir#anon$7] <= C[iir#anon$7];
  assume 0 <= I[iir#anon$8];
  assume I[iir#anon$8] <= R[iir#anon$8];
  assume R[iir#anon$8] <= C[iir#anon$8];
  assume 0 <= I[iir#anon$9];
  assume I[iir#anon$9] <= R[iir#anon$9];
  assume R[iir#anon$9] <= C[iir#anon$9];
  assume 0 <= I[iir#anon$10];
  assume I[iir#anon$10] <= R[iir#anon$10];
  assume R[iir#anon$10] <= C[iir#anon$10];
  assume 0 <= I[iir#anon$11];
  assume I[iir#anon$11] <= R[iir#anon$11];
  assume R[iir#anon$11] <= C[iir#anon$11];
  assume 0 <= I[iir#anon$12];
  assume I[iir#anon$12] <= R[iir#anon$12];
  assume R[iir#anon$12] <= C[iir#anon$12];
  assume 0 <= I[iir#anon$13];
  assume I[iir#anon$13] <= R[iir#anon$13];
  assume R[iir#anon$13] <= C[iir#anon$13];
  assume 0 <= I[iir#anon$14];
  assume I[iir#anon$14] <= R[iir#anon$14];
  assume R[iir#anon$14] <= C[iir#anon$14];
  assume 0 <= I[iir#anon$15];
  assume I[iir#anon$15] <= R[iir#anon$15];
  assume R[iir#anon$15] <= C[iir#anon$15];
  assume 0 <= I[iir#anon$16];
  assume I[iir#anon$16] <= R[iir#anon$16];
  assume R[iir#anon$16] <= C[iir#anon$16];
  assume 0 <= I[iir#anon$17];
  assume I[iir#anon$17] <= R[iir#anon$17];
  assume R[iir#anon$17] <= C[iir#anon$17];
  assume 0 <= I[iir#anon$18];
  assume I[iir#anon$18] <= R[iir#anon$18];
  assume R[iir#anon$18] <= C[iir#anon$18];
  assume 0 <= I[iir#anon$19];
  assume I[iir#anon$19] <= R[iir#anon$19];
  assume R[iir#anon$19] <= C[iir#anon$19];
  assume 0 <= I[iir#anon$20];
  assume I[iir#anon$20] <= R[iir#anon$20];
  assume R[iir#anon$20] <= C[iir#anon$20];
  assume 0 <= I[iir#anon$21];
  assume I[iir#anon$21] <= R[iir#anon$21];
  assume R[iir#anon$21] <= C[iir#anon$21];
  assume 0 <= I[iir#anon$22];
  assume I[iir#anon$22] <= R[iir#anon$22];
  assume R[iir#anon$22] <= C[iir#anon$22];
  assume 0 <= I[iir#anon$23];
  assume I[iir#anon$23] <= R[iir#anon$23];
  assume R[iir#anon$23] <= C[iir#anon$23];
  assume I[iir#anon$23] == R[iir#anon$23];
  assume I[iir#anon$17] == I[iir#anon$8];
  assume I[iir#anon$18] == I[iir#anon$11];
  assume I[iir#anon$19] == I[iir#anon$14];
  assume I[iir#anon$20] == I[iir#anon$16];
  assume I[iir#anon$21] == I[iir#anon$17];
  assume I[iir#anon$21] == I[iir#anon$18];
  assume I[iir#anon$22] == I[iir#anon$19];
  assume I[iir#anon$22] == I[iir#anon$20];
  assume I[iir#anon$23] == I[iir#anon$21];
  assume I[iir#anon$23] == I[iir#anon$22];
  assume I[iir#anon$8] == I[iir#anon$7];
  assume I[iir#anon$9] == I[iir#anon$7];
  assume I[iir#anon$11] == I[iir#anon$10];
  assume I[iir#anon$12] == I[iir#anon$10];
  assume I[iir#anon$14] == I[iir#anon$13];
  assume I[iir#anon$15] == I[iir#anon$13];
  assume (C[iir#anon$10] == 0) ==> (AV#delay_1#data == 0);
  assume (C[iir#anon$10] > 0) ==> (AV#delay_1#data == M[iir#anon$9][R[iir#anon$9] - 1]);
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$10] > 0) ==> (M[iir#anon$10][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$10] - 0)) ==> (M[iir#anon$10][idx] == M[iir#anon$9][idx - 1])
  );
  assume (C[iir#anon$13] == 0) ==> (AV#delay_2#data == 0);
  assume (C[iir#anon$13] > 0) ==> (AV#delay_2#data == M[iir#anon$12][R[iir#anon$12] - 1]);
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$13] > 0) ==> (M[iir#anon$13][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$13] - 0)) ==> (M[iir#anon$13][idx] == M[iir#anon$12][idx - 1])
  );
  assume (C[iir#anon$16] == 0) ==> (AV#delay_3#data == 0);
  assume (C[iir#anon$16] > 0) ==> (AV#delay_3#data == M[iir#anon$15][R[iir#anon$15] - 1]);
  assume R[iir#anon$15] == C[iir#anon$16];
  assume (C[iir#anon$16] > 0) ==> (M[iir#anon$16][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$16] - 0)) ==> (M[iir#anon$16][idx] == M[iir#anon$15][idx - 1])
  );
  assume R[iir#anon$8] == C[iir#anon$17];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$17]) ==> (M[iir#anon$17][idx$] == (37 * M[iir#anon$8][idx$]))
  );
  assume R[iir#anon$11] == C[iir#anon$18];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$18]) ==> (M[iir#anon$18][idx$] == (109 * M[iir#anon$11][idx$]))
  );
  assume R[iir#anon$14] == C[iir#anon$19];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$19]) ==> (M[iir#anon$19][idx$] == (109 * M[iir#anon$14][idx$]))
  );
  assume R[iir#anon$16] == C[iir#anon$20];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$20]) ==> (M[iir#anon$20][idx$] == (37 * M[iir#anon$16][idx$]))
  );
  assume R[iir#anon$17] == C[iir#anon$21];
  assume R[iir#anon$18] == C[iir#anon$21];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$21]) ==> (M[iir#anon$21][idx$] == (M[iir#anon$17][idx$] + M[iir#anon$18][idx$]))
  );
  assume R[iir#anon$19] == C[iir#anon$22];
  assume R[iir#anon$20] == C[iir#anon$22];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$22]) ==> (M[iir#anon$22][idx$] == (M[iir#anon$19][idx$] + M[iir#anon$20][idx$]))
  );
  assume R[iir#anon$21] == C[iir#anon$23];
  assume R[iir#anon$22] == C[iir#anon$23];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$23]) ==> (M[iir#anon$23][idx$] == (M[iir#anon$21][idx$] + M[iir#anon$22][idx$]))
  );
  assume R[iir#anon$7] == C[iir#anon$8];
  assume R[iir#anon$7] == C[iir#anon$9];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$8]) ==> (M[iir#anon$8][idx$] == M[iir#anon$7][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$9]) ==> (M[iir#anon$9][idx$] == M[iir#anon$7][idx$])
  );
  assume R[iir#anon$10] == C[iir#anon$11];
  assume R[iir#anon$10] == C[iir#anon$12];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$11]) ==> (M[iir#anon$11][idx$] == M[iir#anon$10][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$12]) ==> (M[iir#anon$12][idx$] == M[iir#anon$10][idx$])
  );
  assume R[iir#anon$13] == C[iir#anon$14];
  assume R[iir#anon$13] == C[iir#anon$15];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$14]) ==> (M[iir#anon$14][idx$] == M[iir#anon$13][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$15]) ==> (M[iir#anon$15][idx$] == M[iir#anon$13][idx$])
  );
  assume (1 <= (C[iir#anon$21] - R[iir#anon$21])) && (1 <= (C[iir#anon$22] - R[iir#anon$22]));
  in1#i := M[iir#anon$21][R[iir#anon$21]];
  R[iir#anon$21] := R[iir#anon$21] + 1;
  in2#j := M[iir#anon$22][R[iir#anon$22]];
  R[iir#anon$22] := R[iir#anon$22] + 1;
  M[iir#anon$23][C[iir#anon$23]] := in1#i + in2#j;
  C[iir#anon$23] := C[iir#anon$23] + 1;
  assume (C[iir#anon$10] == 0) ==> (AV#delay_1#data == 0);
  assume (C[iir#anon$10] > 0) ==> (AV#delay_1#data == M[iir#anon$9][R[iir#anon$9] - 1]);
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$10] > 0) ==> (M[iir#anon$10][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$10] - 0)) ==> (M[iir#anon$10][idx] == M[iir#anon$9][idx - 1])
  );
  assume (C[iir#anon$13] == 0) ==> (AV#delay_2#data == 0);
  assume (C[iir#anon$13] > 0) ==> (AV#delay_2#data == M[iir#anon$12][R[iir#anon$12] - 1]);
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$13] > 0) ==> (M[iir#anon$13][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$13] - 0)) ==> (M[iir#anon$13][idx] == M[iir#anon$12][idx - 1])
  );
  assume (C[iir#anon$16] == 0) ==> (AV#delay_3#data == 0);
  assume (C[iir#anon$16] > 0) ==> (AV#delay_3#data == M[iir#anon$15][R[iir#anon$15] - 1]);
  assume R[iir#anon$15] == C[iir#anon$16];
  assume (C[iir#anon$16] > 0) ==> (M[iir#anon$16][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$16] - 0)) ==> (M[iir#anon$16][idx] == M[iir#anon$15][idx - 1])
  );
  assume R[iir#anon$8] == C[iir#anon$17];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$17]) ==> (M[iir#anon$17][idx$] == (37 * M[iir#anon$8][idx$]))
  );
  assume R[iir#anon$11] == C[iir#anon$18];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$18]) ==> (M[iir#anon$18][idx$] == (109 * M[iir#anon$11][idx$]))
  );
  assume R[iir#anon$14] == C[iir#anon$19];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$19]) ==> (M[iir#anon$19][idx$] == (109 * M[iir#anon$14][idx$]))
  );
  assume R[iir#anon$16] == C[iir#anon$20];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$20]) ==> (M[iir#anon$20][idx$] == (37 * M[iir#anon$16][idx$]))
  );
  assume R[iir#anon$17] == C[iir#anon$21];
  assume R[iir#anon$18] == C[iir#anon$21];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$21]) ==> (M[iir#anon$21][idx$] == (M[iir#anon$17][idx$] + M[iir#anon$18][idx$]))
  );
  assume R[iir#anon$19] == C[iir#anon$22];
  assume R[iir#anon$20] == C[iir#anon$22];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$22]) ==> (M[iir#anon$22][idx$] == (M[iir#anon$19][idx$] + M[iir#anon$20][idx$]))
  );
  assume R[iir#anon$21] == C[iir#anon$23];
  assume R[iir#anon$22] == C[iir#anon$23];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$23]) ==> (M[iir#anon$23][idx$] == (M[iir#anon$21][idx$] + M[iir#anon$22][idx$]))
  );
  assume R[iir#anon$7] == C[iir#anon$8];
  assume R[iir#anon$7] == C[iir#anon$9];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$8]) ==> (M[iir#anon$8][idx$] == M[iir#anon$7][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$9]) ==> (M[iir#anon$9][idx$] == M[iir#anon$7][idx$])
  );
  assume R[iir#anon$10] == C[iir#anon$11];
  assume R[iir#anon$10] == C[iir#anon$12];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$11]) ==> (M[iir#anon$11][idx$] == M[iir#anon$10][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$12]) ==> (M[iir#anon$12][idx$] == M[iir#anon$10][idx$])
  );
  assume R[iir#anon$13] == C[iir#anon$14];
  assume R[iir#anon$13] == C[iir#anon$15];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$14]) ==> (M[iir#anon$14][idx$] == M[iir#anon$13][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$15]) ==> (M[iir#anon$15][idx$] == M[iir#anon$13][idx$])
  );
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add_3' might not preserve the channel invariant (#209)"} I[iir#anon$17] == I[iir#anon$8];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add_3' might not preserve the channel invariant (#210)"} I[iir#anon$18] == I[iir#anon$11];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add_3' might not preserve the channel invariant (#211)"} I[iir#anon$19] == I[iir#anon$14];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add_3' might not preserve the channel invariant (#212)"} I[iir#anon$20] == I[iir#anon$16];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add_3' might not preserve the channel invariant (#213)"} I[iir#anon$21] == I[iir#anon$17];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add_3' might not preserve the channel invariant (#214)"} I[iir#anon$21] == I[iir#anon$18];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add_3' might not preserve the channel invariant (#215)"} I[iir#anon$22] == I[iir#anon$19];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add_3' might not preserve the channel invariant (#216)"} I[iir#anon$22] == I[iir#anon$20];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add_3' might not preserve the channel invariant (#217)"} I[iir#anon$23] == I[iir#anon$21];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add_3' might not preserve the channel invariant (#218)"} I[iir#anon$23] == I[iir#anon$22];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add_3' might not preserve the channel invariant (#219)"} I[iir#anon$8] == I[iir#anon$7];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add_3' might not preserve the channel invariant (#220)"} I[iir#anon$9] == I[iir#anon$7];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add_3' might not preserve the channel invariant (#221)"} I[iir#anon$11] == I[iir#anon$10];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add_3' might not preserve the channel invariant (#222)"} I[iir#anon$12] == I[iir#anon$10];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add_3' might not preserve the channel invariant (#223)"} I[iir#anon$14] == I[iir#anon$13];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add_3' might not preserve the channel invariant (#224)"} I[iir#anon$15] == I[iir#anon$13];
}
procedure iir##split#anon$5#21()
  modifies C, R, M, I, H;
{
  var iir#delay_1: Actor;
  var iir#delay_2: Actor;
  var iir#delay_3: Actor;
  var iir#mul_1: Actor;
  var iir#mul_2: Actor;
  var iir#mul_3: Actor;
  var iir#mul_4: Actor;
  var iir#add_1: Actor;
  var iir#add_2: Actor;
  var iir#add_3: Actor;
  var iir#spl_1: Actor;
  var iir#spl_2: Actor;
  var iir#spl_3: Actor;
  var iir#anon$7: Chan (int);
  var iir#anon$8: Chan (int);
  var iir#anon$9: Chan (int);
  var iir#anon$10: Chan (int);
  var iir#anon$11: Chan (int);
  var iir#anon$12: Chan (int);
  var iir#anon$13: Chan (int);
  var iir#anon$14: Chan (int);
  var iir#anon$15: Chan (int);
  var iir#anon$16: Chan (int);
  var iir#anon$17: Chan (int);
  var iir#anon$18: Chan (int);
  var iir#anon$19: Chan (int);
  var iir#anon$20: Chan (int);
  var iir#anon$21: Chan (int);
  var iir#anon$22: Chan (int);
  var iir#anon$23: Chan (int);
  var AV#delay_1#data: int;
  var AV#delay_1#y: int;
  var AV#delay_2#data: int;
  var AV#delay_2#y: int;
  var AV#delay_3#data: int;
  var AV#delay_3#y: int;
  var in#i: int;
  assume (iir#delay_1 != iir#delay_2) && (iir#delay_1 != iir#delay_3) && (iir#delay_1 != iir#mul_1) && (iir#delay_1 != iir#mul_2) && (iir#delay_1 != iir#mul_3) && (iir#delay_1 != iir#mul_4) && (iir#delay_1 != iir#add_1) && (iir#delay_1 != iir#add_2) && (iir#delay_1 != iir#add_3) && (iir#delay_1 != iir#spl_1) && (iir#delay_1 != iir#spl_2) && (iir#delay_1 != iir#spl_3) && (iir#delay_2 != iir#delay_3) && (iir#delay_2 != iir#mul_1) && (iir#delay_2 != iir#mul_2) && (iir#delay_2 != iir#mul_3) && (iir#delay_2 != iir#mul_4) && (iir#delay_2 != iir#add_1) && (iir#delay_2 != iir#add_2) && (iir#delay_2 != iir#add_3) && (iir#delay_2 != iir#spl_1) && (iir#delay_2 != iir#spl_2) && (iir#delay_2 != iir#spl_3) && (iir#delay_3 != iir#mul_1) && (iir#delay_3 != iir#mul_2) && (iir#delay_3 != iir#mul_3) && (iir#delay_3 != iir#mul_4) && (iir#delay_3 != iir#add_1) && (iir#delay_3 != iir#add_2) && (iir#delay_3 != iir#add_3) && (iir#delay_3 != iir#spl_1) && (iir#delay_3 != iir#spl_2) && (iir#delay_3 != iir#spl_3) && (iir#mul_1 != iir#mul_2) && (iir#mul_1 != iir#mul_3) && (iir#mul_1 != iir#mul_4) && (iir#mul_1 != iir#add_1) && (iir#mul_1 != iir#add_2) && (iir#mul_1 != iir#add_3) && (iir#mul_1 != iir#spl_1) && (iir#mul_1 != iir#spl_2) && (iir#mul_1 != iir#spl_3) && (iir#mul_2 != iir#mul_3) && (iir#mul_2 != iir#mul_4) && (iir#mul_2 != iir#add_1) && (iir#mul_2 != iir#add_2) && (iir#mul_2 != iir#add_3) && (iir#mul_2 != iir#spl_1) && (iir#mul_2 != iir#spl_2) && (iir#mul_2 != iir#spl_3) && (iir#mul_3 != iir#mul_4) && (iir#mul_3 != iir#add_1) && (iir#mul_3 != iir#add_2) && (iir#mul_3 != iir#add_3) && (iir#mul_3 != iir#spl_1) && (iir#mul_3 != iir#spl_2) && (iir#mul_3 != iir#spl_3) && (iir#mul_4 != iir#add_1) && (iir#mul_4 != iir#add_2) && (iir#mul_4 != iir#add_3) && (iir#mul_4 != iir#spl_1) && (iir#mul_4 != iir#spl_2) && (iir#mul_4 != iir#spl_3) && (iir#add_1 != iir#add_2) && (iir#add_1 != iir#add_3) && (iir#add_1 != iir#spl_1) && (iir#add_1 != iir#spl_2) && (iir#add_1 != iir#spl_3) && (iir#add_2 != iir#add_3) && (iir#add_2 != iir#spl_1) && (iir#add_2 != iir#spl_2) && (iir#add_2 != iir#spl_3) && (iir#add_3 != iir#spl_1) && (iir#add_3 != iir#spl_2) && (iir#add_3 != iir#spl_3) && (iir#spl_1 != iir#spl_2) && (iir#spl_1 != iir#spl_3) && (iir#spl_2 != iir#spl_3);
  assume (iir#anon$7 != iir#anon$8) && (iir#anon$7 != iir#anon$9) && (iir#anon$7 != iir#anon$10) && (iir#anon$7 != iir#anon$11) && (iir#anon$7 != iir#anon$12) && (iir#anon$7 != iir#anon$13) && (iir#anon$7 != iir#anon$14) && (iir#anon$7 != iir#anon$15) && (iir#anon$7 != iir#anon$16) && (iir#anon$7 != iir#anon$17) && (iir#anon$7 != iir#anon$18) && (iir#anon$7 != iir#anon$19) && (iir#anon$7 != iir#anon$20) && (iir#anon$7 != iir#anon$21) && (iir#anon$7 != iir#anon$22) && (iir#anon$7 != iir#anon$23) && (iir#anon$8 != iir#anon$9) && (iir#anon$8 != iir#anon$10) && (iir#anon$8 != iir#anon$11) && (iir#anon$8 != iir#anon$12) && (iir#anon$8 != iir#anon$13) && (iir#anon$8 != iir#anon$14) && (iir#anon$8 != iir#anon$15) && (iir#anon$8 != iir#anon$16) && (iir#anon$8 != iir#anon$17) && (iir#anon$8 != iir#anon$18) && (iir#anon$8 != iir#anon$19) && (iir#anon$8 != iir#anon$20) && (iir#anon$8 != iir#anon$21) && (iir#anon$8 != iir#anon$22) && (iir#anon$8 != iir#anon$23) && (iir#anon$9 != iir#anon$10) && (iir#anon$9 != iir#anon$11) && (iir#anon$9 != iir#anon$12) && (iir#anon$9 != iir#anon$13) && (iir#anon$9 != iir#anon$14) && (iir#anon$9 != iir#anon$15) && (iir#anon$9 != iir#anon$16) && (iir#anon$9 != iir#anon$17) && (iir#anon$9 != iir#anon$18) && (iir#anon$9 != iir#anon$19) && (iir#anon$9 != iir#anon$20) && (iir#anon$9 != iir#anon$21) && (iir#anon$9 != iir#anon$22) && (iir#anon$9 != iir#anon$23) && (iir#anon$10 != iir#anon$11) && (iir#anon$10 != iir#anon$12) && (iir#anon$10 != iir#anon$13) && (iir#anon$10 != iir#anon$14) && (iir#anon$10 != iir#anon$15) && (iir#anon$10 != iir#anon$16) && (iir#anon$10 != iir#anon$17) && (iir#anon$10 != iir#anon$18) && (iir#anon$10 != iir#anon$19) && (iir#anon$10 != iir#anon$20) && (iir#anon$10 != iir#anon$21) && (iir#anon$10 != iir#anon$22) && (iir#anon$10 != iir#anon$23) && (iir#anon$11 != iir#anon$12) && (iir#anon$11 != iir#anon$13) && (iir#anon$11 != iir#anon$14) && (iir#anon$11 != iir#anon$15) && (iir#anon$11 != iir#anon$16) && (iir#anon$11 != iir#anon$17) && (iir#anon$11 != iir#anon$18) && (iir#anon$11 != iir#anon$19) && (iir#anon$11 != iir#anon$20) && (iir#anon$11 != iir#anon$21) && (iir#anon$11 != iir#anon$22) && (iir#anon$11 != iir#anon$23) && (iir#anon$12 != iir#anon$13) && (iir#anon$12 != iir#anon$14) && (iir#anon$12 != iir#anon$15) && (iir#anon$12 != iir#anon$16) && (iir#anon$12 != iir#anon$17) && (iir#anon$12 != iir#anon$18) && (iir#anon$12 != iir#anon$19) && (iir#anon$12 != iir#anon$20) && (iir#anon$12 != iir#anon$21) && (iir#anon$12 != iir#anon$22) && (iir#anon$12 != iir#anon$23) && (iir#anon$13 != iir#anon$14) && (iir#anon$13 != iir#anon$15) && (iir#anon$13 != iir#anon$16) && (iir#anon$13 != iir#anon$17) && (iir#anon$13 != iir#anon$18) && (iir#anon$13 != iir#anon$19) && (iir#anon$13 != iir#anon$20) && (iir#anon$13 != iir#anon$21) && (iir#anon$13 != iir#anon$22) && (iir#anon$13 != iir#anon$23) && (iir#anon$14 != iir#anon$15) && (iir#anon$14 != iir#anon$16) && (iir#anon$14 != iir#anon$17) && (iir#anon$14 != iir#anon$18) && (iir#anon$14 != iir#anon$19) && (iir#anon$14 != iir#anon$20) && (iir#anon$14 != iir#anon$21) && (iir#anon$14 != iir#anon$22) && (iir#anon$14 != iir#anon$23) && (iir#anon$15 != iir#anon$16) && (iir#anon$15 != iir#anon$17) && (iir#anon$15 != iir#anon$18) && (iir#anon$15 != iir#anon$19) && (iir#anon$15 != iir#anon$20) && (iir#anon$15 != iir#anon$21) && (iir#anon$15 != iir#anon$22) && (iir#anon$15 != iir#anon$23) && (iir#anon$16 != iir#anon$17) && (iir#anon$16 != iir#anon$18) && (iir#anon$16 != iir#anon$19) && (iir#anon$16 != iir#anon$20) && (iir#anon$16 != iir#anon$21) && (iir#anon$16 != iir#anon$22) && (iir#anon$16 != iir#anon$23) && (iir#anon$17 != iir#anon$18) && (iir#anon$17 != iir#anon$19) && (iir#anon$17 != iir#anon$20) && (iir#anon$17 != iir#anon$21) && (iir#anon$17 != iir#anon$22) && (iir#anon$17 != iir#anon$23) && (iir#anon$18 != iir#anon$19) && (iir#anon$18 != iir#anon$20) && (iir#anon$18 != iir#anon$21) && (iir#anon$18 != iir#anon$22) && (iir#anon$18 != iir#anon$23) && (iir#anon$19 != iir#anon$20) && (iir#anon$19 != iir#anon$21) && (iir#anon$19 != iir#anon$22) && (iir#anon$19 != iir#anon$23) && (iir#anon$20 != iir#anon$21) && (iir#anon$20 != iir#anon$22) && (iir#anon$20 != iir#anon$23) && (iir#anon$21 != iir#anon$22) && (iir#anon$21 != iir#anon$23) && (iir#anon$22 != iir#anon$23);
  assume 0 <= I[iir#anon$7];
  assume I[iir#anon$7] <= R[iir#anon$7];
  assume R[iir#anon$7] <= C[iir#anon$7];
  assume 0 <= I[iir#anon$8];
  assume I[iir#anon$8] <= R[iir#anon$8];
  assume R[iir#anon$8] <= C[iir#anon$8];
  assume 0 <= I[iir#anon$9];
  assume I[iir#anon$9] <= R[iir#anon$9];
  assume R[iir#anon$9] <= C[iir#anon$9];
  assume 0 <= I[iir#anon$10];
  assume I[iir#anon$10] <= R[iir#anon$10];
  assume R[iir#anon$10] <= C[iir#anon$10];
  assume 0 <= I[iir#anon$11];
  assume I[iir#anon$11] <= R[iir#anon$11];
  assume R[iir#anon$11] <= C[iir#anon$11];
  assume 0 <= I[iir#anon$12];
  assume I[iir#anon$12] <= R[iir#anon$12];
  assume R[iir#anon$12] <= C[iir#anon$12];
  assume 0 <= I[iir#anon$13];
  assume I[iir#anon$13] <= R[iir#anon$13];
  assume R[iir#anon$13] <= C[iir#anon$13];
  assume 0 <= I[iir#anon$14];
  assume I[iir#anon$14] <= R[iir#anon$14];
  assume R[iir#anon$14] <= C[iir#anon$14];
  assume 0 <= I[iir#anon$15];
  assume I[iir#anon$15] <= R[iir#anon$15];
  assume R[iir#anon$15] <= C[iir#anon$15];
  assume 0 <= I[iir#anon$16];
  assume I[iir#anon$16] <= R[iir#anon$16];
  assume R[iir#anon$16] <= C[iir#anon$16];
  assume 0 <= I[iir#anon$17];
  assume I[iir#anon$17] <= R[iir#anon$17];
  assume R[iir#anon$17] <= C[iir#anon$17];
  assume 0 <= I[iir#anon$18];
  assume I[iir#anon$18] <= R[iir#anon$18];
  assume R[iir#anon$18] <= C[iir#anon$18];
  assume 0 <= I[iir#anon$19];
  assume I[iir#anon$19] <= R[iir#anon$19];
  assume R[iir#anon$19] <= C[iir#anon$19];
  assume 0 <= I[iir#anon$20];
  assume I[iir#anon$20] <= R[iir#anon$20];
  assume R[iir#anon$20] <= C[iir#anon$20];
  assume 0 <= I[iir#anon$21];
  assume I[iir#anon$21] <= R[iir#anon$21];
  assume R[iir#anon$21] <= C[iir#anon$21];
  assume 0 <= I[iir#anon$22];
  assume I[iir#anon$22] <= R[iir#anon$22];
  assume R[iir#anon$22] <= C[iir#anon$22];
  assume 0 <= I[iir#anon$23];
  assume I[iir#anon$23] <= R[iir#anon$23];
  assume R[iir#anon$23] <= C[iir#anon$23];
  assume I[iir#anon$23] == R[iir#anon$23];
  assume I[iir#anon$17] == I[iir#anon$8];
  assume I[iir#anon$18] == I[iir#anon$11];
  assume I[iir#anon$19] == I[iir#anon$14];
  assume I[iir#anon$20] == I[iir#anon$16];
  assume I[iir#anon$21] == I[iir#anon$17];
  assume I[iir#anon$21] == I[iir#anon$18];
  assume I[iir#anon$22] == I[iir#anon$19];
  assume I[iir#anon$22] == I[iir#anon$20];
  assume I[iir#anon$23] == I[iir#anon$21];
  assume I[iir#anon$23] == I[iir#anon$22];
  assume I[iir#anon$8] == I[iir#anon$7];
  assume I[iir#anon$9] == I[iir#anon$7];
  assume I[iir#anon$11] == I[iir#anon$10];
  assume I[iir#anon$12] == I[iir#anon$10];
  assume I[iir#anon$14] == I[iir#anon$13];
  assume I[iir#anon$15] == I[iir#anon$13];
  assume (C[iir#anon$10] == 0) ==> (AV#delay_1#data == 0);
  assume (C[iir#anon$10] > 0) ==> (AV#delay_1#data == M[iir#anon$9][R[iir#anon$9] - 1]);
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$10] > 0) ==> (M[iir#anon$10][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$10] - 0)) ==> (M[iir#anon$10][idx] == M[iir#anon$9][idx - 1])
  );
  assume (C[iir#anon$13] == 0) ==> (AV#delay_2#data == 0);
  assume (C[iir#anon$13] > 0) ==> (AV#delay_2#data == M[iir#anon$12][R[iir#anon$12] - 1]);
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$13] > 0) ==> (M[iir#anon$13][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$13] - 0)) ==> (M[iir#anon$13][idx] == M[iir#anon$12][idx - 1])
  );
  assume (C[iir#anon$16] == 0) ==> (AV#delay_3#data == 0);
  assume (C[iir#anon$16] > 0) ==> (AV#delay_3#data == M[iir#anon$15][R[iir#anon$15] - 1]);
  assume R[iir#anon$15] == C[iir#anon$16];
  assume (C[iir#anon$16] > 0) ==> (M[iir#anon$16][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$16] - 0)) ==> (M[iir#anon$16][idx] == M[iir#anon$15][idx - 1])
  );
  assume R[iir#anon$8] == C[iir#anon$17];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$17]) ==> (M[iir#anon$17][idx$] == (37 * M[iir#anon$8][idx$]))
  );
  assume R[iir#anon$11] == C[iir#anon$18];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$18]) ==> (M[iir#anon$18][idx$] == (109 * M[iir#anon$11][idx$]))
  );
  assume R[iir#anon$14] == C[iir#anon$19];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$19]) ==> (M[iir#anon$19][idx$] == (109 * M[iir#anon$14][idx$]))
  );
  assume R[iir#anon$16] == C[iir#anon$20];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$20]) ==> (M[iir#anon$20][idx$] == (37 * M[iir#anon$16][idx$]))
  );
  assume R[iir#anon$17] == C[iir#anon$21];
  assume R[iir#anon$18] == C[iir#anon$21];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$21]) ==> (M[iir#anon$21][idx$] == (M[iir#anon$17][idx$] + M[iir#anon$18][idx$]))
  );
  assume R[iir#anon$19] == C[iir#anon$22];
  assume R[iir#anon$20] == C[iir#anon$22];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$22]) ==> (M[iir#anon$22][idx$] == (M[iir#anon$19][idx$] + M[iir#anon$20][idx$]))
  );
  assume R[iir#anon$21] == C[iir#anon$23];
  assume R[iir#anon$22] == C[iir#anon$23];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$23]) ==> (M[iir#anon$23][idx$] == (M[iir#anon$21][idx$] + M[iir#anon$22][idx$]))
  );
  assume R[iir#anon$7] == C[iir#anon$8];
  assume R[iir#anon$7] == C[iir#anon$9];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$8]) ==> (M[iir#anon$8][idx$] == M[iir#anon$7][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$9]) ==> (M[iir#anon$9][idx$] == M[iir#anon$7][idx$])
  );
  assume R[iir#anon$10] == C[iir#anon$11];
  assume R[iir#anon$10] == C[iir#anon$12];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$11]) ==> (M[iir#anon$11][idx$] == M[iir#anon$10][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$12]) ==> (M[iir#anon$12][idx$] == M[iir#anon$10][idx$])
  );
  assume R[iir#anon$13] == C[iir#anon$14];
  assume R[iir#anon$13] == C[iir#anon$15];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$14]) ==> (M[iir#anon$14][idx$] == M[iir#anon$13][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$15]) ==> (M[iir#anon$15][idx$] == M[iir#anon$13][idx$])
  );
  assume 1 <= (C[iir#anon$7] - R[iir#anon$7]);
  in#i := M[iir#anon$7][R[iir#anon$7]];
  R[iir#anon$7] := R[iir#anon$7] + 1;
  M[iir#anon$8][C[iir#anon$8]] := in#i;
  C[iir#anon$8] := C[iir#anon$8] + 1;
  M[iir#anon$9][C[iir#anon$9]] := in#i;
  C[iir#anon$9] := C[iir#anon$9] + 1;
  assume (C[iir#anon$10] == 0) ==> (AV#delay_1#data == 0);
  assume (C[iir#anon$10] > 0) ==> (AV#delay_1#data == M[iir#anon$9][R[iir#anon$9] - 1]);
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$10] > 0) ==> (M[iir#anon$10][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$10] - 0)) ==> (M[iir#anon$10][idx] == M[iir#anon$9][idx - 1])
  );
  assume (C[iir#anon$13] == 0) ==> (AV#delay_2#data == 0);
  assume (C[iir#anon$13] > 0) ==> (AV#delay_2#data == M[iir#anon$12][R[iir#anon$12] - 1]);
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$13] > 0) ==> (M[iir#anon$13][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$13] - 0)) ==> (M[iir#anon$13][idx] == M[iir#anon$12][idx - 1])
  );
  assume (C[iir#anon$16] == 0) ==> (AV#delay_3#data == 0);
  assume (C[iir#anon$16] > 0) ==> (AV#delay_3#data == M[iir#anon$15][R[iir#anon$15] - 1]);
  assume R[iir#anon$15] == C[iir#anon$16];
  assume (C[iir#anon$16] > 0) ==> (M[iir#anon$16][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$16] - 0)) ==> (M[iir#anon$16][idx] == M[iir#anon$15][idx - 1])
  );
  assume R[iir#anon$8] == C[iir#anon$17];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$17]) ==> (M[iir#anon$17][idx$] == (37 * M[iir#anon$8][idx$]))
  );
  assume R[iir#anon$11] == C[iir#anon$18];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$18]) ==> (M[iir#anon$18][idx$] == (109 * M[iir#anon$11][idx$]))
  );
  assume R[iir#anon$14] == C[iir#anon$19];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$19]) ==> (M[iir#anon$19][idx$] == (109 * M[iir#anon$14][idx$]))
  );
  assume R[iir#anon$16] == C[iir#anon$20];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$20]) ==> (M[iir#anon$20][idx$] == (37 * M[iir#anon$16][idx$]))
  );
  assume R[iir#anon$17] == C[iir#anon$21];
  assume R[iir#anon$18] == C[iir#anon$21];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$21]) ==> (M[iir#anon$21][idx$] == (M[iir#anon$17][idx$] + M[iir#anon$18][idx$]))
  );
  assume R[iir#anon$19] == C[iir#anon$22];
  assume R[iir#anon$20] == C[iir#anon$22];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$22]) ==> (M[iir#anon$22][idx$] == (M[iir#anon$19][idx$] + M[iir#anon$20][idx$]))
  );
  assume R[iir#anon$21] == C[iir#anon$23];
  assume R[iir#anon$22] == C[iir#anon$23];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$23]) ==> (M[iir#anon$23][idx$] == (M[iir#anon$21][idx$] + M[iir#anon$22][idx$]))
  );
  assume R[iir#anon$7] == C[iir#anon$8];
  assume R[iir#anon$7] == C[iir#anon$9];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$8]) ==> (M[iir#anon$8][idx$] == M[iir#anon$7][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$9]) ==> (M[iir#anon$9][idx$] == M[iir#anon$7][idx$])
  );
  assume R[iir#anon$10] == C[iir#anon$11];
  assume R[iir#anon$10] == C[iir#anon$12];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$11]) ==> (M[iir#anon$11][idx$] == M[iir#anon$10][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$12]) ==> (M[iir#anon$12][idx$] == M[iir#anon$10][idx$])
  );
  assume R[iir#anon$13] == C[iir#anon$14];
  assume R[iir#anon$13] == C[iir#anon$15];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$14]) ==> (M[iir#anon$14][idx$] == M[iir#anon$13][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$15]) ==> (M[iir#anon$15][idx$] == M[iir#anon$13][idx$])
  );
  assert {:msg "Action at 32.3 ('anon$5') for actor instance 'spl_1' might not preserve the channel invariant (#225)"} I[iir#anon$17] == I[iir#anon$8];
  assert {:msg "Action at 32.3 ('anon$5') for actor instance 'spl_1' might not preserve the channel invariant (#226)"} I[iir#anon$18] == I[iir#anon$11];
  assert {:msg "Action at 32.3 ('anon$5') for actor instance 'spl_1' might not preserve the channel invariant (#227)"} I[iir#anon$19] == I[iir#anon$14];
  assert {:msg "Action at 32.3 ('anon$5') for actor instance 'spl_1' might not preserve the channel invariant (#228)"} I[iir#anon$20] == I[iir#anon$16];
  assert {:msg "Action at 32.3 ('anon$5') for actor instance 'spl_1' might not preserve the channel invariant (#229)"} I[iir#anon$21] == I[iir#anon$17];
  assert {:msg "Action at 32.3 ('anon$5') for actor instance 'spl_1' might not preserve the channel invariant (#230)"} I[iir#anon$21] == I[iir#anon$18];
  assert {:msg "Action at 32.3 ('anon$5') for actor instance 'spl_1' might not preserve the channel invariant (#231)"} I[iir#anon$22] == I[iir#anon$19];
  assert {:msg "Action at 32.3 ('anon$5') for actor instance 'spl_1' might not preserve the channel invariant (#232)"} I[iir#anon$22] == I[iir#anon$20];
  assert {:msg "Action at 32.3 ('anon$5') for actor instance 'spl_1' might not preserve the channel invariant (#233)"} I[iir#anon$23] == I[iir#anon$21];
  assert {:msg "Action at 32.3 ('anon$5') for actor instance 'spl_1' might not preserve the channel invariant (#234)"} I[iir#anon$23] == I[iir#anon$22];
  assert {:msg "Action at 32.3 ('anon$5') for actor instance 'spl_1' might not preserve the channel invariant (#235)"} I[iir#anon$8] == I[iir#anon$7];
  assert {:msg "Action at 32.3 ('anon$5') for actor instance 'spl_1' might not preserve the channel invariant (#236)"} I[iir#anon$9] == I[iir#anon$7];
  assert {:msg "Action at 32.3 ('anon$5') for actor instance 'spl_1' might not preserve the channel invariant (#237)"} I[iir#anon$11] == I[iir#anon$10];
  assert {:msg "Action at 32.3 ('anon$5') for actor instance 'spl_1' might not preserve the channel invariant (#238)"} I[iir#anon$12] == I[iir#anon$10];
  assert {:msg "Action at 32.3 ('anon$5') for actor instance 'spl_1' might not preserve the channel invariant (#239)"} I[iir#anon$14] == I[iir#anon$13];
  assert {:msg "Action at 32.3 ('anon$5') for actor instance 'spl_1' might not preserve the channel invariant (#240)"} I[iir#anon$15] == I[iir#anon$13];
}
procedure iir##split#anon$5#22()
  modifies C, R, M, I, H;
{
  var iir#delay_1: Actor;
  var iir#delay_2: Actor;
  var iir#delay_3: Actor;
  var iir#mul_1: Actor;
  var iir#mul_2: Actor;
  var iir#mul_3: Actor;
  var iir#mul_4: Actor;
  var iir#add_1: Actor;
  var iir#add_2: Actor;
  var iir#add_3: Actor;
  var iir#spl_1: Actor;
  var iir#spl_2: Actor;
  var iir#spl_3: Actor;
  var iir#anon$7: Chan (int);
  var iir#anon$8: Chan (int);
  var iir#anon$9: Chan (int);
  var iir#anon$10: Chan (int);
  var iir#anon$11: Chan (int);
  var iir#anon$12: Chan (int);
  var iir#anon$13: Chan (int);
  var iir#anon$14: Chan (int);
  var iir#anon$15: Chan (int);
  var iir#anon$16: Chan (int);
  var iir#anon$17: Chan (int);
  var iir#anon$18: Chan (int);
  var iir#anon$19: Chan (int);
  var iir#anon$20: Chan (int);
  var iir#anon$21: Chan (int);
  var iir#anon$22: Chan (int);
  var iir#anon$23: Chan (int);
  var AV#delay_1#data: int;
  var AV#delay_1#y: int;
  var AV#delay_2#data: int;
  var AV#delay_2#y: int;
  var AV#delay_3#data: int;
  var AV#delay_3#y: int;
  var in#i: int;
  assume (iir#delay_1 != iir#delay_2) && (iir#delay_1 != iir#delay_3) && (iir#delay_1 != iir#mul_1) && (iir#delay_1 != iir#mul_2) && (iir#delay_1 != iir#mul_3) && (iir#delay_1 != iir#mul_4) && (iir#delay_1 != iir#add_1) && (iir#delay_1 != iir#add_2) && (iir#delay_1 != iir#add_3) && (iir#delay_1 != iir#spl_1) && (iir#delay_1 != iir#spl_2) && (iir#delay_1 != iir#spl_3) && (iir#delay_2 != iir#delay_3) && (iir#delay_2 != iir#mul_1) && (iir#delay_2 != iir#mul_2) && (iir#delay_2 != iir#mul_3) && (iir#delay_2 != iir#mul_4) && (iir#delay_2 != iir#add_1) && (iir#delay_2 != iir#add_2) && (iir#delay_2 != iir#add_3) && (iir#delay_2 != iir#spl_1) && (iir#delay_2 != iir#spl_2) && (iir#delay_2 != iir#spl_3) && (iir#delay_3 != iir#mul_1) && (iir#delay_3 != iir#mul_2) && (iir#delay_3 != iir#mul_3) && (iir#delay_3 != iir#mul_4) && (iir#delay_3 != iir#add_1) && (iir#delay_3 != iir#add_2) && (iir#delay_3 != iir#add_3) && (iir#delay_3 != iir#spl_1) && (iir#delay_3 != iir#spl_2) && (iir#delay_3 != iir#spl_3) && (iir#mul_1 != iir#mul_2) && (iir#mul_1 != iir#mul_3) && (iir#mul_1 != iir#mul_4) && (iir#mul_1 != iir#add_1) && (iir#mul_1 != iir#add_2) && (iir#mul_1 != iir#add_3) && (iir#mul_1 != iir#spl_1) && (iir#mul_1 != iir#spl_2) && (iir#mul_1 != iir#spl_3) && (iir#mul_2 != iir#mul_3) && (iir#mul_2 != iir#mul_4) && (iir#mul_2 != iir#add_1) && (iir#mul_2 != iir#add_2) && (iir#mul_2 != iir#add_3) && (iir#mul_2 != iir#spl_1) && (iir#mul_2 != iir#spl_2) && (iir#mul_2 != iir#spl_3) && (iir#mul_3 != iir#mul_4) && (iir#mul_3 != iir#add_1) && (iir#mul_3 != iir#add_2) && (iir#mul_3 != iir#add_3) && (iir#mul_3 != iir#spl_1) && (iir#mul_3 != iir#spl_2) && (iir#mul_3 != iir#spl_3) && (iir#mul_4 != iir#add_1) && (iir#mul_4 != iir#add_2) && (iir#mul_4 != iir#add_3) && (iir#mul_4 != iir#spl_1) && (iir#mul_4 != iir#spl_2) && (iir#mul_4 != iir#spl_3) && (iir#add_1 != iir#add_2) && (iir#add_1 != iir#add_3) && (iir#add_1 != iir#spl_1) && (iir#add_1 != iir#spl_2) && (iir#add_1 != iir#spl_3) && (iir#add_2 != iir#add_3) && (iir#add_2 != iir#spl_1) && (iir#add_2 != iir#spl_2) && (iir#add_2 != iir#spl_3) && (iir#add_3 != iir#spl_1) && (iir#add_3 != iir#spl_2) && (iir#add_3 != iir#spl_3) && (iir#spl_1 != iir#spl_2) && (iir#spl_1 != iir#spl_3) && (iir#spl_2 != iir#spl_3);
  assume (iir#anon$7 != iir#anon$8) && (iir#anon$7 != iir#anon$9) && (iir#anon$7 != iir#anon$10) && (iir#anon$7 != iir#anon$11) && (iir#anon$7 != iir#anon$12) && (iir#anon$7 != iir#anon$13) && (iir#anon$7 != iir#anon$14) && (iir#anon$7 != iir#anon$15) && (iir#anon$7 != iir#anon$16) && (iir#anon$7 != iir#anon$17) && (iir#anon$7 != iir#anon$18) && (iir#anon$7 != iir#anon$19) && (iir#anon$7 != iir#anon$20) && (iir#anon$7 != iir#anon$21) && (iir#anon$7 != iir#anon$22) && (iir#anon$7 != iir#anon$23) && (iir#anon$8 != iir#anon$9) && (iir#anon$8 != iir#anon$10) && (iir#anon$8 != iir#anon$11) && (iir#anon$8 != iir#anon$12) && (iir#anon$8 != iir#anon$13) && (iir#anon$8 != iir#anon$14) && (iir#anon$8 != iir#anon$15) && (iir#anon$8 != iir#anon$16) && (iir#anon$8 != iir#anon$17) && (iir#anon$8 != iir#anon$18) && (iir#anon$8 != iir#anon$19) && (iir#anon$8 != iir#anon$20) && (iir#anon$8 != iir#anon$21) && (iir#anon$8 != iir#anon$22) && (iir#anon$8 != iir#anon$23) && (iir#anon$9 != iir#anon$10) && (iir#anon$9 != iir#anon$11) && (iir#anon$9 != iir#anon$12) && (iir#anon$9 != iir#anon$13) && (iir#anon$9 != iir#anon$14) && (iir#anon$9 != iir#anon$15) && (iir#anon$9 != iir#anon$16) && (iir#anon$9 != iir#anon$17) && (iir#anon$9 != iir#anon$18) && (iir#anon$9 != iir#anon$19) && (iir#anon$9 != iir#anon$20) && (iir#anon$9 != iir#anon$21) && (iir#anon$9 != iir#anon$22) && (iir#anon$9 != iir#anon$23) && (iir#anon$10 != iir#anon$11) && (iir#anon$10 != iir#anon$12) && (iir#anon$10 != iir#anon$13) && (iir#anon$10 != iir#anon$14) && (iir#anon$10 != iir#anon$15) && (iir#anon$10 != iir#anon$16) && (iir#anon$10 != iir#anon$17) && (iir#anon$10 != iir#anon$18) && (iir#anon$10 != iir#anon$19) && (iir#anon$10 != iir#anon$20) && (iir#anon$10 != iir#anon$21) && (iir#anon$10 != iir#anon$22) && (iir#anon$10 != iir#anon$23) && (iir#anon$11 != iir#anon$12) && (iir#anon$11 != iir#anon$13) && (iir#anon$11 != iir#anon$14) && (iir#anon$11 != iir#anon$15) && (iir#anon$11 != iir#anon$16) && (iir#anon$11 != iir#anon$17) && (iir#anon$11 != iir#anon$18) && (iir#anon$11 != iir#anon$19) && (iir#anon$11 != iir#anon$20) && (iir#anon$11 != iir#anon$21) && (iir#anon$11 != iir#anon$22) && (iir#anon$11 != iir#anon$23) && (iir#anon$12 != iir#anon$13) && (iir#anon$12 != iir#anon$14) && (iir#anon$12 != iir#anon$15) && (iir#anon$12 != iir#anon$16) && (iir#anon$12 != iir#anon$17) && (iir#anon$12 != iir#anon$18) && (iir#anon$12 != iir#anon$19) && (iir#anon$12 != iir#anon$20) && (iir#anon$12 != iir#anon$21) && (iir#anon$12 != iir#anon$22) && (iir#anon$12 != iir#anon$23) && (iir#anon$13 != iir#anon$14) && (iir#anon$13 != iir#anon$15) && (iir#anon$13 != iir#anon$16) && (iir#anon$13 != iir#anon$17) && (iir#anon$13 != iir#anon$18) && (iir#anon$13 != iir#anon$19) && (iir#anon$13 != iir#anon$20) && (iir#anon$13 != iir#anon$21) && (iir#anon$13 != iir#anon$22) && (iir#anon$13 != iir#anon$23) && (iir#anon$14 != iir#anon$15) && (iir#anon$14 != iir#anon$16) && (iir#anon$14 != iir#anon$17) && (iir#anon$14 != iir#anon$18) && (iir#anon$14 != iir#anon$19) && (iir#anon$14 != iir#anon$20) && (iir#anon$14 != iir#anon$21) && (iir#anon$14 != iir#anon$22) && (iir#anon$14 != iir#anon$23) && (iir#anon$15 != iir#anon$16) && (iir#anon$15 != iir#anon$17) && (iir#anon$15 != iir#anon$18) && (iir#anon$15 != iir#anon$19) && (iir#anon$15 != iir#anon$20) && (iir#anon$15 != iir#anon$21) && (iir#anon$15 != iir#anon$22) && (iir#anon$15 != iir#anon$23) && (iir#anon$16 != iir#anon$17) && (iir#anon$16 != iir#anon$18) && (iir#anon$16 != iir#anon$19) && (iir#anon$16 != iir#anon$20) && (iir#anon$16 != iir#anon$21) && (iir#anon$16 != iir#anon$22) && (iir#anon$16 != iir#anon$23) && (iir#anon$17 != iir#anon$18) && (iir#anon$17 != iir#anon$19) && (iir#anon$17 != iir#anon$20) && (iir#anon$17 != iir#anon$21) && (iir#anon$17 != iir#anon$22) && (iir#anon$17 != iir#anon$23) && (iir#anon$18 != iir#anon$19) && (iir#anon$18 != iir#anon$20) && (iir#anon$18 != iir#anon$21) && (iir#anon$18 != iir#anon$22) && (iir#anon$18 != iir#anon$23) && (iir#anon$19 != iir#anon$20) && (iir#anon$19 != iir#anon$21) && (iir#anon$19 != iir#anon$22) && (iir#anon$19 != iir#anon$23) && (iir#anon$20 != iir#anon$21) && (iir#anon$20 != iir#anon$22) && (iir#anon$20 != iir#anon$23) && (iir#anon$21 != iir#anon$22) && (iir#anon$21 != iir#anon$23) && (iir#anon$22 != iir#anon$23);
  assume 0 <= I[iir#anon$7];
  assume I[iir#anon$7] <= R[iir#anon$7];
  assume R[iir#anon$7] <= C[iir#anon$7];
  assume 0 <= I[iir#anon$8];
  assume I[iir#anon$8] <= R[iir#anon$8];
  assume R[iir#anon$8] <= C[iir#anon$8];
  assume 0 <= I[iir#anon$9];
  assume I[iir#anon$9] <= R[iir#anon$9];
  assume R[iir#anon$9] <= C[iir#anon$9];
  assume 0 <= I[iir#anon$10];
  assume I[iir#anon$10] <= R[iir#anon$10];
  assume R[iir#anon$10] <= C[iir#anon$10];
  assume 0 <= I[iir#anon$11];
  assume I[iir#anon$11] <= R[iir#anon$11];
  assume R[iir#anon$11] <= C[iir#anon$11];
  assume 0 <= I[iir#anon$12];
  assume I[iir#anon$12] <= R[iir#anon$12];
  assume R[iir#anon$12] <= C[iir#anon$12];
  assume 0 <= I[iir#anon$13];
  assume I[iir#anon$13] <= R[iir#anon$13];
  assume R[iir#anon$13] <= C[iir#anon$13];
  assume 0 <= I[iir#anon$14];
  assume I[iir#anon$14] <= R[iir#anon$14];
  assume R[iir#anon$14] <= C[iir#anon$14];
  assume 0 <= I[iir#anon$15];
  assume I[iir#anon$15] <= R[iir#anon$15];
  assume R[iir#anon$15] <= C[iir#anon$15];
  assume 0 <= I[iir#anon$16];
  assume I[iir#anon$16] <= R[iir#anon$16];
  assume R[iir#anon$16] <= C[iir#anon$16];
  assume 0 <= I[iir#anon$17];
  assume I[iir#anon$17] <= R[iir#anon$17];
  assume R[iir#anon$17] <= C[iir#anon$17];
  assume 0 <= I[iir#anon$18];
  assume I[iir#anon$18] <= R[iir#anon$18];
  assume R[iir#anon$18] <= C[iir#anon$18];
  assume 0 <= I[iir#anon$19];
  assume I[iir#anon$19] <= R[iir#anon$19];
  assume R[iir#anon$19] <= C[iir#anon$19];
  assume 0 <= I[iir#anon$20];
  assume I[iir#anon$20] <= R[iir#anon$20];
  assume R[iir#anon$20] <= C[iir#anon$20];
  assume 0 <= I[iir#anon$21];
  assume I[iir#anon$21] <= R[iir#anon$21];
  assume R[iir#anon$21] <= C[iir#anon$21];
  assume 0 <= I[iir#anon$22];
  assume I[iir#anon$22] <= R[iir#anon$22];
  assume R[iir#anon$22] <= C[iir#anon$22];
  assume 0 <= I[iir#anon$23];
  assume I[iir#anon$23] <= R[iir#anon$23];
  assume R[iir#anon$23] <= C[iir#anon$23];
  assume I[iir#anon$23] == R[iir#anon$23];
  assume I[iir#anon$17] == I[iir#anon$8];
  assume I[iir#anon$18] == I[iir#anon$11];
  assume I[iir#anon$19] == I[iir#anon$14];
  assume I[iir#anon$20] == I[iir#anon$16];
  assume I[iir#anon$21] == I[iir#anon$17];
  assume I[iir#anon$21] == I[iir#anon$18];
  assume I[iir#anon$22] == I[iir#anon$19];
  assume I[iir#anon$22] == I[iir#anon$20];
  assume I[iir#anon$23] == I[iir#anon$21];
  assume I[iir#anon$23] == I[iir#anon$22];
  assume I[iir#anon$8] == I[iir#anon$7];
  assume I[iir#anon$9] == I[iir#anon$7];
  assume I[iir#anon$11] == I[iir#anon$10];
  assume I[iir#anon$12] == I[iir#anon$10];
  assume I[iir#anon$14] == I[iir#anon$13];
  assume I[iir#anon$15] == I[iir#anon$13];
  assume (C[iir#anon$10] == 0) ==> (AV#delay_1#data == 0);
  assume (C[iir#anon$10] > 0) ==> (AV#delay_1#data == M[iir#anon$9][R[iir#anon$9] - 1]);
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$10] > 0) ==> (M[iir#anon$10][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$10] - 0)) ==> (M[iir#anon$10][idx] == M[iir#anon$9][idx - 1])
  );
  assume (C[iir#anon$13] == 0) ==> (AV#delay_2#data == 0);
  assume (C[iir#anon$13] > 0) ==> (AV#delay_2#data == M[iir#anon$12][R[iir#anon$12] - 1]);
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$13] > 0) ==> (M[iir#anon$13][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$13] - 0)) ==> (M[iir#anon$13][idx] == M[iir#anon$12][idx - 1])
  );
  assume (C[iir#anon$16] == 0) ==> (AV#delay_3#data == 0);
  assume (C[iir#anon$16] > 0) ==> (AV#delay_3#data == M[iir#anon$15][R[iir#anon$15] - 1]);
  assume R[iir#anon$15] == C[iir#anon$16];
  assume (C[iir#anon$16] > 0) ==> (M[iir#anon$16][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$16] - 0)) ==> (M[iir#anon$16][idx] == M[iir#anon$15][idx - 1])
  );
  assume R[iir#anon$8] == C[iir#anon$17];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$17]) ==> (M[iir#anon$17][idx$] == (37 * M[iir#anon$8][idx$]))
  );
  assume R[iir#anon$11] == C[iir#anon$18];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$18]) ==> (M[iir#anon$18][idx$] == (109 * M[iir#anon$11][idx$]))
  );
  assume R[iir#anon$14] == C[iir#anon$19];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$19]) ==> (M[iir#anon$19][idx$] == (109 * M[iir#anon$14][idx$]))
  );
  assume R[iir#anon$16] == C[iir#anon$20];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$20]) ==> (M[iir#anon$20][idx$] == (37 * M[iir#anon$16][idx$]))
  );
  assume R[iir#anon$17] == C[iir#anon$21];
  assume R[iir#anon$18] == C[iir#anon$21];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$21]) ==> (M[iir#anon$21][idx$] == (M[iir#anon$17][idx$] + M[iir#anon$18][idx$]))
  );
  assume R[iir#anon$19] == C[iir#anon$22];
  assume R[iir#anon$20] == C[iir#anon$22];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$22]) ==> (M[iir#anon$22][idx$] == (M[iir#anon$19][idx$] + M[iir#anon$20][idx$]))
  );
  assume R[iir#anon$21] == C[iir#anon$23];
  assume R[iir#anon$22] == C[iir#anon$23];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$23]) ==> (M[iir#anon$23][idx$] == (M[iir#anon$21][idx$] + M[iir#anon$22][idx$]))
  );
  assume R[iir#anon$7] == C[iir#anon$8];
  assume R[iir#anon$7] == C[iir#anon$9];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$8]) ==> (M[iir#anon$8][idx$] == M[iir#anon$7][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$9]) ==> (M[iir#anon$9][idx$] == M[iir#anon$7][idx$])
  );
  assume R[iir#anon$10] == C[iir#anon$11];
  assume R[iir#anon$10] == C[iir#anon$12];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$11]) ==> (M[iir#anon$11][idx$] == M[iir#anon$10][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$12]) ==> (M[iir#anon$12][idx$] == M[iir#anon$10][idx$])
  );
  assume R[iir#anon$13] == C[iir#anon$14];
  assume R[iir#anon$13] == C[iir#anon$15];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$14]) ==> (M[iir#anon$14][idx$] == M[iir#anon$13][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$15]) ==> (M[iir#anon$15][idx$] == M[iir#anon$13][idx$])
  );
  assume 1 <= (C[iir#anon$10] - R[iir#anon$10]);
  in#i := M[iir#anon$10][R[iir#anon$10]];
  R[iir#anon$10] := R[iir#anon$10] + 1;
  M[iir#anon$11][C[iir#anon$11]] := in#i;
  C[iir#anon$11] := C[iir#anon$11] + 1;
  M[iir#anon$12][C[iir#anon$12]] := in#i;
  C[iir#anon$12] := C[iir#anon$12] + 1;
  assume (C[iir#anon$10] == 0) ==> (AV#delay_1#data == 0);
  assume (C[iir#anon$10] > 0) ==> (AV#delay_1#data == M[iir#anon$9][R[iir#anon$9] - 1]);
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$10] > 0) ==> (M[iir#anon$10][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$10] - 0)) ==> (M[iir#anon$10][idx] == M[iir#anon$9][idx - 1])
  );
  assume (C[iir#anon$13] == 0) ==> (AV#delay_2#data == 0);
  assume (C[iir#anon$13] > 0) ==> (AV#delay_2#data == M[iir#anon$12][R[iir#anon$12] - 1]);
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$13] > 0) ==> (M[iir#anon$13][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$13] - 0)) ==> (M[iir#anon$13][idx] == M[iir#anon$12][idx - 1])
  );
  assume (C[iir#anon$16] == 0) ==> (AV#delay_3#data == 0);
  assume (C[iir#anon$16] > 0) ==> (AV#delay_3#data == M[iir#anon$15][R[iir#anon$15] - 1]);
  assume R[iir#anon$15] == C[iir#anon$16];
  assume (C[iir#anon$16] > 0) ==> (M[iir#anon$16][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$16] - 0)) ==> (M[iir#anon$16][idx] == M[iir#anon$15][idx - 1])
  );
  assume R[iir#anon$8] == C[iir#anon$17];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$17]) ==> (M[iir#anon$17][idx$] == (37 * M[iir#anon$8][idx$]))
  );
  assume R[iir#anon$11] == C[iir#anon$18];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$18]) ==> (M[iir#anon$18][idx$] == (109 * M[iir#anon$11][idx$]))
  );
  assume R[iir#anon$14] == C[iir#anon$19];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$19]) ==> (M[iir#anon$19][idx$] == (109 * M[iir#anon$14][idx$]))
  );
  assume R[iir#anon$16] == C[iir#anon$20];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$20]) ==> (M[iir#anon$20][idx$] == (37 * M[iir#anon$16][idx$]))
  );
  assume R[iir#anon$17] == C[iir#anon$21];
  assume R[iir#anon$18] == C[iir#anon$21];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$21]) ==> (M[iir#anon$21][idx$] == (M[iir#anon$17][idx$] + M[iir#anon$18][idx$]))
  );
  assume R[iir#anon$19] == C[iir#anon$22];
  assume R[iir#anon$20] == C[iir#anon$22];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$22]) ==> (M[iir#anon$22][idx$] == (M[iir#anon$19][idx$] + M[iir#anon$20][idx$]))
  );
  assume R[iir#anon$21] == C[iir#anon$23];
  assume R[iir#anon$22] == C[iir#anon$23];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$23]) ==> (M[iir#anon$23][idx$] == (M[iir#anon$21][idx$] + M[iir#anon$22][idx$]))
  );
  assume R[iir#anon$7] == C[iir#anon$8];
  assume R[iir#anon$7] == C[iir#anon$9];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$8]) ==> (M[iir#anon$8][idx$] == M[iir#anon$7][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$9]) ==> (M[iir#anon$9][idx$] == M[iir#anon$7][idx$])
  );
  assume R[iir#anon$10] == C[iir#anon$11];
  assume R[iir#anon$10] == C[iir#anon$12];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$11]) ==> (M[iir#anon$11][idx$] == M[iir#anon$10][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$12]) ==> (M[iir#anon$12][idx$] == M[iir#anon$10][idx$])
  );
  assume R[iir#anon$13] == C[iir#anon$14];
  assume R[iir#anon$13] == C[iir#anon$15];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$14]) ==> (M[iir#anon$14][idx$] == M[iir#anon$13][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$15]) ==> (M[iir#anon$15][idx$] == M[iir#anon$13][idx$])
  );
  assert {:msg "Action at 32.3 ('anon$5') for actor instance 'spl_2' might not preserve the channel invariant (#241)"} I[iir#anon$17] == I[iir#anon$8];
  assert {:msg "Action at 32.3 ('anon$5') for actor instance 'spl_2' might not preserve the channel invariant (#242)"} I[iir#anon$18] == I[iir#anon$11];
  assert {:msg "Action at 32.3 ('anon$5') for actor instance 'spl_2' might not preserve the channel invariant (#243)"} I[iir#anon$19] == I[iir#anon$14];
  assert {:msg "Action at 32.3 ('anon$5') for actor instance 'spl_2' might not preserve the channel invariant (#244)"} I[iir#anon$20] == I[iir#anon$16];
  assert {:msg "Action at 32.3 ('anon$5') for actor instance 'spl_2' might not preserve the channel invariant (#245)"} I[iir#anon$21] == I[iir#anon$17];
  assert {:msg "Action at 32.3 ('anon$5') for actor instance 'spl_2' might not preserve the channel invariant (#246)"} I[iir#anon$21] == I[iir#anon$18];
  assert {:msg "Action at 32.3 ('anon$5') for actor instance 'spl_2' might not preserve the channel invariant (#247)"} I[iir#anon$22] == I[iir#anon$19];
  assert {:msg "Action at 32.3 ('anon$5') for actor instance 'spl_2' might not preserve the channel invariant (#248)"} I[iir#anon$22] == I[iir#anon$20];
  assert {:msg "Action at 32.3 ('anon$5') for actor instance 'spl_2' might not preserve the channel invariant (#249)"} I[iir#anon$23] == I[iir#anon$21];
  assert {:msg "Action at 32.3 ('anon$5') for actor instance 'spl_2' might not preserve the channel invariant (#250)"} I[iir#anon$23] == I[iir#anon$22];
  assert {:msg "Action at 32.3 ('anon$5') for actor instance 'spl_2' might not preserve the channel invariant (#251)"} I[iir#anon$8] == I[iir#anon$7];
  assert {:msg "Action at 32.3 ('anon$5') for actor instance 'spl_2' might not preserve the channel invariant (#252)"} I[iir#anon$9] == I[iir#anon$7];
  assert {:msg "Action at 32.3 ('anon$5') for actor instance 'spl_2' might not preserve the channel invariant (#253)"} I[iir#anon$11] == I[iir#anon$10];
  assert {:msg "Action at 32.3 ('anon$5') for actor instance 'spl_2' might not preserve the channel invariant (#254)"} I[iir#anon$12] == I[iir#anon$10];
  assert {:msg "Action at 32.3 ('anon$5') for actor instance 'spl_2' might not preserve the channel invariant (#255)"} I[iir#anon$14] == I[iir#anon$13];
  assert {:msg "Action at 32.3 ('anon$5') for actor instance 'spl_2' might not preserve the channel invariant (#256)"} I[iir#anon$15] == I[iir#anon$13];
}
procedure iir##split#anon$5#23()
  modifies C, R, M, I, H;
{
  var iir#delay_1: Actor;
  var iir#delay_2: Actor;
  var iir#delay_3: Actor;
  var iir#mul_1: Actor;
  var iir#mul_2: Actor;
  var iir#mul_3: Actor;
  var iir#mul_4: Actor;
  var iir#add_1: Actor;
  var iir#add_2: Actor;
  var iir#add_3: Actor;
  var iir#spl_1: Actor;
  var iir#spl_2: Actor;
  var iir#spl_3: Actor;
  var iir#anon$7: Chan (int);
  var iir#anon$8: Chan (int);
  var iir#anon$9: Chan (int);
  var iir#anon$10: Chan (int);
  var iir#anon$11: Chan (int);
  var iir#anon$12: Chan (int);
  var iir#anon$13: Chan (int);
  var iir#anon$14: Chan (int);
  var iir#anon$15: Chan (int);
  var iir#anon$16: Chan (int);
  var iir#anon$17: Chan (int);
  var iir#anon$18: Chan (int);
  var iir#anon$19: Chan (int);
  var iir#anon$20: Chan (int);
  var iir#anon$21: Chan (int);
  var iir#anon$22: Chan (int);
  var iir#anon$23: Chan (int);
  var AV#delay_1#data: int;
  var AV#delay_1#y: int;
  var AV#delay_2#data: int;
  var AV#delay_2#y: int;
  var AV#delay_3#data: int;
  var AV#delay_3#y: int;
  var in#i: int;
  assume (iir#delay_1 != iir#delay_2) && (iir#delay_1 != iir#delay_3) && (iir#delay_1 != iir#mul_1) && (iir#delay_1 != iir#mul_2) && (iir#delay_1 != iir#mul_3) && (iir#delay_1 != iir#mul_4) && (iir#delay_1 != iir#add_1) && (iir#delay_1 != iir#add_2) && (iir#delay_1 != iir#add_3) && (iir#delay_1 != iir#spl_1) && (iir#delay_1 != iir#spl_2) && (iir#delay_1 != iir#spl_3) && (iir#delay_2 != iir#delay_3) && (iir#delay_2 != iir#mul_1) && (iir#delay_2 != iir#mul_2) && (iir#delay_2 != iir#mul_3) && (iir#delay_2 != iir#mul_4) && (iir#delay_2 != iir#add_1) && (iir#delay_2 != iir#add_2) && (iir#delay_2 != iir#add_3) && (iir#delay_2 != iir#spl_1) && (iir#delay_2 != iir#spl_2) && (iir#delay_2 != iir#spl_3) && (iir#delay_3 != iir#mul_1) && (iir#delay_3 != iir#mul_2) && (iir#delay_3 != iir#mul_3) && (iir#delay_3 != iir#mul_4) && (iir#delay_3 != iir#add_1) && (iir#delay_3 != iir#add_2) && (iir#delay_3 != iir#add_3) && (iir#delay_3 != iir#spl_1) && (iir#delay_3 != iir#spl_2) && (iir#delay_3 != iir#spl_3) && (iir#mul_1 != iir#mul_2) && (iir#mul_1 != iir#mul_3) && (iir#mul_1 != iir#mul_4) && (iir#mul_1 != iir#add_1) && (iir#mul_1 != iir#add_2) && (iir#mul_1 != iir#add_3) && (iir#mul_1 != iir#spl_1) && (iir#mul_1 != iir#spl_2) && (iir#mul_1 != iir#spl_3) && (iir#mul_2 != iir#mul_3) && (iir#mul_2 != iir#mul_4) && (iir#mul_2 != iir#add_1) && (iir#mul_2 != iir#add_2) && (iir#mul_2 != iir#add_3) && (iir#mul_2 != iir#spl_1) && (iir#mul_2 != iir#spl_2) && (iir#mul_2 != iir#spl_3) && (iir#mul_3 != iir#mul_4) && (iir#mul_3 != iir#add_1) && (iir#mul_3 != iir#add_2) && (iir#mul_3 != iir#add_3) && (iir#mul_3 != iir#spl_1) && (iir#mul_3 != iir#spl_2) && (iir#mul_3 != iir#spl_3) && (iir#mul_4 != iir#add_1) && (iir#mul_4 != iir#add_2) && (iir#mul_4 != iir#add_3) && (iir#mul_4 != iir#spl_1) && (iir#mul_4 != iir#spl_2) && (iir#mul_4 != iir#spl_3) && (iir#add_1 != iir#add_2) && (iir#add_1 != iir#add_3) && (iir#add_1 != iir#spl_1) && (iir#add_1 != iir#spl_2) && (iir#add_1 != iir#spl_3) && (iir#add_2 != iir#add_3) && (iir#add_2 != iir#spl_1) && (iir#add_2 != iir#spl_2) && (iir#add_2 != iir#spl_3) && (iir#add_3 != iir#spl_1) && (iir#add_3 != iir#spl_2) && (iir#add_3 != iir#spl_3) && (iir#spl_1 != iir#spl_2) && (iir#spl_1 != iir#spl_3) && (iir#spl_2 != iir#spl_3);
  assume (iir#anon$7 != iir#anon$8) && (iir#anon$7 != iir#anon$9) && (iir#anon$7 != iir#anon$10) && (iir#anon$7 != iir#anon$11) && (iir#anon$7 != iir#anon$12) && (iir#anon$7 != iir#anon$13) && (iir#anon$7 != iir#anon$14) && (iir#anon$7 != iir#anon$15) && (iir#anon$7 != iir#anon$16) && (iir#anon$7 != iir#anon$17) && (iir#anon$7 != iir#anon$18) && (iir#anon$7 != iir#anon$19) && (iir#anon$7 != iir#anon$20) && (iir#anon$7 != iir#anon$21) && (iir#anon$7 != iir#anon$22) && (iir#anon$7 != iir#anon$23) && (iir#anon$8 != iir#anon$9) && (iir#anon$8 != iir#anon$10) && (iir#anon$8 != iir#anon$11) && (iir#anon$8 != iir#anon$12) && (iir#anon$8 != iir#anon$13) && (iir#anon$8 != iir#anon$14) && (iir#anon$8 != iir#anon$15) && (iir#anon$8 != iir#anon$16) && (iir#anon$8 != iir#anon$17) && (iir#anon$8 != iir#anon$18) && (iir#anon$8 != iir#anon$19) && (iir#anon$8 != iir#anon$20) && (iir#anon$8 != iir#anon$21) && (iir#anon$8 != iir#anon$22) && (iir#anon$8 != iir#anon$23) && (iir#anon$9 != iir#anon$10) && (iir#anon$9 != iir#anon$11) && (iir#anon$9 != iir#anon$12) && (iir#anon$9 != iir#anon$13) && (iir#anon$9 != iir#anon$14) && (iir#anon$9 != iir#anon$15) && (iir#anon$9 != iir#anon$16) && (iir#anon$9 != iir#anon$17) && (iir#anon$9 != iir#anon$18) && (iir#anon$9 != iir#anon$19) && (iir#anon$9 != iir#anon$20) && (iir#anon$9 != iir#anon$21) && (iir#anon$9 != iir#anon$22) && (iir#anon$9 != iir#anon$23) && (iir#anon$10 != iir#anon$11) && (iir#anon$10 != iir#anon$12) && (iir#anon$10 != iir#anon$13) && (iir#anon$10 != iir#anon$14) && (iir#anon$10 != iir#anon$15) && (iir#anon$10 != iir#anon$16) && (iir#anon$10 != iir#anon$17) && (iir#anon$10 != iir#anon$18) && (iir#anon$10 != iir#anon$19) && (iir#anon$10 != iir#anon$20) && (iir#anon$10 != iir#anon$21) && (iir#anon$10 != iir#anon$22) && (iir#anon$10 != iir#anon$23) && (iir#anon$11 != iir#anon$12) && (iir#anon$11 != iir#anon$13) && (iir#anon$11 != iir#anon$14) && (iir#anon$11 != iir#anon$15) && (iir#anon$11 != iir#anon$16) && (iir#anon$11 != iir#anon$17) && (iir#anon$11 != iir#anon$18) && (iir#anon$11 != iir#anon$19) && (iir#anon$11 != iir#anon$20) && (iir#anon$11 != iir#anon$21) && (iir#anon$11 != iir#anon$22) && (iir#anon$11 != iir#anon$23) && (iir#anon$12 != iir#anon$13) && (iir#anon$12 != iir#anon$14) && (iir#anon$12 != iir#anon$15) && (iir#anon$12 != iir#anon$16) && (iir#anon$12 != iir#anon$17) && (iir#anon$12 != iir#anon$18) && (iir#anon$12 != iir#anon$19) && (iir#anon$12 != iir#anon$20) && (iir#anon$12 != iir#anon$21) && (iir#anon$12 != iir#anon$22) && (iir#anon$12 != iir#anon$23) && (iir#anon$13 != iir#anon$14) && (iir#anon$13 != iir#anon$15) && (iir#anon$13 != iir#anon$16) && (iir#anon$13 != iir#anon$17) && (iir#anon$13 != iir#anon$18) && (iir#anon$13 != iir#anon$19) && (iir#anon$13 != iir#anon$20) && (iir#anon$13 != iir#anon$21) && (iir#anon$13 != iir#anon$22) && (iir#anon$13 != iir#anon$23) && (iir#anon$14 != iir#anon$15) && (iir#anon$14 != iir#anon$16) && (iir#anon$14 != iir#anon$17) && (iir#anon$14 != iir#anon$18) && (iir#anon$14 != iir#anon$19) && (iir#anon$14 != iir#anon$20) && (iir#anon$14 != iir#anon$21) && (iir#anon$14 != iir#anon$22) && (iir#anon$14 != iir#anon$23) && (iir#anon$15 != iir#anon$16) && (iir#anon$15 != iir#anon$17) && (iir#anon$15 != iir#anon$18) && (iir#anon$15 != iir#anon$19) && (iir#anon$15 != iir#anon$20) && (iir#anon$15 != iir#anon$21) && (iir#anon$15 != iir#anon$22) && (iir#anon$15 != iir#anon$23) && (iir#anon$16 != iir#anon$17) && (iir#anon$16 != iir#anon$18) && (iir#anon$16 != iir#anon$19) && (iir#anon$16 != iir#anon$20) && (iir#anon$16 != iir#anon$21) && (iir#anon$16 != iir#anon$22) && (iir#anon$16 != iir#anon$23) && (iir#anon$17 != iir#anon$18) && (iir#anon$17 != iir#anon$19) && (iir#anon$17 != iir#anon$20) && (iir#anon$17 != iir#anon$21) && (iir#anon$17 != iir#anon$22) && (iir#anon$17 != iir#anon$23) && (iir#anon$18 != iir#anon$19) && (iir#anon$18 != iir#anon$20) && (iir#anon$18 != iir#anon$21) && (iir#anon$18 != iir#anon$22) && (iir#anon$18 != iir#anon$23) && (iir#anon$19 != iir#anon$20) && (iir#anon$19 != iir#anon$21) && (iir#anon$19 != iir#anon$22) && (iir#anon$19 != iir#anon$23) && (iir#anon$20 != iir#anon$21) && (iir#anon$20 != iir#anon$22) && (iir#anon$20 != iir#anon$23) && (iir#anon$21 != iir#anon$22) && (iir#anon$21 != iir#anon$23) && (iir#anon$22 != iir#anon$23);
  assume 0 <= I[iir#anon$7];
  assume I[iir#anon$7] <= R[iir#anon$7];
  assume R[iir#anon$7] <= C[iir#anon$7];
  assume 0 <= I[iir#anon$8];
  assume I[iir#anon$8] <= R[iir#anon$8];
  assume R[iir#anon$8] <= C[iir#anon$8];
  assume 0 <= I[iir#anon$9];
  assume I[iir#anon$9] <= R[iir#anon$9];
  assume R[iir#anon$9] <= C[iir#anon$9];
  assume 0 <= I[iir#anon$10];
  assume I[iir#anon$10] <= R[iir#anon$10];
  assume R[iir#anon$10] <= C[iir#anon$10];
  assume 0 <= I[iir#anon$11];
  assume I[iir#anon$11] <= R[iir#anon$11];
  assume R[iir#anon$11] <= C[iir#anon$11];
  assume 0 <= I[iir#anon$12];
  assume I[iir#anon$12] <= R[iir#anon$12];
  assume R[iir#anon$12] <= C[iir#anon$12];
  assume 0 <= I[iir#anon$13];
  assume I[iir#anon$13] <= R[iir#anon$13];
  assume R[iir#anon$13] <= C[iir#anon$13];
  assume 0 <= I[iir#anon$14];
  assume I[iir#anon$14] <= R[iir#anon$14];
  assume R[iir#anon$14] <= C[iir#anon$14];
  assume 0 <= I[iir#anon$15];
  assume I[iir#anon$15] <= R[iir#anon$15];
  assume R[iir#anon$15] <= C[iir#anon$15];
  assume 0 <= I[iir#anon$16];
  assume I[iir#anon$16] <= R[iir#anon$16];
  assume R[iir#anon$16] <= C[iir#anon$16];
  assume 0 <= I[iir#anon$17];
  assume I[iir#anon$17] <= R[iir#anon$17];
  assume R[iir#anon$17] <= C[iir#anon$17];
  assume 0 <= I[iir#anon$18];
  assume I[iir#anon$18] <= R[iir#anon$18];
  assume R[iir#anon$18] <= C[iir#anon$18];
  assume 0 <= I[iir#anon$19];
  assume I[iir#anon$19] <= R[iir#anon$19];
  assume R[iir#anon$19] <= C[iir#anon$19];
  assume 0 <= I[iir#anon$20];
  assume I[iir#anon$20] <= R[iir#anon$20];
  assume R[iir#anon$20] <= C[iir#anon$20];
  assume 0 <= I[iir#anon$21];
  assume I[iir#anon$21] <= R[iir#anon$21];
  assume R[iir#anon$21] <= C[iir#anon$21];
  assume 0 <= I[iir#anon$22];
  assume I[iir#anon$22] <= R[iir#anon$22];
  assume R[iir#anon$22] <= C[iir#anon$22];
  assume 0 <= I[iir#anon$23];
  assume I[iir#anon$23] <= R[iir#anon$23];
  assume R[iir#anon$23] <= C[iir#anon$23];
  assume I[iir#anon$23] == R[iir#anon$23];
  assume I[iir#anon$17] == I[iir#anon$8];
  assume I[iir#anon$18] == I[iir#anon$11];
  assume I[iir#anon$19] == I[iir#anon$14];
  assume I[iir#anon$20] == I[iir#anon$16];
  assume I[iir#anon$21] == I[iir#anon$17];
  assume I[iir#anon$21] == I[iir#anon$18];
  assume I[iir#anon$22] == I[iir#anon$19];
  assume I[iir#anon$22] == I[iir#anon$20];
  assume I[iir#anon$23] == I[iir#anon$21];
  assume I[iir#anon$23] == I[iir#anon$22];
  assume I[iir#anon$8] == I[iir#anon$7];
  assume I[iir#anon$9] == I[iir#anon$7];
  assume I[iir#anon$11] == I[iir#anon$10];
  assume I[iir#anon$12] == I[iir#anon$10];
  assume I[iir#anon$14] == I[iir#anon$13];
  assume I[iir#anon$15] == I[iir#anon$13];
  assume (C[iir#anon$10] == 0) ==> (AV#delay_1#data == 0);
  assume (C[iir#anon$10] > 0) ==> (AV#delay_1#data == M[iir#anon$9][R[iir#anon$9] - 1]);
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$10] > 0) ==> (M[iir#anon$10][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$10] - 0)) ==> (M[iir#anon$10][idx] == M[iir#anon$9][idx - 1])
  );
  assume (C[iir#anon$13] == 0) ==> (AV#delay_2#data == 0);
  assume (C[iir#anon$13] > 0) ==> (AV#delay_2#data == M[iir#anon$12][R[iir#anon$12] - 1]);
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$13] > 0) ==> (M[iir#anon$13][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$13] - 0)) ==> (M[iir#anon$13][idx] == M[iir#anon$12][idx - 1])
  );
  assume (C[iir#anon$16] == 0) ==> (AV#delay_3#data == 0);
  assume (C[iir#anon$16] > 0) ==> (AV#delay_3#data == M[iir#anon$15][R[iir#anon$15] - 1]);
  assume R[iir#anon$15] == C[iir#anon$16];
  assume (C[iir#anon$16] > 0) ==> (M[iir#anon$16][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$16] - 0)) ==> (M[iir#anon$16][idx] == M[iir#anon$15][idx - 1])
  );
  assume R[iir#anon$8] == C[iir#anon$17];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$17]) ==> (M[iir#anon$17][idx$] == (37 * M[iir#anon$8][idx$]))
  );
  assume R[iir#anon$11] == C[iir#anon$18];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$18]) ==> (M[iir#anon$18][idx$] == (109 * M[iir#anon$11][idx$]))
  );
  assume R[iir#anon$14] == C[iir#anon$19];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$19]) ==> (M[iir#anon$19][idx$] == (109 * M[iir#anon$14][idx$]))
  );
  assume R[iir#anon$16] == C[iir#anon$20];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$20]) ==> (M[iir#anon$20][idx$] == (37 * M[iir#anon$16][idx$]))
  );
  assume R[iir#anon$17] == C[iir#anon$21];
  assume R[iir#anon$18] == C[iir#anon$21];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$21]) ==> (M[iir#anon$21][idx$] == (M[iir#anon$17][idx$] + M[iir#anon$18][idx$]))
  );
  assume R[iir#anon$19] == C[iir#anon$22];
  assume R[iir#anon$20] == C[iir#anon$22];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$22]) ==> (M[iir#anon$22][idx$] == (M[iir#anon$19][idx$] + M[iir#anon$20][idx$]))
  );
  assume R[iir#anon$21] == C[iir#anon$23];
  assume R[iir#anon$22] == C[iir#anon$23];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$23]) ==> (M[iir#anon$23][idx$] == (M[iir#anon$21][idx$] + M[iir#anon$22][idx$]))
  );
  assume R[iir#anon$7] == C[iir#anon$8];
  assume R[iir#anon$7] == C[iir#anon$9];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$8]) ==> (M[iir#anon$8][idx$] == M[iir#anon$7][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$9]) ==> (M[iir#anon$9][idx$] == M[iir#anon$7][idx$])
  );
  assume R[iir#anon$10] == C[iir#anon$11];
  assume R[iir#anon$10] == C[iir#anon$12];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$11]) ==> (M[iir#anon$11][idx$] == M[iir#anon$10][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$12]) ==> (M[iir#anon$12][idx$] == M[iir#anon$10][idx$])
  );
  assume R[iir#anon$13] == C[iir#anon$14];
  assume R[iir#anon$13] == C[iir#anon$15];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$14]) ==> (M[iir#anon$14][idx$] == M[iir#anon$13][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$15]) ==> (M[iir#anon$15][idx$] == M[iir#anon$13][idx$])
  );
  assume 1 <= (C[iir#anon$13] - R[iir#anon$13]);
  in#i := M[iir#anon$13][R[iir#anon$13]];
  R[iir#anon$13] := R[iir#anon$13] + 1;
  M[iir#anon$14][C[iir#anon$14]] := in#i;
  C[iir#anon$14] := C[iir#anon$14] + 1;
  M[iir#anon$15][C[iir#anon$15]] := in#i;
  C[iir#anon$15] := C[iir#anon$15] + 1;
  assume (C[iir#anon$10] == 0) ==> (AV#delay_1#data == 0);
  assume (C[iir#anon$10] > 0) ==> (AV#delay_1#data == M[iir#anon$9][R[iir#anon$9] - 1]);
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$10] > 0) ==> (M[iir#anon$10][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$10] - 0)) ==> (M[iir#anon$10][idx] == M[iir#anon$9][idx - 1])
  );
  assume (C[iir#anon$13] == 0) ==> (AV#delay_2#data == 0);
  assume (C[iir#anon$13] > 0) ==> (AV#delay_2#data == M[iir#anon$12][R[iir#anon$12] - 1]);
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$13] > 0) ==> (M[iir#anon$13][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$13] - 0)) ==> (M[iir#anon$13][idx] == M[iir#anon$12][idx - 1])
  );
  assume (C[iir#anon$16] == 0) ==> (AV#delay_3#data == 0);
  assume (C[iir#anon$16] > 0) ==> (AV#delay_3#data == M[iir#anon$15][R[iir#anon$15] - 1]);
  assume R[iir#anon$15] == C[iir#anon$16];
  assume (C[iir#anon$16] > 0) ==> (M[iir#anon$16][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$16] - 0)) ==> (M[iir#anon$16][idx] == M[iir#anon$15][idx - 1])
  );
  assume R[iir#anon$8] == C[iir#anon$17];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$17]) ==> (M[iir#anon$17][idx$] == (37 * M[iir#anon$8][idx$]))
  );
  assume R[iir#anon$11] == C[iir#anon$18];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$18]) ==> (M[iir#anon$18][idx$] == (109 * M[iir#anon$11][idx$]))
  );
  assume R[iir#anon$14] == C[iir#anon$19];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$19]) ==> (M[iir#anon$19][idx$] == (109 * M[iir#anon$14][idx$]))
  );
  assume R[iir#anon$16] == C[iir#anon$20];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$20]) ==> (M[iir#anon$20][idx$] == (37 * M[iir#anon$16][idx$]))
  );
  assume R[iir#anon$17] == C[iir#anon$21];
  assume R[iir#anon$18] == C[iir#anon$21];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$21]) ==> (M[iir#anon$21][idx$] == (M[iir#anon$17][idx$] + M[iir#anon$18][idx$]))
  );
  assume R[iir#anon$19] == C[iir#anon$22];
  assume R[iir#anon$20] == C[iir#anon$22];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$22]) ==> (M[iir#anon$22][idx$] == (M[iir#anon$19][idx$] + M[iir#anon$20][idx$]))
  );
  assume R[iir#anon$21] == C[iir#anon$23];
  assume R[iir#anon$22] == C[iir#anon$23];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$23]) ==> (M[iir#anon$23][idx$] == (M[iir#anon$21][idx$] + M[iir#anon$22][idx$]))
  );
  assume R[iir#anon$7] == C[iir#anon$8];
  assume R[iir#anon$7] == C[iir#anon$9];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$8]) ==> (M[iir#anon$8][idx$] == M[iir#anon$7][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$9]) ==> (M[iir#anon$9][idx$] == M[iir#anon$7][idx$])
  );
  assume R[iir#anon$10] == C[iir#anon$11];
  assume R[iir#anon$10] == C[iir#anon$12];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$11]) ==> (M[iir#anon$11][idx$] == M[iir#anon$10][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$12]) ==> (M[iir#anon$12][idx$] == M[iir#anon$10][idx$])
  );
  assume R[iir#anon$13] == C[iir#anon$14];
  assume R[iir#anon$13] == C[iir#anon$15];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$14]) ==> (M[iir#anon$14][idx$] == M[iir#anon$13][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$15]) ==> (M[iir#anon$15][idx$] == M[iir#anon$13][idx$])
  );
  assert {:msg "Action at 32.3 ('anon$5') for actor instance 'spl_3' might not preserve the channel invariant (#257)"} I[iir#anon$17] == I[iir#anon$8];
  assert {:msg "Action at 32.3 ('anon$5') for actor instance 'spl_3' might not preserve the channel invariant (#258)"} I[iir#anon$18] == I[iir#anon$11];
  assert {:msg "Action at 32.3 ('anon$5') for actor instance 'spl_3' might not preserve the channel invariant (#259)"} I[iir#anon$19] == I[iir#anon$14];
  assert {:msg "Action at 32.3 ('anon$5') for actor instance 'spl_3' might not preserve the channel invariant (#260)"} I[iir#anon$20] == I[iir#anon$16];
  assert {:msg "Action at 32.3 ('anon$5') for actor instance 'spl_3' might not preserve the channel invariant (#261)"} I[iir#anon$21] == I[iir#anon$17];
  assert {:msg "Action at 32.3 ('anon$5') for actor instance 'spl_3' might not preserve the channel invariant (#262)"} I[iir#anon$21] == I[iir#anon$18];
  assert {:msg "Action at 32.3 ('anon$5') for actor instance 'spl_3' might not preserve the channel invariant (#263)"} I[iir#anon$22] == I[iir#anon$19];
  assert {:msg "Action at 32.3 ('anon$5') for actor instance 'spl_3' might not preserve the channel invariant (#264)"} I[iir#anon$22] == I[iir#anon$20];
  assert {:msg "Action at 32.3 ('anon$5') for actor instance 'spl_3' might not preserve the channel invariant (#265)"} I[iir#anon$23] == I[iir#anon$21];
  assert {:msg "Action at 32.3 ('anon$5') for actor instance 'spl_3' might not preserve the channel invariant (#266)"} I[iir#anon$23] == I[iir#anon$22];
  assert {:msg "Action at 32.3 ('anon$5') for actor instance 'spl_3' might not preserve the channel invariant (#267)"} I[iir#anon$8] == I[iir#anon$7];
  assert {:msg "Action at 32.3 ('anon$5') for actor instance 'spl_3' might not preserve the channel invariant (#268)"} I[iir#anon$9] == I[iir#anon$7];
  assert {:msg "Action at 32.3 ('anon$5') for actor instance 'spl_3' might not preserve the channel invariant (#269)"} I[iir#anon$11] == I[iir#anon$10];
  assert {:msg "Action at 32.3 ('anon$5') for actor instance 'spl_3' might not preserve the channel invariant (#270)"} I[iir#anon$12] == I[iir#anon$10];
  assert {:msg "Action at 32.3 ('anon$5') for actor instance 'spl_3' might not preserve the channel invariant (#271)"} I[iir#anon$14] == I[iir#anon$13];
  assert {:msg "Action at 32.3 ('anon$5') for actor instance 'spl_3' might not preserve the channel invariant (#272)"} I[iir#anon$15] == I[iir#anon$13];
}
procedure iir#anon$6#input#in#24()
  modifies C, R, M, I, H;
{
  var iir#delay_1: Actor;
  var iir#delay_2: Actor;
  var iir#delay_3: Actor;
  var iir#mul_1: Actor;
  var iir#mul_2: Actor;
  var iir#mul_3: Actor;
  var iir#mul_4: Actor;
  var iir#add_1: Actor;
  var iir#add_2: Actor;
  var iir#add_3: Actor;
  var iir#spl_1: Actor;
  var iir#spl_2: Actor;
  var iir#spl_3: Actor;
  var iir#anon$7: Chan (int);
  var iir#anon$8: Chan (int);
  var iir#anon$9: Chan (int);
  var iir#anon$10: Chan (int);
  var iir#anon$11: Chan (int);
  var iir#anon$12: Chan (int);
  var iir#anon$13: Chan (int);
  var iir#anon$14: Chan (int);
  var iir#anon$15: Chan (int);
  var iir#anon$16: Chan (int);
  var iir#anon$17: Chan (int);
  var iir#anon$18: Chan (int);
  var iir#anon$19: Chan (int);
  var iir#anon$20: Chan (int);
  var iir#anon$21: Chan (int);
  var iir#anon$22: Chan (int);
  var iir#anon$23: Chan (int);
  var AV#delay_1#data: int;
  var AV#delay_1#y: int;
  var AV#delay_2#data: int;
  var AV#delay_2#y: int;
  var AV#delay_3#data: int;
  var AV#delay_3#y: int;
  assume (iir#delay_1 != iir#delay_2) && (iir#delay_1 != iir#delay_3) && (iir#delay_1 != iir#mul_1) && (iir#delay_1 != iir#mul_2) && (iir#delay_1 != iir#mul_3) && (iir#delay_1 != iir#mul_4) && (iir#delay_1 != iir#add_1) && (iir#delay_1 != iir#add_2) && (iir#delay_1 != iir#add_3) && (iir#delay_1 != iir#spl_1) && (iir#delay_1 != iir#spl_2) && (iir#delay_1 != iir#spl_3) && (iir#delay_2 != iir#delay_3) && (iir#delay_2 != iir#mul_1) && (iir#delay_2 != iir#mul_2) && (iir#delay_2 != iir#mul_3) && (iir#delay_2 != iir#mul_4) && (iir#delay_2 != iir#add_1) && (iir#delay_2 != iir#add_2) && (iir#delay_2 != iir#add_3) && (iir#delay_2 != iir#spl_1) && (iir#delay_2 != iir#spl_2) && (iir#delay_2 != iir#spl_3) && (iir#delay_3 != iir#mul_1) && (iir#delay_3 != iir#mul_2) && (iir#delay_3 != iir#mul_3) && (iir#delay_3 != iir#mul_4) && (iir#delay_3 != iir#add_1) && (iir#delay_3 != iir#add_2) && (iir#delay_3 != iir#add_3) && (iir#delay_3 != iir#spl_1) && (iir#delay_3 != iir#spl_2) && (iir#delay_3 != iir#spl_3) && (iir#mul_1 != iir#mul_2) && (iir#mul_1 != iir#mul_3) && (iir#mul_1 != iir#mul_4) && (iir#mul_1 != iir#add_1) && (iir#mul_1 != iir#add_2) && (iir#mul_1 != iir#add_3) && (iir#mul_1 != iir#spl_1) && (iir#mul_1 != iir#spl_2) && (iir#mul_1 != iir#spl_3) && (iir#mul_2 != iir#mul_3) && (iir#mul_2 != iir#mul_4) && (iir#mul_2 != iir#add_1) && (iir#mul_2 != iir#add_2) && (iir#mul_2 != iir#add_3) && (iir#mul_2 != iir#spl_1) && (iir#mul_2 != iir#spl_2) && (iir#mul_2 != iir#spl_3) && (iir#mul_3 != iir#mul_4) && (iir#mul_3 != iir#add_1) && (iir#mul_3 != iir#add_2) && (iir#mul_3 != iir#add_3) && (iir#mul_3 != iir#spl_1) && (iir#mul_3 != iir#spl_2) && (iir#mul_3 != iir#spl_3) && (iir#mul_4 != iir#add_1) && (iir#mul_4 != iir#add_2) && (iir#mul_4 != iir#add_3) && (iir#mul_4 != iir#spl_1) && (iir#mul_4 != iir#spl_2) && (iir#mul_4 != iir#spl_3) && (iir#add_1 != iir#add_2) && (iir#add_1 != iir#add_3) && (iir#add_1 != iir#spl_1) && (iir#add_1 != iir#spl_2) && (iir#add_1 != iir#spl_3) && (iir#add_2 != iir#add_3) && (iir#add_2 != iir#spl_1) && (iir#add_2 != iir#spl_2) && (iir#add_2 != iir#spl_3) && (iir#add_3 != iir#spl_1) && (iir#add_3 != iir#spl_2) && (iir#add_3 != iir#spl_3) && (iir#spl_1 != iir#spl_2) && (iir#spl_1 != iir#spl_3) && (iir#spl_2 != iir#spl_3);
  assume (iir#anon$7 != iir#anon$8) && (iir#anon$7 != iir#anon$9) && (iir#anon$7 != iir#anon$10) && (iir#anon$7 != iir#anon$11) && (iir#anon$7 != iir#anon$12) && (iir#anon$7 != iir#anon$13) && (iir#anon$7 != iir#anon$14) && (iir#anon$7 != iir#anon$15) && (iir#anon$7 != iir#anon$16) && (iir#anon$7 != iir#anon$17) && (iir#anon$7 != iir#anon$18) && (iir#anon$7 != iir#anon$19) && (iir#anon$7 != iir#anon$20) && (iir#anon$7 != iir#anon$21) && (iir#anon$7 != iir#anon$22) && (iir#anon$7 != iir#anon$23) && (iir#anon$8 != iir#anon$9) && (iir#anon$8 != iir#anon$10) && (iir#anon$8 != iir#anon$11) && (iir#anon$8 != iir#anon$12) && (iir#anon$8 != iir#anon$13) && (iir#anon$8 != iir#anon$14) && (iir#anon$8 != iir#anon$15) && (iir#anon$8 != iir#anon$16) && (iir#anon$8 != iir#anon$17) && (iir#anon$8 != iir#anon$18) && (iir#anon$8 != iir#anon$19) && (iir#anon$8 != iir#anon$20) && (iir#anon$8 != iir#anon$21) && (iir#anon$8 != iir#anon$22) && (iir#anon$8 != iir#anon$23) && (iir#anon$9 != iir#anon$10) && (iir#anon$9 != iir#anon$11) && (iir#anon$9 != iir#anon$12) && (iir#anon$9 != iir#anon$13) && (iir#anon$9 != iir#anon$14) && (iir#anon$9 != iir#anon$15) && (iir#anon$9 != iir#anon$16) && (iir#anon$9 != iir#anon$17) && (iir#anon$9 != iir#anon$18) && (iir#anon$9 != iir#anon$19) && (iir#anon$9 != iir#anon$20) && (iir#anon$9 != iir#anon$21) && (iir#anon$9 != iir#anon$22) && (iir#anon$9 != iir#anon$23) && (iir#anon$10 != iir#anon$11) && (iir#anon$10 != iir#anon$12) && (iir#anon$10 != iir#anon$13) && (iir#anon$10 != iir#anon$14) && (iir#anon$10 != iir#anon$15) && (iir#anon$10 != iir#anon$16) && (iir#anon$10 != iir#anon$17) && (iir#anon$10 != iir#anon$18) && (iir#anon$10 != iir#anon$19) && (iir#anon$10 != iir#anon$20) && (iir#anon$10 != iir#anon$21) && (iir#anon$10 != iir#anon$22) && (iir#anon$10 != iir#anon$23) && (iir#anon$11 != iir#anon$12) && (iir#anon$11 != iir#anon$13) && (iir#anon$11 != iir#anon$14) && (iir#anon$11 != iir#anon$15) && (iir#anon$11 != iir#anon$16) && (iir#anon$11 != iir#anon$17) && (iir#anon$11 != iir#anon$18) && (iir#anon$11 != iir#anon$19) && (iir#anon$11 != iir#anon$20) && (iir#anon$11 != iir#anon$21) && (iir#anon$11 != iir#anon$22) && (iir#anon$11 != iir#anon$23) && (iir#anon$12 != iir#anon$13) && (iir#anon$12 != iir#anon$14) && (iir#anon$12 != iir#anon$15) && (iir#anon$12 != iir#anon$16) && (iir#anon$12 != iir#anon$17) && (iir#anon$12 != iir#anon$18) && (iir#anon$12 != iir#anon$19) && (iir#anon$12 != iir#anon$20) && (iir#anon$12 != iir#anon$21) && (iir#anon$12 != iir#anon$22) && (iir#anon$12 != iir#anon$23) && (iir#anon$13 != iir#anon$14) && (iir#anon$13 != iir#anon$15) && (iir#anon$13 != iir#anon$16) && (iir#anon$13 != iir#anon$17) && (iir#anon$13 != iir#anon$18) && (iir#anon$13 != iir#anon$19) && (iir#anon$13 != iir#anon$20) && (iir#anon$13 != iir#anon$21) && (iir#anon$13 != iir#anon$22) && (iir#anon$13 != iir#anon$23) && (iir#anon$14 != iir#anon$15) && (iir#anon$14 != iir#anon$16) && (iir#anon$14 != iir#anon$17) && (iir#anon$14 != iir#anon$18) && (iir#anon$14 != iir#anon$19) && (iir#anon$14 != iir#anon$20) && (iir#anon$14 != iir#anon$21) && (iir#anon$14 != iir#anon$22) && (iir#anon$14 != iir#anon$23) && (iir#anon$15 != iir#anon$16) && (iir#anon$15 != iir#anon$17) && (iir#anon$15 != iir#anon$18) && (iir#anon$15 != iir#anon$19) && (iir#anon$15 != iir#anon$20) && (iir#anon$15 != iir#anon$21) && (iir#anon$15 != iir#anon$22) && (iir#anon$15 != iir#anon$23) && (iir#anon$16 != iir#anon$17) && (iir#anon$16 != iir#anon$18) && (iir#anon$16 != iir#anon$19) && (iir#anon$16 != iir#anon$20) && (iir#anon$16 != iir#anon$21) && (iir#anon$16 != iir#anon$22) && (iir#anon$16 != iir#anon$23) && (iir#anon$17 != iir#anon$18) && (iir#anon$17 != iir#anon$19) && (iir#anon$17 != iir#anon$20) && (iir#anon$17 != iir#anon$21) && (iir#anon$17 != iir#anon$22) && (iir#anon$17 != iir#anon$23) && (iir#anon$18 != iir#anon$19) && (iir#anon$18 != iir#anon$20) && (iir#anon$18 != iir#anon$21) && (iir#anon$18 != iir#anon$22) && (iir#anon$18 != iir#anon$23) && (iir#anon$19 != iir#anon$20) && (iir#anon$19 != iir#anon$21) && (iir#anon$19 != iir#anon$22) && (iir#anon$19 != iir#anon$23) && (iir#anon$20 != iir#anon$21) && (iir#anon$20 != iir#anon$22) && (iir#anon$20 != iir#anon$23) && (iir#anon$21 != iir#anon$22) && (iir#anon$21 != iir#anon$23) && (iir#anon$22 != iir#anon$23);
  assume 0 <= I[iir#anon$7];
  assume I[iir#anon$7] <= R[iir#anon$7];
  assume R[iir#anon$7] <= C[iir#anon$7];
  assume 0 <= I[iir#anon$8];
  assume I[iir#anon$8] <= R[iir#anon$8];
  assume R[iir#anon$8] <= C[iir#anon$8];
  assume 0 <= I[iir#anon$9];
  assume I[iir#anon$9] <= R[iir#anon$9];
  assume R[iir#anon$9] <= C[iir#anon$9];
  assume 0 <= I[iir#anon$10];
  assume I[iir#anon$10] <= R[iir#anon$10];
  assume R[iir#anon$10] <= C[iir#anon$10];
  assume 0 <= I[iir#anon$11];
  assume I[iir#anon$11] <= R[iir#anon$11];
  assume R[iir#anon$11] <= C[iir#anon$11];
  assume 0 <= I[iir#anon$12];
  assume I[iir#anon$12] <= R[iir#anon$12];
  assume R[iir#anon$12] <= C[iir#anon$12];
  assume 0 <= I[iir#anon$13];
  assume I[iir#anon$13] <= R[iir#anon$13];
  assume R[iir#anon$13] <= C[iir#anon$13];
  assume 0 <= I[iir#anon$14];
  assume I[iir#anon$14] <= R[iir#anon$14];
  assume R[iir#anon$14] <= C[iir#anon$14];
  assume 0 <= I[iir#anon$15];
  assume I[iir#anon$15] <= R[iir#anon$15];
  assume R[iir#anon$15] <= C[iir#anon$15];
  assume 0 <= I[iir#anon$16];
  assume I[iir#anon$16] <= R[iir#anon$16];
  assume R[iir#anon$16] <= C[iir#anon$16];
  assume 0 <= I[iir#anon$17];
  assume I[iir#anon$17] <= R[iir#anon$17];
  assume R[iir#anon$17] <= C[iir#anon$17];
  assume 0 <= I[iir#anon$18];
  assume I[iir#anon$18] <= R[iir#anon$18];
  assume R[iir#anon$18] <= C[iir#anon$18];
  assume 0 <= I[iir#anon$19];
  assume I[iir#anon$19] <= R[iir#anon$19];
  assume R[iir#anon$19] <= C[iir#anon$19];
  assume 0 <= I[iir#anon$20];
  assume I[iir#anon$20] <= R[iir#anon$20];
  assume R[iir#anon$20] <= C[iir#anon$20];
  assume 0 <= I[iir#anon$21];
  assume I[iir#anon$21] <= R[iir#anon$21];
  assume R[iir#anon$21] <= C[iir#anon$21];
  assume 0 <= I[iir#anon$22];
  assume I[iir#anon$22] <= R[iir#anon$22];
  assume R[iir#anon$22] <= C[iir#anon$22];
  assume 0 <= I[iir#anon$23];
  assume I[iir#anon$23] <= R[iir#anon$23];
  assume R[iir#anon$23] <= C[iir#anon$23];
  assume I[iir#anon$23] == R[iir#anon$23];
  assume (C[iir#anon$7] - I[iir#anon$7]) < 1;
  assume I[iir#anon$17] == I[iir#anon$8];
  assume I[iir#anon$18] == I[iir#anon$11];
  assume I[iir#anon$19] == I[iir#anon$14];
  assume I[iir#anon$20] == I[iir#anon$16];
  assume I[iir#anon$21] == I[iir#anon$17];
  assume I[iir#anon$21] == I[iir#anon$18];
  assume I[iir#anon$22] == I[iir#anon$19];
  assume I[iir#anon$22] == I[iir#anon$20];
  assume I[iir#anon$23] == I[iir#anon$21];
  assume I[iir#anon$23] == I[iir#anon$22];
  assume I[iir#anon$8] == I[iir#anon$7];
  assume I[iir#anon$9] == I[iir#anon$7];
  assume I[iir#anon$11] == I[iir#anon$10];
  assume I[iir#anon$12] == I[iir#anon$10];
  assume I[iir#anon$14] == I[iir#anon$13];
  assume I[iir#anon$15] == I[iir#anon$13];
  assume (C[iir#anon$10] == 0) ==> (AV#delay_1#data == 0);
  assume (C[iir#anon$10] > 0) ==> (AV#delay_1#data == M[iir#anon$9][R[iir#anon$9] - 1]);
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$10] > 0) ==> (M[iir#anon$10][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$10] - 0)) ==> (M[iir#anon$10][idx] == M[iir#anon$9][idx - 1])
  );
  assume (C[iir#anon$13] == 0) ==> (AV#delay_2#data == 0);
  assume (C[iir#anon$13] > 0) ==> (AV#delay_2#data == M[iir#anon$12][R[iir#anon$12] - 1]);
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$13] > 0) ==> (M[iir#anon$13][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$13] - 0)) ==> (M[iir#anon$13][idx] == M[iir#anon$12][idx - 1])
  );
  assume (C[iir#anon$16] == 0) ==> (AV#delay_3#data == 0);
  assume (C[iir#anon$16] > 0) ==> (AV#delay_3#data == M[iir#anon$15][R[iir#anon$15] - 1]);
  assume R[iir#anon$15] == C[iir#anon$16];
  assume (C[iir#anon$16] > 0) ==> (M[iir#anon$16][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$16] - 0)) ==> (M[iir#anon$16][idx] == M[iir#anon$15][idx - 1])
  );
  assume R[iir#anon$8] == C[iir#anon$17];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$17]) ==> (M[iir#anon$17][idx$] == (37 * M[iir#anon$8][idx$]))
  );
  assume R[iir#anon$11] == C[iir#anon$18];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$18]) ==> (M[iir#anon$18][idx$] == (109 * M[iir#anon$11][idx$]))
  );
  assume R[iir#anon$14] == C[iir#anon$19];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$19]) ==> (M[iir#anon$19][idx$] == (109 * M[iir#anon$14][idx$]))
  );
  assume R[iir#anon$16] == C[iir#anon$20];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$20]) ==> (M[iir#anon$20][idx$] == (37 * M[iir#anon$16][idx$]))
  );
  assume R[iir#anon$17] == C[iir#anon$21];
  assume R[iir#anon$18] == C[iir#anon$21];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$21]) ==> (M[iir#anon$21][idx$] == (M[iir#anon$17][idx$] + M[iir#anon$18][idx$]))
  );
  assume R[iir#anon$19] == C[iir#anon$22];
  assume R[iir#anon$20] == C[iir#anon$22];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$22]) ==> (M[iir#anon$22][idx$] == (M[iir#anon$19][idx$] + M[iir#anon$20][idx$]))
  );
  assume R[iir#anon$21] == C[iir#anon$23];
  assume R[iir#anon$22] == C[iir#anon$23];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$23]) ==> (M[iir#anon$23][idx$] == (M[iir#anon$21][idx$] + M[iir#anon$22][idx$]))
  );
  assume R[iir#anon$7] == C[iir#anon$8];
  assume R[iir#anon$7] == C[iir#anon$9];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$8]) ==> (M[iir#anon$8][idx$] == M[iir#anon$7][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$9]) ==> (M[iir#anon$9][idx$] == M[iir#anon$7][idx$])
  );
  assume R[iir#anon$10] == C[iir#anon$11];
  assume R[iir#anon$10] == C[iir#anon$12];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$11]) ==> (M[iir#anon$11][idx$] == M[iir#anon$10][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$12]) ==> (M[iir#anon$12][idx$] == M[iir#anon$10][idx$])
  );
  assume R[iir#anon$13] == C[iir#anon$14];
  assume R[iir#anon$13] == C[iir#anon$15];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$14]) ==> (M[iir#anon$14][idx$] == M[iir#anon$13][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$15]) ==> (M[iir#anon$15][idx$] == M[iir#anon$13][idx$])
  );
  C[iir#anon$7] := C[iir#anon$7] + 1;
  assert {:msg "Channel invariant might be falsified by network input (#273)"} I[iir#anon$17] == I[iir#anon$8];
  assert {:msg "Channel invariant might be falsified by network input (#274)"} I[iir#anon$18] == I[iir#anon$11];
  assert {:msg "Channel invariant might be falsified by network input (#275)"} I[iir#anon$19] == I[iir#anon$14];
  assert {:msg "Channel invariant might be falsified by network input (#276)"} I[iir#anon$20] == I[iir#anon$16];
  assert {:msg "Channel invariant might be falsified by network input (#277)"} I[iir#anon$21] == I[iir#anon$17];
  assert {:msg "Channel invariant might be falsified by network input (#278)"} I[iir#anon$21] == I[iir#anon$18];
  assert {:msg "Channel invariant might be falsified by network input (#279)"} I[iir#anon$22] == I[iir#anon$19];
  assert {:msg "Channel invariant might be falsified by network input (#280)"} I[iir#anon$22] == I[iir#anon$20];
  assert {:msg "Channel invariant might be falsified by network input (#281)"} I[iir#anon$23] == I[iir#anon$21];
  assert {:msg "Channel invariant might be falsified by network input (#282)"} I[iir#anon$23] == I[iir#anon$22];
  assert {:msg "Channel invariant might be falsified by network input (#283)"} I[iir#anon$8] == I[iir#anon$7];
  assert {:msg "Channel invariant might be falsified by network input (#284)"} I[iir#anon$9] == I[iir#anon$7];
  assert {:msg "Channel invariant might be falsified by network input (#285)"} I[iir#anon$11] == I[iir#anon$10];
  assert {:msg "Channel invariant might be falsified by network input (#286)"} I[iir#anon$12] == I[iir#anon$10];
  assert {:msg "Channel invariant might be falsified by network input (#287)"} I[iir#anon$14] == I[iir#anon$13];
  assert {:msg "Channel invariant might be falsified by network input (#288)"} I[iir#anon$15] == I[iir#anon$13];
}
procedure iir#anon$6#exit#25()
  modifies C, R, M, I, H;
{
  var iir#delay_1: Actor;
  var iir#delay_2: Actor;
  var iir#delay_3: Actor;
  var iir#mul_1: Actor;
  var iir#mul_2: Actor;
  var iir#mul_3: Actor;
  var iir#mul_4: Actor;
  var iir#add_1: Actor;
  var iir#add_2: Actor;
  var iir#add_3: Actor;
  var iir#spl_1: Actor;
  var iir#spl_2: Actor;
  var iir#spl_3: Actor;
  var iir#anon$7: Chan (int);
  var iir#anon$8: Chan (int);
  var iir#anon$9: Chan (int);
  var iir#anon$10: Chan (int);
  var iir#anon$11: Chan (int);
  var iir#anon$12: Chan (int);
  var iir#anon$13: Chan (int);
  var iir#anon$14: Chan (int);
  var iir#anon$15: Chan (int);
  var iir#anon$16: Chan (int);
  var iir#anon$17: Chan (int);
  var iir#anon$18: Chan (int);
  var iir#anon$19: Chan (int);
  var iir#anon$20: Chan (int);
  var iir#anon$21: Chan (int);
  var iir#anon$22: Chan (int);
  var iir#anon$23: Chan (int);
  var AV#delay_1#data: int;
  var AV#delay_1#y: int;
  var AV#delay_2#data: int;
  var AV#delay_2#y: int;
  var AV#delay_3#data: int;
  var AV#delay_3#y: int;
  assume (iir#delay_1 != iir#delay_2) && (iir#delay_1 != iir#delay_3) && (iir#delay_1 != iir#mul_1) && (iir#delay_1 != iir#mul_2) && (iir#delay_1 != iir#mul_3) && (iir#delay_1 != iir#mul_4) && (iir#delay_1 != iir#add_1) && (iir#delay_1 != iir#add_2) && (iir#delay_1 != iir#add_3) && (iir#delay_1 != iir#spl_1) && (iir#delay_1 != iir#spl_2) && (iir#delay_1 != iir#spl_3) && (iir#delay_2 != iir#delay_3) && (iir#delay_2 != iir#mul_1) && (iir#delay_2 != iir#mul_2) && (iir#delay_2 != iir#mul_3) && (iir#delay_2 != iir#mul_4) && (iir#delay_2 != iir#add_1) && (iir#delay_2 != iir#add_2) && (iir#delay_2 != iir#add_3) && (iir#delay_2 != iir#spl_1) && (iir#delay_2 != iir#spl_2) && (iir#delay_2 != iir#spl_3) && (iir#delay_3 != iir#mul_1) && (iir#delay_3 != iir#mul_2) && (iir#delay_3 != iir#mul_3) && (iir#delay_3 != iir#mul_4) && (iir#delay_3 != iir#add_1) && (iir#delay_3 != iir#add_2) && (iir#delay_3 != iir#add_3) && (iir#delay_3 != iir#spl_1) && (iir#delay_3 != iir#spl_2) && (iir#delay_3 != iir#spl_3) && (iir#mul_1 != iir#mul_2) && (iir#mul_1 != iir#mul_3) && (iir#mul_1 != iir#mul_4) && (iir#mul_1 != iir#add_1) && (iir#mul_1 != iir#add_2) && (iir#mul_1 != iir#add_3) && (iir#mul_1 != iir#spl_1) && (iir#mul_1 != iir#spl_2) && (iir#mul_1 != iir#spl_3) && (iir#mul_2 != iir#mul_3) && (iir#mul_2 != iir#mul_4) && (iir#mul_2 != iir#add_1) && (iir#mul_2 != iir#add_2) && (iir#mul_2 != iir#add_3) && (iir#mul_2 != iir#spl_1) && (iir#mul_2 != iir#spl_2) && (iir#mul_2 != iir#spl_3) && (iir#mul_3 != iir#mul_4) && (iir#mul_3 != iir#add_1) && (iir#mul_3 != iir#add_2) && (iir#mul_3 != iir#add_3) && (iir#mul_3 != iir#spl_1) && (iir#mul_3 != iir#spl_2) && (iir#mul_3 != iir#spl_3) && (iir#mul_4 != iir#add_1) && (iir#mul_4 != iir#add_2) && (iir#mul_4 != iir#add_3) && (iir#mul_4 != iir#spl_1) && (iir#mul_4 != iir#spl_2) && (iir#mul_4 != iir#spl_3) && (iir#add_1 != iir#add_2) && (iir#add_1 != iir#add_3) && (iir#add_1 != iir#spl_1) && (iir#add_1 != iir#spl_2) && (iir#add_1 != iir#spl_3) && (iir#add_2 != iir#add_3) && (iir#add_2 != iir#spl_1) && (iir#add_2 != iir#spl_2) && (iir#add_2 != iir#spl_3) && (iir#add_3 != iir#spl_1) && (iir#add_3 != iir#spl_2) && (iir#add_3 != iir#spl_3) && (iir#spl_1 != iir#spl_2) && (iir#spl_1 != iir#spl_3) && (iir#spl_2 != iir#spl_3);
  assume (iir#anon$7 != iir#anon$8) && (iir#anon$7 != iir#anon$9) && (iir#anon$7 != iir#anon$10) && (iir#anon$7 != iir#anon$11) && (iir#anon$7 != iir#anon$12) && (iir#anon$7 != iir#anon$13) && (iir#anon$7 != iir#anon$14) && (iir#anon$7 != iir#anon$15) && (iir#anon$7 != iir#anon$16) && (iir#anon$7 != iir#anon$17) && (iir#anon$7 != iir#anon$18) && (iir#anon$7 != iir#anon$19) && (iir#anon$7 != iir#anon$20) && (iir#anon$7 != iir#anon$21) && (iir#anon$7 != iir#anon$22) && (iir#anon$7 != iir#anon$23) && (iir#anon$8 != iir#anon$9) && (iir#anon$8 != iir#anon$10) && (iir#anon$8 != iir#anon$11) && (iir#anon$8 != iir#anon$12) && (iir#anon$8 != iir#anon$13) && (iir#anon$8 != iir#anon$14) && (iir#anon$8 != iir#anon$15) && (iir#anon$8 != iir#anon$16) && (iir#anon$8 != iir#anon$17) && (iir#anon$8 != iir#anon$18) && (iir#anon$8 != iir#anon$19) && (iir#anon$8 != iir#anon$20) && (iir#anon$8 != iir#anon$21) && (iir#anon$8 != iir#anon$22) && (iir#anon$8 != iir#anon$23) && (iir#anon$9 != iir#anon$10) && (iir#anon$9 != iir#anon$11) && (iir#anon$9 != iir#anon$12) && (iir#anon$9 != iir#anon$13) && (iir#anon$9 != iir#anon$14) && (iir#anon$9 != iir#anon$15) && (iir#anon$9 != iir#anon$16) && (iir#anon$9 != iir#anon$17) && (iir#anon$9 != iir#anon$18) && (iir#anon$9 != iir#anon$19) && (iir#anon$9 != iir#anon$20) && (iir#anon$9 != iir#anon$21) && (iir#anon$9 != iir#anon$22) && (iir#anon$9 != iir#anon$23) && (iir#anon$10 != iir#anon$11) && (iir#anon$10 != iir#anon$12) && (iir#anon$10 != iir#anon$13) && (iir#anon$10 != iir#anon$14) && (iir#anon$10 != iir#anon$15) && (iir#anon$10 != iir#anon$16) && (iir#anon$10 != iir#anon$17) && (iir#anon$10 != iir#anon$18) && (iir#anon$10 != iir#anon$19) && (iir#anon$10 != iir#anon$20) && (iir#anon$10 != iir#anon$21) && (iir#anon$10 != iir#anon$22) && (iir#anon$10 != iir#anon$23) && (iir#anon$11 != iir#anon$12) && (iir#anon$11 != iir#anon$13) && (iir#anon$11 != iir#anon$14) && (iir#anon$11 != iir#anon$15) && (iir#anon$11 != iir#anon$16) && (iir#anon$11 != iir#anon$17) && (iir#anon$11 != iir#anon$18) && (iir#anon$11 != iir#anon$19) && (iir#anon$11 != iir#anon$20) && (iir#anon$11 != iir#anon$21) && (iir#anon$11 != iir#anon$22) && (iir#anon$11 != iir#anon$23) && (iir#anon$12 != iir#anon$13) && (iir#anon$12 != iir#anon$14) && (iir#anon$12 != iir#anon$15) && (iir#anon$12 != iir#anon$16) && (iir#anon$12 != iir#anon$17) && (iir#anon$12 != iir#anon$18) && (iir#anon$12 != iir#anon$19) && (iir#anon$12 != iir#anon$20) && (iir#anon$12 != iir#anon$21) && (iir#anon$12 != iir#anon$22) && (iir#anon$12 != iir#anon$23) && (iir#anon$13 != iir#anon$14) && (iir#anon$13 != iir#anon$15) && (iir#anon$13 != iir#anon$16) && (iir#anon$13 != iir#anon$17) && (iir#anon$13 != iir#anon$18) && (iir#anon$13 != iir#anon$19) && (iir#anon$13 != iir#anon$20) && (iir#anon$13 != iir#anon$21) && (iir#anon$13 != iir#anon$22) && (iir#anon$13 != iir#anon$23) && (iir#anon$14 != iir#anon$15) && (iir#anon$14 != iir#anon$16) && (iir#anon$14 != iir#anon$17) && (iir#anon$14 != iir#anon$18) && (iir#anon$14 != iir#anon$19) && (iir#anon$14 != iir#anon$20) && (iir#anon$14 != iir#anon$21) && (iir#anon$14 != iir#anon$22) && (iir#anon$14 != iir#anon$23) && (iir#anon$15 != iir#anon$16) && (iir#anon$15 != iir#anon$17) && (iir#anon$15 != iir#anon$18) && (iir#anon$15 != iir#anon$19) && (iir#anon$15 != iir#anon$20) && (iir#anon$15 != iir#anon$21) && (iir#anon$15 != iir#anon$22) && (iir#anon$15 != iir#anon$23) && (iir#anon$16 != iir#anon$17) && (iir#anon$16 != iir#anon$18) && (iir#anon$16 != iir#anon$19) && (iir#anon$16 != iir#anon$20) && (iir#anon$16 != iir#anon$21) && (iir#anon$16 != iir#anon$22) && (iir#anon$16 != iir#anon$23) && (iir#anon$17 != iir#anon$18) && (iir#anon$17 != iir#anon$19) && (iir#anon$17 != iir#anon$20) && (iir#anon$17 != iir#anon$21) && (iir#anon$17 != iir#anon$22) && (iir#anon$17 != iir#anon$23) && (iir#anon$18 != iir#anon$19) && (iir#anon$18 != iir#anon$20) && (iir#anon$18 != iir#anon$21) && (iir#anon$18 != iir#anon$22) && (iir#anon$18 != iir#anon$23) && (iir#anon$19 != iir#anon$20) && (iir#anon$19 != iir#anon$21) && (iir#anon$19 != iir#anon$22) && (iir#anon$19 != iir#anon$23) && (iir#anon$20 != iir#anon$21) && (iir#anon$20 != iir#anon$22) && (iir#anon$20 != iir#anon$23) && (iir#anon$21 != iir#anon$22) && (iir#anon$21 != iir#anon$23) && (iir#anon$22 != iir#anon$23);
  assume 0 <= I[iir#anon$7];
  assume I[iir#anon$7] <= R[iir#anon$7];
  assume R[iir#anon$7] <= C[iir#anon$7];
  assume 0 <= I[iir#anon$8];
  assume I[iir#anon$8] <= R[iir#anon$8];
  assume R[iir#anon$8] <= C[iir#anon$8];
  assume 0 <= I[iir#anon$9];
  assume I[iir#anon$9] <= R[iir#anon$9];
  assume R[iir#anon$9] <= C[iir#anon$9];
  assume 0 <= I[iir#anon$10];
  assume I[iir#anon$10] <= R[iir#anon$10];
  assume R[iir#anon$10] <= C[iir#anon$10];
  assume 0 <= I[iir#anon$11];
  assume I[iir#anon$11] <= R[iir#anon$11];
  assume R[iir#anon$11] <= C[iir#anon$11];
  assume 0 <= I[iir#anon$12];
  assume I[iir#anon$12] <= R[iir#anon$12];
  assume R[iir#anon$12] <= C[iir#anon$12];
  assume 0 <= I[iir#anon$13];
  assume I[iir#anon$13] <= R[iir#anon$13];
  assume R[iir#anon$13] <= C[iir#anon$13];
  assume 0 <= I[iir#anon$14];
  assume I[iir#anon$14] <= R[iir#anon$14];
  assume R[iir#anon$14] <= C[iir#anon$14];
  assume 0 <= I[iir#anon$15];
  assume I[iir#anon$15] <= R[iir#anon$15];
  assume R[iir#anon$15] <= C[iir#anon$15];
  assume 0 <= I[iir#anon$16];
  assume I[iir#anon$16] <= R[iir#anon$16];
  assume R[iir#anon$16] <= C[iir#anon$16];
  assume 0 <= I[iir#anon$17];
  assume I[iir#anon$17] <= R[iir#anon$17];
  assume R[iir#anon$17] <= C[iir#anon$17];
  assume 0 <= I[iir#anon$18];
  assume I[iir#anon$18] <= R[iir#anon$18];
  assume R[iir#anon$18] <= C[iir#anon$18];
  assume 0 <= I[iir#anon$19];
  assume I[iir#anon$19] <= R[iir#anon$19];
  assume R[iir#anon$19] <= C[iir#anon$19];
  assume 0 <= I[iir#anon$20];
  assume I[iir#anon$20] <= R[iir#anon$20];
  assume R[iir#anon$20] <= C[iir#anon$20];
  assume 0 <= I[iir#anon$21];
  assume I[iir#anon$21] <= R[iir#anon$21];
  assume R[iir#anon$21] <= C[iir#anon$21];
  assume 0 <= I[iir#anon$22];
  assume I[iir#anon$22] <= R[iir#anon$22];
  assume R[iir#anon$22] <= C[iir#anon$22];
  assume 0 <= I[iir#anon$23];
  assume I[iir#anon$23] <= R[iir#anon$23];
  assume R[iir#anon$23] <= C[iir#anon$23];
  assume I[iir#anon$23] == R[iir#anon$23];
  assume I[iir#anon$17] == I[iir#anon$8];
  assume I[iir#anon$18] == I[iir#anon$11];
  assume I[iir#anon$19] == I[iir#anon$14];
  assume I[iir#anon$20] == I[iir#anon$16];
  assume I[iir#anon$21] == I[iir#anon$17];
  assume I[iir#anon$21] == I[iir#anon$18];
  assume I[iir#anon$22] == I[iir#anon$19];
  assume I[iir#anon$22] == I[iir#anon$20];
  assume I[iir#anon$23] == I[iir#anon$21];
  assume I[iir#anon$23] == I[iir#anon$22];
  assume I[iir#anon$8] == I[iir#anon$7];
  assume I[iir#anon$9] == I[iir#anon$7];
  assume I[iir#anon$11] == I[iir#anon$10];
  assume I[iir#anon$12] == I[iir#anon$10];
  assume I[iir#anon$14] == I[iir#anon$13];
  assume I[iir#anon$15] == I[iir#anon$13];
  assume (C[iir#anon$10] == 0) ==> (AV#delay_1#data == 0);
  assume (C[iir#anon$10] > 0) ==> (AV#delay_1#data == M[iir#anon$9][R[iir#anon$9] - 1]);
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$10] > 0) ==> (M[iir#anon$10][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$10] - 0)) ==> (M[iir#anon$10][idx] == M[iir#anon$9][idx - 1])
  );
  assume (C[iir#anon$13] == 0) ==> (AV#delay_2#data == 0);
  assume (C[iir#anon$13] > 0) ==> (AV#delay_2#data == M[iir#anon$12][R[iir#anon$12] - 1]);
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$13] > 0) ==> (M[iir#anon$13][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$13] - 0)) ==> (M[iir#anon$13][idx] == M[iir#anon$12][idx - 1])
  );
  assume (C[iir#anon$16] == 0) ==> (AV#delay_3#data == 0);
  assume (C[iir#anon$16] > 0) ==> (AV#delay_3#data == M[iir#anon$15][R[iir#anon$15] - 1]);
  assume R[iir#anon$15] == C[iir#anon$16];
  assume (C[iir#anon$16] > 0) ==> (M[iir#anon$16][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$16] - 0)) ==> (M[iir#anon$16][idx] == M[iir#anon$15][idx - 1])
  );
  assume R[iir#anon$8] == C[iir#anon$17];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$17]) ==> (M[iir#anon$17][idx$] == (37 * M[iir#anon$8][idx$]))
  );
  assume R[iir#anon$11] == C[iir#anon$18];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$18]) ==> (M[iir#anon$18][idx$] == (109 * M[iir#anon$11][idx$]))
  );
  assume R[iir#anon$14] == C[iir#anon$19];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$19]) ==> (M[iir#anon$19][idx$] == (109 * M[iir#anon$14][idx$]))
  );
  assume R[iir#anon$16] == C[iir#anon$20];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$20]) ==> (M[iir#anon$20][idx$] == (37 * M[iir#anon$16][idx$]))
  );
  assume R[iir#anon$17] == C[iir#anon$21];
  assume R[iir#anon$18] == C[iir#anon$21];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$21]) ==> (M[iir#anon$21][idx$] == (M[iir#anon$17][idx$] + M[iir#anon$18][idx$]))
  );
  assume R[iir#anon$19] == C[iir#anon$22];
  assume R[iir#anon$20] == C[iir#anon$22];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$22]) ==> (M[iir#anon$22][idx$] == (M[iir#anon$19][idx$] + M[iir#anon$20][idx$]))
  );
  assume R[iir#anon$21] == C[iir#anon$23];
  assume R[iir#anon$22] == C[iir#anon$23];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$23]) ==> (M[iir#anon$23][idx$] == (M[iir#anon$21][idx$] + M[iir#anon$22][idx$]))
  );
  assume R[iir#anon$7] == C[iir#anon$8];
  assume R[iir#anon$7] == C[iir#anon$9];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$8]) ==> (M[iir#anon$8][idx$] == M[iir#anon$7][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$9]) ==> (M[iir#anon$9][idx$] == M[iir#anon$7][idx$])
  );
  assume R[iir#anon$10] == C[iir#anon$11];
  assume R[iir#anon$10] == C[iir#anon$12];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$11]) ==> (M[iir#anon$11][idx$] == M[iir#anon$10][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$12]) ==> (M[iir#anon$12][idx$] == M[iir#anon$10][idx$])
  );
  assume R[iir#anon$13] == C[iir#anon$14];
  assume R[iir#anon$13] == C[iir#anon$15];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$14]) ==> (M[iir#anon$14][idx$] == M[iir#anon$13][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[iir#anon$15]) ==> (M[iir#anon$15][idx$] == M[iir#anon$13][idx$])
  );
  assume (C[iir#anon$7] - I[iir#anon$7]) == 1;
  assume !(1 <= (C[iir#anon$9] - R[iir#anon$9]));
  assume !(1 <= (C[iir#anon$12] - R[iir#anon$12]));
  assume !(1 <= (C[iir#anon$15] - R[iir#anon$15]));
  assume !(1 <= (C[iir#anon$8] - R[iir#anon$8]));
  assume !(1 <= (C[iir#anon$11] - R[iir#anon$11]));
  assume !(1 <= (C[iir#anon$14] - R[iir#anon$14]));
  assume !(1 <= (C[iir#anon$16] - R[iir#anon$16]));
  assume !((1 <= (C[iir#anon$17] - R[iir#anon$17])) && (1 <= (C[iir#anon$18] - R[iir#anon$18])));
  assume !((1 <= (C[iir#anon$19] - R[iir#anon$19])) && (1 <= (C[iir#anon$20] - R[iir#anon$20])));
  assume !((1 <= (C[iir#anon$21] - R[iir#anon$21])) && (1 <= (C[iir#anon$22] - R[iir#anon$22])));
  assume !(1 <= (C[iir#anon$7] - R[iir#anon$7]));
  assume !(1 <= (C[iir#anon$10] - R[iir#anon$10]));
  assume !(1 <= (C[iir#anon$13] - R[iir#anon$13]));
  assert {:msg "38.13: Network action postcondition might not hold (#289)"} (I[iir#anon$23] == 0) ==> (M[iir#anon$23][I[iir#anon$23]] == (37 * M[iir#anon$7][I[iir#anon$7]]));
  assert {:msg "39.13: Network action postcondition might not hold (#290)"} (I[iir#anon$23] == 1) ==> (M[iir#anon$23][I[iir#anon$23]] == ((37 * M[iir#anon$7][I[iir#anon$7]]) + (109 * M[iir#anon$7][I[iir#anon$7] - 1])));
  assert {:msg "40.12: Network action postcondition might not hold (#291)"} (I[iir#anon$23] == 2) ==> (M[iir#anon$23][I[iir#anon$23]] == (((37 * M[iir#anon$7][I[iir#anon$7]]) + (109 * M[iir#anon$7][I[iir#anon$7] - 1])) + (109 * M[iir#anon$7][I[iir#anon$7] - 2])));
  assert {:msg "41.13: Network action postcondition might not hold (#292)"} (I[iir#anon$23] > 3) ==> (M[iir#anon$23][I[iir#anon$23]] == ((((37 * M[iir#anon$7][I[iir#anon$7]]) + (109 * M[iir#anon$7][I[iir#anon$7] - 1])) + (109 * M[iir#anon$7][I[iir#anon$7] - 2])) + (37 * M[iir#anon$7][I[iir#anon$7] - 3])));
  R[iir#anon$23] := R[iir#anon$23] + 1;
  I := R;
  assert {:msg "The network might not preserve the channel invariant (#293)"} I[iir#anon$17] == I[iir#anon$8];
  assert {:msg "The network might not preserve the channel invariant (#294)"} I[iir#anon$18] == I[iir#anon$11];
  assert {:msg "The network might not preserve the channel invariant (#295)"} I[iir#anon$19] == I[iir#anon$14];
  assert {:msg "The network might not preserve the channel invariant (#296)"} I[iir#anon$20] == I[iir#anon$16];
  assert {:msg "The network might not preserve the channel invariant (#297)"} I[iir#anon$21] == I[iir#anon$17];
  assert {:msg "The network might not preserve the channel invariant (#298)"} I[iir#anon$21] == I[iir#anon$18];
  assert {:msg "The network might not preserve the channel invariant (#299)"} I[iir#anon$22] == I[iir#anon$19];
  assert {:msg "The network might not preserve the channel invariant (#300)"} I[iir#anon$22] == I[iir#anon$20];
  assert {:msg "The network might not preserve the channel invariant (#301)"} I[iir#anon$23] == I[iir#anon$21];
  assert {:msg "The network might not preserve the channel invariant (#302)"} I[iir#anon$23] == I[iir#anon$22];
  assert {:msg "The network might not preserve the channel invariant (#303)"} I[iir#anon$8] == I[iir#anon$7];
  assert {:msg "The network might not preserve the channel invariant (#304)"} I[iir#anon$9] == I[iir#anon$7];
  assert {:msg "The network might not preserve the channel invariant (#305)"} I[iir#anon$11] == I[iir#anon$10];
  assert {:msg "The network might not preserve the channel invariant (#306)"} I[iir#anon$12] == I[iir#anon$10];
  assert {:msg "The network might not preserve the channel invariant (#307)"} I[iir#anon$14] == I[iir#anon$13];
  assert {:msg "The network might not preserve the channel invariant (#308)"} I[iir#anon$15] == I[iir#anon$13];
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel anon$7 (#309)"} (C[iir#anon$7] - R[iir#anon$7]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel anon$8 (#310)"} (C[iir#anon$8] - R[iir#anon$8]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel anon$9 (#311)"} (C[iir#anon$9] - R[iir#anon$9]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel anon$10 (#312)"} (C[iir#anon$10] - R[iir#anon$10]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel anon$11 (#313)"} (C[iir#anon$11] - R[iir#anon$11]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel anon$12 (#314)"} (C[iir#anon$12] - R[iir#anon$12]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel anon$13 (#315)"} (C[iir#anon$13] - R[iir#anon$13]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel anon$14 (#316)"} (C[iir#anon$14] - R[iir#anon$14]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel anon$15 (#317)"} (C[iir#anon$15] - R[iir#anon$15]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel anon$16 (#318)"} (C[iir#anon$16] - R[iir#anon$16]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel anon$17 (#319)"} (C[iir#anon$17] - R[iir#anon$17]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel anon$18 (#320)"} (C[iir#anon$18] - R[iir#anon$18]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel anon$19 (#321)"} (C[iir#anon$19] - R[iir#anon$19]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel anon$20 (#322)"} (C[iir#anon$20] - R[iir#anon$20]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel anon$21 (#323)"} (C[iir#anon$21] - R[iir#anon$21]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel anon$22 (#324)"} (C[iir#anon$22] - R[iir#anon$22]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel anon$23 (#325)"} (C[iir#anon$23] - R[iir#anon$23]) == 0;
}

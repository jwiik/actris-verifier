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
var B: CType;

var H: HType;

const unique this#: Actor;

function AT#Min(x:int, y: int): int { if x <= y then x else y }
function AT#Ite<T>(bool, T, T): T;
axiom (
  forall<T> cond: bool, thn: T, els: T :: { AT#Ite(cond, thn, els) }
    (cond ==> AT#Ite(cond,thn,els) == thn &&
    !cond ==> AT#Ite(cond,thn,els) == els)
);

// ---------------------------------------------------------------
// -- Integer division and modulo --------------------------------
// ---------------------------------------------------------------
function AT#Abs(x: int): int { if 0 <= x then x else -x }
function AT#Div(int, int): int;
function AT#Mod(int, int): int;
axiom (forall a,b: int :: AT#Div(a,b)*b + AT#Mod(a,b) == a);
axiom (forall a,b: int :: 0 <= AT#Mod(a,b) && AT#Mod(a,b) < AT#Abs(b));

// ---------------------------------------------------------------
// -- Shift operations for integers ------------------------------
// ---------------------------------------------------------------
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
  assert {:msg "FIR.actor(9.20): Initialization might not establish the invariant (#0)"} (C[out] == 0) ==> (data == k);
  assert {:msg "FIR.actor(10.20): Initialization might not establish the invariant (#1)"} (C[out] > 0) ==> (data == M[in][R[in] - 1]);
  assert {:msg "FIR.actor(11.20): Initialization might not establish the invariant (#2)"} R[in] == C[out];
  assert {:msg "FIR.actor(12.20): Initialization might not establish the invariant (#3)"} (C[out] > 0) ==> (M[out][0] == k);
  assert {:msg "FIR.actor(13.21): Initialization might not establish the invariant (#4)"} (forall idx: int :: 
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
  assume R[in] == C[out];
  in#0 := M[in][R[in]];
  R[in] := R[in] + 1;
  y := data;
  data := in#0;
  M[out][C[out]] := y;
  C[out] := C[out] + 1;
  assert {:msg "FIR.actor(9.20): Action at FIR.actor(16.3) might not preserve invariant (#5)"} (C[out] == 0) ==> (data == k);
  assert {:msg "FIR.actor(10.20): Action at FIR.actor(16.3) might not preserve invariant (#6)"} (C[out] > 0) ==> (data == M[in][R[in] - 1]);
  assert {:msg "FIR.actor(11.20): Action at FIR.actor(16.3) might not preserve invariant (#7)"} R[in] == C[out];
  assert {:msg "FIR.actor(12.20): Action at FIR.actor(16.3) might not preserve invariant (#8)"} (C[out] > 0) ==> (M[out][0] == k);
  assert {:msg "FIR.actor(13.21): Action at FIR.actor(16.3) might not preserve invariant (#9)"} (forall idx: int :: 
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
  assume (B[iir#anon$7] == 1) && (B[iir#anon$23] == 1);
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
  I := R;
  assert {:msg "Initialization of network 'iir' might not establish the network invariant: Unread tokens might be left on channel anon$7 (#10)"} (C[iir#anon$7] - R[iir#anon$7]) == 0;
  assert {:msg "Initialization of network 'iir' might not establish the network invariant: Unread tokens might be left on channel anon$8 (#11)"} (C[iir#anon$8] - R[iir#anon$8]) == 0;
  assert {:msg "Initialization of network 'iir' might not establish the network invariant: Unread tokens might be left on channel anon$9 (#12)"} (C[iir#anon$9] - R[iir#anon$9]) == 0;
  assert {:msg "Initialization of network 'iir' might not establish the network invariant: Unread tokens might be left on channel anon$10 (#13)"} (C[iir#anon$10] - R[iir#anon$10]) == 0;
  assert {:msg "Initialization of network 'iir' might not establish the network invariant: Unread tokens might be left on channel anon$11 (#14)"} (C[iir#anon$11] - R[iir#anon$11]) == 0;
  assert {:msg "Initialization of network 'iir' might not establish the network invariant: Unread tokens might be left on channel anon$12 (#15)"} (C[iir#anon$12] - R[iir#anon$12]) == 0;
  assert {:msg "Initialization of network 'iir' might not establish the network invariant: Unread tokens might be left on channel anon$13 (#16)"} (C[iir#anon$13] - R[iir#anon$13]) == 0;
  assert {:msg "Initialization of network 'iir' might not establish the network invariant: Unread tokens might be left on channel anon$14 (#17)"} (C[iir#anon$14] - R[iir#anon$14]) == 0;
  assert {:msg "Initialization of network 'iir' might not establish the network invariant: Unread tokens might be left on channel anon$15 (#18)"} (C[iir#anon$15] - R[iir#anon$15]) == 0;
  assert {:msg "Initialization of network 'iir' might not establish the network invariant: Unread tokens might be left on channel anon$16 (#19)"} (C[iir#anon$16] - R[iir#anon$16]) == 0;
  assert {:msg "Initialization of network 'iir' might not establish the network invariant: Unread tokens might be left on channel anon$17 (#20)"} (C[iir#anon$17] - R[iir#anon$17]) == 0;
  assert {:msg "Initialization of network 'iir' might not establish the network invariant: Unread tokens might be left on channel anon$18 (#21)"} (C[iir#anon$18] - R[iir#anon$18]) == 0;
  assert {:msg "Initialization of network 'iir' might not establish the network invariant: Unread tokens might be left on channel anon$19 (#22)"} (C[iir#anon$19] - R[iir#anon$19]) == 0;
  assert {:msg "Initialization of network 'iir' might not establish the network invariant: Unread tokens might be left on channel anon$20 (#23)"} (C[iir#anon$20] - R[iir#anon$20]) == 0;
  assert {:msg "Initialization of network 'iir' might not establish the network invariant: Unread tokens might be left on channel anon$21 (#24)"} (C[iir#anon$21] - R[iir#anon$21]) == 0;
  assert {:msg "Initialization of network 'iir' might not establish the network invariant: Unread tokens might be left on channel anon$22 (#25)"} (C[iir#anon$22] - R[iir#anon$22]) == 0;
  assert {:msg "Initialization of network 'iir' might not establish the network invariant: Unread tokens might be left on channel anon$23 (#26)"} (C[iir#anon$23] - R[iir#anon$23]) == 0;
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
  assume (B[iir#anon$7] == 1) && (B[iir#anon$23] == 1);
  assume I[iir#anon$10] == I[iir#anon$9];
  assume I[iir#anon$13] == I[iir#anon$12];
  assume I[iir#anon$16] == I[iir#anon$15];
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
  assume (C[iir#anon$7] - I[iir#anon$7]) <= 1;
  assume (C[iir#anon$10] == 0) ==> (AV#delay_1#data == 0);
  assume (C[iir#anon$10] > 0) ==> (AV#delay_1#data == M[iir#anon$9][R[iir#anon$9] - 1]);
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$10] > 0) ==> (M[iir#anon$10][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$10] - 0)) ==> (M[iir#anon$10][idx] == M[iir#anon$9][idx - 1])
  );
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$13] == 0) ==> (AV#delay_2#data == 0);
  assume (C[iir#anon$13] > 0) ==> (AV#delay_2#data == M[iir#anon$12][R[iir#anon$12] - 1]);
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$13] > 0) ==> (M[iir#anon$13][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$13] - 0)) ==> (M[iir#anon$13][idx] == M[iir#anon$12][idx - 1])
  );
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$16] == 0) ==> (AV#delay_3#data == 0);
  assume (C[iir#anon$16] > 0) ==> (AV#delay_3#data == M[iir#anon$15][R[iir#anon$15] - 1]);
  assume R[iir#anon$15] == C[iir#anon$16];
  assume (C[iir#anon$16] > 0) ==> (M[iir#anon$16][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$16] - 0)) ==> (M[iir#anon$16][idx] == M[iir#anon$15][idx - 1])
  );
  assume R[iir#anon$15] == C[iir#anon$16];
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
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$13] == 0) ==> (AV#delay_2#data == 0);
  assume (C[iir#anon$13] > 0) ==> (AV#delay_2#data == M[iir#anon$12][R[iir#anon$12] - 1]);
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$13] > 0) ==> (M[iir#anon$13][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$13] - 0)) ==> (M[iir#anon$13][idx] == M[iir#anon$12][idx - 1])
  );
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$16] == 0) ==> (AV#delay_3#data == 0);
  assume (C[iir#anon$16] > 0) ==> (AV#delay_3#data == M[iir#anon$15][R[iir#anon$15] - 1]);
  assume R[iir#anon$15] == C[iir#anon$16];
  assume (C[iir#anon$16] > 0) ==> (M[iir#anon$16][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$16] - 0)) ==> (M[iir#anon$16][idx] == M[iir#anon$15][idx - 1])
  );
  assume R[iir#anon$15] == C[iir#anon$16];
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
  assume (B[iir#anon$7] == 1) && (B[iir#anon$23] == 1);
  assume I[iir#anon$10] == I[iir#anon$9];
  assume I[iir#anon$13] == I[iir#anon$12];
  assume I[iir#anon$16] == I[iir#anon$15];
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
  assume (C[iir#anon$7] - I[iir#anon$7]) <= 1;
  assume (C[iir#anon$10] == 0) ==> (AV#delay_1#data == 0);
  assume (C[iir#anon$10] > 0) ==> (AV#delay_1#data == M[iir#anon$9][R[iir#anon$9] - 1]);
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$10] > 0) ==> (M[iir#anon$10][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$10] - 0)) ==> (M[iir#anon$10][idx] == M[iir#anon$9][idx - 1])
  );
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$13] == 0) ==> (AV#delay_2#data == 0);
  assume (C[iir#anon$13] > 0) ==> (AV#delay_2#data == M[iir#anon$12][R[iir#anon$12] - 1]);
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$13] > 0) ==> (M[iir#anon$13][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$13] - 0)) ==> (M[iir#anon$13][idx] == M[iir#anon$12][idx - 1])
  );
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$16] == 0) ==> (AV#delay_3#data == 0);
  assume (C[iir#anon$16] > 0) ==> (AV#delay_3#data == M[iir#anon$15][R[iir#anon$15] - 1]);
  assume R[iir#anon$15] == C[iir#anon$16];
  assume (C[iir#anon$16] > 0) ==> (M[iir#anon$16][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$16] - 0)) ==> (M[iir#anon$16][idx] == M[iir#anon$15][idx - 1])
  );
  assume R[iir#anon$15] == C[iir#anon$16];
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
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$13] == 0) ==> (AV#delay_2#data == 0);
  assume (C[iir#anon$13] > 0) ==> (AV#delay_2#data == M[iir#anon$12][R[iir#anon$12] - 1]);
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$13] > 0) ==> (M[iir#anon$13][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$13] - 0)) ==> (M[iir#anon$13][idx] == M[iir#anon$12][idx - 1])
  );
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$16] == 0) ==> (AV#delay_3#data == 0);
  assume (C[iir#anon$16] > 0) ==> (AV#delay_3#data == M[iir#anon$15][R[iir#anon$15] - 1]);
  assume R[iir#anon$15] == C[iir#anon$16];
  assume (C[iir#anon$16] > 0) ==> (M[iir#anon$16][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$16] - 0)) ==> (M[iir#anon$16][idx] == M[iir#anon$15][idx - 1])
  );
  assume R[iir#anon$15] == C[iir#anon$16];
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
  assume (B[iir#anon$7] == 1) && (B[iir#anon$23] == 1);
  assume I[iir#anon$10] == I[iir#anon$9];
  assume I[iir#anon$13] == I[iir#anon$12];
  assume I[iir#anon$16] == I[iir#anon$15];
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
  assume (C[iir#anon$7] - I[iir#anon$7]) <= 1;
  assume (C[iir#anon$10] == 0) ==> (AV#delay_1#data == 0);
  assume (C[iir#anon$10] > 0) ==> (AV#delay_1#data == M[iir#anon$9][R[iir#anon$9] - 1]);
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$10] > 0) ==> (M[iir#anon$10][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$10] - 0)) ==> (M[iir#anon$10][idx] == M[iir#anon$9][idx - 1])
  );
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$13] == 0) ==> (AV#delay_2#data == 0);
  assume (C[iir#anon$13] > 0) ==> (AV#delay_2#data == M[iir#anon$12][R[iir#anon$12] - 1]);
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$13] > 0) ==> (M[iir#anon$13][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$13] - 0)) ==> (M[iir#anon$13][idx] == M[iir#anon$12][idx - 1])
  );
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$16] == 0) ==> (AV#delay_3#data == 0);
  assume (C[iir#anon$16] > 0) ==> (AV#delay_3#data == M[iir#anon$15][R[iir#anon$15] - 1]);
  assume R[iir#anon$15] == C[iir#anon$16];
  assume (C[iir#anon$16] > 0) ==> (M[iir#anon$16][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$16] - 0)) ==> (M[iir#anon$16][idx] == M[iir#anon$15][idx - 1])
  );
  assume R[iir#anon$15] == C[iir#anon$16];
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
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$13] == 0) ==> (AV#delay_2#data == 0);
  assume (C[iir#anon$13] > 0) ==> (AV#delay_2#data == M[iir#anon$12][R[iir#anon$12] - 1]);
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$13] > 0) ==> (M[iir#anon$13][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$13] - 0)) ==> (M[iir#anon$13][idx] == M[iir#anon$12][idx - 1])
  );
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$16] == 0) ==> (AV#delay_3#data == 0);
  assume (C[iir#anon$16] > 0) ==> (AV#delay_3#data == M[iir#anon$15][R[iir#anon$15] - 1]);
  assume R[iir#anon$15] == C[iir#anon$16];
  assume (C[iir#anon$16] > 0) ==> (M[iir#anon$16][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$16] - 0)) ==> (M[iir#anon$16][idx] == M[iir#anon$15][idx - 1])
  );
  assume R[iir#anon$15] == C[iir#anon$16];
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
  assume (B[iir#anon$7] == 1) && (B[iir#anon$23] == 1);
  assume I[iir#anon$10] == I[iir#anon$9];
  assume I[iir#anon$13] == I[iir#anon$12];
  assume I[iir#anon$16] == I[iir#anon$15];
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
  assume (C[iir#anon$7] - I[iir#anon$7]) <= 1;
  assume (C[iir#anon$10] == 0) ==> (AV#delay_1#data == 0);
  assume (C[iir#anon$10] > 0) ==> (AV#delay_1#data == M[iir#anon$9][R[iir#anon$9] - 1]);
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$10] > 0) ==> (M[iir#anon$10][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$10] - 0)) ==> (M[iir#anon$10][idx] == M[iir#anon$9][idx - 1])
  );
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$13] == 0) ==> (AV#delay_2#data == 0);
  assume (C[iir#anon$13] > 0) ==> (AV#delay_2#data == M[iir#anon$12][R[iir#anon$12] - 1]);
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$13] > 0) ==> (M[iir#anon$13][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$13] - 0)) ==> (M[iir#anon$13][idx] == M[iir#anon$12][idx - 1])
  );
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$16] == 0) ==> (AV#delay_3#data == 0);
  assume (C[iir#anon$16] > 0) ==> (AV#delay_3#data == M[iir#anon$15][R[iir#anon$15] - 1]);
  assume R[iir#anon$15] == C[iir#anon$16];
  assume (C[iir#anon$16] > 0) ==> (M[iir#anon$16][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$16] - 0)) ==> (M[iir#anon$16][idx] == M[iir#anon$15][idx - 1])
  );
  assume R[iir#anon$15] == C[iir#anon$16];
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
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$13] == 0) ==> (AV#delay_2#data == 0);
  assume (C[iir#anon$13] > 0) ==> (AV#delay_2#data == M[iir#anon$12][R[iir#anon$12] - 1]);
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$13] > 0) ==> (M[iir#anon$13][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$13] - 0)) ==> (M[iir#anon$13][idx] == M[iir#anon$12][idx - 1])
  );
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$16] == 0) ==> (AV#delay_3#data == 0);
  assume (C[iir#anon$16] > 0) ==> (AV#delay_3#data == M[iir#anon$15][R[iir#anon$15] - 1]);
  assume R[iir#anon$15] == C[iir#anon$16];
  assume (C[iir#anon$16] > 0) ==> (M[iir#anon$16][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$16] - 0)) ==> (M[iir#anon$16][idx] == M[iir#anon$15][idx - 1])
  );
  assume R[iir#anon$15] == C[iir#anon$16];
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
  assume (B[iir#anon$7] == 1) && (B[iir#anon$23] == 1);
  assume I[iir#anon$10] == I[iir#anon$9];
  assume I[iir#anon$13] == I[iir#anon$12];
  assume I[iir#anon$16] == I[iir#anon$15];
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
  assume (C[iir#anon$7] - I[iir#anon$7]) <= 1;
  assume (C[iir#anon$10] == 0) ==> (AV#delay_1#data == 0);
  assume (C[iir#anon$10] > 0) ==> (AV#delay_1#data == M[iir#anon$9][R[iir#anon$9] - 1]);
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$10] > 0) ==> (M[iir#anon$10][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$10] - 0)) ==> (M[iir#anon$10][idx] == M[iir#anon$9][idx - 1])
  );
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$13] == 0) ==> (AV#delay_2#data == 0);
  assume (C[iir#anon$13] > 0) ==> (AV#delay_2#data == M[iir#anon$12][R[iir#anon$12] - 1]);
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$13] > 0) ==> (M[iir#anon$13][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$13] - 0)) ==> (M[iir#anon$13][idx] == M[iir#anon$12][idx - 1])
  );
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$16] == 0) ==> (AV#delay_3#data == 0);
  assume (C[iir#anon$16] > 0) ==> (AV#delay_3#data == M[iir#anon$15][R[iir#anon$15] - 1]);
  assume R[iir#anon$15] == C[iir#anon$16];
  assume (C[iir#anon$16] > 0) ==> (M[iir#anon$16][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$16] - 0)) ==> (M[iir#anon$16][idx] == M[iir#anon$15][idx - 1])
  );
  assume R[iir#anon$15] == C[iir#anon$16];
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
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$13] == 0) ==> (AV#delay_2#data == 0);
  assume (C[iir#anon$13] > 0) ==> (AV#delay_2#data == M[iir#anon$12][R[iir#anon$12] - 1]);
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$13] > 0) ==> (M[iir#anon$13][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$13] - 0)) ==> (M[iir#anon$13][idx] == M[iir#anon$12][idx - 1])
  );
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$16] == 0) ==> (AV#delay_3#data == 0);
  assume (C[iir#anon$16] > 0) ==> (AV#delay_3#data == M[iir#anon$15][R[iir#anon$15] - 1]);
  assume R[iir#anon$15] == C[iir#anon$16];
  assume (C[iir#anon$16] > 0) ==> (M[iir#anon$16][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$16] - 0)) ==> (M[iir#anon$16][idx] == M[iir#anon$15][idx - 1])
  );
  assume R[iir#anon$15] == C[iir#anon$16];
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
  assume (B[iir#anon$7] == 1) && (B[iir#anon$23] == 1);
  assume I[iir#anon$10] == I[iir#anon$9];
  assume I[iir#anon$13] == I[iir#anon$12];
  assume I[iir#anon$16] == I[iir#anon$15];
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
  assume (C[iir#anon$7] - I[iir#anon$7]) <= 1;
  assume (C[iir#anon$10] == 0) ==> (AV#delay_1#data == 0);
  assume (C[iir#anon$10] > 0) ==> (AV#delay_1#data == M[iir#anon$9][R[iir#anon$9] - 1]);
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$10] > 0) ==> (M[iir#anon$10][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$10] - 0)) ==> (M[iir#anon$10][idx] == M[iir#anon$9][idx - 1])
  );
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$13] == 0) ==> (AV#delay_2#data == 0);
  assume (C[iir#anon$13] > 0) ==> (AV#delay_2#data == M[iir#anon$12][R[iir#anon$12] - 1]);
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$13] > 0) ==> (M[iir#anon$13][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$13] - 0)) ==> (M[iir#anon$13][idx] == M[iir#anon$12][idx - 1])
  );
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$16] == 0) ==> (AV#delay_3#data == 0);
  assume (C[iir#anon$16] > 0) ==> (AV#delay_3#data == M[iir#anon$15][R[iir#anon$15] - 1]);
  assume R[iir#anon$15] == C[iir#anon$16];
  assume (C[iir#anon$16] > 0) ==> (M[iir#anon$16][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$16] - 0)) ==> (M[iir#anon$16][idx] == M[iir#anon$15][idx - 1])
  );
  assume R[iir#anon$15] == C[iir#anon$16];
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
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$13] == 0) ==> (AV#delay_2#data == 0);
  assume (C[iir#anon$13] > 0) ==> (AV#delay_2#data == M[iir#anon$12][R[iir#anon$12] - 1]);
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$13] > 0) ==> (M[iir#anon$13][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$13] - 0)) ==> (M[iir#anon$13][idx] == M[iir#anon$12][idx - 1])
  );
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$16] == 0) ==> (AV#delay_3#data == 0);
  assume (C[iir#anon$16] > 0) ==> (AV#delay_3#data == M[iir#anon$15][R[iir#anon$15] - 1]);
  assume R[iir#anon$15] == C[iir#anon$16];
  assume (C[iir#anon$16] > 0) ==> (M[iir#anon$16][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$16] - 0)) ==> (M[iir#anon$16][idx] == M[iir#anon$15][idx - 1])
  );
  assume R[iir#anon$15] == C[iir#anon$16];
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
  assume (B[iir#anon$7] == 1) && (B[iir#anon$23] == 1);
  assume I[iir#anon$10] == I[iir#anon$9];
  assume I[iir#anon$13] == I[iir#anon$12];
  assume I[iir#anon$16] == I[iir#anon$15];
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
  assume (C[iir#anon$7] - I[iir#anon$7]) <= 1;
  assume (C[iir#anon$10] == 0) ==> (AV#delay_1#data == 0);
  assume (C[iir#anon$10] > 0) ==> (AV#delay_1#data == M[iir#anon$9][R[iir#anon$9] - 1]);
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$10] > 0) ==> (M[iir#anon$10][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$10] - 0)) ==> (M[iir#anon$10][idx] == M[iir#anon$9][idx - 1])
  );
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$13] == 0) ==> (AV#delay_2#data == 0);
  assume (C[iir#anon$13] > 0) ==> (AV#delay_2#data == M[iir#anon$12][R[iir#anon$12] - 1]);
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$13] > 0) ==> (M[iir#anon$13][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$13] - 0)) ==> (M[iir#anon$13][idx] == M[iir#anon$12][idx - 1])
  );
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$16] == 0) ==> (AV#delay_3#data == 0);
  assume (C[iir#anon$16] > 0) ==> (AV#delay_3#data == M[iir#anon$15][R[iir#anon$15] - 1]);
  assume R[iir#anon$15] == C[iir#anon$16];
  assume (C[iir#anon$16] > 0) ==> (M[iir#anon$16][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$16] - 0)) ==> (M[iir#anon$16][idx] == M[iir#anon$15][idx - 1])
  );
  assume R[iir#anon$15] == C[iir#anon$16];
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
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$13] == 0) ==> (AV#delay_2#data == 0);
  assume (C[iir#anon$13] > 0) ==> (AV#delay_2#data == M[iir#anon$12][R[iir#anon$12] - 1]);
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$13] > 0) ==> (M[iir#anon$13][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$13] - 0)) ==> (M[iir#anon$13][idx] == M[iir#anon$12][idx - 1])
  );
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$16] == 0) ==> (AV#delay_3#data == 0);
  assume (C[iir#anon$16] > 0) ==> (AV#delay_3#data == M[iir#anon$15][R[iir#anon$15] - 1]);
  assume R[iir#anon$15] == C[iir#anon$16];
  assume (C[iir#anon$16] > 0) ==> (M[iir#anon$16][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$16] - 0)) ==> (M[iir#anon$16][idx] == M[iir#anon$15][idx - 1])
  );
  assume R[iir#anon$15] == C[iir#anon$16];
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
  assume (B[iir#anon$7] == 1) && (B[iir#anon$23] == 1);
  assume I[iir#anon$10] == I[iir#anon$9];
  assume I[iir#anon$13] == I[iir#anon$12];
  assume I[iir#anon$16] == I[iir#anon$15];
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
  assume (C[iir#anon$7] - I[iir#anon$7]) <= 1;
  assume (C[iir#anon$10] == 0) ==> (AV#delay_1#data == 0);
  assume (C[iir#anon$10] > 0) ==> (AV#delay_1#data == M[iir#anon$9][R[iir#anon$9] - 1]);
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$10] > 0) ==> (M[iir#anon$10][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$10] - 0)) ==> (M[iir#anon$10][idx] == M[iir#anon$9][idx - 1])
  );
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$13] == 0) ==> (AV#delay_2#data == 0);
  assume (C[iir#anon$13] > 0) ==> (AV#delay_2#data == M[iir#anon$12][R[iir#anon$12] - 1]);
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$13] > 0) ==> (M[iir#anon$13][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$13] - 0)) ==> (M[iir#anon$13][idx] == M[iir#anon$12][idx - 1])
  );
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$16] == 0) ==> (AV#delay_3#data == 0);
  assume (C[iir#anon$16] > 0) ==> (AV#delay_3#data == M[iir#anon$15][R[iir#anon$15] - 1]);
  assume R[iir#anon$15] == C[iir#anon$16];
  assume (C[iir#anon$16] > 0) ==> (M[iir#anon$16][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$16] - 0)) ==> (M[iir#anon$16][idx] == M[iir#anon$15][idx - 1])
  );
  assume R[iir#anon$15] == C[iir#anon$16];
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
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$13] == 0) ==> (AV#delay_2#data == 0);
  assume (C[iir#anon$13] > 0) ==> (AV#delay_2#data == M[iir#anon$12][R[iir#anon$12] - 1]);
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$13] > 0) ==> (M[iir#anon$13][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$13] - 0)) ==> (M[iir#anon$13][idx] == M[iir#anon$12][idx - 1])
  );
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$16] == 0) ==> (AV#delay_3#data == 0);
  assume (C[iir#anon$16] > 0) ==> (AV#delay_3#data == M[iir#anon$15][R[iir#anon$15] - 1]);
  assume R[iir#anon$15] == C[iir#anon$16];
  assume (C[iir#anon$16] > 0) ==> (M[iir#anon$16][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$16] - 0)) ==> (M[iir#anon$16][idx] == M[iir#anon$15][idx - 1])
  );
  assume R[iir#anon$15] == C[iir#anon$16];
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
  assume (B[iir#anon$7] == 1) && (B[iir#anon$23] == 1);
  assume I[iir#anon$10] == I[iir#anon$9];
  assume I[iir#anon$13] == I[iir#anon$12];
  assume I[iir#anon$16] == I[iir#anon$15];
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
  assume (C[iir#anon$7] - I[iir#anon$7]) <= 1;
  assume (C[iir#anon$10] == 0) ==> (AV#delay_1#data == 0);
  assume (C[iir#anon$10] > 0) ==> (AV#delay_1#data == M[iir#anon$9][R[iir#anon$9] - 1]);
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$10] > 0) ==> (M[iir#anon$10][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$10] - 0)) ==> (M[iir#anon$10][idx] == M[iir#anon$9][idx - 1])
  );
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$13] == 0) ==> (AV#delay_2#data == 0);
  assume (C[iir#anon$13] > 0) ==> (AV#delay_2#data == M[iir#anon$12][R[iir#anon$12] - 1]);
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$13] > 0) ==> (M[iir#anon$13][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$13] - 0)) ==> (M[iir#anon$13][idx] == M[iir#anon$12][idx - 1])
  );
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$16] == 0) ==> (AV#delay_3#data == 0);
  assume (C[iir#anon$16] > 0) ==> (AV#delay_3#data == M[iir#anon$15][R[iir#anon$15] - 1]);
  assume R[iir#anon$15] == C[iir#anon$16];
  assume (C[iir#anon$16] > 0) ==> (M[iir#anon$16][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$16] - 0)) ==> (M[iir#anon$16][idx] == M[iir#anon$15][idx - 1])
  );
  assume R[iir#anon$15] == C[iir#anon$16];
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
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$13] == 0) ==> (AV#delay_2#data == 0);
  assume (C[iir#anon$13] > 0) ==> (AV#delay_2#data == M[iir#anon$12][R[iir#anon$12] - 1]);
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$13] > 0) ==> (M[iir#anon$13][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$13] - 0)) ==> (M[iir#anon$13][idx] == M[iir#anon$12][idx - 1])
  );
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$16] == 0) ==> (AV#delay_3#data == 0);
  assume (C[iir#anon$16] > 0) ==> (AV#delay_3#data == M[iir#anon$15][R[iir#anon$15] - 1]);
  assume R[iir#anon$15] == C[iir#anon$16];
  assume (C[iir#anon$16] > 0) ==> (M[iir#anon$16][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$16] - 0)) ==> (M[iir#anon$16][idx] == M[iir#anon$15][idx - 1])
  );
  assume R[iir#anon$15] == C[iir#anon$16];
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
  assume (B[iir#anon$7] == 1) && (B[iir#anon$23] == 1);
  assume I[iir#anon$10] == I[iir#anon$9];
  assume I[iir#anon$13] == I[iir#anon$12];
  assume I[iir#anon$16] == I[iir#anon$15];
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
  assume (C[iir#anon$7] - I[iir#anon$7]) <= 1;
  assume (C[iir#anon$10] == 0) ==> (AV#delay_1#data == 0);
  assume (C[iir#anon$10] > 0) ==> (AV#delay_1#data == M[iir#anon$9][R[iir#anon$9] - 1]);
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$10] > 0) ==> (M[iir#anon$10][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$10] - 0)) ==> (M[iir#anon$10][idx] == M[iir#anon$9][idx - 1])
  );
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$13] == 0) ==> (AV#delay_2#data == 0);
  assume (C[iir#anon$13] > 0) ==> (AV#delay_2#data == M[iir#anon$12][R[iir#anon$12] - 1]);
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$13] > 0) ==> (M[iir#anon$13][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$13] - 0)) ==> (M[iir#anon$13][idx] == M[iir#anon$12][idx - 1])
  );
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$16] == 0) ==> (AV#delay_3#data == 0);
  assume (C[iir#anon$16] > 0) ==> (AV#delay_3#data == M[iir#anon$15][R[iir#anon$15] - 1]);
  assume R[iir#anon$15] == C[iir#anon$16];
  assume (C[iir#anon$16] > 0) ==> (M[iir#anon$16][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$16] - 0)) ==> (M[iir#anon$16][idx] == M[iir#anon$15][idx - 1])
  );
  assume R[iir#anon$15] == C[iir#anon$16];
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
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$13] == 0) ==> (AV#delay_2#data == 0);
  assume (C[iir#anon$13] > 0) ==> (AV#delay_2#data == M[iir#anon$12][R[iir#anon$12] - 1]);
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$13] > 0) ==> (M[iir#anon$13][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$13] - 0)) ==> (M[iir#anon$13][idx] == M[iir#anon$12][idx - 1])
  );
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$16] == 0) ==> (AV#delay_3#data == 0);
  assume (C[iir#anon$16] > 0) ==> (AV#delay_3#data == M[iir#anon$15][R[iir#anon$15] - 1]);
  assume R[iir#anon$15] == C[iir#anon$16];
  assume (C[iir#anon$16] > 0) ==> (M[iir#anon$16][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$16] - 0)) ==> (M[iir#anon$16][idx] == M[iir#anon$15][idx - 1])
  );
  assume R[iir#anon$15] == C[iir#anon$16];
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
  assume (B[iir#anon$7] == 1) && (B[iir#anon$23] == 1);
  assume I[iir#anon$10] == I[iir#anon$9];
  assume I[iir#anon$13] == I[iir#anon$12];
  assume I[iir#anon$16] == I[iir#anon$15];
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
  assume (C[iir#anon$7] - I[iir#anon$7]) <= 1;
  assume (C[iir#anon$10] == 0) ==> (AV#delay_1#data == 0);
  assume (C[iir#anon$10] > 0) ==> (AV#delay_1#data == M[iir#anon$9][R[iir#anon$9] - 1]);
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$10] > 0) ==> (M[iir#anon$10][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$10] - 0)) ==> (M[iir#anon$10][idx] == M[iir#anon$9][idx - 1])
  );
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$13] == 0) ==> (AV#delay_2#data == 0);
  assume (C[iir#anon$13] > 0) ==> (AV#delay_2#data == M[iir#anon$12][R[iir#anon$12] - 1]);
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$13] > 0) ==> (M[iir#anon$13][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$13] - 0)) ==> (M[iir#anon$13][idx] == M[iir#anon$12][idx - 1])
  );
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$16] == 0) ==> (AV#delay_3#data == 0);
  assume (C[iir#anon$16] > 0) ==> (AV#delay_3#data == M[iir#anon$15][R[iir#anon$15] - 1]);
  assume R[iir#anon$15] == C[iir#anon$16];
  assume (C[iir#anon$16] > 0) ==> (M[iir#anon$16][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$16] - 0)) ==> (M[iir#anon$16][idx] == M[iir#anon$15][idx - 1])
  );
  assume R[iir#anon$15] == C[iir#anon$16];
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
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$13] == 0) ==> (AV#delay_2#data == 0);
  assume (C[iir#anon$13] > 0) ==> (AV#delay_2#data == M[iir#anon$12][R[iir#anon$12] - 1]);
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$13] > 0) ==> (M[iir#anon$13][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$13] - 0)) ==> (M[iir#anon$13][idx] == M[iir#anon$12][idx - 1])
  );
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$16] == 0) ==> (AV#delay_3#data == 0);
  assume (C[iir#anon$16] > 0) ==> (AV#delay_3#data == M[iir#anon$15][R[iir#anon$15] - 1]);
  assume R[iir#anon$15] == C[iir#anon$16];
  assume (C[iir#anon$16] > 0) ==> (M[iir#anon$16][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$16] - 0)) ==> (M[iir#anon$16][idx] == M[iir#anon$15][idx - 1])
  );
  assume R[iir#anon$15] == C[iir#anon$16];
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
  assume (B[iir#anon$7] == 1) && (B[iir#anon$23] == 1);
  assume I[iir#anon$10] == I[iir#anon$9];
  assume I[iir#anon$13] == I[iir#anon$12];
  assume I[iir#anon$16] == I[iir#anon$15];
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
  assume (C[iir#anon$7] - I[iir#anon$7]) <= 1;
  assume (C[iir#anon$10] == 0) ==> (AV#delay_1#data == 0);
  assume (C[iir#anon$10] > 0) ==> (AV#delay_1#data == M[iir#anon$9][R[iir#anon$9] - 1]);
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$10] > 0) ==> (M[iir#anon$10][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$10] - 0)) ==> (M[iir#anon$10][idx] == M[iir#anon$9][idx - 1])
  );
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$13] == 0) ==> (AV#delay_2#data == 0);
  assume (C[iir#anon$13] > 0) ==> (AV#delay_2#data == M[iir#anon$12][R[iir#anon$12] - 1]);
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$13] > 0) ==> (M[iir#anon$13][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$13] - 0)) ==> (M[iir#anon$13][idx] == M[iir#anon$12][idx - 1])
  );
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$16] == 0) ==> (AV#delay_3#data == 0);
  assume (C[iir#anon$16] > 0) ==> (AV#delay_3#data == M[iir#anon$15][R[iir#anon$15] - 1]);
  assume R[iir#anon$15] == C[iir#anon$16];
  assume (C[iir#anon$16] > 0) ==> (M[iir#anon$16][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$16] - 0)) ==> (M[iir#anon$16][idx] == M[iir#anon$15][idx - 1])
  );
  assume R[iir#anon$15] == C[iir#anon$16];
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
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$13] == 0) ==> (AV#delay_2#data == 0);
  assume (C[iir#anon$13] > 0) ==> (AV#delay_2#data == M[iir#anon$12][R[iir#anon$12] - 1]);
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$13] > 0) ==> (M[iir#anon$13][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$13] - 0)) ==> (M[iir#anon$13][idx] == M[iir#anon$12][idx - 1])
  );
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$16] == 0) ==> (AV#delay_3#data == 0);
  assume (C[iir#anon$16] > 0) ==> (AV#delay_3#data == M[iir#anon$15][R[iir#anon$15] - 1]);
  assume R[iir#anon$15] == C[iir#anon$16];
  assume (C[iir#anon$16] > 0) ==> (M[iir#anon$16][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$16] - 0)) ==> (M[iir#anon$16][idx] == M[iir#anon$15][idx - 1])
  );
  assume R[iir#anon$15] == C[iir#anon$16];
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
  assume (B[iir#anon$7] == 1) && (B[iir#anon$23] == 1);
  assume I[iir#anon$10] == I[iir#anon$9];
  assume I[iir#anon$13] == I[iir#anon$12];
  assume I[iir#anon$16] == I[iir#anon$15];
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
  assume (C[iir#anon$7] - I[iir#anon$7]) <= 1;
  assume (C[iir#anon$10] == 0) ==> (AV#delay_1#data == 0);
  assume (C[iir#anon$10] > 0) ==> (AV#delay_1#data == M[iir#anon$9][R[iir#anon$9] - 1]);
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$10] > 0) ==> (M[iir#anon$10][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$10] - 0)) ==> (M[iir#anon$10][idx] == M[iir#anon$9][idx - 1])
  );
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$13] == 0) ==> (AV#delay_2#data == 0);
  assume (C[iir#anon$13] > 0) ==> (AV#delay_2#data == M[iir#anon$12][R[iir#anon$12] - 1]);
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$13] > 0) ==> (M[iir#anon$13][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$13] - 0)) ==> (M[iir#anon$13][idx] == M[iir#anon$12][idx - 1])
  );
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$16] == 0) ==> (AV#delay_3#data == 0);
  assume (C[iir#anon$16] > 0) ==> (AV#delay_3#data == M[iir#anon$15][R[iir#anon$15] - 1]);
  assume R[iir#anon$15] == C[iir#anon$16];
  assume (C[iir#anon$16] > 0) ==> (M[iir#anon$16][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$16] - 0)) ==> (M[iir#anon$16][idx] == M[iir#anon$15][idx - 1])
  );
  assume R[iir#anon$15] == C[iir#anon$16];
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
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$13] == 0) ==> (AV#delay_2#data == 0);
  assume (C[iir#anon$13] > 0) ==> (AV#delay_2#data == M[iir#anon$12][R[iir#anon$12] - 1]);
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$13] > 0) ==> (M[iir#anon$13][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$13] - 0)) ==> (M[iir#anon$13][idx] == M[iir#anon$12][idx - 1])
  );
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$16] == 0) ==> (AV#delay_3#data == 0);
  assume (C[iir#anon$16] > 0) ==> (AV#delay_3#data == M[iir#anon$15][R[iir#anon$15] - 1]);
  assume R[iir#anon$15] == C[iir#anon$16];
  assume (C[iir#anon$16] > 0) ==> (M[iir#anon$16][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$16] - 0)) ==> (M[iir#anon$16][idx] == M[iir#anon$15][idx - 1])
  );
  assume R[iir#anon$15] == C[iir#anon$16];
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
  assume (B[iir#anon$7] == 1) && (B[iir#anon$23] == 1);
  assume (B[iir#anon$7] == 1) && (B[iir#anon$23] == 1);
  assume (C[iir#anon$7] - I[iir#anon$7]) < 1;
  assume I[iir#anon$10] == I[iir#anon$9];
  assume I[iir#anon$13] == I[iir#anon$12];
  assume I[iir#anon$16] == I[iir#anon$15];
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
  assume (C[iir#anon$7] - I[iir#anon$7]) <= 1;
  assume (C[iir#anon$10] == 0) ==> (AV#delay_1#data == 0);
  assume (C[iir#anon$10] > 0) ==> (AV#delay_1#data == M[iir#anon$9][R[iir#anon$9] - 1]);
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$10] > 0) ==> (M[iir#anon$10][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$10] - 0)) ==> (M[iir#anon$10][idx] == M[iir#anon$9][idx - 1])
  );
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$13] == 0) ==> (AV#delay_2#data == 0);
  assume (C[iir#anon$13] > 0) ==> (AV#delay_2#data == M[iir#anon$12][R[iir#anon$12] - 1]);
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$13] > 0) ==> (M[iir#anon$13][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$13] - 0)) ==> (M[iir#anon$13][idx] == M[iir#anon$12][idx - 1])
  );
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$16] == 0) ==> (AV#delay_3#data == 0);
  assume (C[iir#anon$16] > 0) ==> (AV#delay_3#data == M[iir#anon$15][R[iir#anon$15] - 1]);
  assume R[iir#anon$15] == C[iir#anon$16];
  assume (C[iir#anon$16] > 0) ==> (M[iir#anon$16][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$16] - 0)) ==> (M[iir#anon$16][idx] == M[iir#anon$15][idx - 1])
  );
  assume R[iir#anon$15] == C[iir#anon$16];
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
  assert {:msg "Channel invariant might be falsified by network input (#27)"} I[iir#anon$10] == I[iir#anon$9];
  assert {:msg "Channel invariant might be falsified by network input (#28)"} I[iir#anon$13] == I[iir#anon$12];
  assert {:msg "Channel invariant might be falsified by network input (#29)"} I[iir#anon$16] == I[iir#anon$15];
  assert {:msg "Channel invariant might be falsified by network input (#30)"} I[iir#anon$17] == I[iir#anon$8];
  assert {:msg "Channel invariant might be falsified by network input (#31)"} I[iir#anon$18] == I[iir#anon$11];
  assert {:msg "Channel invariant might be falsified by network input (#32)"} I[iir#anon$19] == I[iir#anon$14];
  assert {:msg "Channel invariant might be falsified by network input (#33)"} I[iir#anon$20] == I[iir#anon$16];
  assert {:msg "Channel invariant might be falsified by network input (#34)"} I[iir#anon$21] == I[iir#anon$17];
  assert {:msg "Channel invariant might be falsified by network input (#35)"} I[iir#anon$21] == I[iir#anon$18];
  assert {:msg "Channel invariant might be falsified by network input (#36)"} I[iir#anon$22] == I[iir#anon$19];
  assert {:msg "Channel invariant might be falsified by network input (#37)"} I[iir#anon$22] == I[iir#anon$20];
  assert {:msg "Channel invariant might be falsified by network input (#38)"} I[iir#anon$23] == I[iir#anon$21];
  assert {:msg "Channel invariant might be falsified by network input (#39)"} I[iir#anon$23] == I[iir#anon$22];
  assert {:msg "Channel invariant might be falsified by network input (#40)"} I[iir#anon$8] == I[iir#anon$7];
  assert {:msg "Channel invariant might be falsified by network input (#41)"} I[iir#anon$9] == I[iir#anon$7];
  assert {:msg "Channel invariant might be falsified by network input (#42)"} I[iir#anon$11] == I[iir#anon$10];
  assert {:msg "Channel invariant might be falsified by network input (#43)"} I[iir#anon$12] == I[iir#anon$10];
  assert {:msg "Channel invariant might be falsified by network input (#44)"} I[iir#anon$14] == I[iir#anon$13];
  assert {:msg "Channel invariant might be falsified by network input (#45)"} I[iir#anon$15] == I[iir#anon$13];
  assert {:msg "Channel invariant might be falsified by network input (#46)"} (C[iir#anon$7] - I[iir#anon$7]) <= 1;
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
  assume (B[iir#anon$7] == 1) && (B[iir#anon$23] == 1);
  assume (B[iir#anon$7] == 1) && (B[iir#anon$23] == 1);
  assume I[iir#anon$10] == I[iir#anon$9];
  assume I[iir#anon$13] == I[iir#anon$12];
  assume I[iir#anon$16] == I[iir#anon$15];
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
  assume (C[iir#anon$7] - I[iir#anon$7]) <= 1;
  assume (C[iir#anon$10] == 0) ==> (AV#delay_1#data == 0);
  assume (C[iir#anon$10] > 0) ==> (AV#delay_1#data == M[iir#anon$9][R[iir#anon$9] - 1]);
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$10] > 0) ==> (M[iir#anon$10][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$10] - 0)) ==> (M[iir#anon$10][idx] == M[iir#anon$9][idx - 1])
  );
  assume R[iir#anon$9] == C[iir#anon$10];
  assume (C[iir#anon$13] == 0) ==> (AV#delay_2#data == 0);
  assume (C[iir#anon$13] > 0) ==> (AV#delay_2#data == M[iir#anon$12][R[iir#anon$12] - 1]);
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$13] > 0) ==> (M[iir#anon$13][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$13] - 0)) ==> (M[iir#anon$13][idx] == M[iir#anon$12][idx - 1])
  );
  assume R[iir#anon$12] == C[iir#anon$13];
  assume (C[iir#anon$16] == 0) ==> (AV#delay_3#data == 0);
  assume (C[iir#anon$16] > 0) ==> (AV#delay_3#data == M[iir#anon$15][R[iir#anon$15] - 1]);
  assume R[iir#anon$15] == C[iir#anon$16];
  assume (C[iir#anon$16] > 0) ==> (M[iir#anon$16][0] == 0);
  assume (forall idx: int :: 
    ((0 + 1) <= idx) && (idx < (C[iir#anon$16] - 0)) ==> (M[iir#anon$16][idx] == M[iir#anon$15][idx - 1])
  );
  assume R[iir#anon$15] == C[iir#anon$16];
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
  assert {:msg "FIR.actor(38.13): Network action postcondition might not hold (#47)"} (I[iir#anon$23] == 0) ==> (M[iir#anon$23][I[iir#anon$23]] == (37 * M[iir#anon$7][I[iir#anon$7]]));
  assert {:msg "FIR.actor(39.13): Network action postcondition might not hold (#48)"} (I[iir#anon$23] == 1) ==> (M[iir#anon$23][I[iir#anon$23]] == ((37 * M[iir#anon$7][I[iir#anon$7]]) + (109 * M[iir#anon$7][I[iir#anon$7] - 1])));
  assert {:msg "FIR.actor(40.12): Network action postcondition might not hold (#49)"} (I[iir#anon$23] == 2) ==> (M[iir#anon$23][I[iir#anon$23]] == (((37 * M[iir#anon$7][I[iir#anon$7]]) + (109 * M[iir#anon$7][I[iir#anon$7] - 1])) + (109 * M[iir#anon$7][I[iir#anon$7] - 2])));
  assert {:msg "FIR.actor(41.13): Network action postcondition might not hold (#50)"} (I[iir#anon$23] > 3) ==> (M[iir#anon$23][I[iir#anon$23]] == ((((37 * M[iir#anon$7][I[iir#anon$7]]) + (109 * M[iir#anon$7][I[iir#anon$7] - 1])) + (109 * M[iir#anon$7][I[iir#anon$7] - 2])) + (37 * M[iir#anon$7][I[iir#anon$7] - 3])));
  R[iir#anon$23] := R[iir#anon$23] + 1;
  I := R;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel anon$7 (#51)"} (C[iir#anon$7] - R[iir#anon$7]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel anon$8 (#52)"} (C[iir#anon$8] - R[iir#anon$8]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel anon$9 (#53)"} (C[iir#anon$9] - R[iir#anon$9]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel anon$10 (#54)"} (C[iir#anon$10] - R[iir#anon$10]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel anon$11 (#55)"} (C[iir#anon$11] - R[iir#anon$11]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel anon$12 (#56)"} (C[iir#anon$12] - R[iir#anon$12]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel anon$13 (#57)"} (C[iir#anon$13] - R[iir#anon$13]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel anon$14 (#58)"} (C[iir#anon$14] - R[iir#anon$14]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel anon$15 (#59)"} (C[iir#anon$15] - R[iir#anon$15]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel anon$16 (#60)"} (C[iir#anon$16] - R[iir#anon$16]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel anon$17 (#61)"} (C[iir#anon$17] - R[iir#anon$17]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel anon$18 (#62)"} (C[iir#anon$18] - R[iir#anon$18]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel anon$19 (#63)"} (C[iir#anon$19] - R[iir#anon$19]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel anon$20 (#64)"} (C[iir#anon$20] - R[iir#anon$20]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel anon$21 (#65)"} (C[iir#anon$21] - R[iir#anon$21]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel anon$22 (#66)"} (C[iir#anon$22] - R[iir#anon$22]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel anon$23 (#67)"} (C[iir#anon$23] - R[iir#anon$23]) == 0;
}

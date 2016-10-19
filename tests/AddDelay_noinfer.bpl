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

// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

procedure Add#init#0()
  modifies C, R, M, I, St;
{
  var in1: Chan (int);
  var in2: Chan (int);
  var out: Chan (int);
  assume (in1 != in2) && (in1 != out) && (in2 != out);
  assume R[in1] == 0;
  assume R[in2] == 0;
  assume C[out] == 0;
  assert {:msg "3.20: Initialization might not establish the invariant (#0)"} (R[in1] == C[out]) && (R[in2] == C[out]);
  assert {:msg "4.21: Initialization might not establish the invariant (#1)"} (forall i: int :: 
    (0 <= i) && (i < C[out]) ==> (M[out][i] == (M[in1][i] + M[in2][i]))
  );
}
procedure Add#anon$0#1()
  modifies C, R, M, I, St;
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
  assume (R[in1] == C[out]) && (R[in2] == C[out]);
  assume (forall i: int :: 
    (0 <= i) && (i < C[out]) ==> (M[out][i] == (M[in1][i] + M[in2][i]))
  );
  in1#0 := M[in1][R[in1]];
  R[in1] := R[in1] + 1;
  in2#0 := M[in2][R[in2]];
  R[in2] := R[in2] + 1;
  assume true;
  M[out][C[out]] := in1#0 + in2#0;
  C[out] := C[out] + 1;
  assert {:msg "3.20: Action at 5.3 might not preserve invariant (#2)"} (R[in1] == C[out]) && (R[in2] == C[out]);
  assert {:msg "4.21: Action at 5.3 might not preserve invariant (#3)"} (forall i: int :: 
    (0 <= i) && (i < C[out]) ==> (M[out][i] == (M[in1][i] + M[in2][i]))
  );
}
procedure Delay#init#2()
  modifies C, R, M, I, St;
{
  var in: Chan (int);
  var out: Chan (int);
  var k: int;
  assume in != out;
  assume R[in] == 0;
  assume C[out] == 0;
  assume true;
  M[out][C[out]] := k;
  C[out] := C[out] + 1;
  assert {:msg "10.20: Initialization might not establish the invariant (#4)"} R[in] == (C[out] - 1);
  assert {:msg "11.20: Initialization might not establish the invariant (#5)"} M[out][0] == k;
  assert {:msg "12.21: Initialization might not establish the invariant (#6)"} (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[out] - 0)) ==> (M[out][i] == M[in][i - 1])
  );
}
procedure Delay#anon$2#3()
  modifies C, R, M, I, St;
{
  var in: Chan (int);
  var out: Chan (int);
  var k: int;
  var in#0: int;
  assume in != out;
  assume 0 <= R[in];
  assume 0 <= C[out];
  assume R[in] == (C[out] - 1);
  assume M[out][0] == k;
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[out] - 0)) ==> (M[out][i] == M[in][i - 1])
  );
  in#0 := M[in][R[in]];
  R[in] := R[in] + 1;
  assume true;
  M[out][C[out]] := in#0;
  C[out] := C[out] + 1;
  assert {:msg "10.20: Action at 14.3 might not preserve invariant (#7)"} R[in] == (C[out] - 1);
  assert {:msg "11.20: Action at 14.3 might not preserve invariant (#8)"} M[out][0] == k;
  assert {:msg "12.21: Action at 14.3 might not preserve invariant (#9)"} (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[out] - 0)) ==> (M[out][i] == M[in][i - 1])
  );
}
procedure Split#init#4()
  modifies C, R, M, I, St;
{
  var in: Chan (int);
  var out1: Chan (int);
  var out2: Chan (int);
  assume (in != out1) && (in != out2) && (out1 != out2);
  assume R[in] == 0;
  assume C[out1] == 0;
  assume C[out2] == 0;
  assert {:msg "19.20: Initialization might not establish the invariant (#10)"} (R[in] == C[out1]) && (R[in] == C[out2]);
  assert {:msg "20.21: Initialization might not establish the invariant (#11)"} (forall i: int :: 
    (0 <= i) && (i < C[out1]) ==> (M[out1][i] == M[in][i]) && (M[out2][i] == M[in][i])
  );
}
procedure Split#anon$3#5()
  modifies C, R, M, I, St;
{
  var in: Chan (int);
  var out1: Chan (int);
  var out2: Chan (int);
  var in#0: int;
  assume (in != out1) && (in != out2) && (out1 != out2);
  assume 0 <= R[in];
  assume 0 <= C[out1];
  assume 0 <= C[out2];
  assume (R[in] == C[out1]) && (R[in] == C[out2]);
  assume (forall i: int :: 
    (0 <= i) && (i < C[out1]) ==> (M[out1][i] == M[in][i]) && (M[out2][i] == M[in][i])
  );
  in#0 := M[in][R[in]];
  R[in] := R[in] + 1;
  assume true;
  M[out1][C[out1]] := in#0;
  C[out1] := C[out1] + 1;
  M[out2][C[out2]] := in#0;
  C[out2] := C[out2] + 1;
  assert {:msg "19.20: Action at 21.3 might not preserve invariant (#12)"} (R[in] == C[out1]) && (R[in] == C[out2]);
  assert {:msg "20.21: Action at 21.3 might not preserve invariant (#13)"} (forall i: int :: 
    (0 <= i) && (i < C[out1]) ==> (M[out1][i] == M[in][i]) && (M[out2][i] == M[in][i])
  );
}
procedure Net#init#6()
  modifies C, R, M, I, St;
{
  var Net#add: Actor;
  var Net#del: Actor;
  var Net#spl: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (int);
  var Net#d: Chan (int);
  var Net#e: Chan (int);
  assume (Net#add != Net#del) && (Net#add != Net#spl) && (Net#del != Net#spl);
  assume (Net#a != Net#b) && (Net#a != Net#c) && (Net#a != Net#d) && (Net#a != Net#e) && (Net#b != Net#c) && (Net#b != Net#d) && (Net#b != Net#e) && (Net#c != Net#d) && (Net#c != Net#e) && (Net#d != Net#e);
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume 0 <= I[Net#c];
  assume I[Net#c] <= R[Net#c];
  assume R[Net#c] <= C[Net#c];
  assume 0 <= I[Net#d];
  assume I[Net#d] <= R[Net#d];
  assume R[Net#d] <= C[Net#d];
  assume I[Net#d] == R[Net#d];
  assume 0 <= I[Net#e];
  assume I[Net#e] <= R[Net#e];
  assume R[Net#e] <= C[Net#e];
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
  assume (R[Net#a] == C[Net#c]) && (R[Net#b] == C[Net#c]);
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#c]) ==> (M[Net#c][i] == (M[Net#a][i] + M[Net#b][i]))
  );
  assume 0 == 0;
  M[Net#b][C[Net#b]] := 0;
  C[Net#b] := C[Net#b] + 1;
  assume R[Net#e] == (C[Net#b] - 1);
  assume M[Net#b][0] == 0;
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[Net#b] - 0)) ==> (M[Net#b][i] == M[Net#e][i - 1])
  );
  assume (R[Net#c] == C[Net#d]) && (R[Net#c] == C[Net#e]);
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#d]) ==> (M[Net#d][i] == M[Net#c][i]) && (M[Net#e][i] == M[Net#c][i])
  );
  assert {:msg "34.15: Initialization of network 'Net' might not establish the channel invariant (#14)"} (I[Net#a] == I[Net#b]) && (I[Net#b] == I[Net#c]) && (I[Net#c] == I[Net#d]) && (I[Net#d] == I[Net#e]);
  assert {:msg "35.15: Initialization of network 'Net' might not establish the channel invariant (#15)"} (I[Net#c] > 0) ==> (M[Net#c][0] == M[Net#a][0]);
  assert {:msg "36.15: Initialization of network 'Net' might not establish the channel invariant (#16)"} (I[Net#c] > 0) ==> (M[Net#c][I[Net#c] - 1] == M[Net#b][I[Net#b]]);
  assert {:msg "Initialization of network 'Net' might not establish the channel invariant (#17)"} true && (forall idx$: int :: 
    (I[Net#a] <= idx$) && (idx$ < C[Net#a]) ==> (0 <= M[Net#a][idx$])
  );
  I := R;
  C[Net#b] := C[Net#b] - 1;
  assert {:msg "45.5: The initialization might produce unspecified tokens on channel a (#18)"} (C[Net#a] - R[Net#a]) == 0;
  assert {:msg "46.5: The initialization might produce unspecified tokens on channel b (#19)"} (C[Net#b] - R[Net#b]) == 0;
  assert {:msg "47.5: The initialization might produce unspecified tokens on channel c (#20)"} (C[Net#c] - R[Net#c]) == 0;
  assert {:msg "48.5: The initialization might produce unspecified tokens on channel d (#21)"} (C[Net#d] - R[Net#d]) == 0;
  assert {:msg "49.5: The initialization might produce unspecified tokens on channel e (#22)"} (C[Net#e] - R[Net#e]) == 0;
}
procedure Net##Add#anon$0#7()
  modifies C, R, M, I, St;
{
  var Net#add: Actor;
  var Net#del: Actor;
  var Net#spl: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (int);
  var Net#d: Chan (int);
  var Net#e: Chan (int);
  var in1#i: int;
  var in2#j: int;
  assume (Net#add != Net#del) && (Net#add != Net#spl) && (Net#del != Net#spl);
  assume (Net#a != Net#b) && (Net#a != Net#c) && (Net#a != Net#d) && (Net#a != Net#e) && (Net#b != Net#c) && (Net#b != Net#d) && (Net#b != Net#e) && (Net#c != Net#d) && (Net#c != Net#e) && (Net#d != Net#e);
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume 0 <= I[Net#c];
  assume I[Net#c] <= R[Net#c];
  assume R[Net#c] <= C[Net#c];
  assume 0 <= I[Net#d];
  assume I[Net#d] <= R[Net#d];
  assume R[Net#d] <= C[Net#d];
  assume I[Net#d] == R[Net#d];
  assume 0 <= I[Net#e];
  assume I[Net#e] <= R[Net#e];
  assume R[Net#e] <= C[Net#e];
  assume (I[Net#a] == I[Net#b]) && (I[Net#b] == I[Net#c]) && (I[Net#c] == I[Net#d]) && (I[Net#d] == I[Net#e]);
  assume (I[Net#c] > 0) ==> (M[Net#c][0] == M[Net#a][0]);
  assume (I[Net#c] > 0) ==> (M[Net#c][I[Net#c] - 1] == M[Net#b][I[Net#b]]);
  assume true && (forall idx$: int :: 
    (I[Net#a] <= idx$) && (idx$ < C[Net#a]) ==> (0 <= M[Net#a][idx$])
  );
  assume (R[Net#a] == C[Net#c]) && (R[Net#b] == C[Net#c]);
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#c]) ==> (M[Net#c][i] == (M[Net#a][i] + M[Net#b][i]))
  );
  assume R[Net#e] == (C[Net#b] - 1);
  assume M[Net#b][0] == 0;
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[Net#b] - 0)) ==> (M[Net#b][i] == M[Net#e][i - 1])
  );
  assume (R[Net#c] == C[Net#d]) && (R[Net#c] == C[Net#e]);
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#d]) ==> (M[Net#d][i] == M[Net#c][i]) && (M[Net#e][i] == M[Net#c][i])
  );
  assume (1 <= (C[Net#a] - R[Net#a])) && (1 <= (C[Net#b] - R[Net#b]));
  assume (R[Net#a] == C[Net#c]) && (R[Net#b] == C[Net#c]);
  assume (forall i: int :: 
    (0 <= in1#i) && (in1#i < C[Net#c]) ==> (M[Net#c][in1#i] == (M[Net#a][in1#i] + M[Net#b][in1#i]))
  );
  in1#i := M[Net#a][R[Net#a]];
  R[Net#a] := R[Net#a] + 1;
  in2#j := M[Net#b][R[Net#b]];
  R[Net#b] := R[Net#b] + 1;
  M[Net#c][C[Net#c]] := in1#i + in2#j;
  C[Net#c] := C[Net#c] + 1;
  assume (R[Net#a] == C[Net#c]) && (R[Net#b] == C[Net#c]);
  assume (forall i: int :: 
    (0 <= in1#i) && (in1#i < C[Net#c]) ==> (M[Net#c][in1#i] == (M[Net#a][in1#i] + M[Net#b][in1#i]))
  );
  assert {:msg "34.15: Action at 5.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#23)"} (I[Net#a] == I[Net#b]) && (I[Net#b] == I[Net#c]) && (I[Net#c] == I[Net#d]) && (I[Net#d] == I[Net#e]);
  assert {:msg "35.15: Action at 5.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#24)"} (I[Net#c] > 0) ==> (M[Net#c][0] == M[Net#a][0]);
  assert {:msg "36.15: Action at 5.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#25)"} (I[Net#c] > 0) ==> (M[Net#c][I[Net#c] - 1] == M[Net#b][I[Net#b]]);
  assert {:msg "Action at 5.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#26)"} true && (forall idx$: int :: 
    (I[Net#a] <= idx$) && (idx$ < C[Net#a]) ==> (0 <= M[Net#a][idx$])
  );
}
procedure Net##Delay#anon$2#8()
  modifies C, R, M, I, St;
{
  var Net#add: Actor;
  var Net#del: Actor;
  var Net#spl: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (int);
  var Net#d: Chan (int);
  var Net#e: Chan (int);
  var in#i: int;
  assume (Net#add != Net#del) && (Net#add != Net#spl) && (Net#del != Net#spl);
  assume (Net#a != Net#b) && (Net#a != Net#c) && (Net#a != Net#d) && (Net#a != Net#e) && (Net#b != Net#c) && (Net#b != Net#d) && (Net#b != Net#e) && (Net#c != Net#d) && (Net#c != Net#e) && (Net#d != Net#e);
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume 0 <= I[Net#c];
  assume I[Net#c] <= R[Net#c];
  assume R[Net#c] <= C[Net#c];
  assume 0 <= I[Net#d];
  assume I[Net#d] <= R[Net#d];
  assume R[Net#d] <= C[Net#d];
  assume I[Net#d] == R[Net#d];
  assume 0 <= I[Net#e];
  assume I[Net#e] <= R[Net#e];
  assume R[Net#e] <= C[Net#e];
  assume (I[Net#a] == I[Net#b]) && (I[Net#b] == I[Net#c]) && (I[Net#c] == I[Net#d]) && (I[Net#d] == I[Net#e]);
  assume (I[Net#c] > 0) ==> (M[Net#c][0] == M[Net#a][0]);
  assume (I[Net#c] > 0) ==> (M[Net#c][I[Net#c] - 1] == M[Net#b][I[Net#b]]);
  assume true && (forall idx$: int :: 
    (I[Net#a] <= idx$) && (idx$ < C[Net#a]) ==> (0 <= M[Net#a][idx$])
  );
  assume (R[Net#a] == C[Net#c]) && (R[Net#b] == C[Net#c]);
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#c]) ==> (M[Net#c][i] == (M[Net#a][i] + M[Net#b][i]))
  );
  assume R[Net#e] == (C[Net#b] - 1);
  assume M[Net#b][0] == 0;
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[Net#b] - 0)) ==> (M[Net#b][i] == M[Net#e][i - 1])
  );
  assume (R[Net#c] == C[Net#d]) && (R[Net#c] == C[Net#e]);
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#d]) ==> (M[Net#d][i] == M[Net#c][i]) && (M[Net#e][i] == M[Net#c][i])
  );
  assume 1 <= (C[Net#e] - R[Net#e]);
  assume R[Net#e] == (C[Net#b] - 1);
  assume M[Net#b][0] == 0;
  assume (forall i: int :: 
    ((0 + 1) <= in#i) && (in#i < (C[Net#b] - 0)) ==> (M[Net#b][in#i] == M[Net#e][in#i - 1])
  );
  in#i := M[Net#e][R[Net#e]];
  R[Net#e] := R[Net#e] + 1;
  M[Net#b][C[Net#b]] := in#i;
  C[Net#b] := C[Net#b] + 1;
  assume R[Net#e] == (C[Net#b] - 1);
  assume M[Net#b][0] == 0;
  assume (forall i: int :: 
    ((0 + 1) <= in#i) && (in#i < (C[Net#b] - 0)) ==> (M[Net#b][in#i] == M[Net#e][in#i - 1])
  );
  assert {:msg "34.15: Action at 14.3 ('anon$2') for actor instance 'del' might not preserve the channel invariant (#27)"} (I[Net#a] == I[Net#b]) && (I[Net#b] == I[Net#c]) && (I[Net#c] == I[Net#d]) && (I[Net#d] == I[Net#e]);
  assert {:msg "35.15: Action at 14.3 ('anon$2') for actor instance 'del' might not preserve the channel invariant (#28)"} (I[Net#c] > 0) ==> (M[Net#c][0] == M[Net#a][0]);
  assert {:msg "36.15: Action at 14.3 ('anon$2') for actor instance 'del' might not preserve the channel invariant (#29)"} (I[Net#c] > 0) ==> (M[Net#c][I[Net#c] - 1] == M[Net#b][I[Net#b]]);
  assert {:msg "Action at 14.3 ('anon$2') for actor instance 'del' might not preserve the channel invariant (#30)"} true && (forall idx$: int :: 
    (I[Net#a] <= idx$) && (idx$ < C[Net#a]) ==> (0 <= M[Net#a][idx$])
  );
}
procedure Net##Split#anon$3#9()
  modifies C, R, M, I, St;
{
  var Net#add: Actor;
  var Net#del: Actor;
  var Net#spl: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (int);
  var Net#d: Chan (int);
  var Net#e: Chan (int);
  var in#i: int;
  assume (Net#add != Net#del) && (Net#add != Net#spl) && (Net#del != Net#spl);
  assume (Net#a != Net#b) && (Net#a != Net#c) && (Net#a != Net#d) && (Net#a != Net#e) && (Net#b != Net#c) && (Net#b != Net#d) && (Net#b != Net#e) && (Net#c != Net#d) && (Net#c != Net#e) && (Net#d != Net#e);
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume 0 <= I[Net#c];
  assume I[Net#c] <= R[Net#c];
  assume R[Net#c] <= C[Net#c];
  assume 0 <= I[Net#d];
  assume I[Net#d] <= R[Net#d];
  assume R[Net#d] <= C[Net#d];
  assume I[Net#d] == R[Net#d];
  assume 0 <= I[Net#e];
  assume I[Net#e] <= R[Net#e];
  assume R[Net#e] <= C[Net#e];
  assume (I[Net#a] == I[Net#b]) && (I[Net#b] == I[Net#c]) && (I[Net#c] == I[Net#d]) && (I[Net#d] == I[Net#e]);
  assume (I[Net#c] > 0) ==> (M[Net#c][0] == M[Net#a][0]);
  assume (I[Net#c] > 0) ==> (M[Net#c][I[Net#c] - 1] == M[Net#b][I[Net#b]]);
  assume true && (forall idx$: int :: 
    (I[Net#a] <= idx$) && (idx$ < C[Net#a]) ==> (0 <= M[Net#a][idx$])
  );
  assume (R[Net#a] == C[Net#c]) && (R[Net#b] == C[Net#c]);
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#c]) ==> (M[Net#c][i] == (M[Net#a][i] + M[Net#b][i]))
  );
  assume R[Net#e] == (C[Net#b] - 1);
  assume M[Net#b][0] == 0;
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[Net#b] - 0)) ==> (M[Net#b][i] == M[Net#e][i - 1])
  );
  assume (R[Net#c] == C[Net#d]) && (R[Net#c] == C[Net#e]);
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#d]) ==> (M[Net#d][i] == M[Net#c][i]) && (M[Net#e][i] == M[Net#c][i])
  );
  assume 1 <= (C[Net#c] - R[Net#c]);
  assume (R[Net#c] == C[Net#d]) && (R[Net#c] == C[Net#e]);
  assume (forall i: int :: 
    (0 <= in#i) && (in#i < C[Net#d]) ==> (M[Net#d][in#i] == M[Net#c][in#i]) && (M[Net#e][in#i] == M[Net#c][in#i])
  );
  in#i := M[Net#c][R[Net#c]];
  R[Net#c] := R[Net#c] + 1;
  M[Net#d][C[Net#d]] := in#i;
  C[Net#d] := C[Net#d] + 1;
  M[Net#e][C[Net#e]] := in#i;
  C[Net#e] := C[Net#e] + 1;
  assume (R[Net#c] == C[Net#d]) && (R[Net#c] == C[Net#e]);
  assume (forall i: int :: 
    (0 <= in#i) && (in#i < C[Net#d]) ==> (M[Net#d][in#i] == M[Net#c][in#i]) && (M[Net#e][in#i] == M[Net#c][in#i])
  );
  assert {:msg "34.15: Action at 21.3 ('anon$3') for actor instance 'spl' might not preserve the channel invariant (#31)"} (I[Net#a] == I[Net#b]) && (I[Net#b] == I[Net#c]) && (I[Net#c] == I[Net#d]) && (I[Net#d] == I[Net#e]);
  assert {:msg "35.15: Action at 21.3 ('anon$3') for actor instance 'spl' might not preserve the channel invariant (#32)"} (I[Net#c] > 0) ==> (M[Net#c][0] == M[Net#a][0]);
  assert {:msg "36.15: Action at 21.3 ('anon$3') for actor instance 'spl' might not preserve the channel invariant (#33)"} (I[Net#c] > 0) ==> (M[Net#c][I[Net#c] - 1] == M[Net#b][I[Net#b]]);
  assert {:msg "Action at 21.3 ('anon$3') for actor instance 'spl' might not preserve the channel invariant (#34)"} true && (forall idx$: int :: 
    (I[Net#a] <= idx$) && (idx$ < C[Net#a]) ==> (0 <= M[Net#a][idx$])
  );
}
procedure Net#entry()
  modifies C, R, M, I, St;
{
  var Net#add: Actor;
  var Net#del: Actor;
  var Net#spl: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (int);
  var Net#d: Chan (int);
  var Net#e: Chan (int);
  assume (Net#add != Net#del) && (Net#add != Net#spl) && (Net#del != Net#spl);
  assume (Net#a != Net#b) && (Net#a != Net#c) && (Net#a != Net#d) && (Net#a != Net#e) && (Net#b != Net#c) && (Net#b != Net#d) && (Net#b != Net#e) && (Net#c != Net#d) && (Net#c != Net#e) && (Net#d != Net#e);
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume 0 <= I[Net#c];
  assume I[Net#c] <= R[Net#c];
  assume R[Net#c] <= C[Net#c];
  assume 0 <= I[Net#d];
  assume I[Net#d] <= R[Net#d];
  assume R[Net#d] <= C[Net#d];
  assume I[Net#d] == R[Net#d];
  assume 0 <= I[Net#e];
  assume I[Net#e] <= R[Net#e];
  assume R[Net#e] <= C[Net#e];
  assume C[Net#a] == R[Net#a];
  assume C[Net#b] == R[Net#b];
  assume C[Net#c] == R[Net#c];
  assume C[Net#d] == R[Net#d];
  assume C[Net#e] == R[Net#e];
  C[Net#b] := C[Net#b] + 1;
  assume (I[Net#a] == I[Net#b]) && (I[Net#b] == I[Net#c]) && (I[Net#c] == I[Net#d]) && (I[Net#d] == I[Net#e]);
  assume (I[Net#c] > 0) ==> (M[Net#c][0] == M[Net#a][0]);
  assume (I[Net#c] > 0) ==> (M[Net#c][I[Net#c] - 1] == M[Net#b][I[Net#b]]);
  assume true && (forall idx$: int :: 
    (I[Net#a] <= idx$) && (idx$ < C[Net#a]) ==> (0 <= M[Net#a][idx$])
  );
  assume (R[Net#a] == C[Net#c]) && (R[Net#b] == C[Net#c]);
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#c]) ==> (M[Net#c][i] == (M[Net#a][i] + M[Net#b][i]))
  );
  assume R[Net#e] == (C[Net#b] - 1);
  assume M[Net#b][0] == 0;
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[Net#b] - 0)) ==> (M[Net#b][i] == M[Net#e][i - 1])
  );
  assume (R[Net#c] == C[Net#d]) && (R[Net#c] == C[Net#e]);
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#d]) ==> (M[Net#d][i] == M[Net#c][i]) && (M[Net#e][i] == M[Net#c][i])
  );
  assert {:msg "24.1: Sub-actors in the network might fire without network input. This is not permitted. (#35)"} !((1 <= (C[Net#a] - R[Net#a])) && (1 <= (C[Net#b] - R[Net#b])));
  assert {:msg "24.1: Sub-actors in the network might fire without network input. This is not permitted. (#36)"} !(1 <= (C[Net#e] - R[Net#e]));
  assert {:msg "24.1: Sub-actors in the network might fire without network input. This is not permitted. (#37)"} !(1 <= (C[Net#c] - R[Net#c]));
}
procedure Net#anon$4#input#in#10()
  modifies C, R, M, I, St;
{
  var Net#add: Actor;
  var Net#del: Actor;
  var Net#spl: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (int);
  var Net#d: Chan (int);
  var Net#e: Chan (int);
  assume (Net#add != Net#del) && (Net#add != Net#spl) && (Net#del != Net#spl);
  assume (Net#a != Net#b) && (Net#a != Net#c) && (Net#a != Net#d) && (Net#a != Net#e) && (Net#b != Net#c) && (Net#b != Net#d) && (Net#b != Net#e) && (Net#c != Net#d) && (Net#c != Net#e) && (Net#d != Net#e);
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume 0 <= I[Net#c];
  assume I[Net#c] <= R[Net#c];
  assume R[Net#c] <= C[Net#c];
  assume 0 <= I[Net#d];
  assume I[Net#d] <= R[Net#d];
  assume R[Net#d] <= C[Net#d];
  assume I[Net#d] == R[Net#d];
  assume 0 <= I[Net#e];
  assume I[Net#e] <= R[Net#e];
  assume R[Net#e] <= C[Net#e];
  assume C[Net#a] < 1;
  assume (I[Net#a] == I[Net#b]) && (I[Net#b] == I[Net#c]) && (I[Net#c] == I[Net#d]) && (I[Net#d] == I[Net#e]);
  assume (I[Net#c] > 0) ==> (M[Net#c][0] == M[Net#a][0]);
  assume (I[Net#c] > 0) ==> (M[Net#c][I[Net#c] - 1] == M[Net#b][I[Net#b]]);
  assume true && (forall idx$: int :: 
    (I[Net#a] <= idx$) && (idx$ < C[Net#a]) ==> (0 <= M[Net#a][idx$])
  );
  assume (R[Net#a] == C[Net#c]) && (R[Net#b] == C[Net#c]);
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#c]) ==> (M[Net#c][i] == (M[Net#a][i] + M[Net#b][i]))
  );
  assume R[Net#e] == (C[Net#b] - 1);
  assume M[Net#b][0] == 0;
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[Net#b] - 0)) ==> (M[Net#b][i] == M[Net#e][i - 1])
  );
  assume (R[Net#c] == C[Net#d]) && (R[Net#c] == C[Net#e]);
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#d]) ==> (M[Net#d][i] == M[Net#c][i]) && (M[Net#e][i] == M[Net#c][i])
  );
  C[Net#a] := C[Net#a] + 1;
  assume 0 <= M[Net#a][I[Net#a]];
  assert {:msg "34.15: Channel invariant might be falsified by network input (#38)"} (I[Net#a] == I[Net#b]) && (I[Net#b] == I[Net#c]) && (I[Net#c] == I[Net#d]) && (I[Net#d] == I[Net#e]);
  assert {:msg "35.15: Channel invariant might be falsified by network input (#39)"} (I[Net#c] > 0) ==> (M[Net#c][0] == M[Net#a][0]);
  assert {:msg "36.15: Channel invariant might be falsified by network input (#40)"} (I[Net#c] > 0) ==> (M[Net#c][I[Net#c] - 1] == M[Net#b][I[Net#b]]);
  assert {:msg "Channel invariant might be falsified by network input (#41)"} true && (forall idx$: int :: 
    (I[Net#a] <= idx$) && (idx$ < C[Net#a]) ==> (0 <= M[Net#a][idx$])
  );
}
procedure Net#anon$4#exit#11()
  modifies C, R, M, I, St;
{
  var Net#add: Actor;
  var Net#del: Actor;
  var Net#spl: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (int);
  var Net#d: Chan (int);
  var Net#e: Chan (int);
  assume (Net#add != Net#del) && (Net#add != Net#spl) && (Net#del != Net#spl);
  assume (Net#a != Net#b) && (Net#a != Net#c) && (Net#a != Net#d) && (Net#a != Net#e) && (Net#b != Net#c) && (Net#b != Net#d) && (Net#b != Net#e) && (Net#c != Net#d) && (Net#c != Net#e) && (Net#d != Net#e);
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume 0 <= I[Net#c];
  assume I[Net#c] <= R[Net#c];
  assume R[Net#c] <= C[Net#c];
  assume 0 <= I[Net#d];
  assume I[Net#d] <= R[Net#d];
  assume R[Net#d] <= C[Net#d];
  assume I[Net#d] == R[Net#d];
  assume 0 <= I[Net#e];
  assume I[Net#e] <= R[Net#e];
  assume R[Net#e] <= C[Net#e];
  assume (I[Net#a] == I[Net#b]) && (I[Net#b] == I[Net#c]) && (I[Net#c] == I[Net#d]) && (I[Net#d] == I[Net#e]);
  assume (I[Net#c] > 0) ==> (M[Net#c][0] == M[Net#a][0]);
  assume (I[Net#c] > 0) ==> (M[Net#c][I[Net#c] - 1] == M[Net#b][I[Net#b]]);
  assume true && (forall idx$: int :: 
    (I[Net#a] <= idx$) && (idx$ < C[Net#a]) ==> (0 <= M[Net#a][idx$])
  );
  assume (R[Net#a] == C[Net#c]) && (R[Net#b] == C[Net#c]);
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#c]) ==> (M[Net#c][i] == (M[Net#a][i] + M[Net#b][i]))
  );
  assume R[Net#e] == (C[Net#b] - 1);
  assume M[Net#b][0] == 0;
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[Net#b] - 0)) ==> (M[Net#b][i] == M[Net#e][i - 1])
  );
  assume (R[Net#c] == C[Net#d]) && (R[Net#c] == C[Net#e]);
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#d]) ==> (M[Net#d][i] == M[Net#c][i]) && (M[Net#e][i] == M[Net#c][i])
  );
  assume (C[Net#a] - I[Net#a]) == 1;
  assume 0 <= M[Net#a][I[Net#a]];
  assume !((1 <= (C[Net#a] - R[Net#a])) && (1 <= (C[Net#b] - R[Net#b])));
  assume !(1 <= (C[Net#e] - R[Net#e]));
  assume !(1 <= (C[Net#c] - R[Net#c]));
  assert {:msg "28.13: Network action postcondition might not hold (#42)"} M[Net#d][0] == M[Net#a][0];
  assert {:msg "29.13: Network action postcondition might not hold (#43)"} (I[Net#d] > 0) ==> (M[Net#d][I[Net#d]] == (M[Net#d][I[Net#d] - 1] + M[Net#a][I[Net#a]]));
  R[Net#d] := R[Net#d] + 1;
  I := R;
  assert {:msg "34.15: The network might not preserve the channel invariant (#44)"} (I[Net#a] == I[Net#b]) && (I[Net#b] == I[Net#c]) && (I[Net#c] == I[Net#d]) && (I[Net#d] == I[Net#e]);
  assert {:msg "35.15: The network might not preserve the channel invariant (#45)"} (I[Net#c] > 0) ==> (M[Net#c][0] == M[Net#a][0]);
  assert {:msg "36.15: The network might not preserve the channel invariant (#46)"} (I[Net#c] > 0) ==> (M[Net#c][I[Net#c] - 1] == M[Net#b][I[Net#b]]);
  assert {:msg "The network might not preserve the channel invariant (#47)"} true && (forall idx$: int :: 
    (I[Net#a] <= idx$) && (idx$ < C[Net#a]) ==> (0 <= M[Net#a][idx$])
  );
  C[Net#b] := C[Net#b] - 1;
  assert {:msg "26.3: The network might leave unread tokens on channel a (#48)"} C[Net#a] == R[Net#a];
  assert {:msg "26.3: The network might leave unread tokens on channel b (#49)"} C[Net#b] == R[Net#b];
  assert {:msg "26.3: The network might leave unread tokens on channel c (#50)"} C[Net#c] == R[Net#c];
  assert {:msg "26.3: The network might not produce the specified number of tokens on output out (#51)"} C[Net#d] == R[Net#d];
  assert {:msg "26.3: The network might leave unread tokens on channel e (#52)"} C[Net#e] == R[Net#e];
}

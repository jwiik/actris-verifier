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
var T: CType;

const unique this#: Actor;
type List a = [int]a;
var AT#intlst: List int;

function AT#Min(x:int, y: int): int { if x <= y then x else y }

// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

procedure Add#init#0()
  modifies C, R, M, I;
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
  assume (R[in1] == C[out]) && (R[in2] == C[out]);
  assume (forall i: int :: 
    (0 <= i) && (i < C[out]) ==> (M[out][i] == (M[in1][i] + M[in2][i]))
  );
  in1#0 := M[in1][R[in1]];
  R[in1] := R[in1] + 1;
  in2#0 := M[in2][R[in2]];
  R[in2] := R[in2] + 1;
  M[out][C[out]] := in1#0 + in2#0;
  C[out] := C[out] + 1;
  assert {:msg "3.20: Action at 5.3 might not preserve invariant (#2)"} (R[in1] == C[out]) && (R[in2] == C[out]);
  assert {:msg "4.21: Action at 5.3 might not preserve invariant (#3)"} (forall i: int :: 
    (0 <= i) && (i < C[out]) ==> (M[out][i] == (M[in1][i] + M[in2][i]))
  );
}
procedure Delay#init#2()
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
  assert {:msg "10.20: Initialization might not establish the invariant (#4)"} R[in] == (C[out] - 1);
  assert {:msg "11.20: Initialization might not establish the invariant (#5)"} M[out][0] == k;
  assert {:msg "12.21: Initialization might not establish the invariant (#6)"} (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[out] - 0)) ==> (M[out][i] == M[in][i - 1])
  );
}
procedure Delay#anon$2#3()
  modifies C, R, M, I;
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
  M[out][C[out]] := in#0;
  C[out] := C[out] + 1;
  assert {:msg "10.20: Action at 14.3 might not preserve invariant (#7)"} R[in] == (C[out] - 1);
  assert {:msg "11.20: Action at 14.3 might not preserve invariant (#8)"} M[out][0] == k;
  assert {:msg "12.21: Action at 14.3 might not preserve invariant (#9)"} (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[out] - 0)) ==> (M[out][i] == M[in][i - 1])
  );
}
procedure Split#init#4()
  modifies C, R, M, I;
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
  assume (R[in] == C[out1]) && (R[in] == C[out2]);
  assume (forall i: int :: 
    (0 <= i) && (i < C[out1]) ==> (M[out1][i] == M[in][i]) && (M[out2][i] == M[in][i])
  );
  in#0 := M[in][R[in]];
  R[in] := R[in] + 1;
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
  modifies C, R, M, I;
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
  assume 0 == 0;
  M[Net#b][C[Net#b]] := 0;
  C[Net#b] := C[Net#b] + 1;
  assert {:msg "34.15: Initialization of network 'Net' might not establish the channel invariant (#14)"} I[Net#a] == I[Net#b];
  assert {:msg "35.15: Initialization of network 'Net' might not establish the channel invariant (#15)"} I[Net#b] == I[Net#c];
  assert {:msg "36.15: Initialization of network 'Net' might not establish the channel invariant (#16)"} I[Net#c] == I[Net#d];
  assert {:msg "37.15: Initialization of network 'Net' might not establish the channel invariant (#17)"} I[Net#d] == I[Net#e];
  assert {:msg "38.15: Initialization of network 'Net' might not establish the channel invariant (#18)"} (I[Net#c] > 0) ==> (M[Net#c][0] == M[Net#a][0]);
  assert {:msg "39.15: Initialization of network 'Net' might not establish the channel invariant (#19)"} (I[Net#c] > 0) ==> (M[Net#c][I[Net#c] - 1] == M[Net#b][I[Net#b]]);
  I := R;
  assert {:msg "32.13: Network initialization might not establish the network invariant (#20)"} (C[Net#b] - R[Net#b]) == 1;
  assert {:msg "48.5: The initialization might produce unspecified tokens on channel a (#21)"} (C[Net#a] - R[Net#a]) == 0;
  assert {:msg "50.5: The initialization might produce unspecified tokens on channel c (#22)"} (C[Net#c] - R[Net#c]) == 0;
  assert {:msg "51.5: The initialization might produce unspecified tokens on channel d (#23)"} (C[Net#d] - R[Net#d]) == 0;
  assert {:msg "52.5: The initialization might produce unspecified tokens on channel e (#24)"} (C[Net#e] - R[Net#e]) == 0;
}
procedure Net##Add#anon$0#7()
  modifies C, R, M, I;
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
  assume I[Net#a] == I[Net#b];
  assume I[Net#b] == I[Net#c];
  assume I[Net#c] == I[Net#d];
  assume I[Net#d] == I[Net#e];
  assume (I[Net#c] > 0) ==> (M[Net#c][0] == M[Net#a][0]);
  assume (I[Net#c] > 0) ==> (M[Net#c][I[Net#c] - 1] == M[Net#b][I[Net#b]]);
  assume 0 <= M[Net#a][I[Net#a]];
  assume R[Net#a] == C[Net#c];
  assume R[Net#b] == C[Net#c];
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#c]) ==> (M[Net#c][i] == (M[Net#a][i] + M[Net#b][i]))
  );
  assume R[Net#e] == (C[Net#b] - 1);
  assume M[Net#b][0] == 0;
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[Net#b] - 0)) ==> (M[Net#b][i] == M[Net#e][i - 1])
  );
  assume R[Net#c] == C[Net#d];
  assume R[Net#c] == C[Net#e];
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#d]) ==> (M[Net#d][i] == M[Net#c][i]) && (M[Net#e][i] == M[Net#c][i])
  );
  assume (1 <= (C[Net#a] - R[Net#a])) && (1 <= (C[Net#b] - R[Net#b]));
  in1#i := M[Net#a][R[Net#a]];
  R[Net#a] := R[Net#a] + 1;
  in2#j := M[Net#b][R[Net#b]];
  R[Net#b] := R[Net#b] + 1;
  M[Net#c][C[Net#c]] := in1#i + in2#j;
  C[Net#c] := C[Net#c] + 1;
  assume R[Net#a] == C[Net#c];
  assume R[Net#b] == C[Net#c];
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#c]) ==> (M[Net#c][i] == (M[Net#a][i] + M[Net#b][i]))
  );
  assume R[Net#e] == (C[Net#b] - 1);
  assume M[Net#b][0] == 0;
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[Net#b] - 0)) ==> (M[Net#b][i] == M[Net#e][i - 1])
  );
  assume R[Net#c] == C[Net#d];
  assume R[Net#c] == C[Net#e];
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#d]) ==> (M[Net#d][i] == M[Net#c][i]) && (M[Net#e][i] == M[Net#c][i])
  );
  assert {:msg "34.15: Action at 5.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#25)"} I[Net#a] == I[Net#b];
  assert {:msg "35.15: Action at 5.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#26)"} I[Net#b] == I[Net#c];
  assert {:msg "36.15: Action at 5.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#27)"} I[Net#c] == I[Net#d];
  assert {:msg "37.15: Action at 5.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#28)"} I[Net#d] == I[Net#e];
  assert {:msg "38.15: Action at 5.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#29)"} (I[Net#c] > 0) ==> (M[Net#c][0] == M[Net#a][0]);
  assert {:msg "39.15: Action at 5.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#30)"} (I[Net#c] > 0) ==> (M[Net#c][I[Net#c] - 1] == M[Net#b][I[Net#b]]);
}
procedure Net##Delay#anon$2#8()
  modifies C, R, M, I;
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
  assume I[Net#a] == I[Net#b];
  assume I[Net#b] == I[Net#c];
  assume I[Net#c] == I[Net#d];
  assume I[Net#d] == I[Net#e];
  assume (I[Net#c] > 0) ==> (M[Net#c][0] == M[Net#a][0]);
  assume (I[Net#c] > 0) ==> (M[Net#c][I[Net#c] - 1] == M[Net#b][I[Net#b]]);
  assume 0 <= M[Net#a][I[Net#a]];
  assume R[Net#a] == C[Net#c];
  assume R[Net#b] == C[Net#c];
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#c]) ==> (M[Net#c][i] == (M[Net#a][i] + M[Net#b][i]))
  );
  assume R[Net#e] == (C[Net#b] - 1);
  assume M[Net#b][0] == 0;
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[Net#b] - 0)) ==> (M[Net#b][i] == M[Net#e][i - 1])
  );
  assume R[Net#c] == C[Net#d];
  assume R[Net#c] == C[Net#e];
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#d]) ==> (M[Net#d][i] == M[Net#c][i]) && (M[Net#e][i] == M[Net#c][i])
  );
  assume 1 <= (C[Net#e] - R[Net#e]);
  in#i := M[Net#e][R[Net#e]];
  R[Net#e] := R[Net#e] + 1;
  M[Net#b][C[Net#b]] := in#i;
  C[Net#b] := C[Net#b] + 1;
  assume R[Net#a] == C[Net#c];
  assume R[Net#b] == C[Net#c];
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#c]) ==> (M[Net#c][i] == (M[Net#a][i] + M[Net#b][i]))
  );
  assume R[Net#e] == (C[Net#b] - 1);
  assume M[Net#b][0] == 0;
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[Net#b] - 0)) ==> (M[Net#b][i] == M[Net#e][i - 1])
  );
  assume R[Net#c] == C[Net#d];
  assume R[Net#c] == C[Net#e];
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#d]) ==> (M[Net#d][i] == M[Net#c][i]) && (M[Net#e][i] == M[Net#c][i])
  );
  assert {:msg "34.15: Action at 14.3 ('anon$2') for actor instance 'del' might not preserve the channel invariant (#31)"} I[Net#a] == I[Net#b];
  assert {:msg "35.15: Action at 14.3 ('anon$2') for actor instance 'del' might not preserve the channel invariant (#32)"} I[Net#b] == I[Net#c];
  assert {:msg "36.15: Action at 14.3 ('anon$2') for actor instance 'del' might not preserve the channel invariant (#33)"} I[Net#c] == I[Net#d];
  assert {:msg "37.15: Action at 14.3 ('anon$2') for actor instance 'del' might not preserve the channel invariant (#34)"} I[Net#d] == I[Net#e];
  assert {:msg "38.15: Action at 14.3 ('anon$2') for actor instance 'del' might not preserve the channel invariant (#35)"} (I[Net#c] > 0) ==> (M[Net#c][0] == M[Net#a][0]);
  assert {:msg "39.15: Action at 14.3 ('anon$2') for actor instance 'del' might not preserve the channel invariant (#36)"} (I[Net#c] > 0) ==> (M[Net#c][I[Net#c] - 1] == M[Net#b][I[Net#b]]);
}
procedure Net##Split#anon$3#9()
  modifies C, R, M, I;
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
  assume I[Net#a] == I[Net#b];
  assume I[Net#b] == I[Net#c];
  assume I[Net#c] == I[Net#d];
  assume I[Net#d] == I[Net#e];
  assume (I[Net#c] > 0) ==> (M[Net#c][0] == M[Net#a][0]);
  assume (I[Net#c] > 0) ==> (M[Net#c][I[Net#c] - 1] == M[Net#b][I[Net#b]]);
  assume 0 <= M[Net#a][I[Net#a]];
  assume R[Net#a] == C[Net#c];
  assume R[Net#b] == C[Net#c];
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#c]) ==> (M[Net#c][i] == (M[Net#a][i] + M[Net#b][i]))
  );
  assume R[Net#e] == (C[Net#b] - 1);
  assume M[Net#b][0] == 0;
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[Net#b] - 0)) ==> (M[Net#b][i] == M[Net#e][i - 1])
  );
  assume R[Net#c] == C[Net#d];
  assume R[Net#c] == C[Net#e];
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#d]) ==> (M[Net#d][i] == M[Net#c][i]) && (M[Net#e][i] == M[Net#c][i])
  );
  assume 1 <= (C[Net#c] - R[Net#c]);
  in#i := M[Net#c][R[Net#c]];
  R[Net#c] := R[Net#c] + 1;
  M[Net#d][C[Net#d]] := in#i;
  C[Net#d] := C[Net#d] + 1;
  M[Net#e][C[Net#e]] := in#i;
  C[Net#e] := C[Net#e] + 1;
  assume R[Net#a] == C[Net#c];
  assume R[Net#b] == C[Net#c];
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#c]) ==> (M[Net#c][i] == (M[Net#a][i] + M[Net#b][i]))
  );
  assume R[Net#e] == (C[Net#b] - 1);
  assume M[Net#b][0] == 0;
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[Net#b] - 0)) ==> (M[Net#b][i] == M[Net#e][i - 1])
  );
  assume R[Net#c] == C[Net#d];
  assume R[Net#c] == C[Net#e];
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#d]) ==> (M[Net#d][i] == M[Net#c][i]) && (M[Net#e][i] == M[Net#c][i])
  );
  assert {:msg "34.15: Action at 21.3 ('anon$3') for actor instance 'spl' might not preserve the channel invariant (#37)"} I[Net#a] == I[Net#b];
  assert {:msg "35.15: Action at 21.3 ('anon$3') for actor instance 'spl' might not preserve the channel invariant (#38)"} I[Net#b] == I[Net#c];
  assert {:msg "36.15: Action at 21.3 ('anon$3') for actor instance 'spl' might not preserve the channel invariant (#39)"} I[Net#c] == I[Net#d];
  assert {:msg "37.15: Action at 21.3 ('anon$3') for actor instance 'spl' might not preserve the channel invariant (#40)"} I[Net#d] == I[Net#e];
  assert {:msg "38.15: Action at 21.3 ('anon$3') for actor instance 'spl' might not preserve the channel invariant (#41)"} (I[Net#c] > 0) ==> (M[Net#c][0] == M[Net#a][0]);
  assert {:msg "39.15: Action at 21.3 ('anon$3') for actor instance 'spl' might not preserve the channel invariant (#42)"} (I[Net#c] > 0) ==> (M[Net#c][I[Net#c] - 1] == M[Net#b][I[Net#b]]);
}
procedure Net#anon$4#input#in#10()
  modifies C, R, M, I;
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
  assume (C[Net#a] - I[Net#a]) < 1;
  assume I[Net#a] == I[Net#b];
  assume I[Net#b] == I[Net#c];
  assume I[Net#c] == I[Net#d];
  assume I[Net#d] == I[Net#e];
  assume (I[Net#c] > 0) ==> (M[Net#c][0] == M[Net#a][0]);
  assume (I[Net#c] > 0) ==> (M[Net#c][I[Net#c] - 1] == M[Net#b][I[Net#b]]);
  assume 0 <= M[Net#a][I[Net#a]];
  assume R[Net#a] == C[Net#c];
  assume R[Net#b] == C[Net#c];
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#c]) ==> (M[Net#c][i] == (M[Net#a][i] + M[Net#b][i]))
  );
  assume R[Net#e] == (C[Net#b] - 1);
  assume M[Net#b][0] == 0;
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[Net#b] - 0)) ==> (M[Net#b][i] == M[Net#e][i - 1])
  );
  assume R[Net#c] == C[Net#d];
  assume R[Net#c] == C[Net#e];
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#d]) ==> (M[Net#d][i] == M[Net#c][i]) && (M[Net#e][i] == M[Net#c][i])
  );
  C[Net#a] := C[Net#a] + 1;
  assume 0 <= M[Net#a][I[Net#a]];
  assert {:msg "34.15: Channel invariant might be falsified by network input (#43)"} I[Net#a] == I[Net#b];
  assert {:msg "35.15: Channel invariant might be falsified by network input (#44)"} I[Net#b] == I[Net#c];
  assert {:msg "36.15: Channel invariant might be falsified by network input (#45)"} I[Net#c] == I[Net#d];
  assert {:msg "37.15: Channel invariant might be falsified by network input (#46)"} I[Net#d] == I[Net#e];
  assert {:msg "38.15: Channel invariant might be falsified by network input (#47)"} (I[Net#c] > 0) ==> (M[Net#c][0] == M[Net#a][0]);
  assert {:msg "39.15: Channel invariant might be falsified by network input (#48)"} (I[Net#c] > 0) ==> (M[Net#c][I[Net#c] - 1] == M[Net#b][I[Net#b]]);
  assert {:msg "27.14: Channel invariant might be falsified by network input (#49)"} 0 <= M[Net#a][I[Net#a]];
}
procedure Net#anon$4#exit#11()
  modifies C, R, M, I;
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
  assume I[Net#a] == I[Net#b];
  assume I[Net#b] == I[Net#c];
  assume I[Net#c] == I[Net#d];
  assume I[Net#d] == I[Net#e];
  assume (I[Net#c] > 0) ==> (M[Net#c][0] == M[Net#a][0]);
  assume (I[Net#c] > 0) ==> (M[Net#c][I[Net#c] - 1] == M[Net#b][I[Net#b]]);
  assume 0 <= M[Net#a][I[Net#a]];
  assume R[Net#a] == C[Net#c];
  assume R[Net#b] == C[Net#c];
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#c]) ==> (M[Net#c][i] == (M[Net#a][i] + M[Net#b][i]))
  );
  assume R[Net#e] == (C[Net#b] - 1);
  assume M[Net#b][0] == 0;
  assume (forall i: int :: 
    ((0 + 1) <= i) && (i < (C[Net#b] - 0)) ==> (M[Net#b][i] == M[Net#e][i - 1])
  );
  assume R[Net#c] == C[Net#d];
  assume R[Net#c] == C[Net#e];
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#d]) ==> (M[Net#d][i] == M[Net#c][i]) && (M[Net#e][i] == M[Net#c][i])
  );
  assume (C[Net#a] - I[Net#a]) == 1;
  assume 0 <= M[Net#a][I[Net#a]];
  assume !((1 <= (C[Net#a] - R[Net#a])) && (1 <= (C[Net#b] - R[Net#b])));
  assume !(1 <= (C[Net#e] - R[Net#e]));
  assume !(1 <= (C[Net#c] - R[Net#c]));
  assert {:msg "28.13: Network action postcondition might not hold (#50)"} M[Net#d][0] == M[Net#a][0];
  assert {:msg "29.13: Network action postcondition might not hold (#51)"} (I[Net#d] > 0) ==> (M[Net#d][I[Net#d]] == (M[Net#d][I[Net#d] - 1] + M[Net#a][I[Net#a]]));
  R[Net#d] := R[Net#d] + 1;
  I := R;
  assert {:msg "34.15: The network might not preserve the channel invariant (#52)"} I[Net#a] == I[Net#b];
  assert {:msg "35.15: The network might not preserve the channel invariant (#53)"} I[Net#b] == I[Net#c];
  assert {:msg "36.15: The network might not preserve the channel invariant (#54)"} I[Net#c] == I[Net#d];
  assert {:msg "37.15: The network might not preserve the channel invariant (#55)"} I[Net#d] == I[Net#e];
  assert {:msg "38.15: The network might not preserve the channel invariant (#56)"} (I[Net#c] > 0) ==> (M[Net#c][0] == M[Net#a][0]);
  assert {:msg "39.15: The network might not preserve the channel invariant (#57)"} (I[Net#c] > 0) ==> (M[Net#c][I[Net#c] - 1] == M[Net#b][I[Net#b]]);
  assert {:msg "32.13: The network might not preserve the network invariant (#58)"} (C[Net#b] - R[Net#b]) == 1;
  assert {:msg "26.3: The network might leave unread tokens on channel a (#59)"} (C[Net#a] - R[Net#a]) == 0;
  assert {:msg "26.3: The network might leave unread tokens on channel c (#60)"} (C[Net#c] - R[Net#c]) == 0;
  assert {:msg "26.3: The network might not produce the specified number of tokens on output out (#61)"} (C[Net#d] - R[Net#d]) == 0;
  assert {:msg "26.3: The network might leave unread tokens on channel e (#62)"} (C[Net#e] - R[Net#e]) == 0;
}

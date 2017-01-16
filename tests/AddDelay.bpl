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
  assert {:msg "Initialization might not establish the invariant (#0)"} R[in1] == C[out];
  assert {:msg "Initialization might not establish the invariant (#1)"} R[in2] == C[out];
  assert {:msg "Initialization might not establish the invariant (#2)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == (M[in1][idx$] + M[in2][idx$]))
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
procedure Split#init#2()
  modifies C, R, M, I;
{
  var in: Chan (int);
  var out1: Chan (int);
  var out2: Chan (int);
  assume (in != out1) && (in != out2) && (out1 != out2);
  assume R[in] == 0;
  assume C[out1] == 0;
  assume C[out2] == 0;
  assert {:msg "Initialization might not establish the invariant (#6)"} R[in] == C[out1];
  assert {:msg "Initialization might not establish the invariant (#7)"} R[in] == C[out2];
  assert {:msg "Initialization might not establish the invariant (#8)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out1]) ==> (M[out1][idx$] == M[in][idx$])
  );
  assert {:msg "Initialization might not establish the invariant (#9)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out2]) ==> (M[out2][idx$] == M[in][idx$])
  );
}
procedure Split#anon$1#3()
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
  assert {:msg "Action at 6.3 might not preserve invariant (#10)"} R[in] == C[out1];
  assert {:msg "Action at 6.3 might not preserve invariant (#11)"} R[in] == C[out2];
  assert {:msg "Action at 6.3 might not preserve invariant (#12)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out1]) ==> (M[out1][idx$] == M[in][idx$])
  );
  assert {:msg "Action at 6.3 might not preserve invariant (#13)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out2]) ==> (M[out2][idx$] == M[in][idx$])
  );
}
procedure Delay#init#4()
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
  assert {:msg "Initialization might not establish the invariant (#14)"} R[in] == (C[out] - 1);
  assert {:msg "Initialization might not establish the invariant (#15)"} (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == M[in][idx$ - 1])
  );
}
procedure Delay#anon$3#5()
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
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == M[in][idx$ - 1])
  );
  in#0 := M[in][R[in]];
  R[in] := R[in] + 1;
  M[out][C[out]] := in#0;
  C[out] := C[out] + 1;
  assert {:msg "Action at 11.3 might not preserve invariant (#16)"} R[in] == (C[out] - 1);
  assert {:msg "Action at 11.3 might not preserve invariant (#17)"} (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == M[in][idx$ - 1])
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
  assert {:msg "24.15: Initialization of network 'Net' might not establish the channel invariant (#18)"} M[Net#b][0] == 0;
  assert {:msg "25.15: Initialization of network 'Net' might not establish the channel invariant (#19)"} 0 <= M[Net#b][I[Net#b]];
  assert {:msg "Initialization of network 'Net' might not establish the channel invariant (#20)"} I[Net#c] == I[Net#a];
  assert {:msg "Initialization of network 'Net' might not establish the channel invariant (#21)"} I[Net#c] == I[Net#b];
  assert {:msg "Initialization of network 'Net' might not establish the channel invariant (#22)"} I[Net#b] == I[Net#e];
  assert {:msg "Initialization of network 'Net' might not establish the channel invariant (#23)"} I[Net#d] == I[Net#c];
  assert {:msg "Initialization of network 'Net' might not establish the channel invariant (#24)"} I[Net#e] == I[Net#c];
  I := R;
  assert {:msg "23.13: Initialization of network 'Net' might not establish the network invariant (#25)"} (C[Net#b] - R[Net#b]) == 1;
  assert {:msg "Initialization of network 'Net' might not establish the network invariant: Unread tokens might be left on channel a (#26)"} (C[Net#a] - R[Net#a]) == 0;
  assert {:msg "Initialization of network 'Net' might not establish the network invariant: Unread tokens might be left on channel c (#27)"} (C[Net#c] - R[Net#c]) == 0;
  assert {:msg "Initialization of network 'Net' might not establish the network invariant: Unread tokens might be left on channel d (#28)"} (C[Net#d] - R[Net#d]) == 0;
  assert {:msg "Initialization of network 'Net' might not establish the network invariant: Unread tokens might be left on channel e (#29)"} (C[Net#e] - R[Net#e]) == 0;
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
  assume M[Net#b][0] == 0;
  assume 0 <= M[Net#b][I[Net#b]];
  assume I[Net#c] == I[Net#a];
  assume I[Net#c] == I[Net#b];
  assume I[Net#b] == I[Net#e];
  assume I[Net#d] == I[Net#c];
  assume I[Net#e] == I[Net#c];
  assume 0 <= M[Net#a][I[Net#a]];
  assume R[Net#a] == C[Net#c];
  assume R[Net#b] == C[Net#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assume R[Net#e] == (C[Net#b] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == M[Net#e][idx$ - 1])
  );
  assume R[Net#c] == C[Net#d];
  assume R[Net#c] == C[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == M[Net#c][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#e][idx$] == M[Net#c][idx$])
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
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assume R[Net#e] == (C[Net#b] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == M[Net#e][idx$ - 1])
  );
  assume R[Net#c] == C[Net#d];
  assume R[Net#c] == C[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == M[Net#c][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assert {:msg "24.15: Action at 2.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#30)"} M[Net#b][0] == 0;
  assert {:msg "25.15: Action at 2.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#31)"} 0 <= M[Net#b][I[Net#b]];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#32)"} I[Net#c] == I[Net#a];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#33)"} I[Net#c] == I[Net#b];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#34)"} I[Net#b] == I[Net#e];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#35)"} I[Net#d] == I[Net#c];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#36)"} I[Net#e] == I[Net#c];
}
procedure Net##Delay#anon$3#8()
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
  assume M[Net#b][0] == 0;
  assume 0 <= M[Net#b][I[Net#b]];
  assume I[Net#c] == I[Net#a];
  assume I[Net#c] == I[Net#b];
  assume I[Net#b] == I[Net#e];
  assume I[Net#d] == I[Net#c];
  assume I[Net#e] == I[Net#c];
  assume 0 <= M[Net#a][I[Net#a]];
  assume R[Net#a] == C[Net#c];
  assume R[Net#b] == C[Net#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assume R[Net#e] == (C[Net#b] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == M[Net#e][idx$ - 1])
  );
  assume R[Net#c] == C[Net#d];
  assume R[Net#c] == C[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == M[Net#c][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assume 1 <= (C[Net#e] - R[Net#e]);
  in#i := M[Net#e][R[Net#e]];
  R[Net#e] := R[Net#e] + 1;
  M[Net#b][C[Net#b]] := in#i;
  C[Net#b] := C[Net#b] + 1;
  assume R[Net#a] == C[Net#c];
  assume R[Net#b] == C[Net#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assume R[Net#e] == (C[Net#b] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == M[Net#e][idx$ - 1])
  );
  assume R[Net#c] == C[Net#d];
  assume R[Net#c] == C[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == M[Net#c][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assert {:msg "24.15: Action at 11.3 ('anon$3') for actor instance 'del' might not preserve the channel invariant (#37)"} M[Net#b][0] == 0;
  assert {:msg "25.15: Action at 11.3 ('anon$3') for actor instance 'del' might not preserve the channel invariant (#38)"} 0 <= M[Net#b][I[Net#b]];
  assert {:msg "Action at 11.3 ('anon$3') for actor instance 'del' might not preserve the channel invariant (#39)"} I[Net#c] == I[Net#a];
  assert {:msg "Action at 11.3 ('anon$3') for actor instance 'del' might not preserve the channel invariant (#40)"} I[Net#c] == I[Net#b];
  assert {:msg "Action at 11.3 ('anon$3') for actor instance 'del' might not preserve the channel invariant (#41)"} I[Net#b] == I[Net#e];
  assert {:msg "Action at 11.3 ('anon$3') for actor instance 'del' might not preserve the channel invariant (#42)"} I[Net#d] == I[Net#c];
  assert {:msg "Action at 11.3 ('anon$3') for actor instance 'del' might not preserve the channel invariant (#43)"} I[Net#e] == I[Net#c];
}
procedure Net##Split#anon$1#9()
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
  assume M[Net#b][0] == 0;
  assume 0 <= M[Net#b][I[Net#b]];
  assume I[Net#c] == I[Net#a];
  assume I[Net#c] == I[Net#b];
  assume I[Net#b] == I[Net#e];
  assume I[Net#d] == I[Net#c];
  assume I[Net#e] == I[Net#c];
  assume 0 <= M[Net#a][I[Net#a]];
  assume R[Net#a] == C[Net#c];
  assume R[Net#b] == C[Net#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assume R[Net#e] == (C[Net#b] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == M[Net#e][idx$ - 1])
  );
  assume R[Net#c] == C[Net#d];
  assume R[Net#c] == C[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == M[Net#c][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#e][idx$] == M[Net#c][idx$])
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
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assume R[Net#e] == (C[Net#b] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == M[Net#e][idx$ - 1])
  );
  assume R[Net#c] == C[Net#d];
  assume R[Net#c] == C[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == M[Net#c][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assert {:msg "24.15: Action at 6.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#44)"} M[Net#b][0] == 0;
  assert {:msg "25.15: Action at 6.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#45)"} 0 <= M[Net#b][I[Net#b]];
  assert {:msg "Action at 6.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#46)"} I[Net#c] == I[Net#a];
  assert {:msg "Action at 6.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#47)"} I[Net#c] == I[Net#b];
  assert {:msg "Action at 6.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#48)"} I[Net#b] == I[Net#e];
  assert {:msg "Action at 6.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#49)"} I[Net#d] == I[Net#c];
  assert {:msg "Action at 6.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#50)"} I[Net#e] == I[Net#c];
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
  assume M[Net#b][0] == 0;
  assume 0 <= M[Net#b][I[Net#b]];
  assume I[Net#c] == I[Net#a];
  assume I[Net#c] == I[Net#b];
  assume I[Net#b] == I[Net#e];
  assume I[Net#d] == I[Net#c];
  assume I[Net#e] == I[Net#c];
  assume 0 <= M[Net#a][I[Net#a]];
  assume R[Net#a] == C[Net#c];
  assume R[Net#b] == C[Net#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assume R[Net#e] == (C[Net#b] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == M[Net#e][idx$ - 1])
  );
  assume R[Net#c] == C[Net#d];
  assume R[Net#c] == C[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == M[Net#c][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  C[Net#a] := C[Net#a] + 1;
  assume 0 <= M[Net#a][I[Net#a]];
  assert {:msg "24.15: Channel invariant might be falsified by network input (#51)"} M[Net#b][0] == 0;
  assert {:msg "25.15: Channel invariant might be falsified by network input (#52)"} 0 <= M[Net#b][I[Net#b]];
  assert {:msg "Channel invariant might be falsified by network input (#53)"} I[Net#c] == I[Net#a];
  assert {:msg "Channel invariant might be falsified by network input (#54)"} I[Net#c] == I[Net#b];
  assert {:msg "Channel invariant might be falsified by network input (#55)"} I[Net#b] == I[Net#e];
  assert {:msg "Channel invariant might be falsified by network input (#56)"} I[Net#d] == I[Net#c];
  assert {:msg "Channel invariant might be falsified by network input (#57)"} I[Net#e] == I[Net#c];
  assert {:msg "17.14: Channel invariant might be falsified by network input (#58)"} 0 <= M[Net#a][I[Net#a]];
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
  assume M[Net#b][0] == 0;
  assume 0 <= M[Net#b][I[Net#b]];
  assume I[Net#c] == I[Net#a];
  assume I[Net#c] == I[Net#b];
  assume I[Net#b] == I[Net#e];
  assume I[Net#d] == I[Net#c];
  assume I[Net#e] == I[Net#c];
  assume 0 <= M[Net#a][I[Net#a]];
  assume R[Net#a] == C[Net#c];
  assume R[Net#b] == C[Net#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> (M[Net#c][idx$] == (M[Net#a][idx$] + M[Net#b][idx$]))
  );
  assume R[Net#e] == (C[Net#b] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == M[Net#e][idx$ - 1])
  );
  assume R[Net#c] == C[Net#d];
  assume R[Net#c] == C[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == M[Net#c][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assume (C[Net#a] - I[Net#a]) == 1;
  assume 0 <= M[Net#a][I[Net#a]];
  assume !((1 <= (C[Net#a] - R[Net#a])) && (1 <= (C[Net#b] - R[Net#b])));
  assume !(1 <= (C[Net#e] - R[Net#e]));
  assume !(1 <= (C[Net#c] - R[Net#c]));
  assert {:msg "18.13: Network action postcondition might not hold (#59)"} M[Net#d][0] == M[Net#a][0];
  assert {:msg "19.13: Network action postcondition might not hold (#60)"} M[Net#d][I[Net#d]] >= M[Net#a][I[Net#a]];
  assert {:msg "20.13: Network action postcondition might not hold (#61)"} (0 < I[Net#d]) ==> (M[Net#d][I[Net#d]] == (M[Net#d][I[Net#d] - 1] + M[Net#a][I[Net#a]]));
  R[Net#d] := R[Net#d] + 1;
  I := R;
  assert {:msg "24.15: The network might not preserve the channel invariant (#62)"} M[Net#b][0] == 0;
  assert {:msg "25.15: The network might not preserve the channel invariant (#63)"} 0 <= M[Net#b][I[Net#b]];
  assert {:msg "The network might not preserve the channel invariant (#64)"} I[Net#c] == I[Net#a];
  assert {:msg "The network might not preserve the channel invariant (#65)"} I[Net#c] == I[Net#b];
  assert {:msg "The network might not preserve the channel invariant (#66)"} I[Net#b] == I[Net#e];
  assert {:msg "The network might not preserve the channel invariant (#67)"} I[Net#d] == I[Net#c];
  assert {:msg "The network might not preserve the channel invariant (#68)"} I[Net#e] == I[Net#c];
  assert {:msg "23.13: The network might not preserve the network invariant (#69)"} (C[Net#b] - R[Net#b]) == 1;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel a (#70)"} (C[Net#a] - R[Net#a]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel c (#71)"} (C[Net#c] - R[Net#c]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel d (#72)"} (C[Net#d] - R[Net#d]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel e (#73)"} (C[Net#e] - R[Net#e]) == 0;
}

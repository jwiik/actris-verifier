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
type ModeType = [Actor]int;

var M#: MType;
var C#: CType;
var R#: CType;
var I#: CType;
var B#: CType;
var Mode#: ModeType;
var I#sub: CType;

var H#: HType;

const unique this#: Actor;

function AT#Min(x:int, y: int): int { if x <= y then x else y }

// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

procedure Add#init#0()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var in1: Chan (int);
  var in2: Chan (int);
  var out: Chan (int);
  assume (in1 != in2) && (in1 != out) && (in2 != out);
  assume (I#[in1] == 0) && (R#[in1] == 0) && (C#[in1] == 0);
  assume (I#[in2] == 0) && (R#[in2] == 0) && (C#[in2] == 0);
  assume (I#[out] == 0) && (R#[out] == 0) && (C#[out] == 0);
  assert {:msg "Initialization might not establish the invariant (#0)"} R#[in1] == C#[out];
  assert {:msg "Initialization might not establish the invariant (#1)"} R#[in2] == C#[out];
  assert {:msg "Initialization might not establish the invariant (#2)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C#[out]) ==> (M#[out][idx$] == (M#[in1][idx$] + M#[in2][idx$]))
  );
}
procedure Add#anon$0#1()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var in1: Chan (int);
  var in2: Chan (int);
  var out: Chan (int);
  var in1#0: int;
  var in2#0: int;
  assume (in1 != in2) && (in1 != out) && (in2 != out);
  assume (0 <= I#[in1]) && (I#[in1] <= R#[in1]) && (R#[in1] <= C#[in1]);
  assume (0 <= I#[in2]) && (I#[in2] <= R#[in2]) && (R#[in2] <= C#[in2]);
  assume (0 <= I#[out]) && (I#[out] <= R#[out]) && (R#[out] <= C#[out]);
  assume R#[in1] == C#[out];
  assume R#[in2] == C#[out];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C#[out]) ==> (M#[out][idx$] == (M#[in1][idx$] + M#[in2][idx$]))
  );
  assume (1 <= (C#[in1] - R#[in1])) && (1 <= (C#[in2] - R#[in2]));
  in1#0 := M#[in1][R#[in1]];
  R#[in1] := R#[in1] + 1;
  in2#0 := M#[in2][R#[in2]];
  R#[in2] := R#[in2] + 1;
  assume true;
  M#[out][C#[out]] := in1#0 + in2#0;
  C#[out] := C#[out] + 1;
  assert {:msg "Action 'anon$0' at AddDelay.actor(2.3) might not preserve the invariant (#3)"} R#[in1] == C#[out];
  assert {:msg "Action 'anon$0' at AddDelay.actor(2.3) might not preserve the invariant (#4)"} R#[in2] == C#[out];
  assert {:msg "Action 'anon$0' at AddDelay.actor(2.3) might not preserve the invariant (#5)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C#[out]) ==> (M#[out][idx$] == (M#[in1][idx$] + M#[in2][idx$]))
  );
}
procedure Split#init#2()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var in: Chan (int);
  var out1: Chan (int);
  var out2: Chan (int);
  assume (in != out1) && (in != out2) && (out1 != out2);
  assume (I#[in] == 0) && (R#[in] == 0) && (C#[in] == 0);
  assume (I#[out1] == 0) && (R#[out1] == 0) && (C#[out1] == 0);
  assume (I#[out2] == 0) && (R#[out2] == 0) && (C#[out2] == 0);
  assert {:msg "Initialization might not establish the invariant (#6)"} R#[in] == C#[out1];
  assert {:msg "Initialization might not establish the invariant (#7)"} R#[in] == C#[out2];
  assert {:msg "Initialization might not establish the invariant (#8)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C#[out1]) ==> (M#[out1][idx$] == M#[in][idx$])
  );
  assert {:msg "Initialization might not establish the invariant (#9)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C#[out2]) ==> (M#[out2][idx$] == M#[in][idx$])
  );
}
procedure Split#anon$1#3()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var in: Chan (int);
  var out1: Chan (int);
  var out2: Chan (int);
  var in#0: int;
  assume (in != out1) && (in != out2) && (out1 != out2);
  assume (0 <= I#[in]) && (I#[in] <= R#[in]) && (R#[in] <= C#[in]);
  assume (0 <= I#[out1]) && (I#[out1] <= R#[out1]) && (R#[out1] <= C#[out1]);
  assume (0 <= I#[out2]) && (I#[out2] <= R#[out2]) && (R#[out2] <= C#[out2]);
  assume R#[in] == C#[out1];
  assume R#[in] == C#[out2];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C#[out1]) ==> (M#[out1][idx$] == M#[in][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C#[out2]) ==> (M#[out2][idx$] == M#[in][idx$])
  );
  assume 1 <= (C#[in] - R#[in]);
  in#0 := M#[in][R#[in]];
  R#[in] := R#[in] + 1;
  assume true;
  M#[out1][C#[out1]] := in#0;
  C#[out1] := C#[out1] + 1;
  M#[out2][C#[out2]] := in#0;
  C#[out2] := C#[out2] + 1;
  assert {:msg "Action 'anon$1' at AddDelay.actor(6.3) might not preserve the invariant (#10)"} R#[in] == C#[out1];
  assert {:msg "Action 'anon$1' at AddDelay.actor(6.3) might not preserve the invariant (#11)"} R#[in] == C#[out2];
  assert {:msg "Action 'anon$1' at AddDelay.actor(6.3) might not preserve the invariant (#12)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C#[out1]) ==> (M#[out1][idx$] == M#[in][idx$])
  );
  assert {:msg "Action 'anon$1' at AddDelay.actor(6.3) might not preserve the invariant (#13)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C#[out2]) ==> (M#[out2][idx$] == M#[in][idx$])
  );
}
procedure Delay#init#4()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var in: Chan (int);
  var out: Chan (int);
  var k: int;
  assume in != out;
  assume (I#[in] == 0) && (R#[in] == 0) && (C#[in] == 0);
  assume (I#[out] == 0) && (R#[out] == 0) && (C#[out] == 0);
  M#[out][C#[out]] := k;
  C#[out] := C#[out] + 1;
  assert {:msg "Initialization might not establish the invariant (#14)"} R#[in] == (C#[out] - 1);
  assert {:msg "Initialization might not establish the invariant (#15)"} (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C#[out]) ==> (M#[out][idx$] == M#[in][idx$ - 1])
  );
}
procedure Delay#anon$3#5()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var in: Chan (int);
  var out: Chan (int);
  var k: int;
  var in#0: int;
  assume in != out;
  assume (0 <= I#[in]) && (I#[in] <= R#[in]) && (R#[in] <= C#[in]);
  assume (0 <= I#[out]) && (I#[out] <= R#[out]) && (R#[out] <= C#[out]);
  assume R#[in] == (C#[out] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C#[out]) ==> (M#[out][idx$] == M#[in][idx$ - 1])
  );
  assume 1 <= (C#[in] - R#[in]);
  in#0 := M#[in][R#[in]];
  R#[in] := R#[in] + 1;
  assume true;
  M#[out][C#[out]] := in#0;
  C#[out] := C#[out] + 1;
  assert {:msg "Action 'anon$3' at AddDelay.actor(11.3) might not preserve the invariant (#16)"} R#[in] == (C#[out] - 1);
  assert {:msg "Action 'anon$3' at AddDelay.actor(11.3) might not preserve the invariant (#17)"} (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C#[out]) ==> (M#[out][idx$] == M#[in][idx$ - 1])
  );
}
procedure Net#init#6()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var Net#add: Actor;
  var Net#del: Actor;
  var Net#spl: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (int);
  var Net#d: Chan (int);
  var Net#e: Chan (int);
  var anon$4: int;
  assume (Net#add != Net#del) && (Net#add != Net#spl) && (Net#del != Net#spl);
  assume (Net#a != Net#b) && (Net#a != Net#c) && (Net#a != Net#d) && (Net#a != Net#e) && (Net#b != Net#c) && (Net#b != Net#d) && (Net#b != Net#e) && (Net#c != Net#d) && (Net#c != Net#e) && (Net#d != Net#e);
  assume 0 <= I#[Net#a];
  assume I#[Net#a] <= R#[Net#a];
  assume R#[Net#a] <= C#[Net#a];
  assume 0 <= I#[Net#b];
  assume I#[Net#b] <= R#[Net#b];
  assume R#[Net#b] <= C#[Net#b];
  assume 0 <= I#[Net#c];
  assume I#[Net#c] <= R#[Net#c];
  assume R#[Net#c] <= C#[Net#c];
  assume 0 <= I#[Net#d];
  assume I#[Net#d] <= R#[Net#d];
  assume R#[Net#d] <= C#[Net#d];
  assume I#[Net#d] == R#[Net#d];
  assume 0 <= I#[Net#e];
  assume I#[Net#e] <= R#[Net#e];
  assume R#[Net#e] <= C#[Net#e];
  assume (B#[Net#a] == 1) && (B#[Net#d] == 2);
  assume anon$4 == 0;
  assume Mode#[this#] == anon$4;
  assume C#[Net#a] == 0;
  assume R#[Net#a] == 0;
  assume C#[Net#b] == 0;
  assume R#[Net#b] == 0;
  assume C#[Net#c] == 0;
  assume R#[Net#c] == 0;
  assume C#[Net#d] == 0;
  assume R#[Net#d] == 0;
  assume C#[Net#e] == 0;
  assume R#[Net#e] == 0;
  assume 0 == 0;
  M#[Net#b][C#[Net#b]] := 0;
  C#[Net#b] := C#[Net#b] + 1;
  assert {:msg "AddDelay.actor(24.15): Initialization of network 'Net' might not establish the channel invariant (#18)"} M#[Net#b][0] == 0;
  assert {:msg "AddDelay.actor(25.15): Initialization of network 'Net' might not establish the channel invariant (#19)"} 0 <= M#[Net#b][I#[Net#b]];
  assert {:msg "Initialization of network 'Net' might not establish the channel invariant (#20)"} I#[Net#c] == I#[Net#a];
  assert {:msg "Initialization of network 'Net' might not establish the channel invariant (#21)"} I#[Net#c] == I#[Net#b];
  assert {:msg "Initialization of network 'Net' might not establish the channel invariant (#22)"} I#[Net#b] == I#[Net#e];
  assert {:msg "Initialization of network 'Net' might not establish the channel invariant (#23)"} I#[Net#d] == I#[Net#c];
  assert {:msg "Initialization of network 'Net' might not establish the channel invariant (#24)"} I#[Net#e] == I#[Net#c];
  assert {:msg "Initialization of network 'Net' might not establish the channel invariant (#25)"} (Mode#[this#] == anon$4) ==> (((C#[Net#a] - I#[Net#a]) >= 1) ==> (0 <= M#[Net#a][I#[Net#a]]));
  assert {:msg "Initialization of network 'Net' might not establish the channel invariant (#26)"} (Mode#[this#] == anon$4) ==> ((C#[Net#a] - I#[Net#a]) <= 1);
  I# := R#;
  assert {:msg "AddDelay.actor(23.13): Initialization of network 'Net' might not establish the network invariant (#27)"} (C#[Net#b] - R#[Net#b]) == 1;
  assert {:msg "Initialization of network 'Net' might not establish the network invariant (#28)"} (2 * R#[Net#a]) == C#[Net#d];
  assert {:msg "Initialization of network 'Net' might not establish the network invariant: Unread tokens might be left on channel a (#29)"} (C#[Net#a] - R#[Net#a]) == 0;
  assert {:msg "Initialization of network 'Net' might not establish the network invariant: Unread tokens might be left on channel c (#30)"} (C#[Net#c] - R#[Net#c]) == 0;
  assert {:msg "Initialization of network 'Net' might not establish the network invariant: Unread tokens might be left on channel d (#31)"} (C#[Net#d] - R#[Net#d]) == 0;
  assert {:msg "Initialization of network 'Net' might not establish the network invariant: Unread tokens might be left on channel e (#32)"} (C#[Net#e] - R#[Net#e]) == 0;
}
procedure Net##Add#anon$0#7()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var Net#add: Actor;
  var Net#del: Actor;
  var Net#spl: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (int);
  var Net#d: Chan (int);
  var Net#e: Chan (int);
  var anon$4: int;
  var in1#i: int;
  var in2#j: int;
  assume (Net#add != Net#del) && (Net#add != Net#spl) && (Net#del != Net#spl);
  assume (Net#a != Net#b) && (Net#a != Net#c) && (Net#a != Net#d) && (Net#a != Net#e) && (Net#b != Net#c) && (Net#b != Net#d) && (Net#b != Net#e) && (Net#c != Net#d) && (Net#c != Net#e) && (Net#d != Net#e);
  assume 0 <= I#[Net#a];
  assume I#[Net#a] <= R#[Net#a];
  assume R#[Net#a] <= C#[Net#a];
  assume 0 <= I#[Net#b];
  assume I#[Net#b] <= R#[Net#b];
  assume R#[Net#b] <= C#[Net#b];
  assume 0 <= I#[Net#c];
  assume I#[Net#c] <= R#[Net#c];
  assume R#[Net#c] <= C#[Net#c];
  assume 0 <= I#[Net#d];
  assume I#[Net#d] <= R#[Net#d];
  assume R#[Net#d] <= C#[Net#d];
  assume I#[Net#d] == R#[Net#d];
  assume 0 <= I#[Net#e];
  assume I#[Net#e] <= R#[Net#e];
  assume R#[Net#e] <= C#[Net#e];
  assume (B#[Net#a] == 1) && (B#[Net#d] == 2);
  assume anon$4 == 0;
  assume Mode#[this#] == anon$4;
  I#sub[Net#a] := R#[Net#a];
  I#sub[Net#b] := R#[Net#b];
  I#sub[Net#c] := C#[Net#c];
  assume M#[Net#b][0] == 0;
  assume 0 <= M#[Net#b][I#[Net#b]];
  assume I#[Net#c] == I#[Net#a];
  assume I#[Net#c] == I#[Net#b];
  assume I#[Net#b] == I#[Net#e];
  assume I#[Net#d] == I#[Net#c];
  assume I#[Net#e] == I#[Net#c];
  assume (Mode#[this#] == anon$4) ==> (((C#[Net#a] - I#[Net#a]) >= 1) ==> (0 <= M#[Net#a][I#[Net#a]]));
  assume (Mode#[this#] == anon$4) ==> ((C#[Net#a] - I#[Net#a]) <= 1);
  assume R#[Net#a] == C#[Net#c];
  assume R#[Net#b] == C#[Net#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C#[Net#c]) ==> (M#[Net#c][idx$] == (M#[Net#a][idx$] + M#[Net#b][idx$]))
  );
  assume R#[Net#e] == (C#[Net#b] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C#[Net#b]) ==> (M#[Net#b][idx$] == M#[Net#e][idx$ - 1])
  );
  assume R#[Net#c] == C#[Net#d];
  assume R#[Net#c] == C#[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C#[Net#d]) ==> (M#[Net#d][idx$] == M#[Net#c][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C#[Net#e]) ==> (M#[Net#e][idx$] == M#[Net#c][idx$])
  );
  assume (1 <= (C#[Net#a] - R#[Net#a])) && (1 <= (C#[Net#b] - R#[Net#b]));
  in1#i := M#[Net#a][R#[Net#a]];
  R#[Net#a] := R#[Net#a] + 1;
  in2#j := M#[Net#b][R#[Net#b]];
  R#[Net#b] := R#[Net#b] + 1;
  M#[Net#c][C#[Net#c]] := in1#i + in2#j;
  C#[Net#c] := C#[Net#c] + 1;
  assert {:msg "AddDelay.actor(24.15): Action at AddDelay.actor(2.3) ('anon$0') for actor instance 'add' might not preserve the channel invariant (#33)"} M#[Net#b][0] == 0;
  assert {:msg "AddDelay.actor(25.15): Action at AddDelay.actor(2.3) ('anon$0') for actor instance 'add' might not preserve the channel invariant (#34)"} 0 <= M#[Net#b][I#[Net#b]];
  assert {:msg "Action at AddDelay.actor(2.3) ('anon$0') for actor instance 'add' might not preserve the channel invariant (#35)"} I#[Net#c] == I#[Net#a];
  assert {:msg "Action at AddDelay.actor(2.3) ('anon$0') for actor instance 'add' might not preserve the channel invariant (#36)"} I#[Net#c] == I#[Net#b];
  assert {:msg "Action at AddDelay.actor(2.3) ('anon$0') for actor instance 'add' might not preserve the channel invariant (#37)"} I#[Net#b] == I#[Net#e];
  assert {:msg "Action at AddDelay.actor(2.3) ('anon$0') for actor instance 'add' might not preserve the channel invariant (#38)"} I#[Net#d] == I#[Net#c];
  assert {:msg "Action at AddDelay.actor(2.3) ('anon$0') for actor instance 'add' might not preserve the channel invariant (#39)"} I#[Net#e] == I#[Net#c];
  assert {:msg "Action at AddDelay.actor(2.3) ('anon$0') for actor instance 'add' might not preserve the channel invariant (#40)"} (Mode#[this#] == anon$4) ==> (((C#[Net#a] - I#[Net#a]) >= 1) ==> (0 <= M#[Net#a][I#[Net#a]]));
  assert {:msg "Action at AddDelay.actor(2.3) ('anon$0') for actor instance 'add' might not preserve the channel invariant (#41)"} (Mode#[this#] == anon$4) ==> ((C#[Net#a] - I#[Net#a]) <= 1);
}
procedure Net##Delay#anon$3#8()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var Net#add: Actor;
  var Net#del: Actor;
  var Net#spl: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (int);
  var Net#d: Chan (int);
  var Net#e: Chan (int);
  var anon$4: int;
  var in#i: int;
  assume (Net#add != Net#del) && (Net#add != Net#spl) && (Net#del != Net#spl);
  assume (Net#a != Net#b) && (Net#a != Net#c) && (Net#a != Net#d) && (Net#a != Net#e) && (Net#b != Net#c) && (Net#b != Net#d) && (Net#b != Net#e) && (Net#c != Net#d) && (Net#c != Net#e) && (Net#d != Net#e);
  assume 0 <= I#[Net#a];
  assume I#[Net#a] <= R#[Net#a];
  assume R#[Net#a] <= C#[Net#a];
  assume 0 <= I#[Net#b];
  assume I#[Net#b] <= R#[Net#b];
  assume R#[Net#b] <= C#[Net#b];
  assume 0 <= I#[Net#c];
  assume I#[Net#c] <= R#[Net#c];
  assume R#[Net#c] <= C#[Net#c];
  assume 0 <= I#[Net#d];
  assume I#[Net#d] <= R#[Net#d];
  assume R#[Net#d] <= C#[Net#d];
  assume I#[Net#d] == R#[Net#d];
  assume 0 <= I#[Net#e];
  assume I#[Net#e] <= R#[Net#e];
  assume R#[Net#e] <= C#[Net#e];
  assume (B#[Net#a] == 1) && (B#[Net#d] == 2);
  assume anon$4 == 0;
  assume Mode#[this#] == anon$4;
  I#sub[Net#e] := R#[Net#e];
  I#sub[Net#b] := C#[Net#b];
  assume M#[Net#b][0] == 0;
  assume 0 <= M#[Net#b][I#[Net#b]];
  assume I#[Net#c] == I#[Net#a];
  assume I#[Net#c] == I#[Net#b];
  assume I#[Net#b] == I#[Net#e];
  assume I#[Net#d] == I#[Net#c];
  assume I#[Net#e] == I#[Net#c];
  assume (Mode#[this#] == anon$4) ==> (((C#[Net#a] - I#[Net#a]) >= 1) ==> (0 <= M#[Net#a][I#[Net#a]]));
  assume (Mode#[this#] == anon$4) ==> ((C#[Net#a] - I#[Net#a]) <= 1);
  assume R#[Net#a] == C#[Net#c];
  assume R#[Net#b] == C#[Net#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C#[Net#c]) ==> (M#[Net#c][idx$] == (M#[Net#a][idx$] + M#[Net#b][idx$]))
  );
  assume R#[Net#e] == (C#[Net#b] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C#[Net#b]) ==> (M#[Net#b][idx$] == M#[Net#e][idx$ - 1])
  );
  assume R#[Net#c] == C#[Net#d];
  assume R#[Net#c] == C#[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C#[Net#d]) ==> (M#[Net#d][idx$] == M#[Net#c][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C#[Net#e]) ==> (M#[Net#e][idx$] == M#[Net#c][idx$])
  );
  assume 1 <= (C#[Net#e] - R#[Net#e]);
  in#i := M#[Net#e][R#[Net#e]];
  R#[Net#e] := R#[Net#e] + 1;
  M#[Net#b][C#[Net#b]] := in#i;
  C#[Net#b] := C#[Net#b] + 1;
  assert {:msg "AddDelay.actor(24.15): Action at AddDelay.actor(11.3) ('anon$3') for actor instance 'del' might not preserve the channel invariant (#42)"} M#[Net#b][0] == 0;
  assert {:msg "AddDelay.actor(25.15): Action at AddDelay.actor(11.3) ('anon$3') for actor instance 'del' might not preserve the channel invariant (#43)"} 0 <= M#[Net#b][I#[Net#b]];
  assert {:msg "Action at AddDelay.actor(11.3) ('anon$3') for actor instance 'del' might not preserve the channel invariant (#44)"} I#[Net#c] == I#[Net#a];
  assert {:msg "Action at AddDelay.actor(11.3) ('anon$3') for actor instance 'del' might not preserve the channel invariant (#45)"} I#[Net#c] == I#[Net#b];
  assert {:msg "Action at AddDelay.actor(11.3) ('anon$3') for actor instance 'del' might not preserve the channel invariant (#46)"} I#[Net#b] == I#[Net#e];
  assert {:msg "Action at AddDelay.actor(11.3) ('anon$3') for actor instance 'del' might not preserve the channel invariant (#47)"} I#[Net#d] == I#[Net#c];
  assert {:msg "Action at AddDelay.actor(11.3) ('anon$3') for actor instance 'del' might not preserve the channel invariant (#48)"} I#[Net#e] == I#[Net#c];
  assert {:msg "Action at AddDelay.actor(11.3) ('anon$3') for actor instance 'del' might not preserve the channel invariant (#49)"} (Mode#[this#] == anon$4) ==> (((C#[Net#a] - I#[Net#a]) >= 1) ==> (0 <= M#[Net#a][I#[Net#a]]));
  assert {:msg "Action at AddDelay.actor(11.3) ('anon$3') for actor instance 'del' might not preserve the channel invariant (#50)"} (Mode#[this#] == anon$4) ==> ((C#[Net#a] - I#[Net#a]) <= 1);
}
procedure Net##Split#anon$1#9()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var Net#add: Actor;
  var Net#del: Actor;
  var Net#spl: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (int);
  var Net#d: Chan (int);
  var Net#e: Chan (int);
  var anon$4: int;
  var in#i: int;
  assume (Net#add != Net#del) && (Net#add != Net#spl) && (Net#del != Net#spl);
  assume (Net#a != Net#b) && (Net#a != Net#c) && (Net#a != Net#d) && (Net#a != Net#e) && (Net#b != Net#c) && (Net#b != Net#d) && (Net#b != Net#e) && (Net#c != Net#d) && (Net#c != Net#e) && (Net#d != Net#e);
  assume 0 <= I#[Net#a];
  assume I#[Net#a] <= R#[Net#a];
  assume R#[Net#a] <= C#[Net#a];
  assume 0 <= I#[Net#b];
  assume I#[Net#b] <= R#[Net#b];
  assume R#[Net#b] <= C#[Net#b];
  assume 0 <= I#[Net#c];
  assume I#[Net#c] <= R#[Net#c];
  assume R#[Net#c] <= C#[Net#c];
  assume 0 <= I#[Net#d];
  assume I#[Net#d] <= R#[Net#d];
  assume R#[Net#d] <= C#[Net#d];
  assume I#[Net#d] == R#[Net#d];
  assume 0 <= I#[Net#e];
  assume I#[Net#e] <= R#[Net#e];
  assume R#[Net#e] <= C#[Net#e];
  assume (B#[Net#a] == 1) && (B#[Net#d] == 2);
  assume anon$4 == 0;
  assume Mode#[this#] == anon$4;
  I#sub[Net#c] := R#[Net#c];
  I#sub[Net#d] := C#[Net#d];
  I#sub[Net#e] := C#[Net#e];
  assume M#[Net#b][0] == 0;
  assume 0 <= M#[Net#b][I#[Net#b]];
  assume I#[Net#c] == I#[Net#a];
  assume I#[Net#c] == I#[Net#b];
  assume I#[Net#b] == I#[Net#e];
  assume I#[Net#d] == I#[Net#c];
  assume I#[Net#e] == I#[Net#c];
  assume (Mode#[this#] == anon$4) ==> (((C#[Net#a] - I#[Net#a]) >= 1) ==> (0 <= M#[Net#a][I#[Net#a]]));
  assume (Mode#[this#] == anon$4) ==> ((C#[Net#a] - I#[Net#a]) <= 1);
  assume R#[Net#a] == C#[Net#c];
  assume R#[Net#b] == C#[Net#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C#[Net#c]) ==> (M#[Net#c][idx$] == (M#[Net#a][idx$] + M#[Net#b][idx$]))
  );
  assume R#[Net#e] == (C#[Net#b] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C#[Net#b]) ==> (M#[Net#b][idx$] == M#[Net#e][idx$ - 1])
  );
  assume R#[Net#c] == C#[Net#d];
  assume R#[Net#c] == C#[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C#[Net#d]) ==> (M#[Net#d][idx$] == M#[Net#c][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C#[Net#e]) ==> (M#[Net#e][idx$] == M#[Net#c][idx$])
  );
  assume 1 <= (C#[Net#c] - R#[Net#c]);
  in#i := M#[Net#c][R#[Net#c]];
  R#[Net#c] := R#[Net#c] + 1;
  M#[Net#d][C#[Net#d]] := in#i;
  C#[Net#d] := C#[Net#d] + 1;
  M#[Net#e][C#[Net#e]] := in#i;
  C#[Net#e] := C#[Net#e] + 1;
  assert {:msg "AddDelay.actor(24.15): Action at AddDelay.actor(6.3) ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#51)"} M#[Net#b][0] == 0;
  assert {:msg "AddDelay.actor(25.15): Action at AddDelay.actor(6.3) ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#52)"} 0 <= M#[Net#b][I#[Net#b]];
  assert {:msg "Action at AddDelay.actor(6.3) ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#53)"} I#[Net#c] == I#[Net#a];
  assert {:msg "Action at AddDelay.actor(6.3) ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#54)"} I#[Net#c] == I#[Net#b];
  assert {:msg "Action at AddDelay.actor(6.3) ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#55)"} I#[Net#b] == I#[Net#e];
  assert {:msg "Action at AddDelay.actor(6.3) ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#56)"} I#[Net#d] == I#[Net#c];
  assert {:msg "Action at AddDelay.actor(6.3) ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#57)"} I#[Net#e] == I#[Net#c];
  assert {:msg "Action at AddDelay.actor(6.3) ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#58)"} (Mode#[this#] == anon$4) ==> (((C#[Net#a] - I#[Net#a]) >= 1) ==> (0 <= M#[Net#a][I#[Net#a]]));
  assert {:msg "Action at AddDelay.actor(6.3) ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#59)"} (Mode#[this#] == anon$4) ==> ((C#[Net#a] - I#[Net#a]) <= 1);
}
procedure Net#anon$4#input#in#10()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var Net#add: Actor;
  var Net#del: Actor;
  var Net#spl: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (int);
  var Net#d: Chan (int);
  var Net#e: Chan (int);
  var anon$4: int;
  assume (Net#add != Net#del) && (Net#add != Net#spl) && (Net#del != Net#spl);
  assume (Net#a != Net#b) && (Net#a != Net#c) && (Net#a != Net#d) && (Net#a != Net#e) && (Net#b != Net#c) && (Net#b != Net#d) && (Net#b != Net#e) && (Net#c != Net#d) && (Net#c != Net#e) && (Net#d != Net#e);
  assume 0 <= I#[Net#a];
  assume I#[Net#a] <= R#[Net#a];
  assume R#[Net#a] <= C#[Net#a];
  assume 0 <= I#[Net#b];
  assume I#[Net#b] <= R#[Net#b];
  assume R#[Net#b] <= C#[Net#b];
  assume 0 <= I#[Net#c];
  assume I#[Net#c] <= R#[Net#c];
  assume R#[Net#c] <= C#[Net#c];
  assume 0 <= I#[Net#d];
  assume I#[Net#d] <= R#[Net#d];
  assume R#[Net#d] <= C#[Net#d];
  assume I#[Net#d] == R#[Net#d];
  assume 0 <= I#[Net#e];
  assume I#[Net#e] <= R#[Net#e];
  assume R#[Net#e] <= C#[Net#e];
  assume (B#[Net#a] == 1) && (B#[Net#d] == 2);
  assume anon$4 == 0;
  assume Mode#[this#] == anon$4;
  assume (B#[Net#a] == 1) && (B#[Net#d] == 2);
  assume Mode#[this#] == anon$4;
  assume (C#[Net#a] - I#[Net#a]) < 1;
  assume M#[Net#b][0] == 0;
  assume 0 <= M#[Net#b][I#[Net#b]];
  assume I#[Net#c] == I#[Net#a];
  assume I#[Net#c] == I#[Net#b];
  assume I#[Net#b] == I#[Net#e];
  assume I#[Net#d] == I#[Net#c];
  assume I#[Net#e] == I#[Net#c];
  assume (Mode#[this#] == anon$4) ==> (((C#[Net#a] - I#[Net#a]) >= 1) ==> (0 <= M#[Net#a][I#[Net#a]]));
  assume (Mode#[this#] == anon$4) ==> ((C#[Net#a] - I#[Net#a]) <= 1);
  assume R#[Net#a] == C#[Net#c];
  assume R#[Net#b] == C#[Net#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C#[Net#c]) ==> (M#[Net#c][idx$] == (M#[Net#a][idx$] + M#[Net#b][idx$]))
  );
  assume R#[Net#e] == (C#[Net#b] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C#[Net#b]) ==> (M#[Net#b][idx$] == M#[Net#e][idx$ - 1])
  );
  assume R#[Net#c] == C#[Net#d];
  assume R#[Net#c] == C#[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C#[Net#d]) ==> (M#[Net#d][idx$] == M#[Net#c][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C#[Net#e]) ==> (M#[Net#e][idx$] == M#[Net#c][idx$])
  );
  C#[Net#a] := C#[Net#a] + 1;
  assume 0 <= M#[Net#a][I#[Net#a]];
  assert {:msg "AddDelay.actor(24.15): Channel invariant might be falsified by network input on port 'in' for contract 'anon$4' (#60)"} M#[Net#b][0] == 0;
  assert {:msg "AddDelay.actor(25.15): Channel invariant might be falsified by network input on port 'in' for contract 'anon$4' (#61)"} 0 <= M#[Net#b][I#[Net#b]];
  assert {:msg "Channel invariant might be falsified by network input on port 'in' for contract 'anon$4' (#62)"} I#[Net#c] == I#[Net#a];
  assert {:msg "Channel invariant might be falsified by network input on port 'in' for contract 'anon$4' (#63)"} I#[Net#c] == I#[Net#b];
  assert {:msg "Channel invariant might be falsified by network input on port 'in' for contract 'anon$4' (#64)"} I#[Net#b] == I#[Net#e];
  assert {:msg "Channel invariant might be falsified by network input on port 'in' for contract 'anon$4' (#65)"} I#[Net#d] == I#[Net#c];
  assert {:msg "Channel invariant might be falsified by network input on port 'in' for contract 'anon$4' (#66)"} I#[Net#e] == I#[Net#c];
  assert {:msg "Channel invariant might be falsified by network input on port 'in' for contract 'anon$4' (#67)"} (Mode#[this#] == anon$4) ==> (((C#[Net#a] - I#[Net#a]) >= 1) ==> (0 <= M#[Net#a][I#[Net#a]]));
  assert {:msg "Channel invariant might be falsified by network input on port 'in' for contract 'anon$4' (#68)"} (Mode#[this#] == anon$4) ==> ((C#[Net#a] - I#[Net#a]) <= 1);
}
procedure Net#anon$4#exit#11()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var Net#add: Actor;
  var Net#del: Actor;
  var Net#spl: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (int);
  var Net#d: Chan (int);
  var Net#e: Chan (int);
  var anon$4: int;
  assume (Net#add != Net#del) && (Net#add != Net#spl) && (Net#del != Net#spl);
  assume (Net#a != Net#b) && (Net#a != Net#c) && (Net#a != Net#d) && (Net#a != Net#e) && (Net#b != Net#c) && (Net#b != Net#d) && (Net#b != Net#e) && (Net#c != Net#d) && (Net#c != Net#e) && (Net#d != Net#e);
  assume 0 <= I#[Net#a];
  assume I#[Net#a] <= R#[Net#a];
  assume R#[Net#a] <= C#[Net#a];
  assume 0 <= I#[Net#b];
  assume I#[Net#b] <= R#[Net#b];
  assume R#[Net#b] <= C#[Net#b];
  assume 0 <= I#[Net#c];
  assume I#[Net#c] <= R#[Net#c];
  assume R#[Net#c] <= C#[Net#c];
  assume 0 <= I#[Net#d];
  assume I#[Net#d] <= R#[Net#d];
  assume R#[Net#d] <= C#[Net#d];
  assume I#[Net#d] == R#[Net#d];
  assume 0 <= I#[Net#e];
  assume I#[Net#e] <= R#[Net#e];
  assume R#[Net#e] <= C#[Net#e];
  assume (B#[Net#a] == 1) && (B#[Net#d] == 2);
  assume anon$4 == 0;
  assume Mode#[this#] == anon$4;
  assume Mode#[this#] == anon$4;
  assume (B#[Net#a] == 1) && (B#[Net#d] == 2);
  assume M#[Net#b][0] == 0;
  assume 0 <= M#[Net#b][I#[Net#b]];
  assume I#[Net#c] == I#[Net#a];
  assume I#[Net#c] == I#[Net#b];
  assume I#[Net#b] == I#[Net#e];
  assume I#[Net#d] == I#[Net#c];
  assume I#[Net#e] == I#[Net#c];
  assume (Mode#[this#] == anon$4) ==> (((C#[Net#a] - I#[Net#a]) >= 1) ==> (0 <= M#[Net#a][I#[Net#a]]));
  assume (Mode#[this#] == anon$4) ==> ((C#[Net#a] - I#[Net#a]) <= 1);
  assume R#[Net#a] == C#[Net#c];
  assume R#[Net#b] == C#[Net#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C#[Net#c]) ==> (M#[Net#c][idx$] == (M#[Net#a][idx$] + M#[Net#b][idx$]))
  );
  assume R#[Net#e] == (C#[Net#b] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C#[Net#b]) ==> (M#[Net#b][idx$] == M#[Net#e][idx$ - 1])
  );
  assume R#[Net#c] == C#[Net#d];
  assume R#[Net#c] == C#[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C#[Net#d]) ==> (M#[Net#d][idx$] == M#[Net#c][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C#[Net#e]) ==> (M#[Net#e][idx$] == M#[Net#c][idx$])
  );
  assume (C#[Net#a] - I#[Net#a]) == 1;
  assume 0 <= M#[Net#a][I#[Net#a]];
  assume !((1 <= (C#[Net#a] - R#[Net#a])) && (1 <= (C#[Net#b] - R#[Net#b])));
  assume !(1 <= (C#[Net#e] - R#[Net#e]));
  assume !(1 <= (C#[Net#c] - R#[Net#c]));
  assert {:msg "AddDelay.actor(16.3): The correct number of tokens might not be produced on output 'out' for contract 'anon$4' (#69)"} (C#[Net#d] - I#[Net#d]) == 2;
  assert {:msg "AddDelay.actor(18.13): Network action postcondition might not hold (#70)"} M#[Net#d][0] == M#[Net#a][0];
  assert {:msg "AddDelay.actor(19.13): Network action postcondition might not hold (#71)"} M#[Net#d][I#[Net#d]] >= M#[Net#a][I#[Net#a]];
  assert {:msg "AddDelay.actor(20.13): Network action postcondition might not hold (#72)"} (0 < I#[Net#d]) ==> (M#[Net#d][I#[Net#d]] == (M#[Net#d][I#[Net#d] - 1] + M#[Net#a][I#[Net#a]]));
  R#[Net#d] := R#[Net#d] + 2;
  I# := R#;
  assert {:msg "AddDelay.actor(24.15): The network might not preserve the channel invariant for contract 'anon$4' (#73)"} M#[Net#b][0] == 0;
  assert {:msg "AddDelay.actor(25.15): The network might not preserve the channel invariant for contract 'anon$4' (#74)"} 0 <= M#[Net#b][I#[Net#b]];
  assert {:msg "The network might not preserve the channel invariant for contract 'anon$4' (#75)"} I#[Net#c] == I#[Net#a];
  assert {:msg "The network might not preserve the channel invariant for contract 'anon$4' (#76)"} I#[Net#c] == I#[Net#b];
  assert {:msg "The network might not preserve the channel invariant for contract 'anon$4' (#77)"} I#[Net#b] == I#[Net#e];
  assert {:msg "The network might not preserve the channel invariant for contract 'anon$4' (#78)"} I#[Net#d] == I#[Net#c];
  assert {:msg "The network might not preserve the channel invariant for contract 'anon$4' (#79)"} I#[Net#e] == I#[Net#c];
  assert {:msg "The network might not preserve the channel invariant for contract 'anon$4' (#80)"} (Mode#[this#] == anon$4) ==> (((C#[Net#a] - I#[Net#a]) >= 1) ==> (0 <= M#[Net#a][I#[Net#a]]));
  assert {:msg "The network might not preserve the channel invariant for contract 'anon$4' (#81)"} (Mode#[this#] == anon$4) ==> ((C#[Net#a] - I#[Net#a]) <= 1);
  assert {:msg "AddDelay.actor(23.13): The network might not preserve the network invariant for contract 'anon$4' (#82)"} (C#[Net#b] - R#[Net#b]) == 1;
  assert {:msg "The network might not preserve the network invariant for contract 'anon$4' (#83)"} (2 * R#[Net#a]) == C#[Net#d];
  assert {:msg "The network might not preserve the network invariant for contract 'anon$4': Unread tokens might be left on channel a (#84)"} (C#[Net#a] - R#[Net#a]) == 0;
  assert {:msg "The network might not preserve the network invariant for contract 'anon$4': Unread tokens might be left on channel c (#85)"} (C#[Net#c] - R#[Net#c]) == 0;
  assert {:msg "The network might not preserve the network invariant for contract 'anon$4': Unread tokens might be left on channel d (#86)"} (C#[Net#d] - R#[Net#d]) == 0;
  assert {:msg "The network might not preserve the network invariant for contract 'anon$4': Unread tokens might be left on channel e (#87)"} (C#[Net#e] - R#[Net#e]) == 0;
}

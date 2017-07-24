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

procedure Add#Add#gen$init#init#0()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var in1: Chan (int);
  var in2: Chan (int);
  var out: Chan (int);
  assume (in1 != in2) && (in1 != out) && (in2 != out);
  assume (0 <= I#[in1]) && (I#[in1] <= R#[in1]) && (R#[in1] <= C#[in1]);
  assume (0 <= I#[in2]) && (I#[in2] <= R#[in2]) && (R#[in2] <= C#[in2]);
  assume (0 <= I#[out]) && (I#[out] <= R#[out]) && (R#[out] <= C#[out]);
  assume (I#[in1] == 0) && (R#[in1] == 0) && (C#[in1] == 0);
  assume (I#[in2] == 0) && (R#[in2] == 0) && (C#[in2] == 0);
  assume (I#[out] == 0) && (R#[out] == 0) && (C#[out] == 0);
  assert {:msg "Initialization might not establish the invariant (#0)"} R#[in1] == C#[out];
  assert {:msg "Initialization might not establish the invariant (#1)"} R#[in2] == C#[out];
  assert {:msg "Initialization might not establish the invariant (#2)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C#[out]) ==> (M#[out][idx$] == (M#[in1][idx$] + M#[in2][idx$]))
  );
}
procedure Add#anon__22#1()
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
  assert {:msg "Action 'anon__22' at AddDelay.actor(2.3) might not preserve the invariant (#3)"} R#[in1] == C#[out];
  assert {:msg "Action 'anon__22' at AddDelay.actor(2.3) might not preserve the invariant (#4)"} R#[in2] == C#[out];
  assert {:msg "Action 'anon__22' at AddDelay.actor(2.3) might not preserve the invariant (#5)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C#[out]) ==> (M#[out][idx$] == (M#[in1][idx$] + M#[in2][idx$]))
  );
}
procedure Split#Split#gen$init#init#2()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var in1: Chan (int);
  var out1: Chan (int);
  var out2: Chan (int);
  assume (in1 != out1) && (in1 != out2) && (out1 != out2);
  assume (0 <= I#[in1]) && (I#[in1] <= R#[in1]) && (R#[in1] <= C#[in1]);
  assume (0 <= I#[out1]) && (I#[out1] <= R#[out1]) && (R#[out1] <= C#[out1]);
  assume (0 <= I#[out2]) && (I#[out2] <= R#[out2]) && (R#[out2] <= C#[out2]);
  assume (I#[in1] == 0) && (R#[in1] == 0) && (C#[in1] == 0);
  assume (I#[out1] == 0) && (R#[out1] == 0) && (C#[out1] == 0);
  assume (I#[out2] == 0) && (R#[out2] == 0) && (C#[out2] == 0);
  assert {:msg "Initialization might not establish the invariant (#6)"} R#[in1] == C#[out1];
  assert {:msg "Initialization might not establish the invariant (#7)"} R#[in1] == C#[out2];
  assert {:msg "Initialization might not establish the invariant (#8)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C#[out1]) ==> (M#[out1][idx$] == M#[in1][idx$])
  );
  assert {:msg "Initialization might not establish the invariant (#9)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C#[out2]) ==> (M#[out2][idx$] == M#[in1][idx$])
  );
}
procedure Split#anon__23#3()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var in1: Chan (int);
  var out1: Chan (int);
  var out2: Chan (int);
  var in1#0: int;
  assume (in1 != out1) && (in1 != out2) && (out1 != out2);
  assume (0 <= I#[in1]) && (I#[in1] <= R#[in1]) && (R#[in1] <= C#[in1]);
  assume (0 <= I#[out1]) && (I#[out1] <= R#[out1]) && (R#[out1] <= C#[out1]);
  assume (0 <= I#[out2]) && (I#[out2] <= R#[out2]) && (R#[out2] <= C#[out2]);
  assume R#[in1] == C#[out1];
  assume R#[in1] == C#[out2];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C#[out1]) ==> (M#[out1][idx$] == M#[in1][idx$])
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C#[out2]) ==> (M#[out2][idx$] == M#[in1][idx$])
  );
  assume 1 <= (C#[in1] - R#[in1]);
  in1#0 := M#[in1][R#[in1]];
  R#[in1] := R#[in1] + 1;
  assume true;
  M#[out1][C#[out1]] := in1#0;
  C#[out1] := C#[out1] + 1;
  M#[out2][C#[out2]] := in1#0;
  C#[out2] := C#[out2] + 1;
  assert {:msg "Action 'anon__23' at AddDelay.actor(6.3) might not preserve the invariant (#10)"} R#[in1] == C#[out1];
  assert {:msg "Action 'anon__23' at AddDelay.actor(6.3) might not preserve the invariant (#11)"} R#[in1] == C#[out2];
  assert {:msg "Action 'anon__23' at AddDelay.actor(6.3) might not preserve the invariant (#12)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C#[out1]) ==> (M#[out1][idx$] == M#[in1][idx$])
  );
  assert {:msg "Action 'anon__23' at AddDelay.actor(6.3) might not preserve the invariant (#13)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C#[out2]) ==> (M#[out2][idx$] == M#[in1][idx$])
  );
}
procedure Delay#anon__24#init#4()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var in1: Chan (int);
  var out: Chan (int);
  var k: int;
  assume in1 != out;
  assume (0 <= I#[in1]) && (I#[in1] <= R#[in1]) && (R#[in1] <= C#[in1]);
  assume (0 <= I#[out]) && (I#[out] <= R#[out]) && (R#[out] <= C#[out]);
  assume (I#[in1] == 0) && (R#[in1] == 0) && (C#[in1] == 0);
  assume (I#[out] == 0) && (R#[out] == 0) && (C#[out] == 0);
  M#[out][C#[out]] := k;
  C#[out] := C#[out] + 1;
  assert {:msg "Initialization might not establish the invariant (#14)"} R#[in1] == (C#[out] - 1);
  assert {:msg "Initialization might not establish the invariant (#15)"} (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C#[out]) ==> (M#[out][idx$] == M#[in1][idx$ - 1])
  );
}
procedure Delay#anon__25#5()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var in1: Chan (int);
  var out: Chan (int);
  var k: int;
  var in1#0: int;
  assume in1 != out;
  assume (0 <= I#[in1]) && (I#[in1] <= R#[in1]) && (R#[in1] <= C#[in1]);
  assume (0 <= I#[out]) && (I#[out] <= R#[out]) && (R#[out] <= C#[out]);
  assume R#[in1] == (C#[out] - 1);
  assume (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C#[out]) ==> (M#[out][idx$] == M#[in1][idx$ - 1])
  );
  assume 1 <= (C#[in1] - R#[in1]);
  in1#0 := M#[in1][R#[in1]];
  R#[in1] := R#[in1] + 1;
  assume true;
  M#[out][C#[out]] := in1#0;
  C#[out] := C#[out] + 1;
  assert {:msg "Action 'anon__25' at AddDelay.actor(11.3) might not preserve the invariant (#16)"} R#[in1] == (C#[out] - 1);
  assert {:msg "Action 'anon__25' at AddDelay.actor(11.3) might not preserve the invariant (#17)"} (forall idx$: int :: 
    (1 <= idx$) && (idx$ < C#[out]) ==> (M#[out][idx$] == M#[in1][idx$ - 1])
  );
}
procedure Netinit#6()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var anon__4: int;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (int);
  var Net#d: Chan (int);
  var Net#e: Chan (int);
  assume anon__4 == 0;
  assume Mode#[this#] == anon__4;
  assume (Net#a != Net#b) && (Net#a != Net#c) && (Net#a != Net#d) && (Net#a != Net#e) && (Net#b != Net#c) && (Net#b != Net#d) && (Net#b != Net#e) && (Net#c != Net#d) && (Net#c != Net#e) && (Net#d != Net#e);
  assume (0 <= I#[Net#a]) && (I#[Net#a] <= R#[Net#a]) && (R#[Net#a] <= C#[Net#a]);
  assume (0 <= I#[Net#b]) && (I#[Net#b] <= R#[Net#b]) && (R#[Net#b] <= C#[Net#b]);
  assume (0 <= I#[Net#c]) && (I#[Net#c] <= R#[Net#c]) && (R#[Net#c] <= C#[Net#c]);
  assume (0 <= I#[Net#d]) && (I#[Net#d] <= R#[Net#d]) && (R#[Net#d] <= C#[Net#d]);
  assume I#[Net#d] == R#[Net#d];
  assume (0 <= I#[Net#e]) && (I#[Net#e] <= R#[Net#e]) && (R#[Net#e] <= C#[Net#e]);
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
  assert {:msg "AddDelay.actor(23.15): Initialization of network 'Net' might not establish the channel invariant (#18)"} M#[Net#b][0] == 0;
  assert {:msg "AddDelay.actor(24.15): Initialization of network 'Net' might not establish the channel invariant (#19)"} 0 <= M#[Net#b][I#[Net#b]];
  assert {:msg "Initialization of network 'Net' might not establish the channel invariant (#20)"} I#[Net#c] == I#[Net#a];
  assert {:msg "Initialization of network 'Net' might not establish the channel invariant (#21)"} I#[Net#c] == I#[Net#b];
  assert {:msg "Initialization of network 'Net' might not establish the channel invariant (#22)"} I#[Net#b] == I#[Net#e];
  assert {:msg "Initialization of network 'Net' might not establish the channel invariant (#23)"} I#[Net#d] == I#[Net#c];
  assert {:msg "Initialization of network 'Net' might not establish the channel invariant (#24)"} I#[Net#e] == I#[Net#c];
  assert {:msg "Initialization of network 'Net' might not establish the channel invariant (#25)"} (Mode#[this#] == anon__4) ==> (((C#[Net#a] - I#[Net#a]) >= 1) ==> (0 <= M#[Net#a][I#[Net#a]]));
  assert {:msg "Initialization of network 'Net' might not establish the channel invariant (#26)"} (Mode#[this#] == anon__4) ==> ((C#[Net#a] - I#[Net#a]) <= 1);
  I# := R#;
  assert {:msg "AddDelay.actor(22.13): Initialization of network 'Net' might not establish the network invariant (#27)"} (C#[Net#b] - R#[Net#b]) == 1;
  assert {:msg "Initialization of network 'Net' might not establish the network invariant: Unread tokens might be left on channel a (#28)"} (C#[Net#a] - R#[Net#a]) == 0;
  assert {:msg "Initialization of network 'Net' might not establish the network invariant: Unread tokens might be left on channel c (#29)"} (C#[Net#c] - R#[Net#c]) == 0;
  assert {:msg "Initialization of network 'Net' might not establish the network invariant: Unread tokens might be left on channel d (#30)"} (C#[Net#d] - R#[Net#d]) == 0;
  assert {:msg "Initialization of network 'Net' might not establish the network invariant: Unread tokens might be left on channel e (#31)"} (C#[Net#e] - R#[Net#e]) == 0;
  assert {:msg "Initialization of network 'Net' might not establish the network invariant (#32)"} R#[Net#a] == C#[Net#d];
}
procedure Net#Add#anon__22#7()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var anon__4: int;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (int);
  var Net#d: Chan (int);
  var Net#e: Chan (int);
  var add#in1#i: int;
  var add#in2#j: int;
  assume anon__4 == 0;
  assume Mode#[this#] == anon__4;
  assume (Net#a != Net#b) && (Net#a != Net#c) && (Net#a != Net#d) && (Net#a != Net#e) && (Net#b != Net#c) && (Net#b != Net#d) && (Net#b != Net#e) && (Net#c != Net#d) && (Net#c != Net#e) && (Net#d != Net#e);
  assume (0 <= I#[Net#a]) && (I#[Net#a] <= R#[Net#a]) && (R#[Net#a] <= C#[Net#a]);
  assume (0 <= I#[Net#b]) && (I#[Net#b] <= R#[Net#b]) && (R#[Net#b] <= C#[Net#b]);
  assume (0 <= I#[Net#c]) && (I#[Net#c] <= R#[Net#c]) && (R#[Net#c] <= C#[Net#c]);
  assume (0 <= I#[Net#d]) && (I#[Net#d] <= R#[Net#d]) && (R#[Net#d] <= C#[Net#d]);
  assume I#[Net#d] == R#[Net#d];
  assume (0 <= I#[Net#e]) && (I#[Net#e] <= R#[Net#e]) && (R#[Net#e] <= C#[Net#e]);
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
  assume (Mode#[this#] == anon__4) ==> (((C#[Net#a] - I#[Net#a]) >= 1) ==> (0 <= M#[Net#a][I#[Net#a]]));
  assume (Mode#[this#] == anon__4) ==> ((C#[Net#a] - I#[Net#a]) <= 1);
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
  add#in1#i := M#[Net#a][R#[Net#a]];
  R#[Net#a] := R#[Net#a] + 1;
  add#in2#j := M#[Net#b][R#[Net#b]];
  R#[Net#b] := R#[Net#b] + 1;
  M#[Net#c][C#[Net#c]] := add#in1#i + add#in2#j;
  C#[Net#c] := C#[Net#c] + 1;
  assert {:msg "AddDelay.actor(23.15): Action at AddDelay.actor(2.3) ('anon__22') for actor instance 'add' might not preserve the channel invariant (#33)"} M#[Net#b][0] == 0;
  assert {:msg "AddDelay.actor(24.15): Action at AddDelay.actor(2.3) ('anon__22') for actor instance 'add' might not preserve the channel invariant (#34)"} 0 <= M#[Net#b][I#[Net#b]];
  assert {:msg "Action at AddDelay.actor(2.3) ('anon__22') for actor instance 'add' might not preserve the channel invariant (#35)"} I#[Net#c] == I#[Net#a];
  assert {:msg "Action at AddDelay.actor(2.3) ('anon__22') for actor instance 'add' might not preserve the channel invariant (#36)"} I#[Net#c] == I#[Net#b];
  assert {:msg "Action at AddDelay.actor(2.3) ('anon__22') for actor instance 'add' might not preserve the channel invariant (#37)"} I#[Net#b] == I#[Net#e];
  assert {:msg "Action at AddDelay.actor(2.3) ('anon__22') for actor instance 'add' might not preserve the channel invariant (#38)"} I#[Net#d] == I#[Net#c];
  assert {:msg "Action at AddDelay.actor(2.3) ('anon__22') for actor instance 'add' might not preserve the channel invariant (#39)"} I#[Net#e] == I#[Net#c];
  assert {:msg "Action at AddDelay.actor(2.3) ('anon__22') for actor instance 'add' might not preserve the channel invariant (#40)"} (Mode#[this#] == anon__4) ==> (((C#[Net#a] - I#[Net#a]) >= 1) ==> (0 <= M#[Net#a][I#[Net#a]]));
  assert {:msg "Action at AddDelay.actor(2.3) ('anon__22') for actor instance 'add' might not preserve the channel invariant (#41)"} (Mode#[this#] == anon__4) ==> ((C#[Net#a] - I#[Net#a]) <= 1);
}
procedure Net#Delay#anon__25#8()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var anon__4: int;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (int);
  var Net#d: Chan (int);
  var Net#e: Chan (int);
  var del#in1#i: int;
  assume anon__4 == 0;
  assume Mode#[this#] == anon__4;
  assume (Net#a != Net#b) && (Net#a != Net#c) && (Net#a != Net#d) && (Net#a != Net#e) && (Net#b != Net#c) && (Net#b != Net#d) && (Net#b != Net#e) && (Net#c != Net#d) && (Net#c != Net#e) && (Net#d != Net#e);
  assume (0 <= I#[Net#a]) && (I#[Net#a] <= R#[Net#a]) && (R#[Net#a] <= C#[Net#a]);
  assume (0 <= I#[Net#b]) && (I#[Net#b] <= R#[Net#b]) && (R#[Net#b] <= C#[Net#b]);
  assume (0 <= I#[Net#c]) && (I#[Net#c] <= R#[Net#c]) && (R#[Net#c] <= C#[Net#c]);
  assume (0 <= I#[Net#d]) && (I#[Net#d] <= R#[Net#d]) && (R#[Net#d] <= C#[Net#d]);
  assume I#[Net#d] == R#[Net#d];
  assume (0 <= I#[Net#e]) && (I#[Net#e] <= R#[Net#e]) && (R#[Net#e] <= C#[Net#e]);
  I#sub[Net#e] := R#[Net#e];
  I#sub[Net#b] := C#[Net#b];
  assume M#[Net#b][0] == 0;
  assume 0 <= M#[Net#b][I#[Net#b]];
  assume I#[Net#c] == I#[Net#a];
  assume I#[Net#c] == I#[Net#b];
  assume I#[Net#b] == I#[Net#e];
  assume I#[Net#d] == I#[Net#c];
  assume I#[Net#e] == I#[Net#c];
  assume (Mode#[this#] == anon__4) ==> (((C#[Net#e] - I#[Net#e]) >= 1) ==> (0 <= M#[Net#e][I#[Net#e]]));
  assume (Mode#[this#] == anon__4) ==> ((C#[Net#e] - I#[Net#e]) <= 1);
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
  del#in1#i := M#[Net#e][R#[Net#e]];
  R#[Net#e] := R#[Net#e] + 1;
  M#[Net#b][C#[Net#b]] := del#in1#i;
  C#[Net#b] := C#[Net#b] + 1;
  assert {:msg "AddDelay.actor(23.15): Action at AddDelay.actor(11.3) ('anon__25') for actor instance 'del' might not preserve the channel invariant (#42)"} M#[Net#b][0] == 0;
  assert {:msg "AddDelay.actor(24.15): Action at AddDelay.actor(11.3) ('anon__25') for actor instance 'del' might not preserve the channel invariant (#43)"} 0 <= M#[Net#b][I#[Net#b]];
  assert {:msg "Action at AddDelay.actor(11.3) ('anon__25') for actor instance 'del' might not preserve the channel invariant (#44)"} I#[Net#c] == I#[Net#a];
  assert {:msg "Action at AddDelay.actor(11.3) ('anon__25') for actor instance 'del' might not preserve the channel invariant (#45)"} I#[Net#c] == I#[Net#b];
  assert {:msg "Action at AddDelay.actor(11.3) ('anon__25') for actor instance 'del' might not preserve the channel invariant (#46)"} I#[Net#b] == I#[Net#e];
  assert {:msg "Action at AddDelay.actor(11.3) ('anon__25') for actor instance 'del' might not preserve the channel invariant (#47)"} I#[Net#d] == I#[Net#c];
  assert {:msg "Action at AddDelay.actor(11.3) ('anon__25') for actor instance 'del' might not preserve the channel invariant (#48)"} I#[Net#e] == I#[Net#c];
  assert {:msg "Action at AddDelay.actor(11.3) ('anon__25') for actor instance 'del' might not preserve the channel invariant (#49)"} (Mode#[this#] == anon__4) ==> (((C#[Net#e] - I#[Net#e]) >= 1) ==> (0 <= M#[Net#e][I#[Net#e]]));
  assert {:msg "Action at AddDelay.actor(11.3) ('anon__25') for actor instance 'del' might not preserve the channel invariant (#50)"} (Mode#[this#] == anon__4) ==> ((C#[Net#e] - I#[Net#e]) <= 1);
}
procedure Net#Split#anon__23#9()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var anon__4: int;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (int);
  var Net#d: Chan (int);
  var Net#e: Chan (int);
  var spl#in1#i: int;
  assume anon__4 == 0;
  assume Mode#[this#] == anon__4;
  assume (Net#a != Net#b) && (Net#a != Net#c) && (Net#a != Net#d) && (Net#a != Net#e) && (Net#b != Net#c) && (Net#b != Net#d) && (Net#b != Net#e) && (Net#c != Net#d) && (Net#c != Net#e) && (Net#d != Net#e);
  assume (0 <= I#[Net#a]) && (I#[Net#a] <= R#[Net#a]) && (R#[Net#a] <= C#[Net#a]);
  assume (0 <= I#[Net#b]) && (I#[Net#b] <= R#[Net#b]) && (R#[Net#b] <= C#[Net#b]);
  assume (0 <= I#[Net#c]) && (I#[Net#c] <= R#[Net#c]) && (R#[Net#c] <= C#[Net#c]);
  assume (0 <= I#[Net#d]) && (I#[Net#d] <= R#[Net#d]) && (R#[Net#d] <= C#[Net#d]);
  assume I#[Net#d] == R#[Net#d];
  assume (0 <= I#[Net#e]) && (I#[Net#e] <= R#[Net#e]) && (R#[Net#e] <= C#[Net#e]);
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
  assume (Mode#[this#] == anon__4) ==> (((C#[Net#c] - I#[Net#c]) >= 1) ==> (0 <= M#[Net#c][I#[Net#c]]));
  assume (Mode#[this#] == anon__4) ==> ((C#[Net#c] - I#[Net#c]) <= 1);
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
  spl#in1#i := M#[Net#c][R#[Net#c]];
  R#[Net#c] := R#[Net#c] + 1;
  M#[Net#d][C#[Net#d]] := spl#in1#i;
  C#[Net#d] := C#[Net#d] + 1;
  M#[Net#e][C#[Net#e]] := spl#in1#i;
  C#[Net#e] := C#[Net#e] + 1;
  assert {:msg "AddDelay.actor(23.15): Action at AddDelay.actor(6.3) ('anon__23') for actor instance 'spl' might not preserve the channel invariant (#51)"} M#[Net#b][0] == 0;
  assert {:msg "AddDelay.actor(24.15): Action at AddDelay.actor(6.3) ('anon__23') for actor instance 'spl' might not preserve the channel invariant (#52)"} 0 <= M#[Net#b][I#[Net#b]];
  assert {:msg "Action at AddDelay.actor(6.3) ('anon__23') for actor instance 'spl' might not preserve the channel invariant (#53)"} I#[Net#c] == I#[Net#a];
  assert {:msg "Action at AddDelay.actor(6.3) ('anon__23') for actor instance 'spl' might not preserve the channel invariant (#54)"} I#[Net#c] == I#[Net#b];
  assert {:msg "Action at AddDelay.actor(6.3) ('anon__23') for actor instance 'spl' might not preserve the channel invariant (#55)"} I#[Net#b] == I#[Net#e];
  assert {:msg "Action at AddDelay.actor(6.3) ('anon__23') for actor instance 'spl' might not preserve the channel invariant (#56)"} I#[Net#d] == I#[Net#c];
  assert {:msg "Action at AddDelay.actor(6.3) ('anon__23') for actor instance 'spl' might not preserve the channel invariant (#57)"} I#[Net#e] == I#[Net#c];
  assert {:msg "Action at AddDelay.actor(6.3) ('anon__23') for actor instance 'spl' might not preserve the channel invariant (#58)"} (Mode#[this#] == anon__4) ==> (((C#[Net#c] - I#[Net#c]) >= 1) ==> (0 <= M#[Net#c][I#[Net#c]]));
  assert {:msg "Action at AddDelay.actor(6.3) ('anon__23') for actor instance 'spl' might not preserve the channel invariant (#59)"} (Mode#[this#] == anon__4) ==> ((C#[Net#c] - I#[Net#c]) <= 1);
}
procedure Netanon__4#input#in1#10()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var anon__4: int;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (int);
  var Net#d: Chan (int);
  var Net#e: Chan (int);
  assume anon__4 == 0;
  assume Mode#[this#] == anon__4;
  assume (Net#a != Net#b) && (Net#a != Net#c) && (Net#a != Net#d) && (Net#a != Net#e) && (Net#b != Net#c) && (Net#b != Net#d) && (Net#b != Net#e) && (Net#c != Net#d) && (Net#c != Net#e) && (Net#d != Net#e);
  assume (0 <= I#[Net#a]) && (I#[Net#a] <= R#[Net#a]) && (R#[Net#a] <= C#[Net#a]);
  assume (0 <= I#[Net#b]) && (I#[Net#b] <= R#[Net#b]) && (R#[Net#b] <= C#[Net#b]);
  assume (0 <= I#[Net#c]) && (I#[Net#c] <= R#[Net#c]) && (R#[Net#c] <= C#[Net#c]);
  assume (0 <= I#[Net#d]) && (I#[Net#d] <= R#[Net#d]) && (R#[Net#d] <= C#[Net#d]);
  assume I#[Net#d] == R#[Net#d];
  assume (0 <= I#[Net#e]) && (I#[Net#e] <= R#[Net#e]) && (R#[Net#e] <= C#[Net#e]);
  assume Mode#[this#] == anon__4;
  assume (C#[Net#a] - I#[Net#a]) < 1;
  assume M#[Net#b][0] == 0;
  assume 0 <= M#[Net#b][I#[Net#b]];
  assume I#[Net#c] == I#[Net#a];
  assume I#[Net#c] == I#[Net#b];
  assume I#[Net#b] == I#[Net#e];
  assume I#[Net#d] == I#[Net#c];
  assume I#[Net#e] == I#[Net#c];
  assume (Mode#[this#] == anon__4) ==> (((C#[Net#a] - I#[Net#a]) >= 1) ==> (0 <= M#[Net#a][I#[Net#a]]));
  assume (Mode#[this#] == anon__4) ==> ((C#[Net#a] - I#[Net#a]) <= 1);
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
  assert {:msg "AddDelay.actor(23.15): Channel invariant might be falsified by network input on port 'in1' for contract 'anon__4' (#60)"} M#[Net#b][0] == 0;
  assert {:msg "AddDelay.actor(24.15): Channel invariant might be falsified by network input on port 'in1' for contract 'anon__4' (#61)"} 0 <= M#[Net#b][I#[Net#b]];
  assert {:msg "Channel invariant might be falsified by network input on port 'in1' for contract 'anon__4' (#62)"} I#[Net#c] == I#[Net#a];
  assert {:msg "Channel invariant might be falsified by network input on port 'in1' for contract 'anon__4' (#63)"} I#[Net#c] == I#[Net#b];
  assert {:msg "Channel invariant might be falsified by network input on port 'in1' for contract 'anon__4' (#64)"} I#[Net#b] == I#[Net#e];
  assert {:msg "Channel invariant might be falsified by network input on port 'in1' for contract 'anon__4' (#65)"} I#[Net#d] == I#[Net#c];
  assert {:msg "Channel invariant might be falsified by network input on port 'in1' for contract 'anon__4' (#66)"} I#[Net#e] == I#[Net#c];
  assert {:msg "Channel invariant might be falsified by network input on port 'in1' for contract 'anon__4' (#67)"} (Mode#[this#] == anon__4) ==> (((C#[Net#a] - I#[Net#a]) >= 1) ==> (0 <= M#[Net#a][I#[Net#a]]));
  assert {:msg "Channel invariant might be falsified by network input on port 'in1' for contract 'anon__4' (#68)"} (Mode#[this#] == anon__4) ==> ((C#[Net#a] - I#[Net#a]) <= 1);
}
procedure Netanon__4#exit#11()
  modifies C#, R#, M#, I#, H#, I#sub;
{
  var anon__4: int;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (int);
  var Net#d: Chan (int);
  var Net#e: Chan (int);
  assume anon__4 == 0;
  assume Mode#[this#] == anon__4;
  assume (Net#a != Net#b) && (Net#a != Net#c) && (Net#a != Net#d) && (Net#a != Net#e) && (Net#b != Net#c) && (Net#b != Net#d) && (Net#b != Net#e) && (Net#c != Net#d) && (Net#c != Net#e) && (Net#d != Net#e);
  assume (0 <= I#[Net#a]) && (I#[Net#a] <= R#[Net#a]) && (R#[Net#a] <= C#[Net#a]);
  assume (0 <= I#[Net#b]) && (I#[Net#b] <= R#[Net#b]) && (R#[Net#b] <= C#[Net#b]);
  assume (0 <= I#[Net#c]) && (I#[Net#c] <= R#[Net#c]) && (R#[Net#c] <= C#[Net#c]);
  assume (0 <= I#[Net#d]) && (I#[Net#d] <= R#[Net#d]) && (R#[Net#d] <= C#[Net#d]);
  assume I#[Net#d] == R#[Net#d];
  assume (0 <= I#[Net#e]) && (I#[Net#e] <= R#[Net#e]) && (R#[Net#e] <= C#[Net#e]);
  assume Mode#[this#] == anon__4;
  assume M#[Net#b][0] == 0;
  assume 0 <= M#[Net#b][I#[Net#b]];
  assume I#[Net#c] == I#[Net#a];
  assume I#[Net#c] == I#[Net#b];
  assume I#[Net#b] == I#[Net#e];
  assume I#[Net#d] == I#[Net#c];
  assume I#[Net#e] == I#[Net#c];
  assume (Mode#[this#] == anon__4) ==> (((C#[Net#a] - I#[Net#a]) >= 1) ==> (0 <= M#[Net#a][I#[Net#a]]));
  assume (Mode#[this#] == anon__4) ==> ((C#[Net#a] - I#[Net#a]) <= 1);
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
  assert {:msg "AddDelay.actor(16.3): The correct number of tokens might not be produced on output 'out' for contract 'anon__4' (#69)"} (C#[Net#d] - I#[Net#d]) == 1;
  assert {:msg "Network action postcondition might not hold (#70)"} M#[Net#d][I#[Net#d]] >= M#[Net#a][I#[Net#a]];
  assert {:msg "Network action postcondition might not hold (#71)"} (0 < I#[Net#d]) ==> (M#[Net#d][I#[Net#d]] == (M#[Net#d][I#[Net#d] - 1] + M#[Net#a][I#[Net#a]]));
  R#[Net#d] := R#[Net#d] + 1;
  I# := R#;
  assert {:msg "AddDelay.actor(23.15): The network might not preserve the channel invariant for contract 'anon__4' (#72)"} M#[Net#b][0] == 0;
  assert {:msg "AddDelay.actor(24.15): The network might not preserve the channel invariant for contract 'anon__4' (#73)"} 0 <= M#[Net#b][I#[Net#b]];
  assert {:msg "The network might not preserve the channel invariant for contract 'anon__4' (#74)"} I#[Net#c] == I#[Net#a];
  assert {:msg "The network might not preserve the channel invariant for contract 'anon__4' (#75)"} I#[Net#c] == I#[Net#b];
  assert {:msg "The network might not preserve the channel invariant for contract 'anon__4' (#76)"} I#[Net#b] == I#[Net#e];
  assert {:msg "The network might not preserve the channel invariant for contract 'anon__4' (#77)"} I#[Net#d] == I#[Net#c];
  assert {:msg "The network might not preserve the channel invariant for contract 'anon__4' (#78)"} I#[Net#e] == I#[Net#c];
  assert {:msg "The network might not preserve the channel invariant for contract 'anon__4' (#79)"} (Mode#[this#] == anon__4) ==> (((C#[Net#a] - I#[Net#a]) >= 1) ==> (0 <= M#[Net#a][I#[Net#a]]));
  assert {:msg "The network might not preserve the channel invariant for contract 'anon__4' (#80)"} (Mode#[this#] == anon__4) ==> ((C#[Net#a] - I#[Net#a]) <= 1);
  assert {:msg "AddDelay.actor(22.13): The network might not preserve the network invariant for contract 'anon__4' (#81)"} (C#[Net#b] - R#[Net#b]) == 1;
  assert {:msg "The network might not preserve the network invariant for contract 'anon__4': Unread tokens might be left on channel a (#82)"} (C#[Net#a] - R#[Net#a]) == 0;
  assert {:msg "The network might not preserve the network invariant for contract 'anon__4': Unread tokens might be left on channel c (#83)"} (C#[Net#c] - R#[Net#c]) == 0;
  assert {:msg "The network might not preserve the network invariant for contract 'anon__4': Unread tokens might be left on channel d (#84)"} (C#[Net#d] - R#[Net#d]) == 0;
  assert {:msg "The network might not preserve the network invariant for contract 'anon__4': Unread tokens might be left on channel e (#85)"} (C#[Net#e] - R#[Net#e]) == 0;
  assert {:msg "The network might not preserve the network invariant for contract 'anon__4' (#86)"} R#[Net#a] == C#[Net#d];
}

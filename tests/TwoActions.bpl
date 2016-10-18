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

function AT#Abs(x: int): int { if 0 <= x then x else -x }
function AT#Div(int, int): int;
function AT#Mod(int, int): int;
axiom (forall a,b: int :: AT#Div(a,b)*b + AT#Mod(a,b) == a);
axiom (forall a,b: int :: 0 <= AT#Mod(a,b) && AT#Mod(a,b) < AT#Abs(b));

// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

procedure AddSub#init#0()
  modifies C, R, M, I, St;
{
  var ctrl: Chan (bool);
  var in1: Chan (int);
  var in2: Chan (int);
  var out: Chan (int);
  var ctrlout: Chan (bool);
  assume (ctrl != ctrlout) && (in1 != in2) && (in1 != out) && (in2 != out);
  assume R[ctrl] == 0;
  assume R[in1] == 0;
  assume R[in2] == 0;
  assume C[out] == 0;
  assume C[ctrlout] == 0;
  assert {:msg "Initialization might not establish the invariant (#0)"} (2 * R[ctrl]) == C[out];
  assert {:msg "Initialization might not establish the invariant (#1)"} (2 * R[in1]) == C[out];
  assert {:msg "Initialization might not establish the invariant (#2)"} (2 * R[in2]) == C[out];
  assert {:msg "Initialization might not establish the invariant (#3)"} R[ctrl] == C[ctrlout];
  assert {:msg "Initialization might not establish the invariant (#4)"} R[in1] == C[ctrlout];
  assert {:msg "Initialization might not establish the invariant (#5)"} R[in2] == C[ctrlout];
  assert {:msg "Initialization might not establish the invariant (#6)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) && (AT#Mod(idx$, 2) == 0) ==> (M[ctrl][AT#Div(idx$, 2)] ==> (M[out][idx$] == (M[in1][AT#Div(idx$, 2)] + M[in2][AT#Div(idx$, 2)]))) && ((!M[ctrl][AT#Div(idx$, 2)]) ==> (M[out][idx$] == (M[in1][AT#Div(idx$, 2)] - M[in2][AT#Div(idx$, 2)])))
  );
  assert {:msg "Initialization might not establish the invariant (#7)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) && (AT#Mod(idx$, 2) == 1) ==> (M[ctrl][AT#Div(idx$, 2)] ==> (M[out][idx$] == (M[in1][AT#Div(idx$, 2)] * M[in2][AT#Div(idx$, 2)]))) && ((!M[ctrl][AT#Div(idx$, 2)]) ==> (M[out][idx$] == AT#Div(M[in1][AT#Div(idx$, 2)], M[in2][AT#Div(idx$, 2)])))
  );
  assert {:msg "Initialization might not establish the invariant (#8)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[ctrlout]) ==> (M[ctrl][idx$] ==> (M[ctrlout][idx$] == M[ctrl][idx$])) && ((!M[ctrl][idx$]) ==> (M[ctrlout][idx$] == M[ctrl][idx$]))
  );
}
procedure AddSub#anon$0#1()
  modifies C, R, M, I, St;
{
  var ctrl: Chan (bool);
  var in1: Chan (int);
  var in2: Chan (int);
  var out: Chan (int);
  var ctrlout: Chan (bool);
  var ctrl#0: bool;
  var in1#0: int;
  var in2#0: int;
  assume (ctrl != ctrlout) && (in1 != in2) && (in1 != out) && (in2 != out);
  assume 0 <= R[ctrl];
  assume 0 <= R[in1];
  assume 0 <= R[in2];
  assume 0 <= C[out];
  assume 0 <= C[ctrlout];
  assume (2 * R[ctrl]) == C[out];
  assume (2 * R[in1]) == C[out];
  assume (2 * R[in2]) == C[out];
  assume R[ctrl] == C[ctrlout];
  assume R[in1] == C[ctrlout];
  assume R[in2] == C[ctrlout];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) && (AT#Mod(idx$, 2) == 0) ==> (M[ctrl][AT#Div(idx$, 2)] ==> (M[out][idx$] == (M[in1][AT#Div(idx$, 2)] + M[in2][AT#Div(idx$, 2)]))) && ((!M[ctrl][AT#Div(idx$, 2)]) ==> (M[out][idx$] == (M[in1][AT#Div(idx$, 2)] - M[in2][AT#Div(idx$, 2)])))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) && (AT#Mod(idx$, 2) == 1) ==> (M[ctrl][AT#Div(idx$, 2)] ==> (M[out][idx$] == (M[in1][AT#Div(idx$, 2)] * M[in2][AT#Div(idx$, 2)]))) && ((!M[ctrl][AT#Div(idx$, 2)]) ==> (M[out][idx$] == AT#Div(M[in1][AT#Div(idx$, 2)], M[in2][AT#Div(idx$, 2)])))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[ctrlout]) ==> (M[ctrl][idx$] ==> (M[ctrlout][idx$] == M[ctrl][idx$])) && ((!M[ctrl][idx$]) ==> (M[ctrlout][idx$] == M[ctrl][idx$]))
  );
  ctrl#0 := M[ctrl][R[ctrl]];
  R[ctrl] := R[ctrl] + 1;
  in1#0 := M[in1][R[in1]];
  R[in1] := R[in1] + 1;
  in2#0 := M[in2][R[in2]];
  R[in2] := R[in2] + 1;
  assume ctrl#0;
  assume true;
  M[out][C[out]] := in1#0 + in2#0;
  C[out] := C[out] + 1;
  M[out][C[out]] := in1#0 * in2#0;
  C[out] := C[out] + 1;
  M[ctrlout][C[ctrlout]] := ctrl#0;
  C[ctrlout] := C[ctrlout] + 1;
  assert {:msg "Action at 2.3 might not preserve invariant (#9)"} (2 * R[ctrl]) == C[out];
  assert {:msg "Action at 2.3 might not preserve invariant (#10)"} (2 * R[in1]) == C[out];
  assert {:msg "Action at 2.3 might not preserve invariant (#11)"} (2 * R[in2]) == C[out];
  assert {:msg "Action at 2.3 might not preserve invariant (#12)"} R[ctrl] == C[ctrlout];
  assert {:msg "Action at 2.3 might not preserve invariant (#13)"} R[in1] == C[ctrlout];
  assert {:msg "Action at 2.3 might not preserve invariant (#14)"} R[in2] == C[ctrlout];
  assert {:msg "Action at 2.3 might not preserve invariant (#15)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) && (AT#Mod(idx$, 2) == 0) ==> (M[ctrl][AT#Div(idx$, 2)] ==> (M[out][idx$] == (M[in1][AT#Div(idx$, 2)] + M[in2][AT#Div(idx$, 2)]))) && ((!M[ctrl][AT#Div(idx$, 2)]) ==> (M[out][idx$] == (M[in1][AT#Div(idx$, 2)] - M[in2][AT#Div(idx$, 2)])))
  );
  assert {:msg "Action at 2.3 might not preserve invariant (#16)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) && (AT#Mod(idx$, 2) == 1) ==> (M[ctrl][AT#Div(idx$, 2)] ==> (M[out][idx$] == (M[in1][AT#Div(idx$, 2)] * M[in2][AT#Div(idx$, 2)]))) && ((!M[ctrl][AT#Div(idx$, 2)]) ==> (M[out][idx$] == AT#Div(M[in1][AT#Div(idx$, 2)], M[in2][AT#Div(idx$, 2)])))
  );
  assert {:msg "Action at 2.3 might not preserve invariant (#17)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[ctrlout]) ==> (M[ctrl][idx$] ==> (M[ctrlout][idx$] == M[ctrl][idx$])) && ((!M[ctrl][idx$]) ==> (M[ctrlout][idx$] == M[ctrl][idx$]))
  );
}
procedure AddSub#anon$1#2()
  modifies C, R, M, I, St;
{
  var ctrl: Chan (bool);
  var in1: Chan (int);
  var in2: Chan (int);
  var out: Chan (int);
  var ctrlout: Chan (bool);
  var ctrl#0: bool;
  var in1#0: int;
  var in2#0: int;
  assume (ctrl != ctrlout) && (in1 != in2) && (in1 != out) && (in2 != out);
  assume 0 <= R[ctrl];
  assume 0 <= R[in1];
  assume 0 <= R[in2];
  assume 0 <= C[out];
  assume 0 <= C[ctrlout];
  assume (2 * R[ctrl]) == C[out];
  assume (2 * R[in1]) == C[out];
  assume (2 * R[in2]) == C[out];
  assume R[ctrl] == C[ctrlout];
  assume R[in1] == C[ctrlout];
  assume R[in2] == C[ctrlout];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) && (AT#Mod(idx$, 2) == 0) ==> (M[ctrl][AT#Div(idx$, 2)] ==> (M[out][idx$] == (M[in1][AT#Div(idx$, 2)] + M[in2][AT#Div(idx$, 2)]))) && ((!M[ctrl][AT#Div(idx$, 2)]) ==> (M[out][idx$] == (M[in1][AT#Div(idx$, 2)] - M[in2][AT#Div(idx$, 2)])))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) && (AT#Mod(idx$, 2) == 1) ==> (M[ctrl][AT#Div(idx$, 2)] ==> (M[out][idx$] == (M[in1][AT#Div(idx$, 2)] * M[in2][AT#Div(idx$, 2)]))) && ((!M[ctrl][AT#Div(idx$, 2)]) ==> (M[out][idx$] == AT#Div(M[in1][AT#Div(idx$, 2)], M[in2][AT#Div(idx$, 2)])))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[ctrlout]) ==> (M[ctrl][idx$] ==> (M[ctrlout][idx$] == M[ctrl][idx$])) && ((!M[ctrl][idx$]) ==> (M[ctrlout][idx$] == M[ctrl][idx$]))
  );
  ctrl#0 := M[ctrl][R[ctrl]];
  R[ctrl] := R[ctrl] + 1;
  in1#0 := M[in1][R[in1]];
  R[in1] := R[in1] + 1;
  in2#0 := M[in2][R[in2]];
  R[in2] := R[in2] + 1;
  assume !ctrl#0;
  assume true;
  M[out][C[out]] := in1#0 - in2#0;
  C[out] := C[out] + 1;
  M[out][C[out]] := AT#Div(in1#0, in2#0);
  C[out] := C[out] + 1;
  M[ctrlout][C[ctrlout]] := ctrl#0;
  C[ctrlout] := C[ctrlout] + 1;
  assert {:msg "Action at 5.3 might not preserve invariant (#18)"} (2 * R[ctrl]) == C[out];
  assert {:msg "Action at 5.3 might not preserve invariant (#19)"} (2 * R[in1]) == C[out];
  assert {:msg "Action at 5.3 might not preserve invariant (#20)"} (2 * R[in2]) == C[out];
  assert {:msg "Action at 5.3 might not preserve invariant (#21)"} R[ctrl] == C[ctrlout];
  assert {:msg "Action at 5.3 might not preserve invariant (#22)"} R[in1] == C[ctrlout];
  assert {:msg "Action at 5.3 might not preserve invariant (#23)"} R[in2] == C[ctrlout];
  assert {:msg "Action at 5.3 might not preserve invariant (#24)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) && (AT#Mod(idx$, 2) == 0) ==> (M[ctrl][AT#Div(idx$, 2)] ==> (M[out][idx$] == (M[in1][AT#Div(idx$, 2)] + M[in2][AT#Div(idx$, 2)]))) && ((!M[ctrl][AT#Div(idx$, 2)]) ==> (M[out][idx$] == (M[in1][AT#Div(idx$, 2)] - M[in2][AT#Div(idx$, 2)])))
  );
  assert {:msg "Action at 5.3 might not preserve invariant (#25)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) && (AT#Mod(idx$, 2) == 1) ==> (M[ctrl][AT#Div(idx$, 2)] ==> (M[out][idx$] == (M[in1][AT#Div(idx$, 2)] * M[in2][AT#Div(idx$, 2)]))) && ((!M[ctrl][AT#Div(idx$, 2)]) ==> (M[out][idx$] == AT#Div(M[in1][AT#Div(idx$, 2)], M[in2][AT#Div(idx$, 2)])))
  );
  assert {:msg "Action at 5.3 might not preserve invariant (#26)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[ctrlout]) ==> (M[ctrl][idx$] ==> (M[ctrlout][idx$] == M[ctrl][idx$])) && ((!M[ctrl][idx$]) ==> (M[ctrlout][idx$] == M[ctrl][idx$]))
  );
}
procedure AddSub##GuardWD#3()
  modifies C, R, M, I, St;
{
  var ctrl: Chan (bool);
  var in1: Chan (int);
  var in2: Chan (int);
  var out: Chan (int);
  var ctrlout: Chan (bool);
  var ctrl#0: bool;
  var in1#0: int;
  var in2#0: int;
  assume (ctrl != ctrlout) && (in1 != in2) && (in1 != out) && (in2 != out);
  assert {:msg "1.1: The actions of actor 'AddSub' might not have mutually exclusive guards (#27)"} !((1 <= (C[ctrl] - R[ctrl])) && (1 <= (C[in1] - R[in1])) && (1 <= (C[in2] - R[in2])) && ctrl#0 && (1 <= (C[ctrl] - R[ctrl])) && (1 <= (C[in1] - R[in1])) && (1 <= (C[in2] - R[in2])) && (!ctrl#0));
}
procedure Net#init#4()
  modifies C, R, M, I, St;
{
  var Net#as: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (bool);
  var Net#d: Chan (int);
  var Net#e: Chan (bool);
  assume (Net#a != Net#b) && (Net#a != Net#d) && (Net#b != Net#d) && (Net#c != Net#e);
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
  assume I[Net#e] == R[Net#e];
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
  assume (2 * R[Net#c]) == C[Net#d];
  assume (2 * R[Net#a]) == C[Net#d];
  assume (2 * R[Net#b]) == C[Net#d];
  assume R[Net#c] == C[Net#e];
  assume R[Net#a] == C[Net#e];
  assume R[Net#b] == C[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) && (AT#Mod(idx$, 2) == 0) ==> (M[Net#c][AT#Div(idx$, 2)] ==> (M[Net#d][idx$] == (M[Net#a][AT#Div(idx$, 2)] + M[Net#b][AT#Div(idx$, 2)]))) && ((!M[Net#c][AT#Div(idx$, 2)]) ==> (M[Net#d][idx$] == (M[Net#a][AT#Div(idx$, 2)] - M[Net#b][AT#Div(idx$, 2)])))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) && (AT#Mod(idx$, 2) == 1) ==> (M[Net#c][AT#Div(idx$, 2)] ==> (M[Net#d][idx$] == (M[Net#a][AT#Div(idx$, 2)] * M[Net#b][AT#Div(idx$, 2)]))) && ((!M[Net#c][AT#Div(idx$, 2)]) ==> (M[Net#d][idx$] == AT#Div(M[Net#a][AT#Div(idx$, 2)], M[Net#b][AT#Div(idx$, 2)])))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#c][idx$] ==> (M[Net#e][idx$] == M[Net#c][idx$])) && ((!M[Net#c][idx$]) ==> (M[Net#e][idx$] == M[Net#c][idx$]))
  );
  assert {:msg "Initialization of network 'Net' might not establish the channel invariant (#28)"} I[Net#d] == (2 * I[Net#c]);
  assert {:msg "Initialization of network 'Net' might not establish the channel invariant (#29)"} I[Net#d] == (2 * I[Net#a]);
  assert {:msg "Initialization of network 'Net' might not establish the channel invariant (#30)"} I[Net#d] == (2 * I[Net#b]);
  assert {:msg "Initialization of network 'Net' might not establish the channel invariant (#31)"} I[Net#e] == I[Net#c];
  assert {:msg "Initialization of network 'Net' might not establish the channel invariant (#32)"} I[Net#e] == I[Net#a];
  assert {:msg "Initialization of network 'Net' might not establish the channel invariant (#33)"} I[Net#e] == I[Net#b];
  I := R;
  assert {:msg "25.5: The initialization might produce unspecified tokens on channel a (#34)"} (C[Net#a] - R[Net#a]) == 0;
  assert {:msg "26.5: The initialization might produce unspecified tokens on channel b (#35)"} (C[Net#b] - R[Net#b]) == 0;
  assert {:msg "27.5: The initialization might produce unspecified tokens on channel c (#36)"} (C[Net#c] - R[Net#c]) == 0;
  assert {:msg "28.5: The initialization might produce unspecified tokens on channel d (#37)"} (C[Net#d] - R[Net#d]) == 0;
  assert {:msg "29.5: The initialization might produce unspecified tokens on channel e (#38)"} (C[Net#e] - R[Net#e]) == 0;
}
procedure Net##AddSub#anon$0#5()
  modifies C, R, M, I, St;
{
  var Net#as: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (bool);
  var Net#d: Chan (int);
  var Net#e: Chan (bool);
  var ctrl#c: bool;
  var in1#i: int;
  var in2#j: int;
  assume (Net#a != Net#b) && (Net#a != Net#d) && (Net#b != Net#d) && (Net#c != Net#e);
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
  assume I[Net#e] == R[Net#e];
  assume I[Net#d] == (2 * I[Net#c]);
  assume I[Net#d] == (2 * I[Net#a]);
  assume I[Net#d] == (2 * I[Net#b]);
  assume I[Net#e] == I[Net#c];
  assume I[Net#e] == I[Net#a];
  assume I[Net#e] == I[Net#b];
  assume (2 * R[Net#c]) == C[Net#d];
  assume (2 * R[Net#a]) == C[Net#d];
  assume (2 * R[Net#b]) == C[Net#d];
  assume R[Net#c] == C[Net#e];
  assume R[Net#a] == C[Net#e];
  assume R[Net#b] == C[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) && (AT#Mod(idx$, 2) == 0) ==> (M[Net#c][AT#Div(idx$, 2)] ==> (M[Net#d][idx$] == (M[Net#a][AT#Div(idx$, 2)] + M[Net#b][AT#Div(idx$, 2)]))) && ((!M[Net#c][AT#Div(idx$, 2)]) ==> (M[Net#d][idx$] == (M[Net#a][AT#Div(idx$, 2)] - M[Net#b][AT#Div(idx$, 2)])))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) && (AT#Mod(idx$, 2) == 1) ==> (M[Net#c][AT#Div(idx$, 2)] ==> (M[Net#d][idx$] == (M[Net#a][AT#Div(idx$, 2)] * M[Net#b][AT#Div(idx$, 2)]))) && ((!M[Net#c][AT#Div(idx$, 2)]) ==> (M[Net#d][idx$] == AT#Div(M[Net#a][AT#Div(idx$, 2)], M[Net#b][AT#Div(idx$, 2)])))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#c][idx$] ==> (M[Net#e][idx$] == M[Net#c][idx$])) && ((!M[Net#c][idx$]) ==> (M[Net#e][idx$] == M[Net#c][idx$]))
  );
  assume (1 <= (C[Net#c] - R[Net#c])) && (1 <= (C[Net#a] - R[Net#a])) && (1 <= (C[Net#b] - R[Net#b])) && M[Net#c][R[Net#c]];
  assume (2 * R[Net#c]) == C[Net#d];
  assume (2 * R[Net#a]) == C[Net#d];
  assume (2 * R[Net#b]) == C[Net#d];
  assume R[Net#c] == C[Net#e];
  assume R[Net#a] == C[Net#e];
  assume R[Net#b] == C[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) && (AT#Mod(idx$, 2) == 0) ==> (M[Net#c][AT#Div(idx$, 2)] ==> (M[Net#d][idx$] == (M[Net#a][AT#Div(idx$, 2)] + M[Net#b][AT#Div(idx$, 2)]))) && ((!M[Net#c][AT#Div(idx$, 2)]) ==> (M[Net#d][idx$] == (M[Net#a][AT#Div(idx$, 2)] - M[Net#b][AT#Div(idx$, 2)])))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) && (AT#Mod(idx$, 2) == 1) ==> (M[Net#c][AT#Div(idx$, 2)] ==> (M[Net#d][idx$] == (M[Net#a][AT#Div(idx$, 2)] * M[Net#b][AT#Div(idx$, 2)]))) && ((!M[Net#c][AT#Div(idx$, 2)]) ==> (M[Net#d][idx$] == AT#Div(M[Net#a][AT#Div(idx$, 2)], M[Net#b][AT#Div(idx$, 2)])))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#c][idx$] ==> (M[Net#e][idx$] == M[Net#c][idx$])) && ((!M[Net#c][idx$]) ==> (M[Net#e][idx$] == M[Net#c][idx$]))
  );
  ctrl#c := M[Net#c][R[Net#c]];
  R[Net#c] := R[Net#c] + 1;
  in1#i := M[Net#a][R[Net#a]];
  R[Net#a] := R[Net#a] + 1;
  in2#j := M[Net#b][R[Net#b]];
  R[Net#b] := R[Net#b] + 1;
  M[Net#d][C[Net#d]] := in1#i + in2#j;
  C[Net#d] := C[Net#d] + 1;
  M[Net#d][C[Net#d]] := in1#i * in2#j;
  C[Net#d] := C[Net#d] + 1;
  M[Net#e][C[Net#e]] := ctrl#c;
  C[Net#e] := C[Net#e] + 1;
  assume (2 * R[Net#c]) == C[Net#d];
  assume (2 * R[Net#a]) == C[Net#d];
  assume (2 * R[Net#b]) == C[Net#d];
  assume R[Net#c] == C[Net#e];
  assume R[Net#a] == C[Net#e];
  assume R[Net#b] == C[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) && (AT#Mod(idx$, 2) == 0) ==> (M[Net#c][AT#Div(idx$, 2)] ==> (M[Net#d][idx$] == (M[Net#a][AT#Div(idx$, 2)] + M[Net#b][AT#Div(idx$, 2)]))) && ((!M[Net#c][AT#Div(idx$, 2)]) ==> (M[Net#d][idx$] == (M[Net#a][AT#Div(idx$, 2)] - M[Net#b][AT#Div(idx$, 2)])))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) && (AT#Mod(idx$, 2) == 1) ==> (M[Net#c][AT#Div(idx$, 2)] ==> (M[Net#d][idx$] == (M[Net#a][AT#Div(idx$, 2)] * M[Net#b][AT#Div(idx$, 2)]))) && ((!M[Net#c][AT#Div(idx$, 2)]) ==> (M[Net#d][idx$] == AT#Div(M[Net#a][AT#Div(idx$, 2)], M[Net#b][AT#Div(idx$, 2)])))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#c][idx$] ==> (M[Net#e][idx$] == M[Net#c][idx$])) && ((!M[Net#c][idx$]) ==> (M[Net#e][idx$] == M[Net#c][idx$]))
  );
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'as' might not preserve the channel invariant (#39)"} I[Net#d] == (2 * I[Net#c]);
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'as' might not preserve the channel invariant (#40)"} I[Net#d] == (2 * I[Net#a]);
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'as' might not preserve the channel invariant (#41)"} I[Net#d] == (2 * I[Net#b]);
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'as' might not preserve the channel invariant (#42)"} I[Net#e] == I[Net#c];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'as' might not preserve the channel invariant (#43)"} I[Net#e] == I[Net#a];
  assert {:msg "Action at 2.3 ('anon$0') for actor instance 'as' might not preserve the channel invariant (#44)"} I[Net#e] == I[Net#b];
}
procedure Net##AddSub#anon$1#6()
  modifies C, R, M, I, St;
{
  var Net#as: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (bool);
  var Net#d: Chan (int);
  var Net#e: Chan (bool);
  var ctrl#c: bool;
  var in1#i: int;
  var in2#j: int;
  assume (Net#a != Net#b) && (Net#a != Net#d) && (Net#b != Net#d) && (Net#c != Net#e);
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
  assume I[Net#e] == R[Net#e];
  assume I[Net#d] == (2 * I[Net#c]);
  assume I[Net#d] == (2 * I[Net#a]);
  assume I[Net#d] == (2 * I[Net#b]);
  assume I[Net#e] == I[Net#c];
  assume I[Net#e] == I[Net#a];
  assume I[Net#e] == I[Net#b];
  assume (2 * R[Net#c]) == C[Net#d];
  assume (2 * R[Net#a]) == C[Net#d];
  assume (2 * R[Net#b]) == C[Net#d];
  assume R[Net#c] == C[Net#e];
  assume R[Net#a] == C[Net#e];
  assume R[Net#b] == C[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) && (AT#Mod(idx$, 2) == 0) ==> (M[Net#c][AT#Div(idx$, 2)] ==> (M[Net#d][idx$] == (M[Net#a][AT#Div(idx$, 2)] + M[Net#b][AT#Div(idx$, 2)]))) && ((!M[Net#c][AT#Div(idx$, 2)]) ==> (M[Net#d][idx$] == (M[Net#a][AT#Div(idx$, 2)] - M[Net#b][AT#Div(idx$, 2)])))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) && (AT#Mod(idx$, 2) == 1) ==> (M[Net#c][AT#Div(idx$, 2)] ==> (M[Net#d][idx$] == (M[Net#a][AT#Div(idx$, 2)] * M[Net#b][AT#Div(idx$, 2)]))) && ((!M[Net#c][AT#Div(idx$, 2)]) ==> (M[Net#d][idx$] == AT#Div(M[Net#a][AT#Div(idx$, 2)], M[Net#b][AT#Div(idx$, 2)])))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#c][idx$] ==> (M[Net#e][idx$] == M[Net#c][idx$])) && ((!M[Net#c][idx$]) ==> (M[Net#e][idx$] == M[Net#c][idx$]))
  );
  assume (1 <= (C[Net#c] - R[Net#c])) && (1 <= (C[Net#a] - R[Net#a])) && (1 <= (C[Net#b] - R[Net#b])) && (!M[Net#c][R[Net#c]]);
  assume (2 * R[Net#c]) == C[Net#d];
  assume (2 * R[Net#a]) == C[Net#d];
  assume (2 * R[Net#b]) == C[Net#d];
  assume R[Net#c] == C[Net#e];
  assume R[Net#a] == C[Net#e];
  assume R[Net#b] == C[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) && (AT#Mod(idx$, 2) == 0) ==> (M[Net#c][AT#Div(idx$, 2)] ==> (M[Net#d][idx$] == (M[Net#a][AT#Div(idx$, 2)] + M[Net#b][AT#Div(idx$, 2)]))) && ((!M[Net#c][AT#Div(idx$, 2)]) ==> (M[Net#d][idx$] == (M[Net#a][AT#Div(idx$, 2)] - M[Net#b][AT#Div(idx$, 2)])))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) && (AT#Mod(idx$, 2) == 1) ==> (M[Net#c][AT#Div(idx$, 2)] ==> (M[Net#d][idx$] == (M[Net#a][AT#Div(idx$, 2)] * M[Net#b][AT#Div(idx$, 2)]))) && ((!M[Net#c][AT#Div(idx$, 2)]) ==> (M[Net#d][idx$] == AT#Div(M[Net#a][AT#Div(idx$, 2)], M[Net#b][AT#Div(idx$, 2)])))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#c][idx$] ==> (M[Net#e][idx$] == M[Net#c][idx$])) && ((!M[Net#c][idx$]) ==> (M[Net#e][idx$] == M[Net#c][idx$]))
  );
  ctrl#c := M[Net#c][R[Net#c]];
  R[Net#c] := R[Net#c] + 1;
  in1#i := M[Net#a][R[Net#a]];
  R[Net#a] := R[Net#a] + 1;
  in2#j := M[Net#b][R[Net#b]];
  R[Net#b] := R[Net#b] + 1;
  M[Net#d][C[Net#d]] := in1#i - in2#j;
  C[Net#d] := C[Net#d] + 1;
  M[Net#d][C[Net#d]] := AT#Div(in1#i, in2#j);
  C[Net#d] := C[Net#d] + 1;
  M[Net#e][C[Net#e]] := ctrl#c;
  C[Net#e] := C[Net#e] + 1;
  assume (2 * R[Net#c]) == C[Net#d];
  assume (2 * R[Net#a]) == C[Net#d];
  assume (2 * R[Net#b]) == C[Net#d];
  assume R[Net#c] == C[Net#e];
  assume R[Net#a] == C[Net#e];
  assume R[Net#b] == C[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) && (AT#Mod(idx$, 2) == 0) ==> (M[Net#c][AT#Div(idx$, 2)] ==> (M[Net#d][idx$] == (M[Net#a][AT#Div(idx$, 2)] + M[Net#b][AT#Div(idx$, 2)]))) && ((!M[Net#c][AT#Div(idx$, 2)]) ==> (M[Net#d][idx$] == (M[Net#a][AT#Div(idx$, 2)] - M[Net#b][AT#Div(idx$, 2)])))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) && (AT#Mod(idx$, 2) == 1) ==> (M[Net#c][AT#Div(idx$, 2)] ==> (M[Net#d][idx$] == (M[Net#a][AT#Div(idx$, 2)] * M[Net#b][AT#Div(idx$, 2)]))) && ((!M[Net#c][AT#Div(idx$, 2)]) ==> (M[Net#d][idx$] == AT#Div(M[Net#a][AT#Div(idx$, 2)], M[Net#b][AT#Div(idx$, 2)])))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#c][idx$] ==> (M[Net#e][idx$] == M[Net#c][idx$])) && ((!M[Net#c][idx$]) ==> (M[Net#e][idx$] == M[Net#c][idx$]))
  );
  assert {:msg "Action at 5.3 ('anon$1') for actor instance 'as' might not preserve the channel invariant (#45)"} I[Net#d] == (2 * I[Net#c]);
  assert {:msg "Action at 5.3 ('anon$1') for actor instance 'as' might not preserve the channel invariant (#46)"} I[Net#d] == (2 * I[Net#a]);
  assert {:msg "Action at 5.3 ('anon$1') for actor instance 'as' might not preserve the channel invariant (#47)"} I[Net#d] == (2 * I[Net#b]);
  assert {:msg "Action at 5.3 ('anon$1') for actor instance 'as' might not preserve the channel invariant (#48)"} I[Net#e] == I[Net#c];
  assert {:msg "Action at 5.3 ('anon$1') for actor instance 'as' might not preserve the channel invariant (#49)"} I[Net#e] == I[Net#a];
  assert {:msg "Action at 5.3 ('anon$1') for actor instance 'as' might not preserve the channel invariant (#50)"} I[Net#e] == I[Net#b];
}
procedure Net#entry()
  modifies C, R, M, I, St;
{
  var Net#as: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (bool);
  var Net#d: Chan (int);
  var Net#e: Chan (bool);
  assume (Net#a != Net#b) && (Net#a != Net#d) && (Net#b != Net#d) && (Net#c != Net#e);
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
  assume I[Net#e] == R[Net#e];
  assume C[Net#a] == R[Net#a];
  assume C[Net#b] == R[Net#b];
  assume C[Net#c] == R[Net#c];
  assume C[Net#d] == R[Net#d];
  assume C[Net#e] == R[Net#e];
  assume I[Net#d] == (2 * I[Net#c]);
  assume I[Net#d] == (2 * I[Net#a]);
  assume I[Net#d] == (2 * I[Net#b]);
  assume I[Net#e] == I[Net#c];
  assume I[Net#e] == I[Net#a];
  assume I[Net#e] == I[Net#b];
  assume (2 * R[Net#c]) == C[Net#d];
  assume (2 * R[Net#a]) == C[Net#d];
  assume (2 * R[Net#b]) == C[Net#d];
  assume R[Net#c] == C[Net#e];
  assume R[Net#a] == C[Net#e];
  assume R[Net#b] == C[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) && (AT#Mod(idx$, 2) == 0) ==> (M[Net#c][AT#Div(idx$, 2)] ==> (M[Net#d][idx$] == (M[Net#a][AT#Div(idx$, 2)] + M[Net#b][AT#Div(idx$, 2)]))) && ((!M[Net#c][AT#Div(idx$, 2)]) ==> (M[Net#d][idx$] == (M[Net#a][AT#Div(idx$, 2)] - M[Net#b][AT#Div(idx$, 2)])))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) && (AT#Mod(idx$, 2) == 1) ==> (M[Net#c][AT#Div(idx$, 2)] ==> (M[Net#d][idx$] == (M[Net#a][AT#Div(idx$, 2)] * M[Net#b][AT#Div(idx$, 2)]))) && ((!M[Net#c][AT#Div(idx$, 2)]) ==> (M[Net#d][idx$] == AT#Div(M[Net#a][AT#Div(idx$, 2)], M[Net#b][AT#Div(idx$, 2)])))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#c][idx$] ==> (M[Net#e][idx$] == M[Net#c][idx$])) && ((!M[Net#c][idx$]) ==> (M[Net#e][idx$] == M[Net#c][idx$]))
  );
  assert {:msg "10.1: Sub-actors in the network might fire without network input. This is not permitted. (#51)"} !((1 <= (C[Net#c] - R[Net#c])) && (1 <= (C[Net#a] - R[Net#a])) && (1 <= (C[Net#b] - R[Net#b])) && M[Net#c][R[Net#c]]);
  assert {:msg "10.1: Sub-actors in the network might fire without network input. This is not permitted. (#52)"} !((1 <= (C[Net#c] - R[Net#c])) && (1 <= (C[Net#a] - R[Net#a])) && (1 <= (C[Net#b] - R[Net#b])) && (!M[Net#c][R[Net#c]]));
}
procedure Net#anon$2#input#ctrl#7()
  modifies C, R, M, I, St;
{
  var Net#as: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (bool);
  var Net#d: Chan (int);
  var Net#e: Chan (bool);
  assume (Net#a != Net#b) && (Net#a != Net#d) && (Net#b != Net#d) && (Net#c != Net#e);
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
  assume I[Net#e] == R[Net#e];
  assume C[Net#c] < 1;
  assume I[Net#d] == (2 * I[Net#c]);
  assume I[Net#d] == (2 * I[Net#a]);
  assume I[Net#d] == (2 * I[Net#b]);
  assume I[Net#e] == I[Net#c];
  assume I[Net#e] == I[Net#a];
  assume I[Net#e] == I[Net#b];
  assume (2 * R[Net#c]) == C[Net#d];
  assume (2 * R[Net#a]) == C[Net#d];
  assume (2 * R[Net#b]) == C[Net#d];
  assume R[Net#c] == C[Net#e];
  assume R[Net#a] == C[Net#e];
  assume R[Net#b] == C[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) && (AT#Mod(idx$, 2) == 0) ==> (M[Net#c][AT#Div(idx$, 2)] ==> (M[Net#d][idx$] == (M[Net#a][AT#Div(idx$, 2)] + M[Net#b][AT#Div(idx$, 2)]))) && ((!M[Net#c][AT#Div(idx$, 2)]) ==> (M[Net#d][idx$] == (M[Net#a][AT#Div(idx$, 2)] - M[Net#b][AT#Div(idx$, 2)])))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) && (AT#Mod(idx$, 2) == 1) ==> (M[Net#c][AT#Div(idx$, 2)] ==> (M[Net#d][idx$] == (M[Net#a][AT#Div(idx$, 2)] * M[Net#b][AT#Div(idx$, 2)]))) && ((!M[Net#c][AT#Div(idx$, 2)]) ==> (M[Net#d][idx$] == AT#Div(M[Net#a][AT#Div(idx$, 2)], M[Net#b][AT#Div(idx$, 2)])))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#c][idx$] ==> (M[Net#e][idx$] == M[Net#c][idx$])) && ((!M[Net#c][idx$]) ==> (M[Net#e][idx$] == M[Net#c][idx$]))
  );
  C[Net#c] := C[Net#c] + 1;
  assert {:msg "Channel invariant might be falsified by network input (#53)"} I[Net#d] == (2 * I[Net#c]);
  assert {:msg "Channel invariant might be falsified by network input (#54)"} I[Net#d] == (2 * I[Net#a]);
  assert {:msg "Channel invariant might be falsified by network input (#55)"} I[Net#d] == (2 * I[Net#b]);
  assert {:msg "Channel invariant might be falsified by network input (#56)"} I[Net#e] == I[Net#c];
  assert {:msg "Channel invariant might be falsified by network input (#57)"} I[Net#e] == I[Net#a];
  assert {:msg "Channel invariant might be falsified by network input (#58)"} I[Net#e] == I[Net#b];
}
procedure Net#anon$2#input#in1#8()
  modifies C, R, M, I, St;
{
  var Net#as: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (bool);
  var Net#d: Chan (int);
  var Net#e: Chan (bool);
  assume (Net#a != Net#b) && (Net#a != Net#d) && (Net#b != Net#d) && (Net#c != Net#e);
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
  assume I[Net#e] == R[Net#e];
  assume C[Net#a] < 1;
  assume I[Net#d] == (2 * I[Net#c]);
  assume I[Net#d] == (2 * I[Net#a]);
  assume I[Net#d] == (2 * I[Net#b]);
  assume I[Net#e] == I[Net#c];
  assume I[Net#e] == I[Net#a];
  assume I[Net#e] == I[Net#b];
  assume (2 * R[Net#c]) == C[Net#d];
  assume (2 * R[Net#a]) == C[Net#d];
  assume (2 * R[Net#b]) == C[Net#d];
  assume R[Net#c] == C[Net#e];
  assume R[Net#a] == C[Net#e];
  assume R[Net#b] == C[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) && (AT#Mod(idx$, 2) == 0) ==> (M[Net#c][AT#Div(idx$, 2)] ==> (M[Net#d][idx$] == (M[Net#a][AT#Div(idx$, 2)] + M[Net#b][AT#Div(idx$, 2)]))) && ((!M[Net#c][AT#Div(idx$, 2)]) ==> (M[Net#d][idx$] == (M[Net#a][AT#Div(idx$, 2)] - M[Net#b][AT#Div(idx$, 2)])))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) && (AT#Mod(idx$, 2) == 1) ==> (M[Net#c][AT#Div(idx$, 2)] ==> (M[Net#d][idx$] == (M[Net#a][AT#Div(idx$, 2)] * M[Net#b][AT#Div(idx$, 2)]))) && ((!M[Net#c][AT#Div(idx$, 2)]) ==> (M[Net#d][idx$] == AT#Div(M[Net#a][AT#Div(idx$, 2)], M[Net#b][AT#Div(idx$, 2)])))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#c][idx$] ==> (M[Net#e][idx$] == M[Net#c][idx$])) && ((!M[Net#c][idx$]) ==> (M[Net#e][idx$] == M[Net#c][idx$]))
  );
  C[Net#a] := C[Net#a] + 1;
  assert {:msg "Channel invariant might be falsified by network input (#59)"} I[Net#d] == (2 * I[Net#c]);
  assert {:msg "Channel invariant might be falsified by network input (#60)"} I[Net#d] == (2 * I[Net#a]);
  assert {:msg "Channel invariant might be falsified by network input (#61)"} I[Net#d] == (2 * I[Net#b]);
  assert {:msg "Channel invariant might be falsified by network input (#62)"} I[Net#e] == I[Net#c];
  assert {:msg "Channel invariant might be falsified by network input (#63)"} I[Net#e] == I[Net#a];
  assert {:msg "Channel invariant might be falsified by network input (#64)"} I[Net#e] == I[Net#b];
}
procedure Net#anon$2#input#in2#9()
  modifies C, R, M, I, St;
{
  var Net#as: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (bool);
  var Net#d: Chan (int);
  var Net#e: Chan (bool);
  assume (Net#a != Net#b) && (Net#a != Net#d) && (Net#b != Net#d) && (Net#c != Net#e);
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
  assume I[Net#e] == R[Net#e];
  assume C[Net#b] < 1;
  assume I[Net#d] == (2 * I[Net#c]);
  assume I[Net#d] == (2 * I[Net#a]);
  assume I[Net#d] == (2 * I[Net#b]);
  assume I[Net#e] == I[Net#c];
  assume I[Net#e] == I[Net#a];
  assume I[Net#e] == I[Net#b];
  assume (2 * R[Net#c]) == C[Net#d];
  assume (2 * R[Net#a]) == C[Net#d];
  assume (2 * R[Net#b]) == C[Net#d];
  assume R[Net#c] == C[Net#e];
  assume R[Net#a] == C[Net#e];
  assume R[Net#b] == C[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) && (AT#Mod(idx$, 2) == 0) ==> (M[Net#c][AT#Div(idx$, 2)] ==> (M[Net#d][idx$] == (M[Net#a][AT#Div(idx$, 2)] + M[Net#b][AT#Div(idx$, 2)]))) && ((!M[Net#c][AT#Div(idx$, 2)]) ==> (M[Net#d][idx$] == (M[Net#a][AT#Div(idx$, 2)] - M[Net#b][AT#Div(idx$, 2)])))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) && (AT#Mod(idx$, 2) == 1) ==> (M[Net#c][AT#Div(idx$, 2)] ==> (M[Net#d][idx$] == (M[Net#a][AT#Div(idx$, 2)] * M[Net#b][AT#Div(idx$, 2)]))) && ((!M[Net#c][AT#Div(idx$, 2)]) ==> (M[Net#d][idx$] == AT#Div(M[Net#a][AT#Div(idx$, 2)], M[Net#b][AT#Div(idx$, 2)])))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#c][idx$] ==> (M[Net#e][idx$] == M[Net#c][idx$])) && ((!M[Net#c][idx$]) ==> (M[Net#e][idx$] == M[Net#c][idx$]))
  );
  C[Net#b] := C[Net#b] + 1;
  assert {:msg "Channel invariant might be falsified by network input (#65)"} I[Net#d] == (2 * I[Net#c]);
  assert {:msg "Channel invariant might be falsified by network input (#66)"} I[Net#d] == (2 * I[Net#a]);
  assert {:msg "Channel invariant might be falsified by network input (#67)"} I[Net#d] == (2 * I[Net#b]);
  assert {:msg "Channel invariant might be falsified by network input (#68)"} I[Net#e] == I[Net#c];
  assert {:msg "Channel invariant might be falsified by network input (#69)"} I[Net#e] == I[Net#a];
  assert {:msg "Channel invariant might be falsified by network input (#70)"} I[Net#e] == I[Net#b];
}
procedure Net#anon$2#exit#10()
  modifies C, R, M, I, St;
{
  var Net#as: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (bool);
  var Net#d: Chan (int);
  var Net#e: Chan (bool);
  assume (Net#a != Net#b) && (Net#a != Net#d) && (Net#b != Net#d) && (Net#c != Net#e);
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
  assume I[Net#e] == R[Net#e];
  assume I[Net#d] == (2 * I[Net#c]);
  assume I[Net#d] == (2 * I[Net#a]);
  assume I[Net#d] == (2 * I[Net#b]);
  assume I[Net#e] == I[Net#c];
  assume I[Net#e] == I[Net#a];
  assume I[Net#e] == I[Net#b];
  assume (2 * R[Net#c]) == C[Net#d];
  assume (2 * R[Net#a]) == C[Net#d];
  assume (2 * R[Net#b]) == C[Net#d];
  assume R[Net#c] == C[Net#e];
  assume R[Net#a] == C[Net#e];
  assume R[Net#b] == C[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) && (AT#Mod(idx$, 2) == 0) ==> (M[Net#c][AT#Div(idx$, 2)] ==> (M[Net#d][idx$] == (M[Net#a][AT#Div(idx$, 2)] + M[Net#b][AT#Div(idx$, 2)]))) && ((!M[Net#c][AT#Div(idx$, 2)]) ==> (M[Net#d][idx$] == (M[Net#a][AT#Div(idx$, 2)] - M[Net#b][AT#Div(idx$, 2)])))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) && (AT#Mod(idx$, 2) == 1) ==> (M[Net#c][AT#Div(idx$, 2)] ==> (M[Net#d][idx$] == (M[Net#a][AT#Div(idx$, 2)] * M[Net#b][AT#Div(idx$, 2)]))) && ((!M[Net#c][AT#Div(idx$, 2)]) ==> (M[Net#d][idx$] == AT#Div(M[Net#a][AT#Div(idx$, 2)], M[Net#b][AT#Div(idx$, 2)])))
  );
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#c][idx$] ==> (M[Net#e][idx$] == M[Net#c][idx$])) && ((!M[Net#c][idx$]) ==> (M[Net#e][idx$] == M[Net#c][idx$]))
  );
  assume (C[Net#a] - I[Net#a]) == 1;
  assume (C[Net#b] - I[Net#b]) == 1;
  assume (C[Net#c] - I[Net#c]) == 1;
  assume !((1 <= (C[Net#c] - R[Net#c])) && (1 <= (C[Net#a] - R[Net#a])) && (1 <= (C[Net#b] - R[Net#b])) && M[Net#c][R[Net#c]]);
  assume !((1 <= (C[Net#c] - R[Net#c])) && (1 <= (C[Net#a] - R[Net#a])) && (1 <= (C[Net#b] - R[Net#b])) && (!M[Net#c][R[Net#c]]));
  assert {:msg "13.13: Network action postcondition might not hold (#71)"} M[Net#c][I[Net#c]] ==> (M[Net#d][I[Net#d]] == (M[Net#a][I[Net#a]] + M[Net#b][I[Net#b]]));
  assert {:msg "14.13: Network action postcondition might not hold (#72)"} (!M[Net#c][I[Net#c]]) ==> (M[Net#d][I[Net#d]] == (M[Net#a][I[Net#a]] - M[Net#b][I[Net#b]]));
  assert {:msg "15.13: Network action postcondition might not hold (#73)"} M[Net#c][I[Net#c]] ==> (M[Net#d][I[Net#d] + 1] == (M[Net#a][I[Net#a]] * M[Net#b][I[Net#b]]));
  assert {:msg "16.13: Network action postcondition might not hold (#74)"} (!M[Net#c][I[Net#c]]) ==> (M[Net#d][I[Net#d] + 1] == AT#Div(M[Net#a][I[Net#a]], M[Net#b][I[Net#b]]));
  assert {:msg "17.13: Network action postcondition might not hold (#75)"} M[Net#e][I[Net#e]] == M[Net#c][I[Net#c]];
  R[Net#d] := R[Net#d] + 2;
  R[Net#e] := R[Net#e] + 1;
  I := R;
  assert {:msg "The network might not preserve the channel invariant (#76)"} I[Net#d] == (2 * I[Net#c]);
  assert {:msg "The network might not preserve the channel invariant (#77)"} I[Net#d] == (2 * I[Net#a]);
  assert {:msg "The network might not preserve the channel invariant (#78)"} I[Net#d] == (2 * I[Net#b]);
  assert {:msg "The network might not preserve the channel invariant (#79)"} I[Net#e] == I[Net#c];
  assert {:msg "The network might not preserve the channel invariant (#80)"} I[Net#e] == I[Net#a];
  assert {:msg "The network might not preserve the channel invariant (#81)"} I[Net#e] == I[Net#b];
  assert {:msg "12.3: The network might leave unread tokens on channel a (#82)"} C[Net#a] == R[Net#a];
  assert {:msg "12.3: The network might leave unread tokens on channel b (#83)"} C[Net#b] == R[Net#b];
  assert {:msg "12.3: The network might leave unread tokens on channel c (#84)"} C[Net#c] == R[Net#c];
  assert {:msg "12.3: The network might not produce the specified number of tokens on output out (#85)"} C[Net#d] == R[Net#d];
  assert {:msg "12.3: The network might not produce the specified number of tokens on output ctrlout (#86)"} C[Net#e] == R[Net#e];
}

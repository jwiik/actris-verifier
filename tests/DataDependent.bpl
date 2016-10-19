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

procedure Gain#init#0()
  modifies C, R, M, I, St;
{
  var in: Chan (int);
  var out: Chan (int);
  assume in != out;
  assume R[in] == 0;
  assume C[out] == 0;
  assert {:msg "2.13: Initialization might not establish the invariant (#0)"} R[in] == C[out];
  assert {:msg "Initialization might not establish the invariant (#1)"} R[in] == C[out];
  assert {:msg "Initialization might not establish the invariant (#2)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == (2 * M[in][idx$]))
  );
}
procedure Gain#anon$0#1()
  modifies C, R, M, I, St;
{
  var in: Chan (int);
  var out: Chan (int);
  var in#0: int;
  assume in != out;
  assume 0 <= R[in];
  assume 0 <= C[out];
  assume R[in] == C[out];
  assume R[in] == C[out];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == (2 * M[in][idx$]))
  );
  in#0 := M[in][R[in]];
  R[in] := R[in] + 1;
  assume true;
  M[out][C[out]] := 2 * in#0;
  C[out] := C[out] + 1;
  assert {:msg "2.13: Action at 3.3 might not preserve invariant (#3)"} R[in] == C[out];
  assert {:msg "Action at 3.3 might not preserve invariant (#4)"} R[in] == C[out];
  assert {:msg "Action at 3.3 might not preserve invariant (#5)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == (2 * M[in][idx$]))
  );
}
procedure Split#init#2()
  modifies C, R, M, I, St;
{
  var in: Chan (int);
  var pos: Chan (int);
  var neg: Chan (int);
  assume (in != pos) && (in != neg) && (pos != neg);
  assume R[in] == 0;
  assume C[pos] == 0;
  assume C[neg] == 0;
}
procedure Split#anon$1#3()
  modifies C, R, M, I, St;
{
  var in: Chan (int);
  var pos: Chan (int);
  var neg: Chan (int);
  var in#0: int;
  assume (in != pos) && (in != neg) && (pos != neg);
  assume 0 <= R[in];
  assume 0 <= C[pos];
  assume 0 <= C[neg];
  in#0 := M[in][R[in]];
  R[in] := R[in] + 1;
  assume 0 <= in#0;
  assume true;
  M[pos][C[pos]] := in#0;
  C[pos] := C[pos] + 1;
}
procedure Split#anon$2#4()
  modifies C, R, M, I, St;
{
  var in: Chan (int);
  var pos: Chan (int);
  var neg: Chan (int);
  var in#0: int;
  assume (in != pos) && (in != neg) && (pos != neg);
  assume 0 <= R[in];
  assume 0 <= C[pos];
  assume 0 <= C[neg];
  in#0 := M[in][R[in]];
  R[in] := R[in] + 1;
  assume in#0 < 0;
  assume true;
  M[neg][C[neg]] := in#0;
  C[neg] := C[neg] + 1;
}
procedure Split##GuardWD#5()
  modifies C, R, M, I, St;
{
  var in: Chan (int);
  var pos: Chan (int);
  var neg: Chan (int);
  var in#0: int;
  assume (in != pos) && (in != neg) && (pos != neg);
  assert {:msg "6.1: The actions of actor 'Split' might not have mutually exclusive guards (#6)"} !((1 <= (C[in] - R[in])) && (0 <= in#0) && (1 <= (C[in] - R[in])) && (in#0 < 0));
}
procedure Net#init#6()
  modifies C, R, M, I, St;
{
  var Net#gain: Actor;
  var Net#split: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (int);
  var Net#d: Chan (int);
  assume Net#gain != Net#split;
  assume (Net#a != Net#b) && (Net#a != Net#c) && (Net#a != Net#d) && (Net#b != Net#c) && (Net#b != Net#d) && (Net#c != Net#d);
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume 0 <= I[Net#c];
  assume I[Net#c] <= R[Net#c];
  assume R[Net#c] <= C[Net#c];
  assume I[Net#c] == R[Net#c];
  assume 0 <= I[Net#d];
  assume I[Net#d] <= R[Net#d];
  assume R[Net#d] <= C[Net#d];
  assume I[Net#d] == R[Net#d];
  assume C[Net#a] == 0;
  assume R[Net#a] == 0;
  assume C[Net#b] == 0;
  assume R[Net#b] == 0;
  assume C[Net#c] == 0;
  assume R[Net#c] == 0;
  assume C[Net#d] == 0;
  assume R[Net#d] == 0;
  assume R[Net#a] == C[Net#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == (2 * M[Net#a][idx$]))
  );
  assert {:msg "27.15: Initialization of network 'Net' might not establish the channel invariant (#7)"} (R[Net#b] - I[Net#b]) == ((C[Net#d] - I[Net#d]) + (C[Net#c] - I[Net#c]));
  assert {:msg "28.15: Initialization of network 'Net' might not establish the channel invariant (#8)"} ((R[Net#b] - I[Net#b]) > 0) && (M[Net#b][I[Net#b]] >= 0) ==> ((C[Net#d] - I[Net#d]) == 0) && (M[Net#c][I[Net#c]] == M[Net#b][I[Net#b]]);
  assert {:msg "29.15: Initialization of network 'Net' might not establish the channel invariant (#9)"} ((R[Net#b] - I[Net#b]) > 0) && (M[Net#b][I[Net#b]] < 0) ==> ((C[Net#c] - I[Net#c]) == 0) && (M[Net#d][I[Net#d]] == M[Net#b][I[Net#b]]);
  assert {:msg "Initialization of network 'Net' might not establish the channel invariant (#10)"} I[Net#b] == I[Net#a];
  assert {:msg "Initialization of network 'Net' might not establish the channel invariant (#11)"} (true && (forall idx$: int :: 
    (I[Net#a] <= idx$) && (idx$ < C[Net#a]) ==> (M[Net#a][idx$] == 1)
  )) || (true && (forall idx$: int :: 
    (I[Net#a] <= idx$) && (idx$ < C[Net#a]) ==> (M[Net#a][idx$] == (-1))
  ));
  I := R;
  assert {:msg "37.5: The initialization might produce unspecified tokens on channel a (#12)"} (C[Net#a] - R[Net#a]) == 0;
  assert {:msg "38.5: The initialization might produce unspecified tokens on channel b (#13)"} (C[Net#b] - R[Net#b]) == 0;
  assert {:msg "39.5: The initialization might produce unspecified tokens on channel c (#14)"} (C[Net#c] - R[Net#c]) == 0;
  assert {:msg "40.5: The initialization might produce unspecified tokens on channel d (#15)"} (C[Net#d] - R[Net#d]) == 0;
}
procedure Net##Gain#anon$0#7()
  modifies C, R, M, I, St;
{
  var Net#gain: Actor;
  var Net#split: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (int);
  var Net#d: Chan (int);
  var in#i: int;
  assume Net#gain != Net#split;
  assume (Net#a != Net#b) && (Net#a != Net#c) && (Net#a != Net#d) && (Net#b != Net#c) && (Net#b != Net#d) && (Net#c != Net#d);
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume 0 <= I[Net#c];
  assume I[Net#c] <= R[Net#c];
  assume R[Net#c] <= C[Net#c];
  assume I[Net#c] == R[Net#c];
  assume 0 <= I[Net#d];
  assume I[Net#d] <= R[Net#d];
  assume R[Net#d] <= C[Net#d];
  assume I[Net#d] == R[Net#d];
  assume (R[Net#b] - I[Net#b]) == ((C[Net#d] - I[Net#d]) + (C[Net#c] - I[Net#c]));
  assume ((R[Net#b] - I[Net#b]) > 0) && (M[Net#b][I[Net#b]] >= 0) ==> ((C[Net#d] - I[Net#d]) == 0) && (M[Net#c][I[Net#c]] == M[Net#b][I[Net#b]]);
  assume ((R[Net#b] - I[Net#b]) > 0) && (M[Net#b][I[Net#b]] < 0) ==> ((C[Net#c] - I[Net#c]) == 0) && (M[Net#d][I[Net#d]] == M[Net#b][I[Net#b]]);
  assume I[Net#b] == I[Net#a];
  assume (true && (forall idx$: int :: 
    (I[Net#a] <= idx$) && (idx$ < C[Net#a]) ==> (M[Net#a][idx$] == 1)
  )) || (true && (forall idx$: int :: 
    (I[Net#a] <= idx$) && (idx$ < C[Net#a]) ==> (M[Net#a][idx$] == (-1))
  ));
  assume R[Net#a] == C[Net#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == (2 * M[Net#a][idx$]))
  );
  assume 1 <= (C[Net#a] - R[Net#a]);
  assume R[Net#a] == C[Net#b];
  assume R[Net#a] == C[Net#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == (2 * M[Net#a][idx$]))
  );
  in#i := M[Net#a][R[Net#a]];
  R[Net#a] := R[Net#a] + 1;
  M[Net#b][C[Net#b]] := 2 * in#i;
  C[Net#b] := C[Net#b] + 1;
  assume R[Net#a] == C[Net#b];
  assume R[Net#a] == C[Net#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == (2 * M[Net#a][idx$]))
  );
  assert {:msg "27.15: Action at 3.3 ('anon$0') for actor instance 'gain' might not preserve the channel invariant (#16)"} (R[Net#b] - I[Net#b]) == ((C[Net#d] - I[Net#d]) + (C[Net#c] - I[Net#c]));
  assert {:msg "28.15: Action at 3.3 ('anon$0') for actor instance 'gain' might not preserve the channel invariant (#17)"} ((R[Net#b] - I[Net#b]) > 0) && (M[Net#b][I[Net#b]] >= 0) ==> ((C[Net#d] - I[Net#d]) == 0) && (M[Net#c][I[Net#c]] == M[Net#b][I[Net#b]]);
  assert {:msg "29.15: Action at 3.3 ('anon$0') for actor instance 'gain' might not preserve the channel invariant (#18)"} ((R[Net#b] - I[Net#b]) > 0) && (M[Net#b][I[Net#b]] < 0) ==> ((C[Net#c] - I[Net#c]) == 0) && (M[Net#d][I[Net#d]] == M[Net#b][I[Net#b]]);
  assert {:msg "Action at 3.3 ('anon$0') for actor instance 'gain' might not preserve the channel invariant (#19)"} I[Net#b] == I[Net#a];
  assert {:msg "Action at 3.3 ('anon$0') for actor instance 'gain' might not preserve the channel invariant (#20)"} (true && (forall idx$: int :: 
    (I[Net#a] <= idx$) && (idx$ < C[Net#a]) ==> (M[Net#a][idx$] == 1)
  )) || (true && (forall idx$: int :: 
    (I[Net#a] <= idx$) && (idx$ < C[Net#a]) ==> (M[Net#a][idx$] == (-1))
  ));
}
procedure Net##Split#anon$1#8()
  modifies C, R, M, I, St;
{
  var Net#gain: Actor;
  var Net#split: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (int);
  var Net#d: Chan (int);
  var in#i: int;
  assume Net#gain != Net#split;
  assume (Net#a != Net#b) && (Net#a != Net#c) && (Net#a != Net#d) && (Net#b != Net#c) && (Net#b != Net#d) && (Net#c != Net#d);
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume 0 <= I[Net#c];
  assume I[Net#c] <= R[Net#c];
  assume R[Net#c] <= C[Net#c];
  assume I[Net#c] == R[Net#c];
  assume 0 <= I[Net#d];
  assume I[Net#d] <= R[Net#d];
  assume R[Net#d] <= C[Net#d];
  assume I[Net#d] == R[Net#d];
  assume (R[Net#b] - I[Net#b]) == ((C[Net#d] - I[Net#d]) + (C[Net#c] - I[Net#c]));
  assume ((R[Net#b] - I[Net#b]) > 0) && (M[Net#b][I[Net#b]] >= 0) ==> ((C[Net#d] - I[Net#d]) == 0) && (M[Net#c][I[Net#c]] == M[Net#b][I[Net#b]]);
  assume ((R[Net#b] - I[Net#b]) > 0) && (M[Net#b][I[Net#b]] < 0) ==> ((C[Net#c] - I[Net#c]) == 0) && (M[Net#d][I[Net#d]] == M[Net#b][I[Net#b]]);
  assume I[Net#b] == I[Net#a];
  assume (true && (forall idx$: int :: 
    (I[Net#a] <= idx$) && (idx$ < C[Net#a]) ==> (M[Net#a][idx$] == 1)
  )) || (true && (forall idx$: int :: 
    (I[Net#a] <= idx$) && (idx$ < C[Net#a]) ==> (M[Net#a][idx$] == (-1))
  ));
  assume R[Net#a] == C[Net#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == (2 * M[Net#a][idx$]))
  );
  assume (1 <= (C[Net#b] - R[Net#b])) && (0 <= M[Net#b][R[Net#b]]);
  in#i := M[Net#b][R[Net#b]];
  R[Net#b] := R[Net#b] + 1;
  M[Net#c][C[Net#c]] := in#i;
  C[Net#c] := C[Net#c] + 1;
  assert {:msg "27.15: Action at 7.3 ('anon$1') for actor instance 'split' might not preserve the channel invariant (#21)"} (R[Net#b] - I[Net#b]) == ((C[Net#d] - I[Net#d]) + (C[Net#c] - I[Net#c]));
  assert {:msg "28.15: Action at 7.3 ('anon$1') for actor instance 'split' might not preserve the channel invariant (#22)"} ((R[Net#b] - I[Net#b]) > 0) && (M[Net#b][I[Net#b]] >= 0) ==> ((C[Net#d] - I[Net#d]) == 0) && (M[Net#c][I[Net#c]] == M[Net#b][I[Net#b]]);
  assert {:msg "29.15: Action at 7.3 ('anon$1') for actor instance 'split' might not preserve the channel invariant (#23)"} ((R[Net#b] - I[Net#b]) > 0) && (M[Net#b][I[Net#b]] < 0) ==> ((C[Net#c] - I[Net#c]) == 0) && (M[Net#d][I[Net#d]] == M[Net#b][I[Net#b]]);
  assert {:msg "Action at 7.3 ('anon$1') for actor instance 'split' might not preserve the channel invariant (#24)"} I[Net#b] == I[Net#a];
  assert {:msg "Action at 7.3 ('anon$1') for actor instance 'split' might not preserve the channel invariant (#25)"} (true && (forall idx$: int :: 
    (I[Net#a] <= idx$) && (idx$ < C[Net#a]) ==> (M[Net#a][idx$] == 1)
  )) || (true && (forall idx$: int :: 
    (I[Net#a] <= idx$) && (idx$ < C[Net#a]) ==> (M[Net#a][idx$] == (-1))
  ));
}
procedure Net##Split#anon$2#9()
  modifies C, R, M, I, St;
{
  var Net#gain: Actor;
  var Net#split: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (int);
  var Net#d: Chan (int);
  var in#j: int;
  assume Net#gain != Net#split;
  assume (Net#a != Net#b) && (Net#a != Net#c) && (Net#a != Net#d) && (Net#b != Net#c) && (Net#b != Net#d) && (Net#c != Net#d);
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume 0 <= I[Net#c];
  assume I[Net#c] <= R[Net#c];
  assume R[Net#c] <= C[Net#c];
  assume I[Net#c] == R[Net#c];
  assume 0 <= I[Net#d];
  assume I[Net#d] <= R[Net#d];
  assume R[Net#d] <= C[Net#d];
  assume I[Net#d] == R[Net#d];
  assume (R[Net#b] - I[Net#b]) == ((C[Net#d] - I[Net#d]) + (C[Net#c] - I[Net#c]));
  assume ((R[Net#b] - I[Net#b]) > 0) && (M[Net#b][I[Net#b]] >= 0) ==> ((C[Net#d] - I[Net#d]) == 0) && (M[Net#c][I[Net#c]] == M[Net#b][I[Net#b]]);
  assume ((R[Net#b] - I[Net#b]) > 0) && (M[Net#b][I[Net#b]] < 0) ==> ((C[Net#c] - I[Net#c]) == 0) && (M[Net#d][I[Net#d]] == M[Net#b][I[Net#b]]);
  assume I[Net#b] == I[Net#a];
  assume (true && (forall idx$: int :: 
    (I[Net#a] <= idx$) && (idx$ < C[Net#a]) ==> (M[Net#a][idx$] == 1)
  )) || (true && (forall idx$: int :: 
    (I[Net#a] <= idx$) && (idx$ < C[Net#a]) ==> (M[Net#a][idx$] == (-1))
  ));
  assume R[Net#a] == C[Net#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == (2 * M[Net#a][idx$]))
  );
  assume (1 <= (C[Net#b] - R[Net#b])) && (M[Net#b][R[Net#b]] < 0);
  in#j := M[Net#b][R[Net#b]];
  R[Net#b] := R[Net#b] + 1;
  M[Net#d][C[Net#d]] := in#j;
  C[Net#d] := C[Net#d] + 1;
  assert {:msg "27.15: Action at 10.3 ('anon$2') for actor instance 'split' might not preserve the channel invariant (#26)"} (R[Net#b] - I[Net#b]) == ((C[Net#d] - I[Net#d]) + (C[Net#c] - I[Net#c]));
  assert {:msg "28.15: Action at 10.3 ('anon$2') for actor instance 'split' might not preserve the channel invariant (#27)"} ((R[Net#b] - I[Net#b]) > 0) && (M[Net#b][I[Net#b]] >= 0) ==> ((C[Net#d] - I[Net#d]) == 0) && (M[Net#c][I[Net#c]] == M[Net#b][I[Net#b]]);
  assert {:msg "29.15: Action at 10.3 ('anon$2') for actor instance 'split' might not preserve the channel invariant (#28)"} ((R[Net#b] - I[Net#b]) > 0) && (M[Net#b][I[Net#b]] < 0) ==> ((C[Net#c] - I[Net#c]) == 0) && (M[Net#d][I[Net#d]] == M[Net#b][I[Net#b]]);
  assert {:msg "Action at 10.3 ('anon$2') for actor instance 'split' might not preserve the channel invariant (#29)"} I[Net#b] == I[Net#a];
  assert {:msg "Action at 10.3 ('anon$2') for actor instance 'split' might not preserve the channel invariant (#30)"} (true && (forall idx$: int :: 
    (I[Net#a] <= idx$) && (idx$ < C[Net#a]) ==> (M[Net#a][idx$] == 1)
  )) || (true && (forall idx$: int :: 
    (I[Net#a] <= idx$) && (idx$ < C[Net#a]) ==> (M[Net#a][idx$] == (-1))
  ));
}
procedure Net#entry()
  modifies C, R, M, I, St;
{
  var Net#gain: Actor;
  var Net#split: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (int);
  var Net#d: Chan (int);
  assume Net#gain != Net#split;
  assume (Net#a != Net#b) && (Net#a != Net#c) && (Net#a != Net#d) && (Net#b != Net#c) && (Net#b != Net#d) && (Net#c != Net#d);
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume 0 <= I[Net#c];
  assume I[Net#c] <= R[Net#c];
  assume R[Net#c] <= C[Net#c];
  assume I[Net#c] == R[Net#c];
  assume 0 <= I[Net#d];
  assume I[Net#d] <= R[Net#d];
  assume R[Net#d] <= C[Net#d];
  assume I[Net#d] == R[Net#d];
  assume C[Net#a] == R[Net#a];
  assume C[Net#b] == R[Net#b];
  assume C[Net#c] == R[Net#c];
  assume C[Net#d] == R[Net#d];
  assert {:msg "15.1: Sub-actors in the network might fire without network input. This is not permitted. (#31)"} !(1 <= (C[Net#a] - R[Net#a]));
  assert {:msg "15.1: Sub-actors in the network might fire without network input. This is not permitted. (#32)"} !((1 <= (C[Net#b] - R[Net#b])) && (M[Net#b][R[Net#b]] < 0));
  assert {:msg "15.1: Sub-actors in the network might fire without network input. This is not permitted. (#33)"} !((1 <= (C[Net#b] - R[Net#b])) && (0 <= M[Net#b][R[Net#b]]));
}
procedure Net#anon$3#input#in#10()
  modifies C, R, M, I, St;
{
  var Net#gain: Actor;
  var Net#split: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (int);
  var Net#d: Chan (int);
  assume Net#gain != Net#split;
  assume (Net#a != Net#b) && (Net#a != Net#c) && (Net#a != Net#d) && (Net#b != Net#c) && (Net#b != Net#d) && (Net#c != Net#d);
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume 0 <= I[Net#c];
  assume I[Net#c] <= R[Net#c];
  assume R[Net#c] <= C[Net#c];
  assume I[Net#c] == R[Net#c];
  assume 0 <= I[Net#d];
  assume I[Net#d] <= R[Net#d];
  assume R[Net#d] <= C[Net#d];
  assume I[Net#d] == R[Net#d];
  assume C[Net#a] < 1;
  assume (R[Net#b] - I[Net#b]) == ((C[Net#d] - I[Net#d]) + (C[Net#c] - I[Net#c]));
  assume ((R[Net#b] - I[Net#b]) > 0) && (M[Net#b][I[Net#b]] >= 0) ==> ((C[Net#d] - I[Net#d]) == 0) && (M[Net#c][I[Net#c]] == M[Net#b][I[Net#b]]);
  assume ((R[Net#b] - I[Net#b]) > 0) && (M[Net#b][I[Net#b]] < 0) ==> ((C[Net#c] - I[Net#c]) == 0) && (M[Net#d][I[Net#d]] == M[Net#b][I[Net#b]]);
  assume I[Net#b] == I[Net#a];
  assume (true && (forall idx$: int :: 
    (I[Net#a] <= idx$) && (idx$ < C[Net#a]) ==> (M[Net#a][idx$] == 1)
  )) || (true && (forall idx$: int :: 
    (I[Net#a] <= idx$) && (idx$ < C[Net#a]) ==> (M[Net#a][idx$] == (-1))
  ));
  assume R[Net#a] == C[Net#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == (2 * M[Net#a][idx$]))
  );
  C[Net#a] := C[Net#a] + 1;
  assume M[Net#a][I[Net#a]] == 1;
  assert {:msg "27.15: Channel invariant might be falsified by network input (#34)"} (R[Net#b] - I[Net#b]) == ((C[Net#d] - I[Net#d]) + (C[Net#c] - I[Net#c]));
  assert {:msg "28.15: Channel invariant might be falsified by network input (#35)"} ((R[Net#b] - I[Net#b]) > 0) && (M[Net#b][I[Net#b]] >= 0) ==> ((C[Net#d] - I[Net#d]) == 0) && (M[Net#c][I[Net#c]] == M[Net#b][I[Net#b]]);
  assert {:msg "29.15: Channel invariant might be falsified by network input (#36)"} ((R[Net#b] - I[Net#b]) > 0) && (M[Net#b][I[Net#b]] < 0) ==> ((C[Net#c] - I[Net#c]) == 0) && (M[Net#d][I[Net#d]] == M[Net#b][I[Net#b]]);
  assert {:msg "Channel invariant might be falsified by network input (#37)"} I[Net#b] == I[Net#a];
  assert {:msg "Channel invariant might be falsified by network input (#38)"} (true && (forall idx$: int :: 
    (I[Net#a] <= idx$) && (idx$ < C[Net#a]) ==> (M[Net#a][idx$] == 1)
  )) || (true && (forall idx$: int :: 
    (I[Net#a] <= idx$) && (idx$ < C[Net#a]) ==> (M[Net#a][idx$] == (-1))
  ));
}
procedure Net#anon$3#exit#11()
  modifies C, R, M, I, St;
{
  var Net#gain: Actor;
  var Net#split: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (int);
  var Net#d: Chan (int);
  assume Net#gain != Net#split;
  assume (Net#a != Net#b) && (Net#a != Net#c) && (Net#a != Net#d) && (Net#b != Net#c) && (Net#b != Net#d) && (Net#c != Net#d);
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume 0 <= I[Net#c];
  assume I[Net#c] <= R[Net#c];
  assume R[Net#c] <= C[Net#c];
  assume I[Net#c] == R[Net#c];
  assume 0 <= I[Net#d];
  assume I[Net#d] <= R[Net#d];
  assume R[Net#d] <= C[Net#d];
  assume I[Net#d] == R[Net#d];
  assume (R[Net#b] - I[Net#b]) == ((C[Net#d] - I[Net#d]) + (C[Net#c] - I[Net#c]));
  assume ((R[Net#b] - I[Net#b]) > 0) && (M[Net#b][I[Net#b]] >= 0) ==> ((C[Net#d] - I[Net#d]) == 0) && (M[Net#c][I[Net#c]] == M[Net#b][I[Net#b]]);
  assume ((R[Net#b] - I[Net#b]) > 0) && (M[Net#b][I[Net#b]] < 0) ==> ((C[Net#c] - I[Net#c]) == 0) && (M[Net#d][I[Net#d]] == M[Net#b][I[Net#b]]);
  assume I[Net#b] == I[Net#a];
  assume (true && (forall idx$: int :: 
    (I[Net#a] <= idx$) && (idx$ < C[Net#a]) ==> (M[Net#a][idx$] == 1)
  )) || (true && (forall idx$: int :: 
    (I[Net#a] <= idx$) && (idx$ < C[Net#a]) ==> (M[Net#a][idx$] == (-1))
  ));
  assume R[Net#a] == C[Net#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == (2 * M[Net#a][idx$]))
  );
  assume (C[Net#a] - I[Net#a]) == 1;
  assume M[Net#a][I[Net#a]] == 1;
  assume !(1 <= (C[Net#a] - R[Net#a]));
  assume !((1 <= (C[Net#b] - R[Net#b])) && (M[Net#b][R[Net#b]] < 0));
  assume !((1 <= (C[Net#b] - R[Net#b])) && (0 <= M[Net#b][R[Net#b]]));
  assert {:msg "19.13: Network action postcondition might not hold (#39)"} M[Net#c][I[Net#c]] == (2 * M[Net#a][I[Net#a]]);
  R[Net#c] := R[Net#c] + 1;
  R[Net#d] := R[Net#d] + 0;
  I := R;
  assert {:msg "27.15: The network might not preserve the channel invariant (#40)"} (R[Net#b] - I[Net#b]) == ((C[Net#d] - I[Net#d]) + (C[Net#c] - I[Net#c]));
  assert {:msg "28.15: The network might not preserve the channel invariant (#41)"} ((R[Net#b] - I[Net#b]) > 0) && (M[Net#b][I[Net#b]] >= 0) ==> ((C[Net#d] - I[Net#d]) == 0) && (M[Net#c][I[Net#c]] == M[Net#b][I[Net#b]]);
  assert {:msg "29.15: The network might not preserve the channel invariant (#42)"} ((R[Net#b] - I[Net#b]) > 0) && (M[Net#b][I[Net#b]] < 0) ==> ((C[Net#c] - I[Net#c]) == 0) && (M[Net#d][I[Net#d]] == M[Net#b][I[Net#b]]);
  assert {:msg "The network might not preserve the channel invariant (#43)"} I[Net#b] == I[Net#a];
  assert {:msg "The network might not preserve the channel invariant (#44)"} (true && (forall idx$: int :: 
    (I[Net#a] <= idx$) && (idx$ < C[Net#a]) ==> (M[Net#a][idx$] == 1)
  )) || (true && (forall idx$: int :: 
    (I[Net#a] <= idx$) && (idx$ < C[Net#a]) ==> (M[Net#a][idx$] == (-1))
  ));
  assert {:msg "17.3: The network might leave unread tokens on channel a (#45)"} C[Net#a] == R[Net#a];
  assert {:msg "17.3: The network might leave unread tokens on channel b (#46)"} C[Net#b] == R[Net#b];
  assert {:msg "17.3: The network might not produce the specified number of tokens on output out1 (#47)"} C[Net#c] == R[Net#c];
  assert {:msg "17.3: The network might not produce the specified number of tokens on output out2 (#48)"} C[Net#d] == R[Net#d];
}
procedure Net#anon$4#input#in#12()
  modifies C, R, M, I, St;
{
  var Net#gain: Actor;
  var Net#split: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (int);
  var Net#d: Chan (int);
  assume Net#gain != Net#split;
  assume (Net#a != Net#b) && (Net#a != Net#c) && (Net#a != Net#d) && (Net#b != Net#c) && (Net#b != Net#d) && (Net#c != Net#d);
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume 0 <= I[Net#c];
  assume I[Net#c] <= R[Net#c];
  assume R[Net#c] <= C[Net#c];
  assume I[Net#c] == R[Net#c];
  assume 0 <= I[Net#d];
  assume I[Net#d] <= R[Net#d];
  assume R[Net#d] <= C[Net#d];
  assume I[Net#d] == R[Net#d];
  assume C[Net#a] < 1;
  assume (R[Net#b] - I[Net#b]) == ((C[Net#d] - I[Net#d]) + (C[Net#c] - I[Net#c]));
  assume ((R[Net#b] - I[Net#b]) > 0) && (M[Net#b][I[Net#b]] >= 0) ==> ((C[Net#d] - I[Net#d]) == 0) && (M[Net#c][I[Net#c]] == M[Net#b][I[Net#b]]);
  assume ((R[Net#b] - I[Net#b]) > 0) && (M[Net#b][I[Net#b]] < 0) ==> ((C[Net#c] - I[Net#c]) == 0) && (M[Net#d][I[Net#d]] == M[Net#b][I[Net#b]]);
  assume I[Net#b] == I[Net#a];
  assume (true && (forall idx$: int :: 
    (I[Net#a] <= idx$) && (idx$ < C[Net#a]) ==> (M[Net#a][idx$] == 1)
  )) || (true && (forall idx$: int :: 
    (I[Net#a] <= idx$) && (idx$ < C[Net#a]) ==> (M[Net#a][idx$] == (-1))
  ));
  assume R[Net#a] == C[Net#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == (2 * M[Net#a][idx$]))
  );
  C[Net#a] := C[Net#a] + 1;
  assume M[Net#a][I[Net#a]] == (-1);
  assert {:msg "27.15: Channel invariant might be falsified by network input (#49)"} (R[Net#b] - I[Net#b]) == ((C[Net#d] - I[Net#d]) + (C[Net#c] - I[Net#c]));
  assert {:msg "28.15: Channel invariant might be falsified by network input (#50)"} ((R[Net#b] - I[Net#b]) > 0) && (M[Net#b][I[Net#b]] >= 0) ==> ((C[Net#d] - I[Net#d]) == 0) && (M[Net#c][I[Net#c]] == M[Net#b][I[Net#b]]);
  assert {:msg "29.15: Channel invariant might be falsified by network input (#51)"} ((R[Net#b] - I[Net#b]) > 0) && (M[Net#b][I[Net#b]] < 0) ==> ((C[Net#c] - I[Net#c]) == 0) && (M[Net#d][I[Net#d]] == M[Net#b][I[Net#b]]);
  assert {:msg "Channel invariant might be falsified by network input (#52)"} I[Net#b] == I[Net#a];
  assert {:msg "Channel invariant might be falsified by network input (#53)"} (true && (forall idx$: int :: 
    (I[Net#a] <= idx$) && (idx$ < C[Net#a]) ==> (M[Net#a][idx$] == 1)
  )) || (true && (forall idx$: int :: 
    (I[Net#a] <= idx$) && (idx$ < C[Net#a]) ==> (M[Net#a][idx$] == (-1))
  ));
}
procedure Net#anon$4#exit#13()
  modifies C, R, M, I, St;
{
  var Net#gain: Actor;
  var Net#split: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var Net#c: Chan (int);
  var Net#d: Chan (int);
  assume Net#gain != Net#split;
  assume (Net#a != Net#b) && (Net#a != Net#c) && (Net#a != Net#d) && (Net#b != Net#c) && (Net#b != Net#d) && (Net#c != Net#d);
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume 0 <= I[Net#c];
  assume I[Net#c] <= R[Net#c];
  assume R[Net#c] <= C[Net#c];
  assume I[Net#c] == R[Net#c];
  assume 0 <= I[Net#d];
  assume I[Net#d] <= R[Net#d];
  assume R[Net#d] <= C[Net#d];
  assume I[Net#d] == R[Net#d];
  assume (R[Net#b] - I[Net#b]) == ((C[Net#d] - I[Net#d]) + (C[Net#c] - I[Net#c]));
  assume ((R[Net#b] - I[Net#b]) > 0) && (M[Net#b][I[Net#b]] >= 0) ==> ((C[Net#d] - I[Net#d]) == 0) && (M[Net#c][I[Net#c]] == M[Net#b][I[Net#b]]);
  assume ((R[Net#b] - I[Net#b]) > 0) && (M[Net#b][I[Net#b]] < 0) ==> ((C[Net#c] - I[Net#c]) == 0) && (M[Net#d][I[Net#d]] == M[Net#b][I[Net#b]]);
  assume I[Net#b] == I[Net#a];
  assume (true && (forall idx$: int :: 
    (I[Net#a] <= idx$) && (idx$ < C[Net#a]) ==> (M[Net#a][idx$] == 1)
  )) || (true && (forall idx$: int :: 
    (I[Net#a] <= idx$) && (idx$ < C[Net#a]) ==> (M[Net#a][idx$] == (-1))
  ));
  assume R[Net#a] == C[Net#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == (2 * M[Net#a][idx$]))
  );
  assume (C[Net#a] - I[Net#a]) == 1;
  assume M[Net#a][I[Net#a]] == (-1);
  assume !(1 <= (C[Net#a] - R[Net#a]));
  assume !((1 <= (C[Net#b] - R[Net#b])) && (M[Net#b][R[Net#b]] < 0));
  assume !((1 <= (C[Net#b] - R[Net#b])) && (0 <= M[Net#b][R[Net#b]]));
  assert {:msg "24.13: Network action postcondition might not hold (#54)"} M[Net#d][I[Net#d]] == (2 * M[Net#a][I[Net#a]]);
  R[Net#c] := R[Net#c] + 0;
  R[Net#d] := R[Net#d] + 1;
  I := R;
  assert {:msg "27.15: The network might not preserve the channel invariant (#55)"} (R[Net#b] - I[Net#b]) == ((C[Net#d] - I[Net#d]) + (C[Net#c] - I[Net#c]));
  assert {:msg "28.15: The network might not preserve the channel invariant (#56)"} ((R[Net#b] - I[Net#b]) > 0) && (M[Net#b][I[Net#b]] >= 0) ==> ((C[Net#d] - I[Net#d]) == 0) && (M[Net#c][I[Net#c]] == M[Net#b][I[Net#b]]);
  assert {:msg "29.15: The network might not preserve the channel invariant (#57)"} ((R[Net#b] - I[Net#b]) > 0) && (M[Net#b][I[Net#b]] < 0) ==> ((C[Net#c] - I[Net#c]) == 0) && (M[Net#d][I[Net#d]] == M[Net#b][I[Net#b]]);
  assert {:msg "The network might not preserve the channel invariant (#58)"} I[Net#b] == I[Net#a];
  assert {:msg "The network might not preserve the channel invariant (#59)"} (true && (forall idx$: int :: 
    (I[Net#a] <= idx$) && (idx$ < C[Net#a]) ==> (M[Net#a][idx$] == 1)
  )) || (true && (forall idx$: int :: 
    (I[Net#a] <= idx$) && (idx$ < C[Net#a]) ==> (M[Net#a][idx$] == (-1))
  ));
  assert {:msg "22.3: The network might leave unread tokens on channel a (#60)"} C[Net#a] == R[Net#a];
  assert {:msg "22.3: The network might leave unread tokens on channel b (#61)"} C[Net#b] == R[Net#b];
  assert {:msg "22.3: The network might not produce the specified number of tokens on output out1 (#62)"} C[Net#c] == R[Net#c];
  assert {:msg "22.3: The network might not produce the specified number of tokens on output out2 (#63)"} C[Net#d] == R[Net#d];
}

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

procedure Gain#init#0()
  modifies C, R, M, I;
{
  var in: Chan (int);
  var out: Chan (int);
  assume in != out;
  assume R[in] == 0;
  assume C[out] == 0;
  assert {:msg "Initialization might not establish the invariant (#0)"} R[in] == C[out];
  assert {:msg "Initialization might not establish the invariant (#1)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == (2 * M[in][idx$]))
  );
}
procedure Gain#anon$0#1()
  modifies C, R, M, I;
{
  var in: Chan (int);
  var out: Chan (int);
  var in#0: int;
  assume in != out;
  assume 0 <= R[in];
  assume 0 <= C[out];
  assume R[in] == C[out];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == (2 * M[in][idx$]))
  );
  in#0 := M[in][R[in]];
  R[in] := R[in] + 1;
  M[out][C[out]] := 2 * in#0;
  C[out] := C[out] + 1;
  assert {:msg "Action at 3.3 might not preserve invariant (#2)"} R[in] == C[out];
  assert {:msg "Action at 3.3 might not preserve invariant (#3)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == (2 * M[in][idx$]))
  );
}
procedure Split#init#2()
  modifies C, R, M, I;
{
  var in: Chan (int);
  var pos: Chan (int);
  var neg: Chan (int);
  assume (in != pos) && (in != neg) && (pos != neg);
  assume R[in] == 0;
  assume C[pos] == 0;
  assume C[neg] == 0;
  assert {:msg "7.20: Initialization might not establish the invariant (#4)"} R[in] == (C[pos] + C[neg]);
  assert {:msg "8.20: Initialization might not establish the invariant (#5)"} (0 < R[in]) && (0 <= M[in][R[in] - 1]) ==> (M[in][R[in] - 1] == M[pos][C[pos] - 1]);
  assert {:msg "9.20: Initialization might not establish the invariant (#6)"} (0 < R[in]) && (M[in][R[in] - 1] < 0) ==> (M[in][R[in] - 1] == M[neg][C[neg] - 1]);
}
procedure Split#anon$1#3()
  modifies C, R, M, I;
{
  var in: Chan (int);
  var pos: Chan (int);
  var neg: Chan (int);
  var in#0: int;
  assume (in != pos) && (in != neg) && (pos != neg);
  assume 0 <= R[in];
  assume 0 <= C[pos];
  assume 0 <= C[neg];
  assume R[in] == (C[pos] + C[neg]);
  assume (0 < R[in]) && (0 <= M[in][R[in] - 1]) ==> (M[in][R[in] - 1] == M[pos][C[pos] - 1]);
  assume (0 < R[in]) && (M[in][R[in] - 1] < 0) ==> (M[in][R[in] - 1] == M[neg][C[neg] - 1]);
  in#0 := M[in][R[in]];
  R[in] := R[in] + 1;
  assume 0 <= in#0;
  M[pos][C[pos]] := in#0;
  C[pos] := C[pos] + 1;
  assert {:msg "7.20: Action at 10.3 might not preserve invariant (#7)"} R[in] == (C[pos] + C[neg]);
  assert {:msg "8.20: Action at 10.3 might not preserve invariant (#8)"} (0 < R[in]) && (0 <= M[in][R[in] - 1]) ==> (M[in][R[in] - 1] == M[pos][C[pos] - 1]);
  assert {:msg "9.20: Action at 10.3 might not preserve invariant (#9)"} (0 < R[in]) && (M[in][R[in] - 1] < 0) ==> (M[in][R[in] - 1] == M[neg][C[neg] - 1]);
}
procedure Split#anon$2#4()
  modifies C, R, M, I;
{
  var in: Chan (int);
  var pos: Chan (int);
  var neg: Chan (int);
  var in#0: int;
  assume (in != pos) && (in != neg) && (pos != neg);
  assume 0 <= R[in];
  assume 0 <= C[pos];
  assume 0 <= C[neg];
  assume R[in] == (C[pos] + C[neg]);
  assume (0 < R[in]) && (0 <= M[in][R[in] - 1]) ==> (M[in][R[in] - 1] == M[pos][C[pos] - 1]);
  assume (0 < R[in]) && (M[in][R[in] - 1] < 0) ==> (M[in][R[in] - 1] == M[neg][C[neg] - 1]);
  in#0 := M[in][R[in]];
  R[in] := R[in] + 1;
  assume in#0 < 0;
  M[neg][C[neg]] := in#0;
  C[neg] := C[neg] + 1;
  assert {:msg "7.20: Action at 13.3 might not preserve invariant (#10)"} R[in] == (C[pos] + C[neg]);
  assert {:msg "8.20: Action at 13.3 might not preserve invariant (#11)"} (0 < R[in]) && (0 <= M[in][R[in] - 1]) ==> (M[in][R[in] - 1] == M[pos][C[pos] - 1]);
  assert {:msg "9.20: Action at 13.3 might not preserve invariant (#12)"} (0 < R[in]) && (M[in][R[in] - 1] < 0) ==> (M[in][R[in] - 1] == M[neg][C[neg] - 1]);
}
procedure Split##GuardWD#5()
  modifies C, R, M, I;
{
  var in: Chan (int);
  var pos: Chan (int);
  var neg: Chan (int);
  var in#0: int;
  assume (in != pos) && (in != neg) && (pos != neg);
  assert {:msg "6.1: The actions of actor 'Split' might not have mutually exclusive guards (#13)"} !((1 <= (C[in] - R[in])) && (0 <= in#0) && (1 <= (C[in] - R[in])) && (in#0 < 0));
}
procedure Net#init#6()
  modifies C, R, M, I;
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
  assert {:msg "32.15: Initialization of network 'Net' might not establish the channel invariant (#14)"} I[Net#b] == (I[Net#d] + I[Net#c]);
  assert {:msg "33.15: Initialization of network 'Net' might not establish the channel invariant (#15)"} (0 < (C[Net#a] - I[Net#a])) ==> ((M[Net#a][I[Net#a]] == 1) || (M[Net#a][I[Net#a]] == (-1)));
  assert {:msg "34.15: Initialization of network 'Net' might not establish the channel invariant (#16)"} (0 < (R[Net#b] - I[Net#b])) && (M[Net#b][I[Net#b]] >= 0) ==> ((C[Net#d] - I[Net#d]) == 0);
  assert {:msg "35.15: Initialization of network 'Net' might not establish the channel invariant (#17)"} (0 < (R[Net#b] - I[Net#b])) && (M[Net#b][I[Net#b]] < 0) ==> ((C[Net#c] - I[Net#c]) == 0);
  assert {:msg "Initialization of network 'Net' might not establish the channel invariant (#18)"} I[Net#b] == I[Net#a];
  I := R;
  assert {:msg "Initialization of network 'Net' might not establish the network invariant: Unread tokens might be left on channel a (#19)"} (C[Net#a] - R[Net#a]) == 0;
  assert {:msg "Initialization of network 'Net' might not establish the network invariant: Unread tokens might be left on channel b (#20)"} (C[Net#b] - R[Net#b]) == 0;
  assert {:msg "Initialization of network 'Net' might not establish the network invariant: Unread tokens might be left on channel c (#21)"} (C[Net#c] - R[Net#c]) == 0;
  assert {:msg "Initialization of network 'Net' might not establish the network invariant: Unread tokens might be left on channel d (#22)"} (C[Net#d] - R[Net#d]) == 0;
}
procedure Net##Gain#anon$0#7()
  modifies C, R, M, I;
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
  assume I[Net#b] == (I[Net#d] + I[Net#c]);
  assume (0 < (C[Net#a] - I[Net#a])) ==> ((M[Net#a][I[Net#a]] == 1) || (M[Net#a][I[Net#a]] == (-1)));
  assume (0 < (R[Net#b] - I[Net#b])) && (M[Net#b][I[Net#b]] >= 0) ==> ((C[Net#d] - I[Net#d]) == 0);
  assume (0 < (R[Net#b] - I[Net#b])) && (M[Net#b][I[Net#b]] < 0) ==> ((C[Net#c] - I[Net#c]) == 0);
  assume I[Net#b] == I[Net#a];
  assume ((M[Net#a][I[Net#a]] == 1) && (forall i: int :: 
    (I[Net#a] <= i) && (i < C[Net#a]) ==> (M[Net#a][i] == 1)
  )) || ((M[Net#a][I[Net#a]] == (-1)) && (forall i: int :: 
    (I[Net#a] <= i) && (i < C[Net#a]) ==> (M[Net#a][i] == (-1))
  ));
  assume R[Net#a] == C[Net#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == (2 * M[Net#a][idx$]))
  );
  assume R[Net#b] == (C[Net#c] + C[Net#d]);
  assume (0 < R[Net#b]) && (0 <= M[Net#b][R[Net#b] - 1]) ==> (M[Net#b][R[Net#b] - 1] == M[Net#c][C[Net#c] - 1]);
  assume (0 < R[Net#b]) && (M[Net#b][R[Net#b] - 1] < 0) ==> (M[Net#b][R[Net#b] - 1] == M[Net#d][C[Net#d] - 1]);
  assume 1 <= (C[Net#a] - R[Net#a]);
  in#i := M[Net#a][R[Net#a]];
  R[Net#a] := R[Net#a] + 1;
  M[Net#b][C[Net#b]] := 2 * in#i;
  C[Net#b] := C[Net#b] + 1;
  assume R[Net#a] == C[Net#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == (2 * M[Net#a][idx$]))
  );
  assume R[Net#b] == (C[Net#c] + C[Net#d]);
  assume (0 < R[Net#b]) && (0 <= M[Net#b][R[Net#b] - 1]) ==> (M[Net#b][R[Net#b] - 1] == M[Net#c][C[Net#c] - 1]);
  assume (0 < R[Net#b]) && (M[Net#b][R[Net#b] - 1] < 0) ==> (M[Net#b][R[Net#b] - 1] == M[Net#d][C[Net#d] - 1]);
  assert {:msg "32.15: Action at 3.3 ('anon$0') for actor instance 'gain' might not preserve the channel invariant (#23)"} I[Net#b] == (I[Net#d] + I[Net#c]);
  assert {:msg "33.15: Action at 3.3 ('anon$0') for actor instance 'gain' might not preserve the channel invariant (#24)"} (0 < (C[Net#a] - I[Net#a])) ==> ((M[Net#a][I[Net#a]] == 1) || (M[Net#a][I[Net#a]] == (-1)));
  assert {:msg "34.15: Action at 3.3 ('anon$0') for actor instance 'gain' might not preserve the channel invariant (#25)"} (0 < (R[Net#b] - I[Net#b])) && (M[Net#b][I[Net#b]] >= 0) ==> ((C[Net#d] - I[Net#d]) == 0);
  assert {:msg "35.15: Action at 3.3 ('anon$0') for actor instance 'gain' might not preserve the channel invariant (#26)"} (0 < (R[Net#b] - I[Net#b])) && (M[Net#b][I[Net#b]] < 0) ==> ((C[Net#c] - I[Net#c]) == 0);
  assert {:msg "Action at 3.3 ('anon$0') for actor instance 'gain' might not preserve the channel invariant (#27)"} I[Net#b] == I[Net#a];
}
procedure Net##Split#anon$1#8()
  modifies C, R, M, I;
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
  assume I[Net#b] == (I[Net#d] + I[Net#c]);
  assume (0 < (C[Net#a] - I[Net#a])) ==> ((M[Net#a][I[Net#a]] == 1) || (M[Net#a][I[Net#a]] == (-1)));
  assume (0 < (R[Net#b] - I[Net#b])) && (M[Net#b][I[Net#b]] >= 0) ==> ((C[Net#d] - I[Net#d]) == 0);
  assume (0 < (R[Net#b] - I[Net#b])) && (M[Net#b][I[Net#b]] < 0) ==> ((C[Net#c] - I[Net#c]) == 0);
  assume I[Net#b] == I[Net#a];
  assume ((M[Net#a][I[Net#a]] == 1) && (forall i: int :: 
    (I[Net#a] <= i) && (i < C[Net#a]) ==> (M[Net#a][i] == 1)
  )) || ((M[Net#a][I[Net#a]] == (-1)) && (forall i: int :: 
    (I[Net#a] <= i) && (i < C[Net#a]) ==> (M[Net#a][i] == (-1))
  ));
  assume R[Net#a] == C[Net#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == (2 * M[Net#a][idx$]))
  );
  assume R[Net#b] == (C[Net#c] + C[Net#d]);
  assume (0 < R[Net#b]) && (0 <= M[Net#b][R[Net#b] - 1]) ==> (M[Net#b][R[Net#b] - 1] == M[Net#c][C[Net#c] - 1]);
  assume (0 < R[Net#b]) && (M[Net#b][R[Net#b] - 1] < 0) ==> (M[Net#b][R[Net#b] - 1] == M[Net#d][C[Net#d] - 1]);
  assume (1 <= (C[Net#b] - R[Net#b])) && (0 <= M[Net#b][R[Net#b]]);
  in#i := M[Net#b][R[Net#b]];
  R[Net#b] := R[Net#b] + 1;
  M[Net#c][C[Net#c]] := in#i;
  C[Net#c] := C[Net#c] + 1;
  assume R[Net#a] == C[Net#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == (2 * M[Net#a][idx$]))
  );
  assume R[Net#b] == (C[Net#c] + C[Net#d]);
  assume (0 < R[Net#b]) && (0 <= M[Net#b][R[Net#b] - 1]) ==> (M[Net#b][R[Net#b] - 1] == M[Net#c][C[Net#c] - 1]);
  assume (0 < R[Net#b]) && (M[Net#b][R[Net#b] - 1] < 0) ==> (M[Net#b][R[Net#b] - 1] == M[Net#d][C[Net#d] - 1]);
  assert {:msg "32.15: Action at 10.3 ('anon$1') for actor instance 'split' might not preserve the channel invariant (#28)"} I[Net#b] == (I[Net#d] + I[Net#c]);
  assert {:msg "33.15: Action at 10.3 ('anon$1') for actor instance 'split' might not preserve the channel invariant (#29)"} (0 < (C[Net#a] - I[Net#a])) ==> ((M[Net#a][I[Net#a]] == 1) || (M[Net#a][I[Net#a]] == (-1)));
  assert {:msg "34.15: Action at 10.3 ('anon$1') for actor instance 'split' might not preserve the channel invariant (#30)"} (0 < (R[Net#b] - I[Net#b])) && (M[Net#b][I[Net#b]] >= 0) ==> ((C[Net#d] - I[Net#d]) == 0);
  assert {:msg "35.15: Action at 10.3 ('anon$1') for actor instance 'split' might not preserve the channel invariant (#31)"} (0 < (R[Net#b] - I[Net#b])) && (M[Net#b][I[Net#b]] < 0) ==> ((C[Net#c] - I[Net#c]) == 0);
  assert {:msg "Action at 10.3 ('anon$1') for actor instance 'split' might not preserve the channel invariant (#32)"} I[Net#b] == I[Net#a];
}
procedure Net##Split#anon$2#9()
  modifies C, R, M, I;
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
  assume I[Net#b] == (I[Net#d] + I[Net#c]);
  assume (0 < (C[Net#a] - I[Net#a])) ==> ((M[Net#a][I[Net#a]] == 1) || (M[Net#a][I[Net#a]] == (-1)));
  assume (0 < (R[Net#b] - I[Net#b])) && (M[Net#b][I[Net#b]] >= 0) ==> ((C[Net#d] - I[Net#d]) == 0);
  assume (0 < (R[Net#b] - I[Net#b])) && (M[Net#b][I[Net#b]] < 0) ==> ((C[Net#c] - I[Net#c]) == 0);
  assume I[Net#b] == I[Net#a];
  assume ((M[Net#a][I[Net#a]] == 1) && (forall i: int :: 
    (I[Net#a] <= i) && (i < C[Net#a]) ==> (M[Net#a][i] == 1)
  )) || ((M[Net#a][I[Net#a]] == (-1)) && (forall i: int :: 
    (I[Net#a] <= i) && (i < C[Net#a]) ==> (M[Net#a][i] == (-1))
  ));
  assume R[Net#a] == C[Net#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == (2 * M[Net#a][idx$]))
  );
  assume R[Net#b] == (C[Net#c] + C[Net#d]);
  assume (0 < R[Net#b]) && (0 <= M[Net#b][R[Net#b] - 1]) ==> (M[Net#b][R[Net#b] - 1] == M[Net#c][C[Net#c] - 1]);
  assume (0 < R[Net#b]) && (M[Net#b][R[Net#b] - 1] < 0) ==> (M[Net#b][R[Net#b] - 1] == M[Net#d][C[Net#d] - 1]);
  assume (1 <= (C[Net#b] - R[Net#b])) && (M[Net#b][R[Net#b]] < 0);
  in#j := M[Net#b][R[Net#b]];
  R[Net#b] := R[Net#b] + 1;
  M[Net#d][C[Net#d]] := in#j;
  C[Net#d] := C[Net#d] + 1;
  assume R[Net#a] == C[Net#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == (2 * M[Net#a][idx$]))
  );
  assume R[Net#b] == (C[Net#c] + C[Net#d]);
  assume (0 < R[Net#b]) && (0 <= M[Net#b][R[Net#b] - 1]) ==> (M[Net#b][R[Net#b] - 1] == M[Net#c][C[Net#c] - 1]);
  assume (0 < R[Net#b]) && (M[Net#b][R[Net#b] - 1] < 0) ==> (M[Net#b][R[Net#b] - 1] == M[Net#d][C[Net#d] - 1]);
  assert {:msg "32.15: Action at 13.3 ('anon$2') for actor instance 'split' might not preserve the channel invariant (#33)"} I[Net#b] == (I[Net#d] + I[Net#c]);
  assert {:msg "33.15: Action at 13.3 ('anon$2') for actor instance 'split' might not preserve the channel invariant (#34)"} (0 < (C[Net#a] - I[Net#a])) ==> ((M[Net#a][I[Net#a]] == 1) || (M[Net#a][I[Net#a]] == (-1)));
  assert {:msg "34.15: Action at 13.3 ('anon$2') for actor instance 'split' might not preserve the channel invariant (#35)"} (0 < (R[Net#b] - I[Net#b])) && (M[Net#b][I[Net#b]] >= 0) ==> ((C[Net#d] - I[Net#d]) == 0);
  assert {:msg "35.15: Action at 13.3 ('anon$2') for actor instance 'split' might not preserve the channel invariant (#36)"} (0 < (R[Net#b] - I[Net#b])) && (M[Net#b][I[Net#b]] < 0) ==> ((C[Net#c] - I[Net#c]) == 0);
  assert {:msg "Action at 13.3 ('anon$2') for actor instance 'split' might not preserve the channel invariant (#37)"} I[Net#b] == I[Net#a];
}
procedure Net#anon$3#input#in#10()
  modifies C, R, M, I;
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
  assume (C[Net#a] - I[Net#a]) < 1;
  assume I[Net#b] == (I[Net#d] + I[Net#c]);
  assume (0 < (C[Net#a] - I[Net#a])) ==> ((M[Net#a][I[Net#a]] == 1) || (M[Net#a][I[Net#a]] == (-1)));
  assume (0 < (R[Net#b] - I[Net#b])) && (M[Net#b][I[Net#b]] >= 0) ==> ((C[Net#d] - I[Net#d]) == 0);
  assume (0 < (R[Net#b] - I[Net#b])) && (M[Net#b][I[Net#b]] < 0) ==> ((C[Net#c] - I[Net#c]) == 0);
  assume I[Net#b] == I[Net#a];
  assume ((M[Net#a][I[Net#a]] == 1) && (forall i: int :: 
    (I[Net#a] <= i) && (i < C[Net#a]) ==> (M[Net#a][i] == 1)
  )) || ((M[Net#a][I[Net#a]] == (-1)) && (forall i: int :: 
    (I[Net#a] <= i) && (i < C[Net#a]) ==> (M[Net#a][i] == (-1))
  ));
  assume R[Net#a] == C[Net#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == (2 * M[Net#a][idx$]))
  );
  assume R[Net#b] == (C[Net#c] + C[Net#d]);
  assume (0 < R[Net#b]) && (0 <= M[Net#b][R[Net#b] - 1]) ==> (M[Net#b][R[Net#b] - 1] == M[Net#c][C[Net#c] - 1]);
  assume (0 < R[Net#b]) && (M[Net#b][R[Net#b] - 1] < 0) ==> (M[Net#b][R[Net#b] - 1] == M[Net#d][C[Net#d] - 1]);
  C[Net#a] := C[Net#a] + 1;
  assume M[Net#a][I[Net#a]] == 1;
  assume (forall i: int :: 
    (I[Net#a] <= i) && (i < C[Net#a]) ==> (M[Net#a][i] == 1)
  );
  assert {:msg "32.15: Channel invariant might be falsified by network input (#38)"} I[Net#b] == (I[Net#d] + I[Net#c]);
  assert {:msg "33.15: Channel invariant might be falsified by network input (#39)"} (0 < (C[Net#a] - I[Net#a])) ==> ((M[Net#a][I[Net#a]] == 1) || (M[Net#a][I[Net#a]] == (-1)));
  assert {:msg "34.15: Channel invariant might be falsified by network input (#40)"} (0 < (R[Net#b] - I[Net#b])) && (M[Net#b][I[Net#b]] >= 0) ==> ((C[Net#d] - I[Net#d]) == 0);
  assert {:msg "35.15: Channel invariant might be falsified by network input (#41)"} (0 < (R[Net#b] - I[Net#b])) && (M[Net#b][I[Net#b]] < 0) ==> ((C[Net#c] - I[Net#c]) == 0);
  assert {:msg "Channel invariant might be falsified by network input (#42)"} I[Net#b] == I[Net#a];
  assert {:msg "Channel invariant might be falsified by network input (#43)"} ((M[Net#a][I[Net#a]] == 1) && (forall i: int :: 
    (I[Net#a] <= i) && (i < C[Net#a]) ==> (M[Net#a][i] == 1)
  )) || ((M[Net#a][I[Net#a]] == (-1)) && (forall i: int :: 
    (I[Net#a] <= i) && (i < C[Net#a]) ==> (M[Net#a][i] == (-1))
  ));
}
procedure Net#anon$3#exit#11()
  modifies C, R, M, I;
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
  assume I[Net#b] == (I[Net#d] + I[Net#c]);
  assume (0 < (C[Net#a] - I[Net#a])) ==> ((M[Net#a][I[Net#a]] == 1) || (M[Net#a][I[Net#a]] == (-1)));
  assume (0 < (R[Net#b] - I[Net#b])) && (M[Net#b][I[Net#b]] >= 0) ==> ((C[Net#d] - I[Net#d]) == 0);
  assume (0 < (R[Net#b] - I[Net#b])) && (M[Net#b][I[Net#b]] < 0) ==> ((C[Net#c] - I[Net#c]) == 0);
  assume I[Net#b] == I[Net#a];
  assume ((M[Net#a][I[Net#a]] == 1) && (forall i: int :: 
    (I[Net#a] <= i) && (i < C[Net#a]) ==> (M[Net#a][i] == 1)
  )) || ((M[Net#a][I[Net#a]] == (-1)) && (forall i: int :: 
    (I[Net#a] <= i) && (i < C[Net#a]) ==> (M[Net#a][i] == (-1))
  ));
  assume R[Net#a] == C[Net#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == (2 * M[Net#a][idx$]))
  );
  assume R[Net#b] == (C[Net#c] + C[Net#d]);
  assume (0 < R[Net#b]) && (0 <= M[Net#b][R[Net#b] - 1]) ==> (M[Net#b][R[Net#b] - 1] == M[Net#c][C[Net#c] - 1]);
  assume (0 < R[Net#b]) && (M[Net#b][R[Net#b] - 1] < 0) ==> (M[Net#b][R[Net#b] - 1] == M[Net#d][C[Net#d] - 1]);
  assume (C[Net#a] - I[Net#a]) == 1;
  assume M[Net#a][I[Net#a]] == 1;
  assume (forall i: int :: 
    (I[Net#a] <= i) && (i < C[Net#a]) ==> (M[Net#a][i] == 1)
  );
  assume !(1 <= (C[Net#a] - R[Net#a]));
  assume !((1 <= (C[Net#b] - R[Net#b])) && (0 <= M[Net#b][R[Net#b]]));
  assume !((1 <= (C[Net#b] - R[Net#b])) && (M[Net#b][R[Net#b]] < 0));
  assert {:msg "23.13: Network action postcondition might not hold (#44)"} M[Net#c][I[Net#c]] == (2 * M[Net#a][I[Net#a]]);
  R[Net#c] := R[Net#c] + 1;
  R[Net#d] := R[Net#d] + 0;
  I := R;
  assert {:msg "32.15: The network might not preserve the channel invariant (#45)"} I[Net#b] == (I[Net#d] + I[Net#c]);
  assert {:msg "33.15: The network might not preserve the channel invariant (#46)"} (0 < (C[Net#a] - I[Net#a])) ==> ((M[Net#a][I[Net#a]] == 1) || (M[Net#a][I[Net#a]] == (-1)));
  assert {:msg "34.15: The network might not preserve the channel invariant (#47)"} (0 < (R[Net#b] - I[Net#b])) && (M[Net#b][I[Net#b]] >= 0) ==> ((C[Net#d] - I[Net#d]) == 0);
  assert {:msg "35.15: The network might not preserve the channel invariant (#48)"} (0 < (R[Net#b] - I[Net#b])) && (M[Net#b][I[Net#b]] < 0) ==> ((C[Net#c] - I[Net#c]) == 0);
  assert {:msg "The network might not preserve the channel invariant (#49)"} I[Net#b] == I[Net#a];
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel a (#50)"} (C[Net#a] - R[Net#a]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel b (#51)"} (C[Net#b] - R[Net#b]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel c (#52)"} (C[Net#c] - R[Net#c]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel d (#53)"} (C[Net#d] - R[Net#d]) == 0;
}
procedure Net#anon$4#input#in#12()
  modifies C, R, M, I;
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
  assume (C[Net#a] - I[Net#a]) < 1;
  assume I[Net#b] == (I[Net#d] + I[Net#c]);
  assume (0 < (C[Net#a] - I[Net#a])) ==> ((M[Net#a][I[Net#a]] == 1) || (M[Net#a][I[Net#a]] == (-1)));
  assume (0 < (R[Net#b] - I[Net#b])) && (M[Net#b][I[Net#b]] >= 0) ==> ((C[Net#d] - I[Net#d]) == 0);
  assume (0 < (R[Net#b] - I[Net#b])) && (M[Net#b][I[Net#b]] < 0) ==> ((C[Net#c] - I[Net#c]) == 0);
  assume I[Net#b] == I[Net#a];
  assume ((M[Net#a][I[Net#a]] == 1) && (forall i: int :: 
    (I[Net#a] <= i) && (i < C[Net#a]) ==> (M[Net#a][i] == 1)
  )) || ((M[Net#a][I[Net#a]] == (-1)) && (forall i: int :: 
    (I[Net#a] <= i) && (i < C[Net#a]) ==> (M[Net#a][i] == (-1))
  ));
  assume R[Net#a] == C[Net#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == (2 * M[Net#a][idx$]))
  );
  assume R[Net#b] == (C[Net#c] + C[Net#d]);
  assume (0 < R[Net#b]) && (0 <= M[Net#b][R[Net#b] - 1]) ==> (M[Net#b][R[Net#b] - 1] == M[Net#c][C[Net#c] - 1]);
  assume (0 < R[Net#b]) && (M[Net#b][R[Net#b] - 1] < 0) ==> (M[Net#b][R[Net#b] - 1] == M[Net#d][C[Net#d] - 1]);
  C[Net#a] := C[Net#a] + 1;
  assume M[Net#a][I[Net#a]] == (-1);
  assume (forall i: int :: 
    (I[Net#a] <= i) && (i < C[Net#a]) ==> (M[Net#a][i] == (-1))
  );
  assert {:msg "32.15: Channel invariant might be falsified by network input (#54)"} I[Net#b] == (I[Net#d] + I[Net#c]);
  assert {:msg "33.15: Channel invariant might be falsified by network input (#55)"} (0 < (C[Net#a] - I[Net#a])) ==> ((M[Net#a][I[Net#a]] == 1) || (M[Net#a][I[Net#a]] == (-1)));
  assert {:msg "34.15: Channel invariant might be falsified by network input (#56)"} (0 < (R[Net#b] - I[Net#b])) && (M[Net#b][I[Net#b]] >= 0) ==> ((C[Net#d] - I[Net#d]) == 0);
  assert {:msg "35.15: Channel invariant might be falsified by network input (#57)"} (0 < (R[Net#b] - I[Net#b])) && (M[Net#b][I[Net#b]] < 0) ==> ((C[Net#c] - I[Net#c]) == 0);
  assert {:msg "Channel invariant might be falsified by network input (#58)"} I[Net#b] == I[Net#a];
  assert {:msg "Channel invariant might be falsified by network input (#59)"} ((M[Net#a][I[Net#a]] == 1) && (forall i: int :: 
    (I[Net#a] <= i) && (i < C[Net#a]) ==> (M[Net#a][i] == 1)
  )) || ((M[Net#a][I[Net#a]] == (-1)) && (forall i: int :: 
    (I[Net#a] <= i) && (i < C[Net#a]) ==> (M[Net#a][i] == (-1))
  ));
}
procedure Net#anon$4#exit#13()
  modifies C, R, M, I;
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
  assume I[Net#b] == (I[Net#d] + I[Net#c]);
  assume (0 < (C[Net#a] - I[Net#a])) ==> ((M[Net#a][I[Net#a]] == 1) || (M[Net#a][I[Net#a]] == (-1)));
  assume (0 < (R[Net#b] - I[Net#b])) && (M[Net#b][I[Net#b]] >= 0) ==> ((C[Net#d] - I[Net#d]) == 0);
  assume (0 < (R[Net#b] - I[Net#b])) && (M[Net#b][I[Net#b]] < 0) ==> ((C[Net#c] - I[Net#c]) == 0);
  assume I[Net#b] == I[Net#a];
  assume ((M[Net#a][I[Net#a]] == 1) && (forall i: int :: 
    (I[Net#a] <= i) && (i < C[Net#a]) ==> (M[Net#a][i] == 1)
  )) || ((M[Net#a][I[Net#a]] == (-1)) && (forall i: int :: 
    (I[Net#a] <= i) && (i < C[Net#a]) ==> (M[Net#a][i] == (-1))
  ));
  assume R[Net#a] == C[Net#b];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#b]) ==> (M[Net#b][idx$] == (2 * M[Net#a][idx$]))
  );
  assume R[Net#b] == (C[Net#c] + C[Net#d]);
  assume (0 < R[Net#b]) && (0 <= M[Net#b][R[Net#b] - 1]) ==> (M[Net#b][R[Net#b] - 1] == M[Net#c][C[Net#c] - 1]);
  assume (0 < R[Net#b]) && (M[Net#b][R[Net#b] - 1] < 0) ==> (M[Net#b][R[Net#b] - 1] == M[Net#d][C[Net#d] - 1]);
  assume (C[Net#a] - I[Net#a]) == 1;
  assume M[Net#a][I[Net#a]] == (-1);
  assume (forall i: int :: 
    (I[Net#a] <= i) && (i < C[Net#a]) ==> (M[Net#a][i] == (-1))
  );
  assume !(1 <= (C[Net#a] - R[Net#a]));
  assume !((1 <= (C[Net#b] - R[Net#b])) && (0 <= M[Net#b][R[Net#b]]));
  assume !((1 <= (C[Net#b] - R[Net#b])) && (M[Net#b][R[Net#b]] < 0));
  assert {:msg "29.13: Network action postcondition might not hold (#60)"} M[Net#d][I[Net#d]] == (2 * M[Net#a][I[Net#a]]);
  R[Net#c] := R[Net#c] + 0;
  R[Net#d] := R[Net#d] + 1;
  I := R;
  assert {:msg "32.15: The network might not preserve the channel invariant (#61)"} I[Net#b] == (I[Net#d] + I[Net#c]);
  assert {:msg "33.15: The network might not preserve the channel invariant (#62)"} (0 < (C[Net#a] - I[Net#a])) ==> ((M[Net#a][I[Net#a]] == 1) || (M[Net#a][I[Net#a]] == (-1)));
  assert {:msg "34.15: The network might not preserve the channel invariant (#63)"} (0 < (R[Net#b] - I[Net#b])) && (M[Net#b][I[Net#b]] >= 0) ==> ((C[Net#d] - I[Net#d]) == 0);
  assert {:msg "35.15: The network might not preserve the channel invariant (#64)"} (0 < (R[Net#b] - I[Net#b])) && (M[Net#b][I[Net#b]] < 0) ==> ((C[Net#c] - I[Net#c]) == 0);
  assert {:msg "The network might not preserve the channel invariant (#65)"} I[Net#b] == I[Net#a];
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel a (#66)"} (C[Net#a] - R[Net#a]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel b (#67)"} (C[Net#b] - R[Net#b]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel c (#68)"} (C[Net#c] - R[Net#c]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel d (#69)"} (C[Net#d] - R[Net#d]) == 0;
}

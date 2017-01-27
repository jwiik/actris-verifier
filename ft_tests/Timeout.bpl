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

// -- Sequence numbering for FT ----------------------------------
const unique sqn#: Field int;

// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

const unique Int.i: Field (int);
procedure Rep#init#0()
  modifies C, R, M, I, H;
{
  var in: Chan (Ref);
  var out: Chan (Ref);
  assume in != out;
  assume R[in] == 0;
  assume C[out] == 0;
  assert {:msg "Initialization might not establish the invariant (#0)"} R[in] == C[out];
  assert {:msg "Initialization might not establish the invariant (#1)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == M[in][idx$])
  );
}
procedure Rep#anon$0#1()
  modifies C, R, M, I, H;
{
  var in: Chan (Ref);
  var out: Chan (Ref);
  var in#0: Ref;
  assume in != out;
  assume 0 <= R[in];
  assume 0 <= C[out];
  assume R[in] == C[out];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == M[in][idx$])
  );
  in#0 := M[in][R[in]];
  R[in] := R[in] + 1;
  M[out][C[out]] := in#0;
  C[out] := C[out] + 1;
  assert {:msg "Action at 4.3 might not preserve invariant (#2)"} R[in] == C[out];
  assert {:msg "Action at 4.3 might not preserve invariant (#3)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == M[in][idx$])
  );
}
procedure Split#init#2()
  modifies C, R, M, I, H;
{
  var in: Chan (int);
  var out1: Chan (Ref);
  var out2: Chan (Ref);
  var y: Ref;
  var c: int;
  assume out1 != out2;
  assume R[in] == 0;
  assume C[out1] == 0;
  assume C[out2] == 0;
  c := 0;
  assert {:msg "8.13: Initialization might not establish the invariant (#4)"} c == C[out1];
  assert {:msg "9.20: Initialization might not establish the invariant (#5)"} R[in] == C[out1];
  assert {:msg "10.20: Initialization might not establish the invariant (#6)"} C[out1] == C[out2];
  assert {:msg "11.21: Initialization might not establish the invariant (#7)"} (forall i: int :: 
    (0 <= i) && (i < C[out1]) ==> (H[M[out1][i]][sqn#] == i)
  );
  assert {:msg "12.21: Initialization might not establish the invariant (#8)"} (forall i: int :: 
    (0 <= i) && (i < C[out1]) ==> (H[M[out1][i]][sqn#] == H[M[out2][i]][sqn#])
  );
}
procedure Split#anon$1#3()
  modifies C, R, M, I, H;
{
  var in: Chan (int);
  var out1: Chan (Ref);
  var out2: Chan (Ref);
  var y: Ref;
  var c: int;
  var in#0: int;
  assume out1 != out2;
  assume 0 <= R[in];
  assume 0 <= C[out1];
  assume 0 <= C[out2];
  assume c == C[out1];
  assume R[in] == C[out1];
  assume C[out1] == C[out2];
  assume (forall i: int :: 
    (0 <= i) && (i < C[out1]) ==> (H[M[out1][i]][sqn#] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[out1]) ==> (H[M[out1][i]][sqn#] == H[M[out2][i]][sqn#])
  );
  in#0 := M[in][R[in]];
  R[in] := R[in] + 1;
  H[y][sqn#] := c;
  c := c + 1;
  M[out1][C[out1]] := y;
  C[out1] := C[out1] + 1;
  M[out2][C[out2]] := y;
  C[out2] := C[out2] + 1;
  assert {:msg "8.13: Action at 15.3 might not preserve invariant (#9)"} c == C[out1];
  assert {:msg "9.20: Action at 15.3 might not preserve invariant (#10)"} R[in] == C[out1];
  assert {:msg "10.20: Action at 15.3 might not preserve invariant (#11)"} C[out1] == C[out2];
  assert {:msg "11.21: Action at 15.3 might not preserve invariant (#12)"} (forall i: int :: 
    (0 <= i) && (i < C[out1]) ==> (H[M[out1][i]][sqn#] == i)
  );
  assert {:msg "12.21: Action at 15.3 might not preserve invariant (#13)"} (forall i: int :: 
    (0 <= i) && (i < C[out1]) ==> (H[M[out1][i]][sqn#] == H[M[out2][i]][sqn#])
  );
}
procedure Adjudicator#init#4()
  modifies C, R, M, I, H;
{
  var x1: Chan (Ref);
  var x2: Chan (Ref);
  var y: Chan (Ref);
  var c: int;
  assume (x1 != x2) && (x1 != y) && (x2 != y);
  assume R[x1] == 0;
  assume R[x2] == 0;
  assume C[y] == 0;
  c := 0;
  assert {:msg "28.20: Initialization might not establish the invariant (#14)"} C[y] == R[x2];
  assert {:msg "29.20: Initialization might not establish the invariant (#15)"} R[x1] <= R[x2];
  assert {:msg "31.13: Initialization might not establish the invariant (#16)"} R[x2] == c;
  assert {:msg "32.21: Initialization might not establish the invariant (#17)"} (forall i: int :: 
    (0 <= i) && (i < R[x2]) ==> (H[M[x2][i]][sqn#] == i)
  );
  assert {:msg "33.21: Initialization might not establish the invariant (#18)"} (forall i: int :: 
    (0 <= i) && (i < C[y]) ==> (H[M[y][i]][sqn#] == i)
  );
}
procedure Adjudicator#normal#5()
  modifies C, R, M, I, H;
{
  var x1: Chan (Ref);
  var x2: Chan (Ref);
  var y: Chan (Ref);
  var c: int;
  var x1#0: Ref;
  var x2#0: Ref;
  assume (x1 != x2) && (x1 != y) && (x2 != y);
  assume 0 <= R[x1];
  assume 0 <= R[x2];
  assume 0 <= C[y];
  assume C[y] == R[x2];
  assume R[x1] <= R[x2];
  assume R[x2] == c;
  assume (forall i: int :: 
    (0 <= i) && (i < R[x2]) ==> (H[M[x2][i]][sqn#] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[y]) ==> (H[M[y][i]][sqn#] == i)
  );
  x1#0 := M[x1][R[x1]];
  R[x1] := R[x1] + 1;
  x2#0 := M[x2][R[x2]];
  R[x2] := R[x2] + 1;
  assume !((1 <= (C[x2] - R[x2])) && (H[x2#0][sqn#] == c));
  assume !((1 <= (C[x1] - R[x1])) && (H[x1#0][sqn#] < c));
  assume (H[x1#0][sqn#] == H[x2#0][sqn#]) && (H[x1#0][sqn#] == c);
  c := c + 1;
  M[y][C[y]] := x1#0;
  C[y] := C[y] + 1;
  assert {:msg "28.20: Action at 37.3 might not preserve invariant (#19)"} C[y] == R[x2];
  assert {:msg "29.20: Action at 37.3 might not preserve invariant (#20)"} R[x1] <= R[x2];
  assert {:msg "31.13: Action at 37.3 might not preserve invariant (#21)"} R[x2] == c;
  assert {:msg "32.21: Action at 37.3 might not preserve invariant (#22)"} (forall i: int :: 
    (0 <= i) && (i < R[x2]) ==> (H[M[x2][i]][sqn#] == i)
  );
  assert {:msg "33.21: Action at 37.3 might not preserve invariant (#23)"} (forall i: int :: 
    (0 <= i) && (i < C[y]) ==> (H[M[y][i]][sqn#] == i)
  );
}
procedure Adjudicator#timeout#6()
  modifies C, R, M, I, H;
{
  var x1: Chan (Ref);
  var x2: Chan (Ref);
  var y: Chan (Ref);
  var c: int;
  var x1#0: Ref;
  var x2#0: Ref;
  assume (x1 != x2) && (x1 != y) && (x2 != y);
  assume 0 <= R[x1];
  assume 0 <= R[x2];
  assume 0 <= C[y];
  assume C[y] == R[x2];
  assume R[x1] <= R[x2];
  assume R[x2] == c;
  assume (forall i: int :: 
    (0 <= i) && (i < R[x2]) ==> (H[M[x2][i]][sqn#] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[y]) ==> (H[M[y][i]][sqn#] == i)
  );
  x2#0 := M[x2][R[x2]];
  R[x2] := R[x2] + 1;
  assume !((1 <= (C[x1] - R[x1])) && (H[x1#0][sqn#] < c));
  assume H[x2#0][sqn#] == c;
  c := c + 1;
  M[y][C[y]] := x2#0;
  C[y] := C[y] + 1;
  assert {:msg "28.20: Action at 42.3 might not preserve invariant (#24)"} C[y] == R[x2];
  assert {:msg "29.20: Action at 42.3 might not preserve invariant (#25)"} R[x1] <= R[x2];
  assert {:msg "31.13: Action at 42.3 might not preserve invariant (#26)"} R[x2] == c;
  assert {:msg "32.21: Action at 42.3 might not preserve invariant (#27)"} (forall i: int :: 
    (0 <= i) && (i < R[x2]) ==> (H[M[x2][i]][sqn#] == i)
  );
  assert {:msg "33.21: Action at 42.3 might not preserve invariant (#28)"} (forall i: int :: 
    (0 <= i) && (i < C[y]) ==> (H[M[y][i]][sqn#] == i)
  );
}
procedure Adjudicator#readoff#7()
  modifies C, R, M, I, H;
{
  var x1: Chan (Ref);
  var x2: Chan (Ref);
  var y: Chan (Ref);
  var c: int;
  var x1#0: Ref;
  var x2#0: Ref;
  assume (x1 != x2) && (x1 != y) && (x2 != y);
  assume 0 <= R[x1];
  assume 0 <= R[x2];
  assume 0 <= C[y];
  assume C[y] == R[x2];
  assume R[x1] <= R[x2];
  assume R[x2] == c;
  assume (forall i: int :: 
    (0 <= i) && (i < R[x2]) ==> (H[M[x2][i]][sqn#] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[y]) ==> (H[M[y][i]][sqn#] == i)
  );
  x1#0 := M[x1][R[x1]];
  R[x1] := R[x1] + 1;
  assume R[x1] < R[x2];
  assume H[x1#0][sqn#] < c;
  assert {:msg "28.20: Action at 47.3 might not preserve invariant (#29)"} C[y] == R[x2];
  assert {:msg "29.20: Action at 47.3 might not preserve invariant (#30)"} R[x1] <= R[x2];
  assert {:msg "31.13: Action at 47.3 might not preserve invariant (#31)"} R[x2] == c;
  assert {:msg "32.21: Action at 47.3 might not preserve invariant (#32)"} (forall i: int :: 
    (0 <= i) && (i < R[x2]) ==> (H[M[x2][i]][sqn#] == i)
  );
  assert {:msg "33.21: Action at 47.3 might not preserve invariant (#33)"} (forall i: int :: 
    (0 <= i) && (i < C[y]) ==> (H[M[y][i]][sqn#] == i)
  );
}
procedure Adjudicator##GuardWD#8()
  modifies C, R, M, I, H;
{
  var x1: Chan (Ref);
  var x2: Chan (Ref);
  var y: Chan (Ref);
  var c: int;
  var x1#0: Ref;
  var x2#0: Ref;
  assume (x1 != x2) && (x1 != y) && (x2 != y);
  assert {:msg "26.1: The actions 'normal' and 'timeout' of actor 'Adjudicator' might not have mutually exclusive guards (#34)"} !(true && (!((1 <= (C[x2] - R[x2])) && (H[x2#0][sqn#] == c))) && (!((1 <= (C[x1] - R[x1])) && (H[x1#0][sqn#] < c))) && (1 <= (C[x1] - R[x1])) && (1 <= (C[x2] - R[x2])) && (H[x1#0][sqn#] == H[x2#0][sqn#]) && (H[x1#0][sqn#] == c) && true && (!((1 <= (C[x1] - R[x1])) && (H[x1#0][sqn#] < c))) && (1 <= (C[x2] - R[x2])) && (H[x2#0][sqn#] == c));
  assert {:msg "26.1: The actions 'normal' and 'readoff' of actor 'Adjudicator' might not have mutually exclusive guards (#35)"} !(true && (!((1 <= (C[x2] - R[x2])) && (H[x2#0][sqn#] == c))) && (!((1 <= (C[x1] - R[x1])) && (H[x1#0][sqn#] < c))) && (1 <= (C[x1] - R[x1])) && (1 <= (C[x2] - R[x2])) && (H[x1#0][sqn#] == H[x2#0][sqn#]) && (H[x1#0][sqn#] == c) && true && (1 <= (C[x1] - R[x1])) && (H[x1#0][sqn#] < c));
  assert {:msg "26.1: The actions 'timeout' and 'readoff' of actor 'Adjudicator' might not have mutually exclusive guards (#36)"} !(true && (!((1 <= (C[x1] - R[x1])) && (H[x1#0][sqn#] < c))) && (1 <= (C[x2] - R[x2])) && (H[x2#0][sqn#] == c) && true && (1 <= (C[x1] - R[x1])) && (H[x1#0][sqn#] < c));
}
procedure Net#init#9()
  modifies C, R, M, I, H;
{
  var Net#spl: Actor;
  var Net#pri: Actor;
  var Net#sec: Actor;
  var Net#adj: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (Ref);
  var Net#c: Chan (Ref);
  var Net#d: Chan (Ref);
  var Net#e: Chan (Ref);
  var Net#f: Chan (Ref);
  var AV#spl#y: Ref;
  var AV#spl#c: int;
  var AV#adj#c: int;
  assume (Net#spl != Net#pri) && (Net#spl != Net#sec) && (Net#spl != Net#adj) && (Net#pri != Net#sec) && (Net#pri != Net#adj) && (Net#sec != Net#adj);
  assume (Net#b != Net#c) && (Net#b != Net#d) && (Net#b != Net#e) && (Net#b != Net#f) && (Net#c != Net#d) && (Net#c != Net#e) && (Net#c != Net#f) && (Net#d != Net#e) && (Net#d != Net#f) && (Net#e != Net#f);
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
  assume 0 <= I[Net#e];
  assume I[Net#e] <= R[Net#e];
  assume R[Net#e] <= C[Net#e];
  assume 0 <= I[Net#f];
  assume I[Net#f] <= R[Net#f];
  assume R[Net#f] <= C[Net#f];
  assume I[Net#f] == R[Net#f];
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
  assume C[Net#f] == 0;
  assume R[Net#f] == 0;
  assert {:msg "68.15: Initialization of network 'Net' might not establish the channel invariant (#37)"} I[Net#f] == I[Net#d];
  assert {:msg "69.15: Initialization of network 'Net' might not establish the channel invariant (#38)"} I[Net#f] == I[Net#e];
  assert {:msg "Initialization of network 'Net' might not establish the channel invariant (#39)"} I[Net#d] == I[Net#b];
  assert {:msg "Initialization of network 'Net' might not establish the channel invariant (#40)"} I[Net#e] == I[Net#c];
  I := R;
  assert {:msg "Initialization of network 'Net' might not establish the network invariant: Unread tokens might be left on channel a (#41)"} (C[Net#a] - R[Net#a]) == 0;
  assert {:msg "Initialization of network 'Net' might not establish the network invariant: Unread tokens might be left on channel b (#42)"} (C[Net#b] - R[Net#b]) == 0;
  assert {:msg "Initialization of network 'Net' might not establish the network invariant: Unread tokens might be left on channel c (#43)"} (C[Net#c] - R[Net#c]) == 0;
  assert {:msg "Initialization of network 'Net' might not establish the network invariant: Unread tokens might be left on channel d (#44)"} (C[Net#d] - R[Net#d]) == 0;
  assert {:msg "Initialization of network 'Net' might not establish the network invariant: Unread tokens might be left on channel e (#45)"} (C[Net#e] - R[Net#e]) == 0;
  assert {:msg "Initialization of network 'Net' might not establish the network invariant: Unread tokens might be left on channel f (#46)"} (C[Net#f] - R[Net#f]) == 0;
}
procedure Net##Split#anon$1#10()
  modifies C, R, M, I, H;
{
  var Net#spl: Actor;
  var Net#pri: Actor;
  var Net#sec: Actor;
  var Net#adj: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (Ref);
  var Net#c: Chan (Ref);
  var Net#d: Chan (Ref);
  var Net#e: Chan (Ref);
  var Net#f: Chan (Ref);
  var AV#spl#y: Ref;
  var AV#spl#c: int;
  var AV#adj#c: int;
  var in#i: int;
  assume (Net#spl != Net#pri) && (Net#spl != Net#sec) && (Net#spl != Net#adj) && (Net#pri != Net#sec) && (Net#pri != Net#adj) && (Net#sec != Net#adj);
  assume (Net#b != Net#c) && (Net#b != Net#d) && (Net#b != Net#e) && (Net#b != Net#f) && (Net#c != Net#d) && (Net#c != Net#e) && (Net#c != Net#f) && (Net#d != Net#e) && (Net#d != Net#f) && (Net#e != Net#f);
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
  assume 0 <= I[Net#e];
  assume I[Net#e] <= R[Net#e];
  assume R[Net#e] <= C[Net#e];
  assume 0 <= I[Net#f];
  assume I[Net#f] <= R[Net#f];
  assume R[Net#f] <= C[Net#f];
  assume I[Net#f] == R[Net#f];
  assume I[Net#f] == I[Net#d];
  assume I[Net#f] == I[Net#e];
  assume I[Net#d] == I[Net#b];
  assume I[Net#e] == I[Net#c];
  assume R[Net#a] == C[Net#b];
  assume C[Net#b] == C[Net#c];
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#b]) ==> (H[M[Net#b][i]][sqn#] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#b]) ==> (H[M[Net#b][i]][sqn#] == H[M[Net#c][i]][sqn#])
  );
  assume R[Net#b] == C[Net#d];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assume R[Net#c] == C[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assume C[Net#f] == R[Net#e];
  assume R[Net#d] <= R[Net#e];
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (H[M[Net#e][i]][sqn#] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#f]) ==> (H[M[Net#f][i]][sqn#] == i)
  );
  assume 1 <= (C[Net#a] - R[Net#a]);
  in#i := M[Net#a][R[Net#a]];
  R[Net#a] := R[Net#a] + 1;
  havoc H;
  assume (forall<a> r$: Ref, f$: Field a :: 
    (H[r$][f$] == old(H)[r$][f$]) || ((r$ == AV#spl#y) && (f$ == sqn#))
  );
  havoc AV#spl#c;
  M[Net#b][C[Net#b]] := AV#spl#y;
  C[Net#b] := C[Net#b] + 1;
  M[Net#c][C[Net#c]] := AV#spl#y;
  C[Net#c] := C[Net#c] + 1;
  assume R[Net#a] == C[Net#b];
  assume C[Net#b] == C[Net#c];
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#b]) ==> (H[M[Net#b][i]][sqn#] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#b]) ==> (H[M[Net#b][i]][sqn#] == H[M[Net#c][i]][sqn#])
  );
  assume R[Net#b] == C[Net#d];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assume R[Net#c] == C[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assume C[Net#f] == R[Net#e];
  assume R[Net#d] <= R[Net#e];
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (H[M[Net#e][i]][sqn#] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#f]) ==> (H[M[Net#f][i]][sqn#] == i)
  );
  assert {:msg "68.15: Action at 15.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#47)"} I[Net#f] == I[Net#d];
  assert {:msg "69.15: Action at 15.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#48)"} I[Net#f] == I[Net#e];
  assert {:msg "Action at 15.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#49)"} I[Net#d] == I[Net#b];
  assert {:msg "Action at 15.3 ('anon$1') for actor instance 'spl' might not preserve the channel invariant (#50)"} I[Net#e] == I[Net#c];
}
procedure Net##Rep#anon$0#11()
  modifies C, R, M, I, H;
{
  var Net#spl: Actor;
  var Net#pri: Actor;
  var Net#sec: Actor;
  var Net#adj: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (Ref);
  var Net#c: Chan (Ref);
  var Net#d: Chan (Ref);
  var Net#e: Chan (Ref);
  var Net#f: Chan (Ref);
  var AV#spl#y: Ref;
  var AV#spl#c: int;
  var AV#adj#c: int;
  var in#i: Ref;
  assume (Net#spl != Net#pri) && (Net#spl != Net#sec) && (Net#spl != Net#adj) && (Net#pri != Net#sec) && (Net#pri != Net#adj) && (Net#sec != Net#adj);
  assume (Net#b != Net#c) && (Net#b != Net#d) && (Net#b != Net#e) && (Net#b != Net#f) && (Net#c != Net#d) && (Net#c != Net#e) && (Net#c != Net#f) && (Net#d != Net#e) && (Net#d != Net#f) && (Net#e != Net#f);
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
  assume 0 <= I[Net#e];
  assume I[Net#e] <= R[Net#e];
  assume R[Net#e] <= C[Net#e];
  assume 0 <= I[Net#f];
  assume I[Net#f] <= R[Net#f];
  assume R[Net#f] <= C[Net#f];
  assume I[Net#f] == R[Net#f];
  assume I[Net#f] == I[Net#d];
  assume I[Net#f] == I[Net#e];
  assume I[Net#d] == I[Net#b];
  assume I[Net#e] == I[Net#c];
  assume R[Net#a] == C[Net#b];
  assume C[Net#b] == C[Net#c];
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#b]) ==> (H[M[Net#b][i]][sqn#] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#b]) ==> (H[M[Net#b][i]][sqn#] == H[M[Net#c][i]][sqn#])
  );
  assume R[Net#b] == C[Net#d];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assume R[Net#c] == C[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assume C[Net#f] == R[Net#e];
  assume R[Net#d] <= R[Net#e];
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (H[M[Net#e][i]][sqn#] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#f]) ==> (H[M[Net#f][i]][sqn#] == i)
  );
  assume 1 <= (C[Net#b] - R[Net#b]);
  in#i := M[Net#b][R[Net#b]];
  R[Net#b] := R[Net#b] + 1;
  M[Net#d][C[Net#d]] := in#i;
  C[Net#d] := C[Net#d] + 1;
  assume R[Net#a] == C[Net#b];
  assume C[Net#b] == C[Net#c];
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#b]) ==> (H[M[Net#b][i]][sqn#] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#b]) ==> (H[M[Net#b][i]][sqn#] == H[M[Net#c][i]][sqn#])
  );
  assume R[Net#b] == C[Net#d];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assume R[Net#c] == C[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assume C[Net#f] == R[Net#e];
  assume R[Net#d] <= R[Net#e];
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (H[M[Net#e][i]][sqn#] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#f]) ==> (H[M[Net#f][i]][sqn#] == i)
  );
  assert {:msg "68.15: Action at 4.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#51)"} I[Net#f] == I[Net#d];
  assert {:msg "69.15: Action at 4.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#52)"} I[Net#f] == I[Net#e];
  assert {:msg "Action at 4.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#53)"} I[Net#d] == I[Net#b];
  assert {:msg "Action at 4.3 ('anon$0') for actor instance 'pri' might not preserve the channel invariant (#54)"} I[Net#e] == I[Net#c];
}
procedure Net##Rep#anon$0#12()
  modifies C, R, M, I, H;
{
  var Net#spl: Actor;
  var Net#pri: Actor;
  var Net#sec: Actor;
  var Net#adj: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (Ref);
  var Net#c: Chan (Ref);
  var Net#d: Chan (Ref);
  var Net#e: Chan (Ref);
  var Net#f: Chan (Ref);
  var AV#spl#y: Ref;
  var AV#spl#c: int;
  var AV#adj#c: int;
  var in#i: Ref;
  assume (Net#spl != Net#pri) && (Net#spl != Net#sec) && (Net#spl != Net#adj) && (Net#pri != Net#sec) && (Net#pri != Net#adj) && (Net#sec != Net#adj);
  assume (Net#b != Net#c) && (Net#b != Net#d) && (Net#b != Net#e) && (Net#b != Net#f) && (Net#c != Net#d) && (Net#c != Net#e) && (Net#c != Net#f) && (Net#d != Net#e) && (Net#d != Net#f) && (Net#e != Net#f);
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
  assume 0 <= I[Net#e];
  assume I[Net#e] <= R[Net#e];
  assume R[Net#e] <= C[Net#e];
  assume 0 <= I[Net#f];
  assume I[Net#f] <= R[Net#f];
  assume R[Net#f] <= C[Net#f];
  assume I[Net#f] == R[Net#f];
  assume I[Net#f] == I[Net#d];
  assume I[Net#f] == I[Net#e];
  assume I[Net#d] == I[Net#b];
  assume I[Net#e] == I[Net#c];
  assume R[Net#a] == C[Net#b];
  assume C[Net#b] == C[Net#c];
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#b]) ==> (H[M[Net#b][i]][sqn#] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#b]) ==> (H[M[Net#b][i]][sqn#] == H[M[Net#c][i]][sqn#])
  );
  assume R[Net#b] == C[Net#d];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assume R[Net#c] == C[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assume C[Net#f] == R[Net#e];
  assume R[Net#d] <= R[Net#e];
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (H[M[Net#e][i]][sqn#] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#f]) ==> (H[M[Net#f][i]][sqn#] == i)
  );
  assume 1 <= (C[Net#c] - R[Net#c]);
  in#i := M[Net#c][R[Net#c]];
  R[Net#c] := R[Net#c] + 1;
  M[Net#e][C[Net#e]] := in#i;
  C[Net#e] := C[Net#e] + 1;
  assume R[Net#a] == C[Net#b];
  assume C[Net#b] == C[Net#c];
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#b]) ==> (H[M[Net#b][i]][sqn#] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#b]) ==> (H[M[Net#b][i]][sqn#] == H[M[Net#c][i]][sqn#])
  );
  assume R[Net#b] == C[Net#d];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assume R[Net#c] == C[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assume C[Net#f] == R[Net#e];
  assume R[Net#d] <= R[Net#e];
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (H[M[Net#e][i]][sqn#] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#f]) ==> (H[M[Net#f][i]][sqn#] == i)
  );
  assert {:msg "68.15: Action at 4.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#55)"} I[Net#f] == I[Net#d];
  assert {:msg "69.15: Action at 4.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#56)"} I[Net#f] == I[Net#e];
  assert {:msg "Action at 4.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#57)"} I[Net#d] == I[Net#b];
  assert {:msg "Action at 4.3 ('anon$0') for actor instance 'sec' might not preserve the channel invariant (#58)"} I[Net#e] == I[Net#c];
}
procedure Net##Adjudicator#normal#13()
  modifies C, R, M, I, H;
{
  var Net#spl: Actor;
  var Net#pri: Actor;
  var Net#sec: Actor;
  var Net#adj: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (Ref);
  var Net#c: Chan (Ref);
  var Net#d: Chan (Ref);
  var Net#e: Chan (Ref);
  var Net#f: Chan (Ref);
  var AV#spl#y: Ref;
  var AV#spl#c: int;
  var AV#adj#c: int;
  var x1#i: Ref;
  var x2#j: Ref;
  assume (Net#spl != Net#pri) && (Net#spl != Net#sec) && (Net#spl != Net#adj) && (Net#pri != Net#sec) && (Net#pri != Net#adj) && (Net#sec != Net#adj);
  assume (Net#b != Net#c) && (Net#b != Net#d) && (Net#b != Net#e) && (Net#b != Net#f) && (Net#c != Net#d) && (Net#c != Net#e) && (Net#c != Net#f) && (Net#d != Net#e) && (Net#d != Net#f) && (Net#e != Net#f);
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
  assume 0 <= I[Net#e];
  assume I[Net#e] <= R[Net#e];
  assume R[Net#e] <= C[Net#e];
  assume 0 <= I[Net#f];
  assume I[Net#f] <= R[Net#f];
  assume R[Net#f] <= C[Net#f];
  assume I[Net#f] == R[Net#f];
  assume I[Net#f] == I[Net#d];
  assume I[Net#f] == I[Net#e];
  assume I[Net#d] == I[Net#b];
  assume I[Net#e] == I[Net#c];
  assume R[Net#a] == C[Net#b];
  assume C[Net#b] == C[Net#c];
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#b]) ==> (H[M[Net#b][i]][sqn#] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#b]) ==> (H[M[Net#b][i]][sqn#] == H[M[Net#c][i]][sqn#])
  );
  assume R[Net#b] == C[Net#d];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assume R[Net#c] == C[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assume C[Net#f] == R[Net#e];
  assume R[Net#d] <= R[Net#e];
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (H[M[Net#e][i]][sqn#] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#f]) ==> (H[M[Net#f][i]][sqn#] == i)
  );
  assume (1 <= (C[Net#d] - R[Net#d])) && (1 <= (C[Net#e] - R[Net#e])) && (H[M[Net#d][R[Net#d]]][sqn#] == H[M[Net#e][R[Net#e]]][sqn#]) && (H[M[Net#d][R[Net#d]]][sqn#] == AV#adj#c);
  x1#i := M[Net#d][R[Net#d]];
  R[Net#d] := R[Net#d] + 1;
  x2#j := M[Net#e][R[Net#e]];
  R[Net#e] := R[Net#e] + 1;
  havoc AV#adj#c;
  M[Net#f][C[Net#f]] := x1#i;
  C[Net#f] := C[Net#f] + 1;
  assume R[Net#a] == C[Net#b];
  assume C[Net#b] == C[Net#c];
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#b]) ==> (H[M[Net#b][i]][sqn#] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#b]) ==> (H[M[Net#b][i]][sqn#] == H[M[Net#c][i]][sqn#])
  );
  assume R[Net#b] == C[Net#d];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assume R[Net#c] == C[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assume C[Net#f] == R[Net#e];
  assume R[Net#d] <= R[Net#e];
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (H[M[Net#e][i]][sqn#] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#f]) ==> (H[M[Net#f][i]][sqn#] == i)
  );
  assert {:msg "68.15: Action at 37.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#59)"} I[Net#f] == I[Net#d];
  assert {:msg "69.15: Action at 37.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#60)"} I[Net#f] == I[Net#e];
  assert {:msg "Action at 37.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#61)"} I[Net#d] == I[Net#b];
  assert {:msg "Action at 37.3 ('normal') for actor instance 'adj' might not preserve the channel invariant (#62)"} I[Net#e] == I[Net#c];
}
procedure Net##Adjudicator#timeout#14()
  modifies C, R, M, I, H;
{
  var Net#spl: Actor;
  var Net#pri: Actor;
  var Net#sec: Actor;
  var Net#adj: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (Ref);
  var Net#c: Chan (Ref);
  var Net#d: Chan (Ref);
  var Net#e: Chan (Ref);
  var Net#f: Chan (Ref);
  var AV#spl#y: Ref;
  var AV#spl#c: int;
  var AV#adj#c: int;
  var x2#j: Ref;
  assume (Net#spl != Net#pri) && (Net#spl != Net#sec) && (Net#spl != Net#adj) && (Net#pri != Net#sec) && (Net#pri != Net#adj) && (Net#sec != Net#adj);
  assume (Net#b != Net#c) && (Net#b != Net#d) && (Net#b != Net#e) && (Net#b != Net#f) && (Net#c != Net#d) && (Net#c != Net#e) && (Net#c != Net#f) && (Net#d != Net#e) && (Net#d != Net#f) && (Net#e != Net#f);
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
  assume 0 <= I[Net#e];
  assume I[Net#e] <= R[Net#e];
  assume R[Net#e] <= C[Net#e];
  assume 0 <= I[Net#f];
  assume I[Net#f] <= R[Net#f];
  assume R[Net#f] <= C[Net#f];
  assume I[Net#f] == R[Net#f];
  assume I[Net#f] == I[Net#d];
  assume I[Net#f] == I[Net#e];
  assume I[Net#d] == I[Net#b];
  assume I[Net#e] == I[Net#c];
  assume R[Net#a] == C[Net#b];
  assume C[Net#b] == C[Net#c];
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#b]) ==> (H[M[Net#b][i]][sqn#] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#b]) ==> (H[M[Net#b][i]][sqn#] == H[M[Net#c][i]][sqn#])
  );
  assume R[Net#b] == C[Net#d];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assume R[Net#c] == C[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assume C[Net#f] == R[Net#e];
  assume R[Net#d] <= R[Net#e];
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (H[M[Net#e][i]][sqn#] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#f]) ==> (H[M[Net#f][i]][sqn#] == i)
  );
  assume (1 <= (C[Net#e] - R[Net#e])) && (H[M[Net#e][R[Net#e]]][sqn#] == AV#adj#c);
  x2#j := M[Net#e][R[Net#e]];
  R[Net#e] := R[Net#e] + 1;
  havoc AV#adj#c;
  M[Net#f][C[Net#f]] := x2#j;
  C[Net#f] := C[Net#f] + 1;
  assume R[Net#a] == C[Net#b];
  assume C[Net#b] == C[Net#c];
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#b]) ==> (H[M[Net#b][i]][sqn#] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#b]) ==> (H[M[Net#b][i]][sqn#] == H[M[Net#c][i]][sqn#])
  );
  assume R[Net#b] == C[Net#d];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assume R[Net#c] == C[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assume C[Net#f] == R[Net#e];
  assume R[Net#d] <= R[Net#e];
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (H[M[Net#e][i]][sqn#] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#f]) ==> (H[M[Net#f][i]][sqn#] == i)
  );
  assert {:msg "68.15: Action at 42.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#63)"} I[Net#f] == I[Net#d];
  assert {:msg "69.15: Action at 42.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#64)"} I[Net#f] == I[Net#e];
  assert {:msg "Action at 42.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#65)"} I[Net#d] == I[Net#b];
  assert {:msg "Action at 42.3 ('timeout') for actor instance 'adj' might not preserve the channel invariant (#66)"} I[Net#e] == I[Net#c];
}
procedure Net##Adjudicator#readoff#15()
  modifies C, R, M, I, H;
{
  var Net#spl: Actor;
  var Net#pri: Actor;
  var Net#sec: Actor;
  var Net#adj: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (Ref);
  var Net#c: Chan (Ref);
  var Net#d: Chan (Ref);
  var Net#e: Chan (Ref);
  var Net#f: Chan (Ref);
  var AV#spl#y: Ref;
  var AV#spl#c: int;
  var AV#adj#c: int;
  var x1#i: Ref;
  assume (Net#spl != Net#pri) && (Net#spl != Net#sec) && (Net#spl != Net#adj) && (Net#pri != Net#sec) && (Net#pri != Net#adj) && (Net#sec != Net#adj);
  assume (Net#b != Net#c) && (Net#b != Net#d) && (Net#b != Net#e) && (Net#b != Net#f) && (Net#c != Net#d) && (Net#c != Net#e) && (Net#c != Net#f) && (Net#d != Net#e) && (Net#d != Net#f) && (Net#e != Net#f);
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
  assume 0 <= I[Net#e];
  assume I[Net#e] <= R[Net#e];
  assume R[Net#e] <= C[Net#e];
  assume 0 <= I[Net#f];
  assume I[Net#f] <= R[Net#f];
  assume R[Net#f] <= C[Net#f];
  assume I[Net#f] == R[Net#f];
  assume I[Net#f] == I[Net#d];
  assume I[Net#f] == I[Net#e];
  assume I[Net#d] == I[Net#b];
  assume I[Net#e] == I[Net#c];
  assume R[Net#a] == C[Net#b];
  assume C[Net#b] == C[Net#c];
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#b]) ==> (H[M[Net#b][i]][sqn#] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#b]) ==> (H[M[Net#b][i]][sqn#] == H[M[Net#c][i]][sqn#])
  );
  assume R[Net#b] == C[Net#d];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assume R[Net#c] == C[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assume C[Net#f] == R[Net#e];
  assume R[Net#d] <= R[Net#e];
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (H[M[Net#e][i]][sqn#] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#f]) ==> (H[M[Net#f][i]][sqn#] == i)
  );
  assume (1 <= (C[Net#d] - R[Net#d])) && (H[M[Net#d][R[Net#d]]][sqn#] < AV#adj#c);
  x1#i := M[Net#d][R[Net#d]];
  R[Net#d] := R[Net#d] + 1;
  assert {:msg "49.14: Precondition might not hold for instance at 75.5 (#67)"} R[Net#d] < R[Net#e];
  assume R[Net#a] == C[Net#b];
  assume C[Net#b] == C[Net#c];
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#b]) ==> (H[M[Net#b][i]][sqn#] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#b]) ==> (H[M[Net#b][i]][sqn#] == H[M[Net#c][i]][sqn#])
  );
  assume R[Net#b] == C[Net#d];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assume R[Net#c] == C[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assume C[Net#f] == R[Net#e];
  assume R[Net#d] <= R[Net#e];
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (H[M[Net#e][i]][sqn#] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#f]) ==> (H[M[Net#f][i]][sqn#] == i)
  );
  assert {:msg "68.15: Action at 47.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#68)"} I[Net#f] == I[Net#d];
  assert {:msg "69.15: Action at 47.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#69)"} I[Net#f] == I[Net#e];
  assert {:msg "Action at 47.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#70)"} I[Net#d] == I[Net#b];
  assert {:msg "Action at 47.3 ('readoff') for actor instance 'adj' might not preserve the channel invariant (#71)"} I[Net#e] == I[Net#c];
}
procedure Net#anon$4#input#in#16()
  modifies C, R, M, I, H;
{
  var Net#spl: Actor;
  var Net#pri: Actor;
  var Net#sec: Actor;
  var Net#adj: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (Ref);
  var Net#c: Chan (Ref);
  var Net#d: Chan (Ref);
  var Net#e: Chan (Ref);
  var Net#f: Chan (Ref);
  var AV#spl#y: Ref;
  var AV#spl#c: int;
  var AV#adj#c: int;
  assume (Net#spl != Net#pri) && (Net#spl != Net#sec) && (Net#spl != Net#adj) && (Net#pri != Net#sec) && (Net#pri != Net#adj) && (Net#sec != Net#adj);
  assume (Net#b != Net#c) && (Net#b != Net#d) && (Net#b != Net#e) && (Net#b != Net#f) && (Net#c != Net#d) && (Net#c != Net#e) && (Net#c != Net#f) && (Net#d != Net#e) && (Net#d != Net#f) && (Net#e != Net#f);
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
  assume 0 <= I[Net#e];
  assume I[Net#e] <= R[Net#e];
  assume R[Net#e] <= C[Net#e];
  assume 0 <= I[Net#f];
  assume I[Net#f] <= R[Net#f];
  assume R[Net#f] <= C[Net#f];
  assume I[Net#f] == R[Net#f];
  assume (C[Net#a] - I[Net#a]) < 1;
  assume I[Net#f] == I[Net#d];
  assume I[Net#f] == I[Net#e];
  assume I[Net#d] == I[Net#b];
  assume I[Net#e] == I[Net#c];
  assume R[Net#a] == C[Net#b];
  assume C[Net#b] == C[Net#c];
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#b]) ==> (H[M[Net#b][i]][sqn#] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#b]) ==> (H[M[Net#b][i]][sqn#] == H[M[Net#c][i]][sqn#])
  );
  assume R[Net#b] == C[Net#d];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assume R[Net#c] == C[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assume C[Net#f] == R[Net#e];
  assume R[Net#d] <= R[Net#e];
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (H[M[Net#e][i]][sqn#] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#f]) ==> (H[M[Net#f][i]][sqn#] == i)
  );
  C[Net#a] := C[Net#a] + 1;
  assert {:msg "68.15: Channel invariant might be falsified by network input (#72)"} I[Net#f] == I[Net#d];
  assert {:msg "69.15: Channel invariant might be falsified by network input (#73)"} I[Net#f] == I[Net#e];
  assert {:msg "Channel invariant might be falsified by network input (#74)"} I[Net#d] == I[Net#b];
  assert {:msg "Channel invariant might be falsified by network input (#75)"} I[Net#e] == I[Net#c];
}
procedure Net#anon$4#exit#17()
  modifies C, R, M, I, H;
{
  var Net#spl: Actor;
  var Net#pri: Actor;
  var Net#sec: Actor;
  var Net#adj: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (Ref);
  var Net#c: Chan (Ref);
  var Net#d: Chan (Ref);
  var Net#e: Chan (Ref);
  var Net#f: Chan (Ref);
  var AV#spl#y: Ref;
  var AV#spl#c: int;
  var AV#adj#c: int;
  assume (Net#spl != Net#pri) && (Net#spl != Net#sec) && (Net#spl != Net#adj) && (Net#pri != Net#sec) && (Net#pri != Net#adj) && (Net#sec != Net#adj);
  assume (Net#b != Net#c) && (Net#b != Net#d) && (Net#b != Net#e) && (Net#b != Net#f) && (Net#c != Net#d) && (Net#c != Net#e) && (Net#c != Net#f) && (Net#d != Net#e) && (Net#d != Net#f) && (Net#e != Net#f);
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
  assume 0 <= I[Net#e];
  assume I[Net#e] <= R[Net#e];
  assume R[Net#e] <= C[Net#e];
  assume 0 <= I[Net#f];
  assume I[Net#f] <= R[Net#f];
  assume R[Net#f] <= C[Net#f];
  assume I[Net#f] == R[Net#f];
  assume I[Net#f] == I[Net#d];
  assume I[Net#f] == I[Net#e];
  assume I[Net#d] == I[Net#b];
  assume I[Net#e] == I[Net#c];
  assume R[Net#a] == C[Net#b];
  assume C[Net#b] == C[Net#c];
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#b]) ==> (H[M[Net#b][i]][sqn#] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#b]) ==> (H[M[Net#b][i]][sqn#] == H[M[Net#c][i]][sqn#])
  );
  assume R[Net#b] == C[Net#d];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#d]) ==> (M[Net#d][idx$] == M[Net#b][idx$])
  );
  assume R[Net#c] == C[Net#e];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#e]) ==> (M[Net#e][idx$] == M[Net#c][idx$])
  );
  assume C[Net#f] == R[Net#e];
  assume R[Net#d] <= R[Net#e];
  assume (forall i: int :: 
    (0 <= i) && (i < R[Net#e]) ==> (H[M[Net#e][i]][sqn#] == i)
  );
  assume (forall i: int :: 
    (0 <= i) && (i < C[Net#f]) ==> (H[M[Net#f][i]][sqn#] == i)
  );
  assume (C[Net#a] - I[Net#a]) == 1;
  assume !(1 <= (C[Net#a] - R[Net#a]));
  assume !(1 <= (C[Net#b] - R[Net#b]));
  assume !(1 <= (C[Net#c] - R[Net#c]));
  assume !((1 <= (C[Net#d] - R[Net#d])) && (1 <= (C[Net#e] - R[Net#e])) && (H[M[Net#d][R[Net#d]]][sqn#] == H[M[Net#e][R[Net#e]]][sqn#]) && (H[M[Net#d][R[Net#d]]][sqn#] == AV#adj#c));
  assume !((1 <= (C[Net#e] - R[Net#e])) && (H[M[Net#e][R[Net#e]]][sqn#] == AV#adj#c));
  assume !((1 <= (C[Net#d] - R[Net#d])) && (H[M[Net#d][R[Net#d]]][sqn#] < AV#adj#c));
  R[Net#f] := R[Net#f] + 1;
  I := R;
  assert {:msg "68.15: The network might not preserve the channel invariant (#76)"} I[Net#f] == I[Net#d];
  assert {:msg "69.15: The network might not preserve the channel invariant (#77)"} I[Net#f] == I[Net#e];
  assert {:msg "The network might not preserve the channel invariant (#78)"} I[Net#d] == I[Net#b];
  assert {:msg "The network might not preserve the channel invariant (#79)"} I[Net#e] == I[Net#c];
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel a (#80)"} (C[Net#a] - R[Net#a]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel b (#81)"} (C[Net#b] - R[Net#b]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel c (#82)"} (C[Net#c] - R[Net#c]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel d (#83)"} (C[Net#d] - R[Net#d]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel e (#84)"} (C[Net#e] - R[Net#e]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel f (#85)"} (C[Net#f] - R[Net#f]) == 0;
}

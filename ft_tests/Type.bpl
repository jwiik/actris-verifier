// ---------------------------------------------------------------
// -- Types and global variables ---------------------------------
// ---------------------------------------------------------------
type Ref;
type Chan a;
type Field a;
type Actor;
type CType = <a>[Chan a]int;
type MType = <a>[Chan a][int]a;
type HType = <a>[Ref,Field a]a;

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

const unique C.i: Field (int);
const unique C.j: Field (Ref);
procedure Add#init#0()
  modifies C, R, M, I, H;
{
  var in: Chan (Ref);
  var out: Chan (Ref);
  assume in != out;
  assume R[in] == 0;
  assume C[out] == 0;
  assert {:msg "Initialization might not establish the invariant (#0)"} R[in] == C[out];
  assert {:msg "Initialization might not establish the invariant (#1)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> ((H[M[in][idx$], C.i] == 0) ==> (M[out][idx$] == M[in][idx$])) && ((H[M[in][idx$], C.i] > 0) ==> (M[out][idx$] == M[in][idx$]))
  );
}
procedure Add#anon$0#1()
  modifies C, R, M, I, H;
{
  var in: Chan (Ref);
  var out: Chan (Ref);
  var in#0: Ref;
  var in#0#sqn: int;
  assume in != out;
  assume 0 <= R[in];
  assume 0 <= C[out];
  assume R[in] == C[out];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> ((H[M[in][idx$], C.i] == 0) ==> (M[out][idx$] == M[in][idx$])) && ((H[M[in][idx$], C.i] > 0) ==> (M[out][idx$] == M[in][idx$]))
  );
  in#0 := M[in][R[in]];
  R[in] := R[in] + 1;
  assume H[in#0, C.i] == 0;
  H[in#0, C.i] := H[in#0, C.i] + 1;
  assert {:msg "6.13: Action postcondition might not hold (#2)"} 1 <= H[in#0, C.i];
  M[out][C[out]] := in#0;
  C[out] := C[out] + 1;
  assert {:msg "Action at 4.3 might not preserve invariant (#3)"} R[in] == C[out];
  assert {:msg "Action at 4.3 might not preserve invariant (#4)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> ((H[M[in][idx$], C.i] == 0) ==> (M[out][idx$] == M[in][idx$])) && ((H[M[in][idx$], C.i] > 0) ==> (M[out][idx$] == M[in][idx$]))
  );
}
procedure Add#anon$1#2()
  modifies C, R, M, I, H;
{
  var in: Chan (Ref);
  var out: Chan (Ref);
  var in#0: Ref;
  var in#0#sqn: int;
  assume in != out;
  assume 0 <= R[in];
  assume 0 <= C[out];
  assume R[in] == C[out];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> ((H[M[in][idx$], C.i] == 0) ==> (M[out][idx$] == M[in][idx$])) && ((H[M[in][idx$], C.i] > 0) ==> (M[out][idx$] == M[in][idx$]))
  );
  in#0 := M[in][R[in]];
  R[in] := R[in] + 1;
  assume H[in#0, C.i] > 0;
  M[out][C[out]] := in#0;
  C[out] := C[out] + 1;
  assert {:msg "Action at 9.3 might not preserve invariant (#5)"} R[in] == C[out];
  assert {:msg "Action at 9.3 might not preserve invariant (#6)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> ((H[M[in][idx$], C.i] == 0) ==> (M[out][idx$] == M[in][idx$])) && ((H[M[in][idx$], C.i] > 0) ==> (M[out][idx$] == M[in][idx$]))
  );
}
procedure Add##GuardWD#3()
  modifies C, R, M, I, H;
{
  var in: Chan (Ref);
  var out: Chan (Ref);
  var in#0: Ref;
  var in#0#sqn: int;
  assume in != out;
  assert {:msg "3.1: The actions 'anon$0' and 'anon$1' of actor 'Add' might not have mutually exclusive guards (#7)"} !(true && (1 <= (C[in] - R[in])) && (H[in#0, C.i] == 0) && true && (1 <= (C[in] - R[in])) && (H[in#0, C.i] > 0));
}
procedure Net#init#4()
  modifies C, R, M, I, H;
{
  var Net#add: Actor;
  var Net#a: Chan (Ref);
  var Net#c: Chan (Ref);
  assume Net#a != Net#c;
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#c];
  assume I[Net#c] <= R[Net#c];
  assume R[Net#c] <= C[Net#c];
  assume I[Net#c] == R[Net#c];
  assume C[Net#a] == 0;
  assume R[Net#a] == 0;
  assume C[Net#c] == 0;
  assume R[Net#c] == 0;
  assert {:msg "22.15: Initialization of network 'Net' might not establish the channel invariant (#8)"} ((C[Net#c] - I[Net#c]) > 0) ==> (1 <= H[M[Net#c][I[Net#c]], C.i]);
  assert {:msg "Initialization of network 'Net' might not establish the channel invariant (#9)"} I[Net#c] == I[Net#a];
  I := R;
  assert {:msg "Initialization of network 'Net' might not establish the network invariant: Unread tokens might be left on channel a (#10)"} (C[Net#a] - R[Net#a]) == 0;
  assert {:msg "Initialization of network 'Net' might not establish the network invariant: Unread tokens might be left on channel c (#11)"} (C[Net#c] - R[Net#c]) == 0;
}
procedure Net##Add#anon$0#5()
  modifies C, R, M, I, H;
{
  var Net#add: Actor;
  var Net#a: Chan (Ref);
  var Net#c: Chan (Ref);
  var in#t: Ref;
  assume Net#a != Net#c;
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#c];
  assume I[Net#c] <= R[Net#c];
  assume R[Net#c] <= C[Net#c];
  assume I[Net#c] == R[Net#c];
  assume ((C[Net#c] - I[Net#c]) > 0) ==> (1 <= H[M[Net#c][I[Net#c]], C.i]);
  assume I[Net#c] == I[Net#a];
  assume (0 <= H[M[Net#a][I[Net#a]], sqn#]) && (0 <= H[M[Net#a][I[Net#a]], C.i]);
  assume R[Net#a] == C[Net#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> ((H[M[Net#a][idx$], C.i] == 0) ==> (M[Net#c][idx$] == M[Net#a][idx$])) && ((H[M[Net#a][idx$], C.i] > 0) ==> (M[Net#c][idx$] == M[Net#a][idx$]))
  );
  assume (1 <= (C[Net#a] - R[Net#a])) && (H[M[Net#a][R[Net#a]], C.i] == 0);
  in#t := M[Net#a][R[Net#a]];
  R[Net#a] := R[Net#a] + 1;
  havoc in#t;
  M[Net#c][C[Net#c]] := in#t;
  C[Net#c] := C[Net#c] + 1;
  assume 1 <= H[in#t, C.i];
  assume R[Net#a] == C[Net#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> ((H[M[Net#a][idx$], C.i] == 0) ==> (M[Net#c][idx$] == M[Net#a][idx$])) && ((H[M[Net#a][idx$], C.i] > 0) ==> (M[Net#c][idx$] == M[Net#a][idx$]))
  );
  assert {:msg "22.15: Action at 4.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#12)"} ((C[Net#c] - I[Net#c]) > 0) ==> (1 <= H[M[Net#c][I[Net#c]], C.i]);
  assert {:msg "Action at 4.3 ('anon$0') for actor instance 'add' might not preserve the channel invariant (#13)"} I[Net#c] == I[Net#a];
}
procedure Net##Add#anon$1#6()
  modifies C, R, M, I, H;
{
  var Net#add: Actor;
  var Net#a: Chan (Ref);
  var Net#c: Chan (Ref);
  var in#t: Ref;
  assume Net#a != Net#c;
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#c];
  assume I[Net#c] <= R[Net#c];
  assume R[Net#c] <= C[Net#c];
  assume I[Net#c] == R[Net#c];
  assume ((C[Net#c] - I[Net#c]) > 0) ==> (1 <= H[M[Net#c][I[Net#c]], C.i]);
  assume I[Net#c] == I[Net#a];
  assume (0 <= H[M[Net#a][I[Net#a]], sqn#]) && (0 <= H[M[Net#a][I[Net#a]], C.i]);
  assume R[Net#a] == C[Net#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> ((H[M[Net#a][idx$], C.i] == 0) ==> (M[Net#c][idx$] == M[Net#a][idx$])) && ((H[M[Net#a][idx$], C.i] > 0) ==> (M[Net#c][idx$] == M[Net#a][idx$]))
  );
  assume (1 <= (C[Net#a] - R[Net#a])) && (H[M[Net#a][R[Net#a]], C.i] > 0);
  in#t := M[Net#a][R[Net#a]];
  R[Net#a] := R[Net#a] + 1;
  M[Net#c][C[Net#c]] := in#t;
  C[Net#c] := C[Net#c] + 1;
  assume R[Net#a] == C[Net#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> ((H[M[Net#a][idx$], C.i] == 0) ==> (M[Net#c][idx$] == M[Net#a][idx$])) && ((H[M[Net#a][idx$], C.i] > 0) ==> (M[Net#c][idx$] == M[Net#a][idx$]))
  );
  assert {:msg "22.15: Action at 9.3 ('anon$1') for actor instance 'add' might not preserve the channel invariant (#14)"} ((C[Net#c] - I[Net#c]) > 0) ==> (1 <= H[M[Net#c][I[Net#c]], C.i]);
  assert {:msg "Action at 9.3 ('anon$1') for actor instance 'add' might not preserve the channel invariant (#15)"} I[Net#c] == I[Net#a];
}
procedure Net#anon$2#input#in#7()
  modifies C, R, M, I, H;
{
  var Net#add: Actor;
  var Net#a: Chan (Ref);
  var Net#c: Chan (Ref);
  assume Net#a != Net#c;
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#c];
  assume I[Net#c] <= R[Net#c];
  assume R[Net#c] <= C[Net#c];
  assume I[Net#c] == R[Net#c];
  assume (C[Net#a] - I[Net#a]) < 1;
  assume ((C[Net#c] - I[Net#c]) > 0) ==> (1 <= H[M[Net#c][I[Net#c]], C.i]);
  assume I[Net#c] == I[Net#a];
  assume (0 <= H[M[Net#a][I[Net#a]], sqn#]) && (0 <= H[M[Net#a][I[Net#a]], C.i]);
  assume R[Net#a] == C[Net#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> ((H[M[Net#a][idx$], C.i] == 0) ==> (M[Net#c][idx$] == M[Net#a][idx$])) && ((H[M[Net#a][idx$], C.i] > 0) ==> (M[Net#c][idx$] == M[Net#a][idx$]))
  );
  C[Net#a] := C[Net#a] + 1;
  assume 0 <= H[M[Net#a][I[Net#a]], sqn#];
  assume 0 <= H[M[Net#a][I[Net#a]], C.i];
  assert {:msg "22.15: Channel invariant might be falsified by network input (#16)"} ((C[Net#c] - I[Net#c]) > 0) ==> (1 <= H[M[Net#c][I[Net#c]], C.i]);
  assert {:msg "Channel invariant might be falsified by network input (#17)"} I[Net#c] == I[Net#a];
  assert {:msg "Channel invariant might be falsified by network input (#18)"} (0 <= H[M[Net#a][I[Net#a]], sqn#]) && (0 <= H[M[Net#a][I[Net#a]], C.i]);
}
procedure Net#anon$2#exit#8()
  modifies C, R, M, I, H;
{
  var Net#add: Actor;
  var Net#a: Chan (Ref);
  var Net#c: Chan (Ref);
  assume Net#a != Net#c;
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#c];
  assume I[Net#c] <= R[Net#c];
  assume R[Net#c] <= C[Net#c];
  assume I[Net#c] == R[Net#c];
  assume ((C[Net#c] - I[Net#c]) > 0) ==> (1 <= H[M[Net#c][I[Net#c]], C.i]);
  assume I[Net#c] == I[Net#a];
  assume (0 <= H[M[Net#a][I[Net#a]], sqn#]) && (0 <= H[M[Net#a][I[Net#a]], C.i]);
  assume R[Net#a] == C[Net#c];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Net#c]) ==> ((H[M[Net#a][idx$], C.i] == 0) ==> (M[Net#c][idx$] == M[Net#a][idx$])) && ((H[M[Net#a][idx$], C.i] > 0) ==> (M[Net#c][idx$] == M[Net#a][idx$]))
  );
  assume (C[Net#a] - I[Net#a]) == 1;
  assume 0 <= H[M[Net#a][I[Net#a]], sqn#];
  assume 0 <= H[M[Net#a][I[Net#a]], C.i];
  assume !((1 <= (C[Net#a] - R[Net#a])) && (H[M[Net#a][R[Net#a]], C.i] == 0));
  assume !((1 <= (C[Net#a] - R[Net#a])) && (H[M[Net#a][R[Net#a]], C.i] > 0));
  assert {:msg "19.13: Network action postcondition might not hold (#19)"} 1 <= H[M[Net#c][I[Net#c]], C.i];
  R[Net#c] := R[Net#c] + 1;
  I := R;
  assert {:msg "22.15: The network might not preserve the channel invariant (#20)"} ((C[Net#c] - I[Net#c]) > 0) ==> (1 <= H[M[Net#c][I[Net#c]], C.i]);
  assert {:msg "The network might not preserve the channel invariant (#21)"} I[Net#c] == I[Net#a];
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel a (#22)"} (C[Net#a] - R[Net#a]) == 0;
  assert {:msg "The network might not preserve the network invariant: Unread tokens might be left on channel c (#23)"} (C[Net#c] - R[Net#c]) == 0;
}

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
procedure Split#anon$0#1()
  modifies C, R, M, I, H;
{
  var in: Chan (int);
  var out1: Chan (Ref);
  var out2: Chan (Ref);
  var y1: Ref;
  var y2: Ref;
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
  H[y1][Int.i] := in#0;
  H[y2][Int.i] := in#0;
  H[y1][sqn#] := c;
  H[y2][sqn#] := c;
  assert {:msg "21.14: Condition might not hold (#5)"} H[y1][sqn#] == H[y2][sqn#];
  c := c + 1;
  M[out1][C[out1]] := y1;
  C[out1] := C[out1] + 1;
  M[out2][C[out2]] := y2;
  C[out2] := C[out2] + 1;
  assert M[out1][C[out1]-1] == y1 && M[out2][C[out2]-1] == y2;
  assert H[M[out1][C[out1]-1]][sqn#] == c-1;
  assert H[M[out2][C[out2]-1]][sqn#] == c-1;
  assert {:msg "5.13: Action at 15.3 might not preserve invariant (#6)"} c == C[out1];
  assert {:msg "6.20: Action at 15.3 might not preserve invariant (#7)"} R[in] == C[out1];
  assert {:msg "7.20: Action at 15.3 might not preserve invariant (#8)"} C[out1] == C[out2];
  assert {:msg "9.21: Action at 15.3 might not preserve invariant (#9)"} (forall i: int :: 
    (0 <= i) && (i < C[out1]) ==> (H[M[out1][i]][sqn#] == i)
  );
  assert {:msg "10.21: Action at 15.3 might not preserve invariant (#10)"} (forall i: int :: 
    (0 <= i) && (i < C[out1]) ==> (H[M[out1][i]][sqn#] == H[M[out2][i]][sqn#])
  );
}

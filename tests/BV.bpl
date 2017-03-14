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

function AT#Min(x:int, y: int): int { if x <= y then x else y }

// ---------------------------------------------------------------
// -- Bit vector operations --------------------------------------
// ---------------------------------------------------------------
// Size: 12
function {:bvbuiltin "bvand"} AT#BvAnd12(a: bv12, b: bv12): bv12;
function {:bvbuiltin "bvor"} AT#BvOr12(a: bv12, b: bv12): bv12;
function {:bvbuiltin "bvnot"} AT#BvNot12(a: bv12): bv12;
function {:bvbuiltin "bvadd"} AT#BvAdd12(a: bv12, b: bv12): bv12;
function {:bvbuiltin "bvsub"} AT#BvSub12(a: bv12, b: bv12): bv12;
function {:bvbuiltin "bvmul"} AT#BvMul12(a: bv12, b: bv12): bv12;
function {:bvbuiltin "bvshl"} AT#BvShl12(bv12,bv12): bv12;
function {:bvbuiltin "bvlshr"} AT#BvLshr12(bv12,bv12): bv12;
function {:bvbuiltin "bvashr"} AT#BvAshr12(bv12,bv12): bv12;
function {:bvbuiltin "bvule"} AT#BvUle12(a: bv12, b: bv12): bool;
function {:bvbuiltin "bvult"} AT#BvUlt12(a: bv12, b: bv12): bool;
function {:bvbuiltin "bvuge"} AT#BvUge12(a: bv12, b: bv12): bool;
function {:bvbuiltin "bvugt"} AT#BvUgt12(a: bv12, b: bv12): bool;
function AT#BvXor12(a: bv12, b: bv12): bv12;

axiom (forall a,b: bv12 :: AT#BvXor12(a,b) == AT#BvAnd12(AT#BvOr12(a,b), AT#BvNot12(AT#BvAnd12(a,b))) );

// ---------------------------------------------------------------
// -- Bit vector operations --------------------------------------
// ---------------------------------------------------------------
// Size: 4
function {:bvbuiltin "bvand"} AT#BvAnd4(a: bv4, b: bv4): bv4;
function {:bvbuiltin "bvor"} AT#BvOr4(a: bv4, b: bv4): bv4;
function {:bvbuiltin "bvnot"} AT#BvNot4(a: bv4): bv4;
function {:bvbuiltin "bvadd"} AT#BvAdd4(a: bv4, b: bv4): bv4;
function {:bvbuiltin "bvsub"} AT#BvSub4(a: bv4, b: bv4): bv4;
function {:bvbuiltin "bvmul"} AT#BvMul4(a: bv4, b: bv4): bv4;
function {:bvbuiltin "bvshl"} AT#BvShl4(bv4,bv4): bv4;
function {:bvbuiltin "bvlshr"} AT#BvLshr4(bv4,bv4): bv4;
function {:bvbuiltin "bvashr"} AT#BvAshr4(bv4,bv4): bv4;
function {:bvbuiltin "bvule"} AT#BvUle4(a: bv4, b: bv4): bool;
function {:bvbuiltin "bvult"} AT#BvUlt4(a: bv4, b: bv4): bool;
function {:bvbuiltin "bvuge"} AT#BvUge4(a: bv4, b: bv4): bool;
function {:bvbuiltin "bvugt"} AT#BvUgt4(a: bv4, b: bv4): bool;
function AT#BvXor4(a: bv4, b: bv4): bv4;

axiom (forall a,b: bv4 :: AT#BvXor4(a,b) == AT#BvAnd4(AT#BvOr4(a,b), AT#BvNot4(AT#BvAnd4(a,b))) );

// ---------------------------------------------------------------
// -- Bit vector operations --------------------------------------
// ---------------------------------------------------------------
// Size: 8
function {:bvbuiltin "bvand"} AT#BvAnd8(a: bv8, b: bv8): bv8;
function {:bvbuiltin "bvor"} AT#BvOr8(a: bv8, b: bv8): bv8;
function {:bvbuiltin "bvnot"} AT#BvNot8(a: bv8): bv8;
function {:bvbuiltin "bvadd"} AT#BvAdd8(a: bv8, b: bv8): bv8;
function {:bvbuiltin "bvsub"} AT#BvSub8(a: bv8, b: bv8): bv8;
function {:bvbuiltin "bvmul"} AT#BvMul8(a: bv8, b: bv8): bv8;
function {:bvbuiltin "bvshl"} AT#BvShl8(bv8,bv8): bv8;
function {:bvbuiltin "bvlshr"} AT#BvLshr8(bv8,bv8): bv8;
function {:bvbuiltin "bvashr"} AT#BvAshr8(bv8,bv8): bv8;
function {:bvbuiltin "bvule"} AT#BvUle8(a: bv8, b: bv8): bool;
function {:bvbuiltin "bvult"} AT#BvUlt8(a: bv8, b: bv8): bool;
function {:bvbuiltin "bvuge"} AT#BvUge8(a: bv8, b: bv8): bool;
function {:bvbuiltin "bvugt"} AT#BvUgt8(a: bv8, b: bv8): bool;
function AT#BvXor8(a: bv8, b: bv8): bv8;

axiom (forall a,b: bv8 :: AT#BvXor8(a,b) == AT#BvAnd8(AT#BvOr8(a,b), AT#BvNot8(AT#BvAnd8(a,b))) );

// ---------------------------------------------------------------
// -- Bit vector operations --------------------------------------
// ---------------------------------------------------------------
// Size: 16
function {:bvbuiltin "bvand"} AT#BvAnd16(a: bv16, b: bv16): bv16;
function {:bvbuiltin "bvor"} AT#BvOr16(a: bv16, b: bv16): bv16;
function {:bvbuiltin "bvnot"} AT#BvNot16(a: bv16): bv16;
function {:bvbuiltin "bvadd"} AT#BvAdd16(a: bv16, b: bv16): bv16;
function {:bvbuiltin "bvsub"} AT#BvSub16(a: bv16, b: bv16): bv16;
function {:bvbuiltin "bvmul"} AT#BvMul16(a: bv16, b: bv16): bv16;
function {:bvbuiltin "bvshl"} AT#BvShl16(bv16,bv16): bv16;
function {:bvbuiltin "bvlshr"} AT#BvLshr16(bv16,bv16): bv16;
function {:bvbuiltin "bvashr"} AT#BvAshr16(bv16,bv16): bv16;
function {:bvbuiltin "bvule"} AT#BvUle16(a: bv16, b: bv16): bool;
function {:bvbuiltin "bvult"} AT#BvUlt16(a: bv16, b: bv16): bool;
function {:bvbuiltin "bvuge"} AT#BvUge16(a: bv16, b: bv16): bool;
function {:bvbuiltin "bvugt"} AT#BvUgt16(a: bv16, b: bv16): bool;
function AT#BvXor16(a: bv16, b: bv16): bv16;

axiom (forall a,b: bv16 :: AT#BvXor16(a,b) == AT#BvAnd16(AT#BvOr16(a,b), AT#BvNot16(AT#BvAnd16(a,b))) );

// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

procedure LShift8#init#0()
  modifies C, R, M, I, H;
{
  var In: Chan (bv8);
  var Out: Chan (bv8);
  assume In != Out;
  assume R[In] == 0;
  assume C[Out] == 0;
  assert {:msg "Initialization might not establish the invariant (#0)"} R[In] == C[Out];
  assert {:msg "Initialization might not establish the invariant (#1)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Out]) ==> (M[Out][idx$] == AT#BvShl8(M[In][idx$], 2bv8))
  );
}
procedure LShift8#anon$0#1()
  modifies C, R, M, I, H;
{
  var In: Chan (bv8);
  var Out: Chan (bv8);
  var In#0: bv8;
  assume In != Out;
  assume 0 <= R[In];
  assume 0 <= C[Out];
  assume R[In] == C[Out];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Out]) ==> (M[Out][idx$] == AT#BvShl8(M[In][idx$], 2bv8))
  );
  In#0 := M[In][R[In]];
  R[In] := R[In] + 1;
  M[Out][C[Out]] := AT#BvShl8(In#0, 2bv8);
  C[Out] := C[Out] + 1;
  assert {:msg "Action at 2.3 might not preserve invariant (#2)"} R[In] == C[Out];
  assert {:msg "Action at 2.3 might not preserve invariant (#3)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Out]) ==> (M[Out][idx$] == AT#BvShl8(M[In][idx$], 2bv8))
  );
}
procedure BvAnd8#init#2()
  modifies C, R, M, I, H;
{
  var In1: Chan (bv8);
  var In2: Chan (bv8);
  var Out: Chan (bv8);
  assume (In1 != In2) && (In1 != Out) && (In2 != Out);
  assume R[In1] == 0;
  assume R[In2] == 0;
  assume C[Out] == 0;
  assert {:msg "Initialization might not establish the invariant (#4)"} R[In1] == C[Out];
  assert {:msg "Initialization might not establish the invariant (#5)"} R[In2] == C[Out];
  assert {:msg "Initialization might not establish the invariant (#6)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Out]) ==> (M[Out][idx$] == AT#BvAnd8(M[In1][idx$], M[In2][idx$]))
  );
}
procedure BvAnd8#anon$1#3()
  modifies C, R, M, I, H;
{
  var In1: Chan (bv8);
  var In2: Chan (bv8);
  var Out: Chan (bv8);
  var In1#0: bv8;
  var In2#0: bv8;
  assume (In1 != In2) && (In1 != Out) && (In2 != Out);
  assume 0 <= R[In1];
  assume 0 <= R[In2];
  assume 0 <= C[Out];
  assume R[In1] == C[Out];
  assume R[In2] == C[Out];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Out]) ==> (M[Out][idx$] == AT#BvAnd8(M[In1][idx$], M[In2][idx$]))
  );
  In1#0 := M[In1][R[In1]];
  R[In1] := R[In1] + 1;
  In2#0 := M[In2][R[In2]];
  R[In2] := R[In2] + 1;
  assume AT#BvAnd8(In1#0, 1bv8) == 1bv8;
  assume AT#BvAnd8(In2#0, 1bv8) == 1bv8;
  assert {:msg "9.13: Action postcondition might not hold (#7)"} AT#BvAnd8(AT#BvAnd8(In1#0, In2#0), 1bv8) == 1bv8;
  M[Out][C[Out]] := AT#BvAnd8(In1#0, In2#0);
  C[Out] := C[Out] + 1;
  assert {:msg "Action at 6.3 might not preserve invariant (#8)"} R[In1] == C[Out];
  assert {:msg "Action at 6.3 might not preserve invariant (#9)"} R[In2] == C[Out];
  assert {:msg "Action at 6.3 might not preserve invariant (#10)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Out]) ==> (M[Out][idx$] == AT#BvAnd8(M[In1][idx$], M[In2][idx$]))
  );
}
procedure BvOr16#init#4()
  modifies C, R, M, I, H;
{
  var In1: Chan (bv16);
  var In2: Chan (bv16);
  var Out: Chan (bv16);
  assume (In1 != In2) && (In1 != Out) && (In2 != Out);
  assume R[In1] == 0;
  assume R[In2] == 0;
  assume C[Out] == 0;
  assert {:msg "Initialization might not establish the invariant (#11)"} R[In1] == C[Out];
  assert {:msg "Initialization might not establish the invariant (#12)"} R[In2] == C[Out];
  assert {:msg "Initialization might not establish the invariant (#13)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Out]) ==> (M[Out][idx$] == AT#BvOr16(M[In1][idx$], M[In2][idx$]))
  );
}
procedure BvOr16#anon$2#5()
  modifies C, R, M, I, H;
{
  var In1: Chan (bv16);
  var In2: Chan (bv16);
  var Out: Chan (bv16);
  var In1#0: bv16;
  var In2#0: bv16;
  assume (In1 != In2) && (In1 != Out) && (In2 != Out);
  assume 0 <= R[In1];
  assume 0 <= R[In2];
  assume 0 <= C[Out];
  assume R[In1] == C[Out];
  assume R[In2] == C[Out];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Out]) ==> (M[Out][idx$] == AT#BvOr16(M[In1][idx$], M[In2][idx$]))
  );
  In1#0 := M[In1][R[In1]];
  R[In1] := R[In1] + 1;
  In2#0 := M[In2][R[In2]];
  R[In2] := R[In2] + 1;
  assume (AT#BvAnd16(In1#0, 1bv16) == 1bv16) || (AT#BvAnd16(In2#0, 1bv16) == 1bv16);
  assert {:msg "16.13: Action postcondition might not hold (#14)"} AT#BvAnd16(AT#BvOr16(In1#0, In2#0), 1bv16) == 1bv16;
  M[Out][C[Out]] := AT#BvOr16(In1#0, In2#0);
  C[Out] := C[Out] + 1;
  assert {:msg "Action at 14.3 might not preserve invariant (#15)"} R[In1] == C[Out];
  assert {:msg "Action at 14.3 might not preserve invariant (#16)"} R[In2] == C[Out];
  assert {:msg "Action at 14.3 might not preserve invariant (#17)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Out]) ==> (M[Out][idx$] == AT#BvOr16(M[In1][idx$], M[In2][idx$]))
  );
}
procedure BvXor12#init#6()
  modifies C, R, M, I, H;
{
  var In1: Chan (bv12);
  var In2: Chan (bv12);
  var Out: Chan (bv12);
  assume (In1 != In2) && (In1 != Out) && (In2 != Out);
  assume R[In1] == 0;
  assume R[In2] == 0;
  assume C[Out] == 0;
  assert {:msg "Initialization might not establish the invariant (#18)"} R[In1] == C[Out];
  assert {:msg "Initialization might not establish the invariant (#19)"} R[In2] == C[Out];
  assert {:msg "Initialization might not establish the invariant (#20)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Out]) ==> (M[Out][idx$] == AT#BvXor12(M[In1][idx$], M[In2][idx$]))
  );
}
procedure BvXor12#anon$3#7()
  modifies C, R, M, I, H;
{
  var In1: Chan (bv12);
  var In2: Chan (bv12);
  var Out: Chan (bv12);
  var In1#0: bv12;
  var In2#0: bv12;
  assume (In1 != In2) && (In1 != Out) && (In2 != Out);
  assume 0 <= R[In1];
  assume 0 <= R[In2];
  assume 0 <= C[Out];
  assume R[In1] == C[Out];
  assume R[In2] == C[Out];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Out]) ==> (M[Out][idx$] == AT#BvXor12(M[In1][idx$], M[In2][idx$]))
  );
  In1#0 := M[In1][R[In1]];
  R[In1] := R[In1] + 1;
  In2#0 := M[In2][R[In2]];
  R[In2] := R[In2] + 1;
  assume (AT#BvAnd12(In1#0, 1bv12) == 1bv12) && (AT#BvAnd12(In2#0, 1bv12) == 1bv12);
  assert {:msg "23.13: Action postcondition might not hold (#21)"} AT#BvAnd12(AT#BvXor12(In1#0, In2#0), 1bv12) == 0bv12;
  M[Out][C[Out]] := AT#BvXor12(In1#0, In2#0);
  C[Out] := C[Out] + 1;
  assert {:msg "Action at 21.3 might not preserve invariant (#22)"} R[In1] == C[Out];
  assert {:msg "Action at 21.3 might not preserve invariant (#23)"} R[In2] == C[Out];
  assert {:msg "Action at 21.3 might not preserve invariant (#24)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Out]) ==> (M[Out][idx$] == AT#BvXor12(M[In1][idx$], M[In2][idx$]))
  );
}
procedure BvNot4#init#8()
  modifies C, R, M, I, H;
{
  var In: Chan (bv4);
  var Out: Chan (bv4);
  assume In != Out;
  assume R[In] == 0;
  assume C[Out] == 0;
  assert {:msg "Initialization might not establish the invariant (#25)"} R[In] == C[Out];
  assert {:msg "Initialization might not establish the invariant (#26)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Out]) ==> (M[Out][idx$] == AT#BvNot4(M[In][idx$]))
  );
}
procedure BvNot4#anon$4#9()
  modifies C, R, M, I, H;
{
  var In: Chan (bv4);
  var Out: Chan (bv4);
  var In#0: bv4;
  assume In != Out;
  assume 0 <= R[In];
  assume 0 <= C[Out];
  assume R[In] == C[Out];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Out]) ==> (M[Out][idx$] == AT#BvNot4(M[In][idx$]))
  );
  In#0 := M[In][R[In]];
  R[In] := R[In] + 1;
  assume In#0 == 0bv4;
  assert {:msg "30.13: Action postcondition might not hold (#27)"} AT#BvNot4(In#0) == 15bv4;
  M[Out][C[Out]] := AT#BvNot4(In#0);
  C[Out] := C[Out] + 1;
  assert {:msg "Action at 28.3 might not preserve invariant (#28)"} R[In] == C[Out];
  assert {:msg "Action at 28.3 might not preserve invariant (#29)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[Out]) ==> (M[Out][idx$] == AT#BvNot4(M[In][idx$]))
  );
}

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
var B: CType;

var H: HType;

const unique this#: Actor;

function AT#Min(x:int, y: int): int { if x <= y then x else y }
function AT#Ite<T>(bool, T, T): T;
axiom (
  forall<T> cond: bool, thn: T, els: T :: { AT#Ite(cond, thn, els) }
    (cond ==> AT#Ite(cond,thn,els) == thn &&
    !cond ==> AT#Ite(cond,thn,els) == els)
);

// ---------------------------------------------------------------
// -- Bit vector operations --------------------------------------
// ---------------------------------------------------------------
// Size: 32
function {:bvbuiltin "bvand"} AT#BvAnd32(a: bv32, b: bv32): bv32;
function {:bvbuiltin "bvor"} AT#BvOr32(a: bv32, b: bv32): bv32;
function {:bvbuiltin "bvnot"} AT#BvNot32(a: bv32): bv32;
function {:bvbuiltin "bvadd"} AT#BvAdd32(a: bv32, b: bv32): bv32;
function {:bvbuiltin "bvsub"} AT#BvSub32(a: bv32, b: bv32): bv32;
function {:bvbuiltin "bvmul"} AT#BvMul32(a: bv32, b: bv32): bv32;
function {:bvbuiltin "bvshl"} AT#BvShl32(bv32,bv32): bv32;
function {:bvbuiltin "bvlshr"} AT#BvLshr32(bv32,bv32): bv32;
function {:bvbuiltin "bvashr"} AT#BvAshr32(bv32,bv32): bv32;
function {:bvbuiltin "bvule"} AT#BvUle32(a: bv32, b: bv32): bool;
function {:bvbuiltin "bvult"} AT#BvUlt32(a: bv32, b: bv32): bool;
function {:bvbuiltin "bvuge"} AT#BvUge32(a: bv32, b: bv32): bool;
function {:bvbuiltin "bvugt"} AT#BvUgt32(a: bv32, b: bv32): bool;
function AT#BvXor32(a: bv32, b: bv32): bv32;

axiom (forall a,b: bv32 :: AT#BvXor32(a,b) == AT#BvAnd32(AT#BvOr32(a,b), AT#BvNot32(AT#BvAnd32(a,b))) );
function AT#Bit0(vec: bv32): bool { AT#BvAnd32(vec,1bv32) != 0bv32 }
function AT#Bit1(vec: bv32): bool { AT#BvAnd32(vec,2bv32) != 0bv32 }
function AT#Bit2(vec: bv32): bool { AT#BvAnd32(vec,4bv32) != 0bv32 }
function AT#Bit3(vec: bv32): bool { AT#BvAnd32(vec,8bv32) != 0bv32 }
function AT#Bit4(vec: bv32): bool { AT#BvAnd32(vec,16bv32) != 0bv32 }
function AT#Bit5(vec: bv32): bool { AT#BvAnd32(vec,32bv32) != 0bv32 }
function AT#Bit6(vec: bv32): bool { AT#BvAnd32(vec,64bv32) != 0bv32 }
function AT#Bit7(vec: bv32): bool { AT#BvAnd32(vec,128bv32) != 0bv32 }
function AT#Bit8(vec: bv32): bool { AT#BvAnd32(vec,256bv32) != 0bv32 }
function AT#Bit9(vec: bv32): bool { AT#BvAnd32(vec,512bv32) != 0bv32 }
function AT#Bit10(vec: bv32): bool { AT#BvAnd32(vec,1024bv32) != 0bv32 }
function AT#Bit11(vec: bv32): bool { AT#BvAnd32(vec,2048bv32) != 0bv32 }
function AT#Bit12(vec: bv32): bool { AT#BvAnd32(vec,4096bv32) != 0bv32 }
function AT#Bit13(vec: bv32): bool { AT#BvAnd32(vec,8192bv32) != 0bv32 }
function AT#Bit14(vec: bv32): bool { AT#BvAnd32(vec,16384bv32) != 0bv32 }
function AT#Bit15(vec: bv32): bool { AT#BvAnd32(vec,32768bv32) != 0bv32 }
function AT#Bit16(vec: bv32): bool { AT#BvAnd32(vec,65536bv32) != 0bv32 }
function AT#Bit17(vec: bv32): bool { AT#BvAnd32(vec,131072bv32) != 0bv32 }
function AT#Bit18(vec: bv32): bool { AT#BvAnd32(vec,262144bv32) != 0bv32 }
function AT#Bit19(vec: bv32): bool { AT#BvAnd32(vec,524288bv32) != 0bv32 }
function AT#Bit20(vec: bv32): bool { AT#BvAnd32(vec,1048576bv32) != 0bv32 }
function AT#Bit21(vec: bv32): bool { AT#BvAnd32(vec,2097152bv32) != 0bv32 }
function AT#Bit22(vec: bv32): bool { AT#BvAnd32(vec,4194304bv32) != 0bv32 }
function AT#Bit23(vec: bv32): bool { AT#BvAnd32(vec,8388608bv32) != 0bv32 }
function AT#Bit24(vec: bv32): bool { AT#BvAnd32(vec,16777216bv32) != 0bv32 }
function AT#Bit25(vec: bv32): bool { AT#BvAnd32(vec,33554432bv32) != 0bv32 }
function AT#Bit26(vec: bv32): bool { AT#BvAnd32(vec,67108864bv32) != 0bv32 }
function AT#Bit27(vec: bv32): bool { AT#BvAnd32(vec,134217728bv32) != 0bv32 }
function AT#Bit28(vec: bv32): bool { AT#BvAnd32(vec,268435456bv32) != 0bv32 }
function AT#Bit29(vec: bv32): bool { AT#BvAnd32(vec,536870912bv32) != 0bv32 }
function AT#Bit30(vec: bv32): bool { AT#BvAnd32(vec,1073741824bv32) != 0bv32 }
function AT#Bit31(vec: bv32): bool { AT#BvAnd32(vec,2147483648bv32) != 0bv32 }

function AT#Bv2Int32(vec: bv32): int {
  1*(if AT#Bit0(vec) then 1 else 0) +
  2*(if AT#Bit1(vec) then 1 else 0) +
  4*(if AT#Bit2(vec) then 1 else 0) +
  8*(if AT#Bit3(vec) then 1 else 0) +
  16*(if AT#Bit4(vec) then 1 else 0) +
  32*(if AT#Bit5(vec) then 1 else 0) +
  64*(if AT#Bit6(vec) then 1 else 0) +
  128*(if AT#Bit7(vec) then 1 else 0) +
  256*(if AT#Bit8(vec) then 1 else 0) +
  512*(if AT#Bit9(vec) then 1 else 0) +
  1024*(if AT#Bit10(vec) then 1 else 0) +
  2048*(if AT#Bit11(vec) then 1 else 0) +
  4096*(if AT#Bit12(vec) then 1 else 0) +
  8192*(if AT#Bit13(vec) then 1 else 0) +
  16384*(if AT#Bit14(vec) then 1 else 0) +
  32768*(if AT#Bit15(vec) then 1 else 0) +
  65536*(if AT#Bit16(vec) then 1 else 0) +
  131072*(if AT#Bit17(vec) then 1 else 0) +
  262144*(if AT#Bit18(vec) then 1 else 0) +
  524288*(if AT#Bit19(vec) then 1 else 0) +
  1048576*(if AT#Bit20(vec) then 1 else 0) +
  2097152*(if AT#Bit21(vec) then 1 else 0) +
  4194304*(if AT#Bit22(vec) then 1 else 0) +
  8388608*(if AT#Bit23(vec) then 1 else 0) +
  16777216*(if AT#Bit24(vec) then 1 else 0) +
  33554432*(if AT#Bit25(vec) then 1 else 0) +
  67108864*(if AT#Bit26(vec) then 1 else 0) +
  134217728*(if AT#Bit27(vec) then 1 else 0) +
  268435456*(if AT#Bit28(vec) then 1 else 0) +
  536870912*(if AT#Bit29(vec) then 1 else 0) +
  1073741824*(if AT#Bit30(vec) then 1 else 0) +
  2147483648*(if AT#Bit31(vec) then 1 else 0)
}
// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

procedure Bv2Int#init#0()
  modifies C, R, M, I, H;
{
  var in: Chan (bv32);
  var out: Chan (int);
  assume true;
  assume R[in] == 0;
  assume C[out] == 0;
  assert {:msg "<unknown_file>(-1.-1): Initialization might not establish the invariant (#0)"} R[in] == C[out];
  assert {:msg "<unknown_file>(-1.-1): Initialization might not establish the invariant (#1)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == AT#Bv2Int32(M[in][idx$]))
  );
}
procedure Bv2Int#anon$0#1()
  modifies C, R, M, I, H;
{
  var in: Chan (bv32);
  var out: Chan (int);
  var in#0: bv32;
  assume true;
  assume 0 <= R[in];
  assume 0 <= C[out];
  assume R[in] == C[out];
  assume (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == AT#Bv2Int32(M[in][idx$]))
  );
  in#0 := M[in][R[in]];
  R[in] := R[in] + 1;
  M[out][C[out]] := AT#Bv2Int32(in#0);
  C[out] := C[out] + 1;
  assert {:msg "<unknown_file>(-1.-1): Action at Bv2Int.actor(3.3) might not preserve invariant (#2)"} R[in] == C[out];
  assert {:msg "<unknown_file>(-1.-1): Action at Bv2Int.actor(3.3) might not preserve invariant (#3)"} (forall idx$: int :: 
    (0 <= idx$) && (idx$ < C[out]) ==> (M[out][idx$] == AT#Bv2Int32(M[in][idx$]))
  );
}

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

const NEWVOP: bv12;
axiom NEWVOP == 2048bv12;
const INTRA: bv12;
axiom INTRA == 1024bv12;
const INTER: bv12;
axiom INTER == 512bv12;
const MOTION: bv12;
axiom MOTION == 8bv12;
const ACCODED: bv12;
axiom ACCODED == 2bv12;
const ACPRED: bv12;
axiom ACPRED == 1bv12;

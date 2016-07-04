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
var C#init: CType;
var St: [Actor]State;

const unique this#: Actor;

type List a = [int]a;
var AT#intlst: List int;


// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

const unique pulseShape#s_start: State;
const unique pulseShape#s_idle: State;
procedure pulseShape#init#0()
  modifies C, R, M, St;
{
  var this#: Actor;
  var symb_mem: int;
  var body_iterations: int;
  var body_index: int;
  var FILT_COEFF0: int;
  var FILT_COEFF1: int;
  var FILT_COEFF2: int;
  var FILT_COEFF3: int;
  var FILT_COEFF4: int;
  var IV#len#len_in: int;
  assume (St[this#] == pulseShape#s_start) || (St[this#] == pulseShape#s_idle);
  assume St[this#] == pulseShape#s_start;
  body_iterations := IV#len#len_in * 32;
  body_index := 0;
  symb_mem := 111;
  St[this#] := pulseShape#s_idle;
  assert {:msg "  1.1: Action at 28.2 might not preserve invariant"} (St[this#] == pulseShape#s_start) || (St[this#] == pulseShape#s_idle);
}
procedure pulseShape#tx_body#1()
  modifies C, R, M, St;
{
  var this#: Actor;
  var symb_mem: int;
  var body_iterations: int;
  var body_index: int;
  var FILT_COEFF0: int;
  var FILT_COEFF1: int;
  var FILT_COEFF2: int;
  var FILT_COEFF3: int;
  var FILT_COEFF4: int;
  var IV#symb#symb_1: int;
  var IV#symb#symb_2: int;
  var ActionVar#hsps: List (int);
  assume (St[this#] == pulseShape#s_start) || (St[this#] == pulseShape#s_idle);
  assume St[this#] == pulseShape#s_idle;
  assume body_index < body_iterations;
  ActionVar#hsps[0] := UDef#mul8(FILT_COEFF0, IV#symb#symb_1);
  ActionVar#hsps[1] := UDef#mul8(FILT_COEFF4, symb_mem);
  ActionVar#hsps[2] := UDef#mul8(FILT_COEFF1, IV#symb#symb_1);
  ActionVar#hsps[3] := UDef#mul8(FILT_COEFF3, symb_mem);
  ActionVar#hsps[4] := UDef#mul8(FILT_COEFF2, IV#symb#symb_1);
  ActionVar#hsps[5] := UDef#mul8(FILT_COEFF2, symb_mem);
  ActionVar#hsps[6] := UDef#mul8(FILT_COEFF3, IV#symb#symb_1);
  ActionVar#hsps[7] := UDef#mul8(FILT_COEFF1, symb_mem);
  ActionVar#hsps[8] := UDef#mul8(FILT_COEFF4, IV#symb#symb_1);
  ActionVar#hsps[9] := UDef#mul8(FILT_COEFF0, IV#symb#symb_2);
  ActionVar#hsps[10] := UDef#mul8(FILT_COEFF3, IV#symb#symb_1);
  ActionVar#hsps[11] := UDef#mul8(FILT_COEFF1, IV#symb#symb_2);
  ActionVar#hsps[12] := UDef#mul8(FILT_COEFF2, IV#symb#symb_1);
  ActionVar#hsps[13] := UDef#mul8(FILT_COEFF2, IV#symb#symb_2);
  ActionVar#hsps[14] := UDef#mul8(FILT_COEFF1, IV#symb#symb_1);
  ActionVar#hsps[15] := UDef#mul8(FILT_COEFF3, IV#symb#symb_2);
  symb_mem := IV#symb#symb_2;
  body_index := body_index + 1;
  St[this#] := pulseShape#s_idle;
  assert {:msg "  1.1: Action at 37.2 might not preserve invariant"} (St[this#] == pulseShape#s_start) || (St[this#] == pulseShape#s_idle);
}
procedure pulseShape#tx_tail#2()
  modifies C, R, M, St;
{
  var this#: Actor;
  var symb_mem: int;
  var body_iterations: int;
  var body_index: int;
  var FILT_COEFF0: int;
  var FILT_COEFF1: int;
  var FILT_COEFF2: int;
  var FILT_COEFF3: int;
  var FILT_COEFF4: int;
  var ActionVar#hsps: List (int);
  assume (St[this#] == pulseShape#s_start) || (St[this#] == pulseShape#s_idle);
  assume St[this#] == pulseShape#s_idle;
  assume body_index == body_iterations;
  ActionVar#hsps[0] := UDef#mul8(FILT_COEFF0, 111);
  ActionVar#hsps[1] := UDef#mul8(FILT_COEFF4, symb_mem);
  ActionVar#hsps[2] := UDef#mul8(FILT_COEFF1, 111);
  ActionVar#hsps[3] := UDef#mul8(FILT_COEFF3, symb_mem);
  ActionVar#hsps[4] := UDef#mul8(FILT_COEFF2, 111);
  ActionVar#hsps[5] := UDef#mul8(FILT_COEFF2, symb_mem);
  ActionVar#hsps[6] := UDef#mul8(FILT_COEFF3, 111);
  ActionVar#hsps[7] := UDef#mul8(FILT_COEFF1, symb_mem);
  St[this#] := pulseShape#s_start;
  assert {:msg "  1.1: Action at 73.2 might not preserve invariant"} (St[this#] == pulseShape#s_start) || (St[this#] == pulseShape#s_idle);
}

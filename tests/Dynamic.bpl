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

const unique this#: Actor;
type List a = [int]a;
var AT#intlst: List int;

function AT#Min(x:int, y: int): int { if x <= y then x else y }

// ---------------------------------------------------------------
// -- End of prelude ---------------------------------------------
// ---------------------------------------------------------------

procedure Dynamic#init#0()
  modifies C, R, M, I;
{
  var in: Chan (int);
  var out: Chan (int);
  var St: int;
  var index: int;
  var iterations: int;
  var rds: int;
  var tots: int;
  assume in != out;
  assume R[in] == 0;
  assume C[out] == 0;
  rds := R[in];
  tots := C[out];
  index := 0;
  iterations := 0;
  St := 0;
  assert {:msg "9.12: Initialization might not establish the invariant (#0)"} (R[in] == 0) ==> (iterations == 0);
  assert {:msg "10.15: Initialization might not establish the invariant (#1)"} (R[in] > 0) ==> (iterations == M[in][R[in] - 1]);
  assert {:msg "11.12: Initialization might not establish the invariant (#2)"} index <= iterations;
  assert {:msg "12.12: Initialization might not establish the invariant (#3)"} (St == 0) <==> (index == iterations);
  assert {:msg "13.12: Initialization might not establish the invariant (#4)"} (St == 1) <==> (index < iterations);
  assert {:msg "14.12: Initialization might not establish the invariant (#5)"} C[out] == (tots + index);
  assert {:msg "15.12: Initialization might not establish the invariant (#6)"} (St == 0) <==> ((C[out] - tots) == (iterations * (R[in] - rds)));
}
procedure Dynamic#anon$1#1()
  modifies C, R, M, I;
{
  var in: Chan (int);
  var out: Chan (int);
  var St: int;
  var index: int;
  var iterations: int;
  var rds: int;
  var tots: int;
  var in#0: int;
  assume in != out;
  assume 0 <= R[in];
  assume 0 <= C[out];
  assume (R[in] == 0) ==> (iterations == 0);
  assume (R[in] > 0) ==> (iterations == M[in][R[in] - 1]);
  assume index <= iterations;
  assume (St == 0) <==> (index == iterations);
  assume (St == 1) <==> (index < iterations);
  assume C[out] == (tots + index);
  assume (St == 0) <==> ((C[out] - tots) == (iterations * (R[in] - rds)));
  in#0 := M[in][R[in]];
  R[in] := R[in] + 1;
  assume in#0 >= 1;
  assume St == 0;
  rds := R[in];
  tots := C[out];
  iterations := in#0;
  index := 0;
  St := 1;
  assert {:msg "9.12: Action at 26.2 might not preserve invariant (#7)"} (R[in] == 0) ==> (iterations == 0);
  assert {:msg "10.15: Action at 26.2 might not preserve invariant (#8)"} (R[in] > 0) ==> (iterations == M[in][R[in] - 1]);
  assert {:msg "11.12: Action at 26.2 might not preserve invariant (#9)"} index <= iterations;
  assert {:msg "12.12: Action at 26.2 might not preserve invariant (#10)"} (St == 0) <==> (index == iterations);
  assert {:msg "13.12: Action at 26.2 might not preserve invariant (#11)"} (St == 1) <==> (index < iterations);
  assert {:msg "14.12: Action at 26.2 might not preserve invariant (#12)"} C[out] == (tots + index);
  assert {:msg "15.12: Action at 26.2 might not preserve invariant (#13)"} (St == 0) <==> ((C[out] - tots) == (iterations * (R[in] - rds)));
}
procedure Dynamic#anon$2#2()
  modifies C, R, M, I;
{
  var in: Chan (int);
  var out: Chan (int);
  var St: int;
  var index: int;
  var iterations: int;
  var rds: int;
  var tots: int;
  assume in != out;
  assume 0 <= R[in];
  assume 0 <= C[out];
  assume (R[in] == 0) ==> (iterations == 0);
  assume (R[in] > 0) ==> (iterations == M[in][R[in] - 1]);
  assume index <= iterations;
  assume (St == 0) <==> (index == iterations);
  assume (St == 1) <==> (index < iterations);
  assume C[out] == (tots + index);
  assume (St == 0) <==> ((C[out] - tots) == (iterations * (R[in] - rds)));
  assume (St == 1) && (index < iterations);
  index := index + 1;
  havoc St;
  assume (index < iterations) ==> (St == 1);
  assume (index == iterations) ==> (St == 0);
  M[out][C[out]] := index;
  C[out] := C[out] + 1;
  assert {:msg "9.12: Action at 37.2 might not preserve invariant (#14)"} (R[in] == 0) ==> (iterations == 0);
  assert {:msg "10.15: Action at 37.2 might not preserve invariant (#15)"} (R[in] > 0) ==> (iterations == M[in][R[in] - 1]);
  assert {:msg "11.12: Action at 37.2 might not preserve invariant (#16)"} index <= iterations;
  assert {:msg "12.12: Action at 37.2 might not preserve invariant (#17)"} (St == 0) <==> (index == iterations);
  assert {:msg "13.12: Action at 37.2 might not preserve invariant (#18)"} (St == 1) <==> (index < iterations);
  assert {:msg "14.12: Action at 37.2 might not preserve invariant (#19)"} C[out] == (tots + index);
  assert {:msg "15.12: Action at 37.2 might not preserve invariant (#20)"} (St == 0) <==> ((C[out] - tots) == (iterations * (R[in] - rds)));
}
procedure Dynamic#finalize#3()
  modifies C, R, M, I;
{
  var in: Chan (int);
  var out: Chan (int);
  var St: int;
  var index: int;
  var iterations: int;
  var rds: int;
  var tots: int;
  assume in != out;
  assume 0 <= R[in];
  assume 0 <= C[out];
  assume (R[in] == 0) ==> (iterations == 0);
  assume (R[in] > 0) ==> (iterations == M[in][R[in] - 1]);
  assume index <= iterations;
  assume (St == 0) <==> (index == iterations);
  assume (St == 1) <==> (index < iterations);
  assume C[out] == (tots + index);
  assume (St == 0) <==> ((C[out] - tots) == (iterations * (R[in] - rds)));
  assume (St == 1) && (index == iterations);
  St := 0;
  assert {:msg "9.12: Action at 47.2 might not preserve invariant (#21)"} (R[in] == 0) ==> (iterations == 0);
  assert {:msg "10.15: Action at 47.2 might not preserve invariant (#22)"} (R[in] > 0) ==> (iterations == M[in][R[in] - 1]);
  assert {:msg "11.12: Action at 47.2 might not preserve invariant (#23)"} index <= iterations;
  assert {:msg "12.12: Action at 47.2 might not preserve invariant (#24)"} (St == 0) <==> (index == iterations);
  assert {:msg "13.12: Action at 47.2 might not preserve invariant (#25)"} (St == 1) <==> (index < iterations);
  assert {:msg "14.12: Action at 47.2 might not preserve invariant (#26)"} C[out] == (tots + index);
  assert {:msg "15.12: Action at 47.2 might not preserve invariant (#27)"} (St == 0) <==> ((C[out] - tots) == (iterations * (R[in] - rds)));
}
procedure Dynamic##GuardWD#4()
  modifies C, R, M, I;
{
  var in: Chan (int);
  var out: Chan (int);
  var St: int;
  var index: int;
  var iterations: int;
  var rds: int;
  var tots: int;
  var in#0: int;
  assume in != out;
  assert {:msg "1.1: The actions of actor 'Dynamic' might not have mutually exclusive guards (#28)"} !((1 <= (C[in] - R[in])) && (St == 0) && (St == 1) && (index < iterations));
  assert {:msg "1.1: The actions of actor 'Dynamic' might not have mutually exclusive guards (#29)"} !((1 <= (C[in] - R[in])) && (St == 0) && (St == 1) && (index == iterations));
  assert {:msg "1.1: The actions of actor 'Dynamic' might not have mutually exclusive guards (#30)"} !((St == 1) && (index < iterations) && (St == 1) && (index == iterations));
}
procedure Net#init#5()
  modifies C, R, M, I;
{
  var Net#shp: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var AV#shp#St: int;
  var AV#shp#index: int;
  var AV#shp#iterations: int;
  var AV#shp#rds: int;
  var AV#shp#tots: int;
  assume Net#a != Net#b;
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume I[Net#b] == R[Net#b];
  assume C[Net#a] == 0;
  assume R[Net#a] == 0;
  assume C[Net#b] == 0;
  assume R[Net#b] == 0;
  assume (R[Net#a] == 0) ==> (AV#shp#iterations == 0);
  assume (R[Net#a] > 0) ==> (AV#shp#iterations == M[Net#a][R[Net#a] - 1]);
  assume AV#shp#index <= AV#shp#iterations;
  assume (AV#shp#St == 0) <==> (AV#shp#index == AV#shp#iterations);
  assume (AV#shp#St == 1) <==> (AV#shp#index < AV#shp#iterations);
  assume C[Net#b] == (AV#shp#tots + AV#shp#index);
  assume (AV#shp#St == 0) <==> ((C[Net#b] - AV#shp#tots) == (AV#shp#iterations * (R[Net#a] - AV#shp#rds)));
  assert {:msg "65.15: Initialization of network 'Net' might not establish the channel invariant (#31)"} (3 * I[Net#a]) == I[Net#b];
  assert {:msg "66.15: Initialization of network 'Net' might not establish the channel invariant (#32)"} (AV#shp#St == 0) ==> ((3 * R[Net#a]) == C[Net#b]);
  assert {:msg "67.15: Initialization of network 'Net' might not establish the channel invariant (#33)"} ((R[Net#a] - I[Net#a]) > 0) ==> (AV#shp#iterations == M[Net#a][R[Net#a] - 1]);
  assert {:msg "68.15: Initialization of network 'Net' might not establish the channel invariant (#34)"} ((R[Net#a] - I[Net#a]) > 0) ==> (AV#shp#tots == I[Net#b]);
  assert {:msg "Initialization of network 'Net' might not establish the channel invariant (#35)"} true && (forall idx$: int :: 
    (I[Net#a] <= idx$) && (idx$ < C[Net#a]) ==> (M[Net#a][idx$] == 3)
  );
  I := R;
  assert {:msg "75.5: The initialization might produce unspecified tokens on channel a (#36)"} (C[Net#a] - R[Net#a]) == 0;
  assert {:msg "76.5: The initialization might produce unspecified tokens on channel b (#37)"} (C[Net#b] - R[Net#b]) == 0;
}
procedure Net##Dynamic#anon$1#6()
  modifies C, R, M, I;
{
  var Net#shp: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var AV#shp#St: int;
  var AV#shp#index: int;
  var AV#shp#iterations: int;
  var AV#shp#rds: int;
  var AV#shp#tots: int;
  var in#len_in: int;
  assume Net#a != Net#b;
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume I[Net#b] == R[Net#b];
  assume (3 * I[Net#a]) == I[Net#b];
  assume (AV#shp#St == 0) ==> ((3 * R[Net#a]) == C[Net#b]);
  assume ((R[Net#a] - I[Net#a]) > 0) ==> (AV#shp#iterations == M[Net#a][R[Net#a] - 1]);
  assume ((R[Net#a] - I[Net#a]) > 0) ==> (AV#shp#tots == I[Net#b]);
  assume true && (forall idx$: int :: 
    (I[Net#a] <= idx$) && (idx$ < C[Net#a]) ==> (M[Net#a][idx$] == 3)
  );
  assume (R[Net#a] == 0) ==> (AV#shp#iterations == 0);
  assume (R[Net#a] > 0) ==> (AV#shp#iterations == M[Net#a][R[Net#a] - 1]);
  assume AV#shp#index <= AV#shp#iterations;
  assume (AV#shp#St == 0) <==> (AV#shp#index == AV#shp#iterations);
  assume (AV#shp#St == 1) <==> (AV#shp#index < AV#shp#iterations);
  assume C[Net#b] == (AV#shp#tots + AV#shp#index);
  assume (AV#shp#St == 0) <==> ((C[Net#b] - AV#shp#tots) == (AV#shp#iterations * (R[Net#a] - AV#shp#rds)));
  assume (1 <= (C[Net#a] - R[Net#a])) && (AV#shp#St == 0);
  assume (R[Net#a] == 0) ==> (AV#shp#iterations == 0);
  assume (R[Net#a] > 0) ==> (AV#shp#iterations == M[Net#a][R[Net#a] - 1]);
  assume AV#shp#index <= AV#shp#iterations;
  assume (AV#shp#St == 0) <==> (AV#shp#index == AV#shp#iterations);
  assume (AV#shp#St == 1) <==> (AV#shp#index < AV#shp#iterations);
  assume C[Net#b] == (AV#shp#tots + AV#shp#index);
  assume (AV#shp#St == 0) <==> ((C[Net#b] - AV#shp#tots) == (AV#shp#iterations * (R[Net#a] - AV#shp#rds)));
  in#len_in := M[Net#a][R[Net#a]];
  R[Net#a] := R[Net#a] + 1;
  assert {:msg "28.11: Precondition might not hold for instance at 71.5 (#38)"} in#len_in >= 1;
  havoc AV#shp#tots;
  havoc AV#shp#iterations;
  havoc AV#shp#rds;
  havoc AV#shp#St;
  havoc AV#shp#index;
  assume (R[Net#a] == 0) ==> (AV#shp#iterations == 0);
  assume (R[Net#a] > 0) ==> (AV#shp#iterations == M[Net#a][R[Net#a] - 1]);
  assume AV#shp#index <= AV#shp#iterations;
  assume (AV#shp#St == 0) <==> (AV#shp#index == AV#shp#iterations);
  assume (AV#shp#St == 1) <==> (AV#shp#index < AV#shp#iterations);
  assume C[Net#b] == (AV#shp#tots + AV#shp#index);
  assume (AV#shp#St == 0) <==> ((C[Net#b] - AV#shp#tots) == (AV#shp#iterations * (R[Net#a] - AV#shp#rds)));
  assume (R[Net#a] == 0) ==> (AV#shp#iterations == 0);
  assume (R[Net#a] > 0) ==> (AV#shp#iterations == M[Net#a][R[Net#a] - 1]);
  assume AV#shp#index <= AV#shp#iterations;
  assume (AV#shp#St == 0) <==> (AV#shp#index == AV#shp#iterations);
  assume (AV#shp#St == 1) <==> (AV#shp#index < AV#shp#iterations);
  assume C[Net#b] == (AV#shp#tots + AV#shp#index);
  assume (AV#shp#St == 0) <==> ((C[Net#b] - AV#shp#tots) == (AV#shp#iterations * (R[Net#a] - AV#shp#rds)));
  assert {:msg "65.15: Action at 26.2 ('anon$1') for actor instance 'shp' might not preserve the channel invariant (#39)"} (3 * I[Net#a]) == I[Net#b];
  assert {:msg "66.15: Action at 26.2 ('anon$1') for actor instance 'shp' might not preserve the channel invariant (#40)"} (AV#shp#St == 0) ==> ((3 * R[Net#a]) == C[Net#b]);
  assert {:msg "67.15: Action at 26.2 ('anon$1') for actor instance 'shp' might not preserve the channel invariant (#41)"} ((R[Net#a] - I[Net#a]) > 0) ==> (AV#shp#iterations == M[Net#a][R[Net#a] - 1]);
  assert {:msg "68.15: Action at 26.2 ('anon$1') for actor instance 'shp' might not preserve the channel invariant (#42)"} ((R[Net#a] - I[Net#a]) > 0) ==> (AV#shp#tots == I[Net#b]);
  assert {:msg "Action at 26.2 ('anon$1') for actor instance 'shp' might not preserve the channel invariant (#43)"} true && (forall idx$: int :: 
    (I[Net#a] <= idx$) && (idx$ < C[Net#a]) ==> (M[Net#a][idx$] == 3)
  );
}
procedure Net##Dynamic#anon$2#7()
  modifies C, R, M, I;
{
  var Net#shp: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var AV#shp#St: int;
  var AV#shp#index: int;
  var AV#shp#iterations: int;
  var AV#shp#rds: int;
  var AV#shp#tots: int;
  assume Net#a != Net#b;
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume I[Net#b] == R[Net#b];
  assume (3 * I[Net#a]) == I[Net#b];
  assume (AV#shp#St == 0) ==> ((3 * R[Net#a]) == C[Net#b]);
  assume ((R[Net#a] - I[Net#a]) > 0) ==> (AV#shp#iterations == M[Net#a][R[Net#a] - 1]);
  assume ((R[Net#a] - I[Net#a]) > 0) ==> (AV#shp#tots == I[Net#b]);
  assume true && (forall idx$: int :: 
    (I[Net#a] <= idx$) && (idx$ < C[Net#a]) ==> (M[Net#a][idx$] == 3)
  );
  assume (R[Net#a] == 0) ==> (AV#shp#iterations == 0);
  assume (R[Net#a] > 0) ==> (AV#shp#iterations == M[Net#a][R[Net#a] - 1]);
  assume AV#shp#index <= AV#shp#iterations;
  assume (AV#shp#St == 0) <==> (AV#shp#index == AV#shp#iterations);
  assume (AV#shp#St == 1) <==> (AV#shp#index < AV#shp#iterations);
  assume C[Net#b] == (AV#shp#tots + AV#shp#index);
  assume (AV#shp#St == 0) <==> ((C[Net#b] - AV#shp#tots) == (AV#shp#iterations * (R[Net#a] - AV#shp#rds)));
  assume (AV#shp#St == 1) && (AV#shp#index < AV#shp#iterations);
  assume (R[Net#a] == 0) ==> (AV#shp#iterations == 0);
  assume (R[Net#a] > 0) ==> (AV#shp#iterations == M[Net#a][R[Net#a] - 1]);
  assume AV#shp#index <= AV#shp#iterations;
  assume (AV#shp#St == 0) <==> (AV#shp#index == AV#shp#iterations);
  assume (AV#shp#St == 1) <==> (AV#shp#index < AV#shp#iterations);
  assume C[Net#b] == (AV#shp#tots + AV#shp#index);
  assume (AV#shp#St == 0) <==> ((C[Net#b] - AV#shp#tots) == (AV#shp#iterations * (R[Net#a] - AV#shp#rds)));
  havoc AV#shp#index;
  M[Net#b][C[Net#b]] := AV#shp#index;
  C[Net#b] := C[Net#b] + 1;
  assume (R[Net#a] == 0) ==> (AV#shp#iterations == 0);
  assume (R[Net#a] > 0) ==> (AV#shp#iterations == M[Net#a][R[Net#a] - 1]);
  assume AV#shp#index <= AV#shp#iterations;
  assume (AV#shp#St == 0) <==> (AV#shp#index == AV#shp#iterations);
  assume (AV#shp#St == 1) <==> (AV#shp#index < AV#shp#iterations);
  assume C[Net#b] == (AV#shp#tots + AV#shp#index);
  assume (AV#shp#St == 0) <==> ((C[Net#b] - AV#shp#tots) == (AV#shp#iterations * (R[Net#a] - AV#shp#rds)));
  assume (R[Net#a] == 0) ==> (AV#shp#iterations == 0);
  assume (R[Net#a] > 0) ==> (AV#shp#iterations == M[Net#a][R[Net#a] - 1]);
  assume AV#shp#index <= AV#shp#iterations;
  assume (AV#shp#St == 0) <==> (AV#shp#index == AV#shp#iterations);
  assume (AV#shp#St == 1) <==> (AV#shp#index < AV#shp#iterations);
  assume C[Net#b] == (AV#shp#tots + AV#shp#index);
  assume (AV#shp#St == 0) <==> ((C[Net#b] - AV#shp#tots) == (AV#shp#iterations * (R[Net#a] - AV#shp#rds)));
  assert {:msg "65.15: Action at 37.2 ('anon$2') for actor instance 'shp' might not preserve the channel invariant (#44)"} (3 * I[Net#a]) == I[Net#b];
  assert {:msg "66.15: Action at 37.2 ('anon$2') for actor instance 'shp' might not preserve the channel invariant (#45)"} (AV#shp#St == 0) ==> ((3 * R[Net#a]) == C[Net#b]);
  assert {:msg "67.15: Action at 37.2 ('anon$2') for actor instance 'shp' might not preserve the channel invariant (#46)"} ((R[Net#a] - I[Net#a]) > 0) ==> (AV#shp#iterations == M[Net#a][R[Net#a] - 1]);
  assert {:msg "68.15: Action at 37.2 ('anon$2') for actor instance 'shp' might not preserve the channel invariant (#47)"} ((R[Net#a] - I[Net#a]) > 0) ==> (AV#shp#tots == I[Net#b]);
  assert {:msg "Action at 37.2 ('anon$2') for actor instance 'shp' might not preserve the channel invariant (#48)"} true && (forall idx$: int :: 
    (I[Net#a] <= idx$) && (idx$ < C[Net#a]) ==> (M[Net#a][idx$] == 3)
  );
}
procedure Net##Dynamic#finalize#8()
  modifies C, R, M, I;
{
  var Net#shp: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var AV#shp#St: int;
  var AV#shp#index: int;
  var AV#shp#iterations: int;
  var AV#shp#rds: int;
  var AV#shp#tots: int;
  assume Net#a != Net#b;
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume I[Net#b] == R[Net#b];
  assume (3 * I[Net#a]) == I[Net#b];
  assume (AV#shp#St == 0) ==> ((3 * R[Net#a]) == C[Net#b]);
  assume ((R[Net#a] - I[Net#a]) > 0) ==> (AV#shp#iterations == M[Net#a][R[Net#a] - 1]);
  assume ((R[Net#a] - I[Net#a]) > 0) ==> (AV#shp#tots == I[Net#b]);
  assume true && (forall idx$: int :: 
    (I[Net#a] <= idx$) && (idx$ < C[Net#a]) ==> (M[Net#a][idx$] == 3)
  );
  assume (R[Net#a] == 0) ==> (AV#shp#iterations == 0);
  assume (R[Net#a] > 0) ==> (AV#shp#iterations == M[Net#a][R[Net#a] - 1]);
  assume AV#shp#index <= AV#shp#iterations;
  assume (AV#shp#St == 0) <==> (AV#shp#index == AV#shp#iterations);
  assume (AV#shp#St == 1) <==> (AV#shp#index < AV#shp#iterations);
  assume C[Net#b] == (AV#shp#tots + AV#shp#index);
  assume (AV#shp#St == 0) <==> ((C[Net#b] - AV#shp#tots) == (AV#shp#iterations * (R[Net#a] - AV#shp#rds)));
  assume (AV#shp#St == 1) && (AV#shp#index == AV#shp#iterations);
  assume (R[Net#a] == 0) ==> (AV#shp#iterations == 0);
  assume (R[Net#a] > 0) ==> (AV#shp#iterations == M[Net#a][R[Net#a] - 1]);
  assume AV#shp#index <= AV#shp#iterations;
  assume (AV#shp#St == 0) <==> (AV#shp#index == AV#shp#iterations);
  assume (AV#shp#St == 1) <==> (AV#shp#index < AV#shp#iterations);
  assume C[Net#b] == (AV#shp#tots + AV#shp#index);
  assume (AV#shp#St == 0) <==> ((C[Net#b] - AV#shp#tots) == (AV#shp#iterations * (R[Net#a] - AV#shp#rds)));
  havoc AV#shp#St;
  assume (R[Net#a] == 0) ==> (AV#shp#iterations == 0);
  assume (R[Net#a] > 0) ==> (AV#shp#iterations == M[Net#a][R[Net#a] - 1]);
  assume AV#shp#index <= AV#shp#iterations;
  assume (AV#shp#St == 0) <==> (AV#shp#index == AV#shp#iterations);
  assume (AV#shp#St == 1) <==> (AV#shp#index < AV#shp#iterations);
  assume C[Net#b] == (AV#shp#tots + AV#shp#index);
  assume (AV#shp#St == 0) <==> ((C[Net#b] - AV#shp#tots) == (AV#shp#iterations * (R[Net#a] - AV#shp#rds)));
  assume (R[Net#a] == 0) ==> (AV#shp#iterations == 0);
  assume (R[Net#a] > 0) ==> (AV#shp#iterations == M[Net#a][R[Net#a] - 1]);
  assume AV#shp#index <= AV#shp#iterations;
  assume (AV#shp#St == 0) <==> (AV#shp#index == AV#shp#iterations);
  assume (AV#shp#St == 1) <==> (AV#shp#index < AV#shp#iterations);
  assume C[Net#b] == (AV#shp#tots + AV#shp#index);
  assume (AV#shp#St == 0) <==> ((C[Net#b] - AV#shp#tots) == (AV#shp#iterations * (R[Net#a] - AV#shp#rds)));
  assert {:msg "65.15: Action at 47.2 ('finalize') for actor instance 'shp' might not preserve the channel invariant (#49)"} (3 * I[Net#a]) == I[Net#b];
  assert {:msg "66.15: Action at 47.2 ('finalize') for actor instance 'shp' might not preserve the channel invariant (#50)"} (AV#shp#St == 0) ==> ((3 * R[Net#a]) == C[Net#b]);
  assert {:msg "67.15: Action at 47.2 ('finalize') for actor instance 'shp' might not preserve the channel invariant (#51)"} ((R[Net#a] - I[Net#a]) > 0) ==> (AV#shp#iterations == M[Net#a][R[Net#a] - 1]);
  assert {:msg "68.15: Action at 47.2 ('finalize') for actor instance 'shp' might not preserve the channel invariant (#52)"} ((R[Net#a] - I[Net#a]) > 0) ==> (AV#shp#tots == I[Net#b]);
  assert {:msg "Action at 47.2 ('finalize') for actor instance 'shp' might not preserve the channel invariant (#53)"} true && (forall idx$: int :: 
    (I[Net#a] <= idx$) && (idx$ < C[Net#a]) ==> (M[Net#a][idx$] == 3)
  );
}
procedure Net#entry()
  modifies C, R, M, I;
{
  var Net#shp: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var AV#shp#St: int;
  var AV#shp#index: int;
  var AV#shp#iterations: int;
  var AV#shp#rds: int;
  var AV#shp#tots: int;
  assume Net#a != Net#b;
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume I[Net#b] == R[Net#b];
  assume C[Net#a] == R[Net#a];
  assume C[Net#b] == R[Net#b];
  assume AV#shp#St == 0;
  assume (3 * I[Net#a]) == I[Net#b];
  assume (AV#shp#St == 0) ==> ((3 * R[Net#a]) == C[Net#b]);
  assume ((R[Net#a] - I[Net#a]) > 0) ==> (AV#shp#iterations == M[Net#a][R[Net#a] - 1]);
  assume ((R[Net#a] - I[Net#a]) > 0) ==> (AV#shp#tots == I[Net#b]);
  assume true && (forall idx$: int :: 
    (I[Net#a] <= idx$) && (idx$ < C[Net#a]) ==> (M[Net#a][idx$] == 3)
  );
  assume (R[Net#a] == 0) ==> (AV#shp#iterations == 0);
  assume (R[Net#a] > 0) ==> (AV#shp#iterations == M[Net#a][R[Net#a] - 1]);
  assume AV#shp#index <= AV#shp#iterations;
  assume (AV#shp#St == 0) <==> (AV#shp#index == AV#shp#iterations);
  assume (AV#shp#St == 1) <==> (AV#shp#index < AV#shp#iterations);
  assume C[Net#b] == (AV#shp#tots + AV#shp#index);
  assume (AV#shp#St == 0) <==> ((C[Net#b] - AV#shp#tots) == (AV#shp#iterations * (R[Net#a] - AV#shp#rds)));
  assert {:msg "57.1: Sub-actors in the network might fire without network input. This is not permitted. (#54)"} !((1 <= (C[Net#a] - R[Net#a])) && (AV#shp#St == 0));
  assert {:msg "57.1: Sub-actors in the network might fire without network input. This is not permitted. (#55)"} !((AV#shp#St == 1) && (AV#shp#index < AV#shp#iterations));
  assert {:msg "57.1: Sub-actors in the network might fire without network input. This is not permitted. (#56)"} !((AV#shp#St == 1) && (AV#shp#index == AV#shp#iterations));
}
procedure Net#anon$3#input#in#9()
  modifies C, R, M, I;
{
  var Net#shp: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var AV#shp#St: int;
  var AV#shp#index: int;
  var AV#shp#iterations: int;
  var AV#shp#rds: int;
  var AV#shp#tots: int;
  assume Net#a != Net#b;
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume I[Net#b] == R[Net#b];
  assume C[Net#a] < 1;
  assume (3 * I[Net#a]) == I[Net#b];
  assume (AV#shp#St == 0) ==> ((3 * R[Net#a]) == C[Net#b]);
  assume ((R[Net#a] - I[Net#a]) > 0) ==> (AV#shp#iterations == M[Net#a][R[Net#a] - 1]);
  assume ((R[Net#a] - I[Net#a]) > 0) ==> (AV#shp#tots == I[Net#b]);
  assume true && (forall idx$: int :: 
    (I[Net#a] <= idx$) && (idx$ < C[Net#a]) ==> (M[Net#a][idx$] == 3)
  );
  assume (R[Net#a] == 0) ==> (AV#shp#iterations == 0);
  assume (R[Net#a] > 0) ==> (AV#shp#iterations == M[Net#a][R[Net#a] - 1]);
  assume AV#shp#index <= AV#shp#iterations;
  assume (AV#shp#St == 0) <==> (AV#shp#index == AV#shp#iterations);
  assume (AV#shp#St == 1) <==> (AV#shp#index < AV#shp#iterations);
  assume C[Net#b] == (AV#shp#tots + AV#shp#index);
  assume (AV#shp#St == 0) <==> ((C[Net#b] - AV#shp#tots) == (AV#shp#iterations * (R[Net#a] - AV#shp#rds)));
  C[Net#a] := C[Net#a] + 1;
  assume M[Net#a][I[Net#a]] == 3;
  assert {:msg "65.15: Channel invariant might be falsified by network input (#57)"} (3 * I[Net#a]) == I[Net#b];
  assert {:msg "66.15: Channel invariant might be falsified by network input (#58)"} (AV#shp#St == 0) ==> ((3 * R[Net#a]) == C[Net#b]);
  assert {:msg "67.15: Channel invariant might be falsified by network input (#59)"} ((R[Net#a] - I[Net#a]) > 0) ==> (AV#shp#iterations == M[Net#a][R[Net#a] - 1]);
  assert {:msg "68.15: Channel invariant might be falsified by network input (#60)"} ((R[Net#a] - I[Net#a]) > 0) ==> (AV#shp#tots == I[Net#b]);
  assert {:msg "Channel invariant might be falsified by network input (#61)"} true && (forall idx$: int :: 
    (I[Net#a] <= idx$) && (idx$ < C[Net#a]) ==> (M[Net#a][idx$] == 3)
  );
}
procedure Net#anon$3#exit#10()
  modifies C, R, M, I;
{
  var Net#shp: Actor;
  var Net#a: Chan (int);
  var Net#b: Chan (int);
  var AV#shp#St: int;
  var AV#shp#index: int;
  var AV#shp#iterations: int;
  var AV#shp#rds: int;
  var AV#shp#tots: int;
  assume Net#a != Net#b;
  assume 0 <= I[Net#a];
  assume I[Net#a] <= R[Net#a];
  assume R[Net#a] <= C[Net#a];
  assume 0 <= I[Net#b];
  assume I[Net#b] <= R[Net#b];
  assume R[Net#b] <= C[Net#b];
  assume I[Net#b] == R[Net#b];
  assume (3 * I[Net#a]) == I[Net#b];
  assume (AV#shp#St == 0) ==> ((3 * R[Net#a]) == C[Net#b]);
  assume ((R[Net#a] - I[Net#a]) > 0) ==> (AV#shp#iterations == M[Net#a][R[Net#a] - 1]);
  assume ((R[Net#a] - I[Net#a]) > 0) ==> (AV#shp#tots == I[Net#b]);
  assume true && (forall idx$: int :: 
    (I[Net#a] <= idx$) && (idx$ < C[Net#a]) ==> (M[Net#a][idx$] == 3)
  );
  assume (R[Net#a] == 0) ==> (AV#shp#iterations == 0);
  assume (R[Net#a] > 0) ==> (AV#shp#iterations == M[Net#a][R[Net#a] - 1]);
  assume AV#shp#index <= AV#shp#iterations;
  assume (AV#shp#St == 0) <==> (AV#shp#index == AV#shp#iterations);
  assume (AV#shp#St == 1) <==> (AV#shp#index < AV#shp#iterations);
  assume C[Net#b] == (AV#shp#tots + AV#shp#index);
  assume (AV#shp#St == 0) <==> ((C[Net#b] - AV#shp#tots) == (AV#shp#iterations * (R[Net#a] - AV#shp#rds)));
  assume (C[Net#a] - I[Net#a]) == 1;
  assume M[Net#a][I[Net#a]] == 3;
  assume !((1 <= (C[Net#a] - R[Net#a])) && (AV#shp#St == 0));
  assume !((AV#shp#St == 1) && (AV#shp#index < AV#shp#iterations));
  assume !((AV#shp#St == 1) && (AV#shp#index == AV#shp#iterations));
  R[Net#b] := R[Net#b] + 3;
  I := R;
  assert {:msg "65.15: The network might not preserve the channel invariant (#62)"} (3 * I[Net#a]) == I[Net#b];
  assert {:msg "66.15: The network might not preserve the channel invariant (#63)"} (AV#shp#St == 0) ==> ((3 * R[Net#a]) == C[Net#b]);
  assert {:msg "67.15: The network might not preserve the channel invariant (#64)"} ((R[Net#a] - I[Net#a]) > 0) ==> (AV#shp#iterations == M[Net#a][R[Net#a] - 1]);
  assert {:msg "68.15: The network might not preserve the channel invariant (#65)"} ((R[Net#a] - I[Net#a]) > 0) ==> (AV#shp#tots == I[Net#b]);
  assert {:msg "The network might not preserve the channel invariant (#66)"} true && (forall idx$: int :: 
    (I[Net#a] <= idx$) && (idx$ < C[Net#a]) ==> (M[Net#a][idx$] == 3)
  );
  assert {:msg "59.3: The network might leave unread tokens on channel a (#67)"} C[Net#a] == R[Net#a];
  assert {:msg "59.3: The network might not produce the specified number of tokens on output out (#68)"} C[Net#b] == R[Net#b];
}

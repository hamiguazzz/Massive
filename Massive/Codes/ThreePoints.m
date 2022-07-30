LogPri["ThreePoints loaded"];
(*In paper arXiv: 1709.04891, \[Lambda]s without tilde as angle brackets are selected as massive basis,
  which will lead to the same result with the opposite one.*)
(* we use the opposite one here, m omitted *)

(* ::Section:: *)
(* Output fun *)

Reduce3Pt[amp_] := Module[{
  r1, r2
},
  r1 = amp;
  r2 = amp /. rule3PtReduce // Expand;
  While[r1 =!= r2, r1 = r2; r2 = r1 /. rule3PtReduce // Expand;];
  Return@(r1 //. rule3PtMass);
];
Reduce3Pt[amp_List] := (Last@FactorizeBracket@#&) /@ Flatten[Sum2List /@ Reduce3Pt /@ amp] // DeleteDuplicates // DeleteCases[0];

rule3PtMass = {h : (ab | sb)[i_, j_]^m_. /; (j + i === 7) -> 1};
rule3PtReduce = ruleP1[3] ~ Join ~ {
  ab[i_, j_]^m_. sb[k_, l_]^n_. /;
      ((And @@ ((# >= 1 && # <= 3) & /@ {i, j, k, l})) && 2 === Length@DeleteDuplicates@{i, j, k, l}) :>
      ab[i, j]^(m - 1) * sb[k, l]^(n - 1),
  ab[i_, j_]^m_. sb[k_, l_]^n_. /;
      ((And @@ ((# >= 1 && # <= 3) & /@ {i, j, k, l})) && 3 === Length@DeleteDuplicates@{i, j, k, l}) :>
      ab[i, j]^(m - 1) * sb[k, l]^(n - 1)} ~ Join ~ ruleSchS ~ Join ~ ruleSchA;
bL = sb;
bLT = ab;

Options@Construct3PBasis = {mass -> All};
Construct3PBasis::wrong = "Wrong amount";
Construct3PBasis::parm = "All massless mass:`1`";
Construct3PBasis::construction = "Wrong 3pt construction: shape: `1` filling: `2`";
Construct3PBasis[spins : {s1_, s2_, s3_}, OptionsPattern[]] :=
    Module[{massOp = MassOption[OptionValue@mass, 3], masslessPos, massivePos, sortedS, f, rule, re},
      masslessPos = If[KeyExistsQ[#, 0], #[0], {}] &[PositionIndex@massOp];
      massivePos = Complement[Range[3], masslessPos];
      If[Length@masslessPos === 3, Message[Construct3PBasis::parm, massOp]; Return[{}]];
      f = Switch[Length@masslessPos, 0, Gen3LYT, 1, Gen1H2LYT, 2, Gen2H1LYT];
      sortedS = spins[[massivePos]] ~ Join ~ spins[[masslessPos]];
      rule = Flatten@Table[{i -> massivePos[[i]], 7 - i -> 7 - massivePos[[i]]}, {i, Length@massivePos}] ~ Join ~
          Table[j + Length@massivePos -> masslessPos[[j]], {j, Length@masslessPos}];
      re = f[sortedS];
      re = If[Head@sortedS === List, ReplaceBraNumber[rule] /@ re, {}];
      If[Check3PointAmount[{s1, s2, s3}, mass -> OptionValue@mass] != Length@re, Message[Construct3PBasis::wrong ]];
      Return[re];
    ];

Options@Check3PointAmount = {mass -> All};
Check3PointAmount[spins : {s1_, s2_, s3_}, OptionsPattern[]] :=
    Module[{massOp = MassOption[OptionValue@mass, 3], zeroPos, nonZeroPos, sortedS, f, rule, re},
      zeroPos = If[KeyExistsQ[#, 0], #[0], {}] &[PositionIndex@massOp];
      nonZeroPos = Complement[Range[3], zeroPos];
      If[Length@zeroPos === 3, Return[{}]];
      f = Switch[Length@zeroPos, 0, CheckAmount3L, 1, CheckAmount1H2LUE, 2, CheckAmount2H1L];
      sortedS = spins[[zeroPos]] ~ Join ~ spins[[nonZeroPos]];
      re = f[sortedS];
      Return@re;
    ];

(* ::Section:: *)
(* 1709 *)

(*Gen2H1L[spins : {h1_, h2_, s_}] /;*)
(*    And @@ (IntegerQ /@ (2 * spins)) &&*)
(*        s >= 0 &&*)
(*        IntegerQ@(Plus @@ spins) :=*)
(*    Module[{v1, v2, p1, p2, amp},*)
(*      *)(*    If[h2<h1, exchangeFlag = True; {h1,h2} = {h2,h1};];*)
(*      v1 = {s + h2 - h1, s + h1 - h2};*)
(*      *)(* Can it be 0? *)
(*      If[v1[[1]] < 0 || v1[[2]] < 0, Return[{}];];*)
(*      *)(* Use less *)
(*      *)(*  mn = -(2s + h1 + h2 - 1);*)
(*      v2 = s + h1 + h2;*)
(*      p1 = bL[1, 4]^v1[[1]] * bL[2, 4]^v1[[2]];*)
(*      p2 = bLT[1, 2]^v2;*)
(*      amp = p1 * p2;*)
(*      *)(*    If[exchangeFlag, amp = ReplaceBraNumber[{1->2,2->1}][amp];];*)
(*      Return[{amp}];*)
(*    ];*)

(*Gen1H2LUE[spins : {h_, s1_, s2_}] /;*)
(*    And @@ (IntegerQ /@ (2 * spins)) &&*)
(*        s1 >= 0 && s2 >= 0 &&*)
(*        IntegerQ@(Plus @@ spins) :=*)
(*    Module[{nU, nV, u, v, C, amp},*)
(*      C = s1 + s2 - Abs[s1 - s2] + 1;*)
(*      If[C < 1 || !IntegerQ[C], Return[{}]];*)
(*      nU = s1 + s2 + h;*)
(*      nV = s1 + s2 - h;*)
(*      If[!(IntegerQ@nU && IntegerQ@nV), Return[{}]];*)
(*      *)(*10 as temp massive particle,4 as massive 3, 5 as massive 2*)
(*      u = bL[1, 10];*)
(*      v = bL[2, 10] * bLT[1, 2];*)
(*      *)(*contract v mostly with 5*)
(*      amp = If[*)
(*        *)(*group s1 can hold all v*)
(*        2 * s1 >= nV,*)
(*        *)(*contract all v with 2 and move v to another group by i*)
(*        Table[*)
(*          ReplaceBraNumber[{10 -> 5}][v]^(nV - i)*)
(*              * ReplaceBraNumber[{10 -> 5}][u]^(2 * s1 - (nV - i))*)
(*              * ReplaceBraNumber[{10 -> 4}][v]^i*)
(*              * ReplaceBraNumber[{10 -> 4}][u]^(nU - (2 * s1 - (nV - i))),*)
(*          {i, 0, C - 1}],*)
(*        *)(*contract all u with 3 while switch u to another group by i*)
(*        Table[*)
(*          ReplaceBraNumber[{10 -> 5}][v]^(2 * s1 - i)*)
(*              * ReplaceBraNumber[{10 -> 5}][u]^i*)
(*              * ReplaceBraNumber[{10 -> 4}][v]^(nV - (2 * s1 - i))*)
(*              * ReplaceBraNumber[{10 -> 4}][u]^(nU - i)  ,*)
(*          {i, 0, C - 1}]*)
(*      ];*)
(*      *)(*Remove terms with denominator*)
(*      amp = amp // DeleteCases[___ * Power[_, i_] /; i < 0];*)
(*      Return[amp];*)
(*    ];*)

(*Gen3L[spins : {s1_, s2_, s3_}] /;*)
(*    And @@ (IntegerQ /@ (2 * spins)) &&*)
(*        And @@ (# >= 0& /@ spins) &&*)
(*        IntegerQ@(Plus @@ spins) :=*)
(*    Module[{p1, p2, mrules, frules, ReduceAmpMass,*)
(*      Gen1, Gen2, ps, ps2, amps1, amps2, re},*)
(*      *)(*10,11 as Temp; 12,13 as Temp; 6,5,4 as massive 1,2,3*)
(*      p1 = bL[1, 10] * bL[2, 11] * bLT[1, 2];*)
(*      p2 = bL[12, 13];*)

(*      *)(*reduce*)
(*      mrules = {h : (bL | bLT)[i_, j_] /; (j + i === 7) -> 1, Power[h : (bL | bLT)[i_, j_] /; (j + i === 7), _] -> 1};*)
(*      *)(*      frules = {11 -> 1, 12 -> 2, 13 -> 3};*)
(*      *)(*      ReduceAmp[amp_] := ReplaceBraNumber[frules][amp /. mrules];*)
(*      ReduceAmpMass[amp_] := amp /. mrules;*)

(*      *)(* Gen amp from filling lists *)
(*      Gen1[{la_List, lb_List}] /; (Length@la === Length@lb) := Times @@ Table[*)
(*        ReplaceBraNumber[{10 -> la[[i]], 11 -> lb[[i]]}]@p1*)
(*        , {i, Length@la}] // ReduceAmpMass;*)
(*      Gen2[{la_List, lb_List, {xa_, xb_}}] /; (Length@la === Length@lb) :=*)
(*          Gen1[{la, lb}] * (ReplaceBraNumber[{12 -> xa, 13 -> xb}][p2] // ReduceAmpMass);*)

(*      *)(*All indices list*)
(*      ps = Permutations[Join[Table[6, 2 * s1], Table[5, 2 * s2], Table[4, 2 * s3]]];*)

(*      *)(*Type I, i = 0*)
(*      ps2 = {Sort[#[[1 ;; s1 + s2 + s3]]], Sort[#[[s1 + s2 + s3 + 1 ;;]]]}& /@ ps // DeleteDuplicates;*)
(*      amps1 = Gen1 /@ ps2;*)

(*      *)(*Type II, i = 1*)
(*      ps2 = {Sort[#[[1 ;; s1 + s2 + s3 - 1]]], Sort[#[[s1 + s2 + s3 ;; -3]]], Sort[#[[-2 ;; -1]]]}& /@ ps //*)
(*          DeleteDuplicates // DeleteCases[{_, _, {i_, j_}} /; i == j];*)
(*      amps2 = Gen2 /@ ps2;*)
(*      re = (Last@FactorizeBracket@#&) /@ Join[amps1, amps2] // DeleteDuplicates;*)
(*      Return[re];*)
(*    ];*)

(* ::Section:: *)
(* Dong Detail *)

(* ::Subsection:: *)
(* Checking methods *)
CheckAmount2H1L[spins : {h1_, h2_, s_}] := With[{},
  If[!(And @@ (IntegerQ /@ (2 * spins)) &&
      s >= 0 &&
      IntegerQ@(Plus @@ spins)), Return[0]];
  If[s < Abs[h1 - h2],
    Return[0],
    Return[1]];
];

CheckAmount1H2LUE[spins : {h_, s1_, s2_}] := With[{},
  If[!(And @@ (IntegerQ /@ (2 * spins)) &&
      s1 >= 0 && s2 >= 0 &&
      IntegerQ@(Plus @@ spins)), Return[0]];
  If[Abs[h] > s1 + s2, Return@0];
  If[Abs[h] <= s1 + s2 && Abs[h] >= Abs[s1 - s2], Return@(s1 + s2 - Abs@h + 1)];
  If[Abs[h] < Abs[s1 - s2], Return@(2 * Min[s1, s2] + 1)];
];

CheckAmount3L[spins : {s1_, s2_, s3_}] := Module[
  {s, p},
  If[!(And @@ (IntegerQ /@ (2 * spins)) &&
      And @@ (# >= 0& /@ spins) &&
      IntegerQ@(Plus @@ spins)), Return@0];
  s = Sort@spins;
  p = Max[s[[1]] + s[[2]] - s[[3]], 0];
  Return[(2 * s[[1]] + 1) * (2 * s[[2]] + 1) - p * (p + 1)];
];

(* ::Subsection:: *)
(* Construction methods *)
AmpFromYTP3[shape : {L_, R_}, filling_List] := Module[
  {A = Table[0, 2, R], sf = Sort@filling, p = {1, 2, 3}, pm = {4, 5, 6}, YTRs, YTL},
  YTRs = StrangeSSYT[A, sf[[L + 1 ;;]], 0 , pm];
  YTL = If[L > 0, {sf[[1 ;; L]]}, {{}}];
  Return[YTtoAmpmass[YTL, L, p] * YTtoAmpmass[#, 0, p]& /@ YTRs];
];

Gen2H1LYT[{s_, h2_, h3_}] := Module[
  {
    h2I = h2, h3I = h3, exchange = h2 < h3, re, shape, filling, flagTrueResult = False
  },
  If[exchange, {h2I, h3I} = {h3I, h2I}];
  If[Check3PointAmount[{s, h2I, h3I}, mass -> {1}] === 0, Return[{}]];
  If[h3I >= 0, shape = {0, 2 * h2I};];
  If[h2I >= 0 && h3I < 0, shape = {-2 * h3I, 2 * h2I - 2 * h3I};];
  If[0 > h2I, shape = {-2 * h3I, -2 * h2I - 2 * h3I};];

  (*try to add momentum*)
  shape[[0]] --;
  Do[
    shape[[0]] ++;
    filling = Join[Table[1, shape[[1]]], Table[2, shape[[1]] + 2 * h2I],
      Table[3, shape[[1]] + 2 * h3I], Table[6, 2 * s]];
    shape[[2]] += (Length@filling - shape[[1]] - shape[[2]] * 2) / 2;
    If[!IntegerQ@shape[[2]], Continue[]];
    re = Reduce3Pt@AmpFromYTP3[shape, filling] // DeleteCases[0];
    If[Length@re === 1,
      flagTrueResult = True;
      Break[];
    ];,
    {tryL, 0, 10}];
  If[exchange, re = ReplaceBraNumber[{2 -> 3, 3 -> 2}] /@ re];
  If[!flagTrueResult, re = {}; Message[Construct3PBasis::construction, shape, filling];];
  Return[re];
];

Gen1H2LYT[{s1_, s2_, h3_}] := Module[
  {reAll = {}, shape, filling, reNow},
  If[Check3PointAmount[{s1, s2, h3}, mass -> {1, 2}] === 0, Return[{}]];
  shape = If[h3 >= 0, {0, 2 * h3}, {-2h3, -2h3}];
  shape[[1]]--;
  Do[
    shape[[1]]++;
    filling = Join[Table[1, shape[[1]]], Table[2, shape[[1]]],
      Table[3, shape[[1]] + 2 * h3], Table[6, 2 * s1], Table[5, 2 * s2]];
    shape[[2]] += (Length@filling - shape[[1]] - shape[[2]] * 2) / 2;
    (*    Print["shape:", shape, "filling:", filling];*)
    If[!IntegerQ@shape[[2]], Message[Construct3PBasis::construction, shape, filling]; Return[Null];];
    reNow = AmpFromYTP3[shape, filling];
    reAll = reAll ~ Join ~ reNow;,
    {J, 0, s1 + s2}];
  Return@Reduce3Pt@reAll;
];

Gen3LYT[spins : {s1_, s2_, s3_}] := Module[
  {reAll = {}, shape, reNow, filling},
  If[Check3PointAmount[{s1, s2, s3}, mass -> All] === 0, Return[{}]];
  Do[
    shape = {L, 0};
    filling = Flatten@Table[i, {i, 3}, shape[[1]]] ~ Join ~ Flatten@Table[7 - i, {i, 3}, {2 * spins[[i]]}];
    shape[[2]] += (Length@filling - shape[[1]] - shape[[2]] * 2) / 2;
    If[!IntegerQ@shape[[2]], Message[Construct3PBasis::construction, shape, filling]; Return[Null];];
    reNow = AmpFromYTP3[shape, filling];
    reAll = reAll ~ Join ~ reNow;,
    {L, 0, s1 + s2 + s3}];
  Return@Reduce3Pt@reAll;
];
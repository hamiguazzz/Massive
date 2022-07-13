LogPri["ThreePoints loaded"];
(*In paper arXiv: 1709.04891, \[Lambda]s without tilde as angle brackets are selected as massive basis,
  which will lead to the same result with the opposite one.*)
(* we use the opposite one here, m omitted *)

(*$$Require$$ ReplaceBraNumber, MassOption, ab, sb*)
bL = ab;
bLT = sb;
Reduce3Pt[amp_] := Module[{rule = ruleP1[3]},
  Return[amp /. rule];
];
Options@Construct3PBasis = {mass -> All};
Construct3PBasis[spins : {s1_, s2_, s3_}, OptionsPattern[]] :=
    Module[{massOp = MassOption[OptionValue@mass, 3], zeroPos, nonZeroPos, sortedS, f, rule, re},
      zeroPos = If[KeyExistsQ[#, 0], #[0], {}] &[PositionIndex@massOp];
      nonZeroPos = Complement[Range[3], zeroPos];
      If[Length@zeroPos === 3, Return[{}]];
      f = Switch[Length@zeroPos, 0, Gen3L, 1, Gen1H2LUE, 2, Gen2H1L];
      sortedS = spins[[zeroPos]] ~ Join ~ spins[[nonZeroPos]];
      rule = Table[i -> zeroPos[[i]], {i, Length@zeroPos}] ~ Join ~ Table[j + Length@zeroPos -> nonZeroPos[[j]], {j, Length@nonZeroPos}];
      re = f[sortedS];
      re = If[Head@sortedS === List, ReplaceBraNumber[rule] /@ re, {}];
      re = Reduce3Pt /@ re // DeleteCases[0];
      Return[re];
    ];

Gen2H1L[spins : {h1_, h2_, s_}] /;
    And @@ (IntegerQ /@ (2 * spins)) &&
        s >= 0 &&
        IntegerQ@(Plus @@ spins) :=
    Module[{v1, v2, p1, p2, amp},
      (*    If[h2<h1, exchangeFlag = True; {h1,h2} = {h2,h1};];*)
      v1 = {s + h2 - h1, s + h1 - h2};
      (* Can it be 0? *)
      If[v1[[1]] < 0 || v1[[2]] < 0, Return[{}];];
      (* Use less *)
      (*  mn = -(2s + h1 + h2 - 1);*)
      v2 = s + h1 + h2;
      p1 = bL[1, 3]^v1[[1]] * bL[2, 3]^v1[[2]];
      p2 = bLT[1, 2]^v2;
      amp = p1 * p2;
      (*    If[exchangeFlag, amp = ReplaceBraNumber[{1->2,2->1}][amp];];*)
      amp = Reduce3Pt /@ amp // DeleteCases[0];
      Return@{amp};
    ];

Gen1H2LUE[spins : {h_, s1_, s2_}] /;
    And @@ (IntegerQ /@ (2 * spins)) &&
        s1 >= 0 && s2 >= 0 &&
        IntegerQ@(Plus @@ spins) :=
    Module[{nU, nV, u, v, C, amp},
      C = s1 + s2 - Abs[s1 - s2] + 1;
      If[C < 1 || !IntegerQ[C], Return[{}]];
      nU = s1 + s2 + h;
      nV = s1 + s2 - h;
      If[!(IntegerQ@nU && IntegerQ@nV), Return[{}]];
      (*4 as temp, 5 as massive 2*)
      u = bL[1, 4];
      v = bL[2, 4] * bLT[1, 2];
      (*contract v mostly with 5*)
      amp = If[
        (*group s1 can hold all v*)
        2 * s1 >= nV,
        (*contract all v with 2 and move v to another group by i*)
        Table[
          ReplaceBraNumber[{4 -> 5}][v]^(nV - i)
              * ReplaceBraNumber[{4 -> 5}][u]^(2 * s1 - (nV - i))
              * ReplaceBraNumber[{4 -> 3}][v]^i
              * ReplaceBraNumber[{4 -> 3}][u]^(nU - (2 * s1 - (nV - i))),
          {i, 0, C - 1}],
        (*contract all u with 3 while switch u to another group by i*)
        Table[
          ReplaceBraNumber[{4 -> 5}][v]^(2 * s1 - i)
              * ReplaceBraNumber[{4 -> 5}][u]^i
              * ReplaceBraNumber[{4 -> 3}][v]^(nV - (2 * s1 - i))
              * ReplaceBraNumber[{4 -> 3}][u]^(nU - i)  ,
          {i, 0, C - 1}]
      ];
      (*contract [25]->m and omit m*)
      amp = amp /. bL[2, 5] -> 1;
      (*recovery*)
      (*      amp = ReplaceBraNumber[{5 -> 2}] /@ amp ;*)
      amp = ReplaceBraNumber[{5 -> 2}] /@ amp // DeleteCases[___ * Power[_, i_] /; i < 0];
      amp = Reduce3Pt /@ amp // DeleteCases[0];
      Return[amp];
    ];

Gen3L[spins : {s1_, s2_, s3_}] /;
    And @@ (IntegerQ /@ (2 * spins)) &&
        And @@ (# >= 0& /@ spins) &&
        IntegerQ@(Plus @@ spins) :=
    Module[{p1, p2, mrules, frules, ReduceAmp,
      Gen1, Gen2, ps, ps2, amps1, amps2, re},
      (*4,5 as Temp; 6,7 as Temp; 11,12,13 as massive 1,2,3*)
      p1 = bL[1, 4] * bL[2, 5] * bLT[1, 2];
      p2 = bL[6, 7];

      (*reduce*)
      mrules = {bL[1, 11] -> 1, bL[2, 12] -> 1, bL[3, 13] -> 1};
      frules = {11 -> 1, 12 -> 2, 13 -> 3};
      ReduceAmp[amp_] := ReplaceBraNumber[frules][amp /. mrules];

      (* Gen amp from filling lists *)
      Gen1[{l4_List, l5_List}] := Times @@ Table[
        ReplaceBraNumber[{4 -> l4[[i]], 5 -> l5[[i]]}]@p1
        , {i, Length@l4}] // ReduceAmp;
      Gen2[{l4_List, l5_List, {x6_, x7_}}] := Gen1[{l4, l5}] * (ReplaceBraNumber[{6 -> x6, 7 -> x7}][p2] // ReduceAmp);

      (*All indices list*)
      ps = Permutations[Join[Table[11, 2 * s1], Table[12, 2 * s2], Table[13, 2 * s3]]];

      (*Type I, i = 0*)
      ps2 = {Sort[#[[1 ;; s1 + s2 + s3]]], Sort[#[[s1 + s2 + s3 + 1 ;;]]]}& /@ ps // DeleteDuplicates;
      amps1 = Gen1 /@ ps2;

      (*Type II, i = 1*)
      ps2 = {Sort[#[[1 ;; s1 + s2 + s3 - 1]]], Sort[#[[s1 + s2 + s3 ;; -3]]], Sort[#[[-2 ;; -1]]]}& /@ ps //
          DeleteDuplicates // DeleteCases[{_, _, {i_, j_}} /; i == j];
      amps2 = Gen2 /@ ps2;
      re = Reduce3Pt /@ re // DeleteCases[0];
      re = (Last@FactorizeBracket@#&) /@ Join[amps1, amps2] // DeleteDuplicates;
      Return[re];
    ];
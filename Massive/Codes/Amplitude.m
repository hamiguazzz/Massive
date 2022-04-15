(* ::Package:: *)

LogPri["Amplitude Loaded"];



(* ::Section:: *)
(*Construct Amplitude*)


MassOption[masses_List, np_] :=
    If[np > Length@masses,
      masses ~ Join ~ ConstantArray[0, np - Length@masses],
      masses[[1 ;; np]]
    ];
MassOption[massiveParticles_List, np_] /; And @@ ((IntegerQ@# && # >= 1 && # <= np)& /@ massiveParticles) := Table[
  If[!MemberQ[massiveParticles, i], 0, "\!\(\*SubscriptBox[\(m\), \(" <> ToString@i <> "\)]\)"],
  {i, np}];
MassOption[All, np_] := Table["\!\(\*SubscriptBox[\(m\), \(" <> ToString@i <> "\)]\)", {i, np}];

(*TODO change massless dealing*)
Options[ConstructAmp] = {
  antispinor -> None,
  fund -> "\[Lambda]t",
  mass -> All};
ConstructAmp[spins_, codeDim_, OptionsPattern[]] :=
    Module[ {np = Length@spins, antispinors, para, yd, filling, amps, masses},
      If[np < 4, Return[Null]];
      masses = MassOption[OptionValue@mass, np];
      antispinors = If[OptionValue@antispinor === None, ConstantArray[0, np], OptionValue@antispinor];
      If[np > Length@antispinors,
        antispinors = antispinors ~ Join ~ ConstantArray[0, np - Length@antispinors];
      ];
      If[!CheckAmpConstruction[spins, codeDim - np, antispinors, masses], Return[{}]];
      para = InnerConstructAmp[spins, antispinors, np, codeDim, masses];
      If[ Length@Select[para, Negative[#]&] != 0,
        Return[{}]
      ];
      yd = Table[0, 2, para[[1]] + para[[2]]] ~ Join ~ Table[0, np - 4, para[[1]]];
      filling = Table[Table[i, para[[2 + i]]], {i, np}]
          ~ Join ~ Table[Table[np * 2 + 1 - i, para[[-(np + 1 - i)]]], {i, np}] // Flatten // Sort;
      amps = YTtoAmpmass[#, para[[1]], Range[np],
        fund -> OptionValue[fund]]& /@
          StrangeSSYT[yd, filling, para[[1]], Range[np + 1, 2 * np, 1]];
      Return[amps];
    ];

CheckAmpConstruction[spins_, ampDim_, antispinors_, masses_] := Module[{np, minAmpDim},
  np = Length@spins;
  If[np < 3 || np != Length@antispinors || np != Length@masses, Return[False]];
  minAmpDim = Plus @@ Abs@spins;
  If[0 =!= Plus @@ MapThread[
    If[#3 === 0,
      If[#2 =!= 0, 1, 0],
      If[#2 > #1 || #2 < 0, 1, 0]
    ]&,
    {2 * spins, antispinors, masses}],
    Return[False];
  ];
  If[ampDim < minAmpDim || OddQ[ampDim + Plus @@ MapThread[
    If[#3 === 0, If[#1 > 0, 0, -2 * #1], #2]&,
    {spins, antispinors, masses}] - minAmpDim], Return[False]];
  Return[True];
];

InnerConstructAmp[spins_, antispinors_, np_, ampDim_, masses_] :=
    Module[ {Left, Right},
      Right = (ampDim - np + Total@spins - Total@antispinors) / 2;
      Left = (ampDim - np - Total@spins + Total@antispinors) / 2;
      {Left, Right} ~ Join ~
          Table[
            If[ masses[[i]] =!= 0,
              Left - antispinors[[i]],
              Left + 2 spins[[i]]],
            {i, np}] ~ Join ~
          Table[
            If[  masses[[i]] =!= 0,
              2 * spins[[i]] - antispinors[[i]],
              0],
            {i, np}] // Return;
    ];



(* ::Section:: *)
(*Massless limit reduce rules*)
(*In fact reduce faster by omitting these lower dimensions*)


(*FruleP1MLL[np_] := {*)
(*  sb[1, i_] * ab[1, j_] -> Sum[-sb[k, i] * ab[k, j], {k, 2, np}],*)
(*  sb[1, i_]^m_ * ab[1, j_] -> Sum[-sb[1, i]^(m - 1) * sb[k, i] * ab[k, j], {k, 2, np}],*)
(*  sb[1, i_] * ab[1, j_]^n_ -> Sum[-ab[1, j]^(n - 1) * sb[k, i] * ab[k, j], {k, 2, np}],*)
(*  sb[1, i_]^m_ * ab[1, j_]^n_ -> Sum[-sb[1, i]^(m - 1) * ab[1, j]^(n - 1) * sb[k, i] * ab[k, j], {k, 2, np}]};*)
(*FruleP3MLL[np_] := {*)
(*  sb[2, 3] * ab[2, 3] -> -(Sum[sb[i, j] * ab[i, j], {i, 2, 3}, {j, 4, np}]*)
(*      + Sum[sb[i, j] * ab[i, j], {i, 4, np - 1}, {j, i + 1, np}]),*)
(*  sb[2, 3]^m_ * ab[2, 3] -> -sb[2, 3]^(m - 1)*)
(*      * (Sum[sb[i, j] * ab[i, j], {i, 2, 3}, {j, 4, np}]*)
(*      + Sum[sb[i, j] * ab[i, j], {i, 4, np - 1}, {j, i + 1, np}]),*)
(*  sb[2, 3] * ab[2, 3]^n_ -> -ab[2, 3]^(n - 1)*)
(*      * (Sum[sb[i, j] * ab[i, j], {i, 2, 3}, {j, 4, np}]*)
(*      + Sum[sb[i, j] * ab[i, j], {i, 4, np - 1}, {j, i + 1, np}]),*)
(*  sb[2, 3]^m_ * ab[2, 3]^n_ -> -sb[2, 3]^(m - 1) * ab[2, 3]^(n - 1)*)
(*      * (Sum[sb[i, j] * ab[i, j], {i, 2, 3}, {j, 4, np}]*)
(*      + Sum[sb[i, j] * ab[i, j], {i, 4, np - 1}, {j, i + 1, np}])*)
(*};*)
(*  sb[2, 3] * ab[2, 3] :> Sum[sb[i, j]ab[j, i], {i, 2, np}, {j, Max[i + 1, np], np}],*)
(*  sb[2, 3]^m_ * ab[2, 3] :> sb[2, 3]^(m - 1) Sum[sb[i, j]ab[j, i], {i, 2, np}, {j, Max[i + 1, np], np}],*)
(*  sb[2, 3] * ab[2, 3]^n_ :> ab[2, 3]^(n - 1) Sum[sb[i, j]ab[j, i], {i, 2, np}, {j, Max[i + 1, np], np}],*)
(*  sb[2, 3]^m_ * ab[2, 3]^n_ :> sb[2, 3]^(m - 1) ab[2, 3]^(n - 1) Sum[sb[i, j]ab[j, i], {i, 2, np}, {j, Max[i + 1, np], np}]};*)
(*ruleSchAMLL = {*)
(*  ab[i_, l_] * ab[j_, k_] /; Signature[{i, j}] > 0 && Signature[{k, l}] > 0*)
(*      :> -ab[i, j]ab[k, l] + ab[i, k]ab[j, l],*)
(*  ab[i_, l_]^m_ * ab[j_, k_] /; Signature[{i, j}] > 0 && Signature[{k, l}] > 0*)
(*      :> ab[i, l]^(m - 1) (-ab[i, j]ab[k, l] + ab[i, k]ab[j, l]),*)
(*  ab[i_, l_] * ab[j_, k_]^n_ /; Signature[{i, j}] > 0 && Signature[{k, l}] > 0*)
(*      :> ab[j, k]^(n - 1) (-ab[i, j]ab[k, l] + ab[i, k]ab[j, l]),*)
(*  ab[i_, l_]^m_ * ab[j_, k_]^n_ /; Signature[{i, j}] > 0 && Signature[{k, l}] > 0*)
(*      :> ab[i, l]^(m - 1) ab[j, k]^(n - 1) (-ab[i, j]ab[k, l] + ab[i, k]ab[j, l])};*)
(*ruleSchSMLL = ruleSchAMLL /. ab -> sb;*)
s[i_, j_] := ab[i, j] sb[j, i];
ruleP1[Num_] := {
  sb[1, i_] ab[1, j_] :>
      Sum[-sb[k, i] ab[k, j], {k, 2, Num}],
  sb[1, i_]^m_ ab[1, j_] :>
      Sum[-sb[1, i]^(m - 1) sb[k, i] ab[k, j], {k, 2, Num}],
  sb[1, i_] ab[1, j_]^n_ :>
      Sum[-ab[1, j]^(n - 1) sb[k, i] ab[k, j], {k, 2, Num}],
  sb[1, i_]^m_ ab[1, j_]^n_ :>
      Sum[-sb[1, i]^(m - 1) ab[1, j]^(n - 1) sb[k, i] ab[k, j], {k, 2, Num}]};
ruleP2[Num_] := {
  sb[1, 2] ab[2, i_ /; i > 2 && i <= Num] :>
      Sum[-sb[1, k] ab[k, i], {k, 3, Num}],
  sb[1, 2]^m_ ab[2, i_ /; i > 2 && i <= Num] :>
      Sum[-sb[1, 2]^(m - 1) sb[1, k] ab[k, i], {k, 3, Num}],
  sb[1, 2] ab[2, i_ /; i > 2 && i <= Num]^n_ :>
      Sum[-ab[2, i]^(n - 1) sb[1, k] ab[k, i], {k, 3, Num}],
  sb[1, 2]^m_ ab[2, i_ /; i > 2 && i <= Num]^n_ :>
      Sum[-sb[1, 2]^(m - 1) ab[2, i]^(n - 1) sb[1, k] ab[k, i], {k, 3, Num}],
  sb[2, i_ /; i > 2 && i <= Num] ab[1, 2] :>
      Sum[-sb[k, i] ab[1, k], {k, 3, Num}],
  sb[2, i_ /; i > 2 && i <= Num]^m_ ab[1, 2] :>
      Sum[-sb[2, i]^(m - 1) sb[k, i] ab[1, k], {k, 3, Num}],
  sb[2, i_ /; i > 2 && i <= Num] ab[1, 2]^n_ :>
      Sum[-ab[1, 2]^(n - 1) sb[k, i] ab[1, k], {k, 3, Num}],
  sb[2, i_ /; i > 2 && i <= Num]^m_ ab[1, 2]^n_ :>
      Sum[-sb[2, i]^(m - 1) ab[1, 2]^(n - 1) sb[k, i] ab[1, k], {k, 3,
        Num}],
  sb[1, 3] ab[2, 3] :> Sum[-sb[1, i] ab[2, i], {i, 4, Num}],
  sb[1, 3]^m_ ab[2, 3] :>
      Sum[-sb[1, 3]^(m - 1) sb[1, i] ab[2, i], {i, 4, Num}],
  sb[1, 3] ab[2, 3]^n_ :>
      Sum[-ab[2, 3]^(n - 1) sb[1, i] ab[2, i], {i, 4, Num}],
  sb[1, 3]^m_ ab[2, 3]^n_ :>
      Sum[-sb[1, 3]^(m - 1) ab[2, 3]^(n - 1) sb[1, i] ab[2, i], {i, 4,
        Num}],
  sb[2, 3] ab[1, 3] :> Sum[-sb[2, i] ab[1, i], {i, 4, Num}],
  sb[2, 3]^m_ ab[1, 3] :>
      Sum[-sb[2, 3]^(m - 1) sb[2, i] ab[1, i], {i, 4, Num}],
  sb[2, 3] ab[1, 3]^n_ :>
      Sum[-ab[1, 3]^(n - 1) sb[2, i] ab[1, i], {i, 4, Num}],
  sb[2, 3]^m_ ab[1, 3]^n_ :>
      Sum[-sb[2, 3]^(m - 1) ab[1, 3]^(n - 1) sb[2, i] ab[1, i], {i, 4, Num}]
  (*~Join~{-sb[2,3]^(m-1) ab[1,3]^(n-1)esb[2]ab[1,2],-sb[2,3]^(m-1) ab[1,3]^(n-1)sb[2,1]eab[1]}*)
};
ruleP3[Num_] := {sb[2, 3] ab[2, 3] :>
    Sum[s[i, j], {i, 2, Num}, {j, Max[i + 1, 4], Num}],
  sb[2, 3]^m_ ab[2, 3] :>
      sb[2, 3]^(m - 1) Sum[
        s[i, j], {i, 2, Num}, {j, Max[i + 1, 4], Num}],
  sb[2, 3] ab[2, 3]^n_ :>
      ab[2, 3]^(n - 1) Sum[
        s[i, j], {i, 2, Num}, {j, Max[i + 1, 4], Num}],
  sb[2, 3]^m_ ab[2, 3]^n_ :>
      sb[2, 3]^(m - 1) ab[2, 3]^(n - 1) Sum[
        s[i, j], {i, 2, Num}, {j, Max[i + 1, 4], Num}]};
ruleSchA = {ab[i_, l_] ab[j_, k_] /;
    i < j < k < l :> (-ab[i, j] ab[k, l] + ab[i, k] ab[j, l]),
  ab[i_, l_]^m_ ab[j_, k_] /; i < j < k < l :>
      ab[i, l]^(m - 1) (-ab[i, j] ab[k, l] + ab[i, k] ab[j, l]),
  ab[i_, l_] ab[j_, k_]^n_ /; i < j < k < l :>
      ab[j, k]^(n - 1) (-ab[i, j] ab[k, l] + ab[i, k] ab[j, l]),
  ab[i_, l_]^m_ ab[j_, k_]^n_ /; i < j < k < l :>
      ab[i, l]^(m - 1) ab[j, k]^(n - 1) (-ab[i, j] ab[k, l] +
          ab[i, k] ab[j, l])};
ruleSchS = ruleSchA /. ab -> sb;
RuleOmitLowDim[np_] := Table[sb[i, 2 * np - i + 1] -> 0, {i, 1, np}];


(* ::Section:: *)
(*matching mass dimension*)


Options[MatchCFDim] = {
  explicitmass -> False,
  fund -> "\[Lambda]t",
  mass -> All};
MatchCFDim[np_, opts : OptionsPattern[]] := MatchCFDim[#, np, FilterRules[{opts}, Options[MatchCFDim]]]&;
MatchCFDim[amp_, np_, OptionsPattern[]] :=
    Module[ {
      massRev, masses = MassOption[OptionValue@mass, np],
      amplist1, amplist2,
      labelnum1 = Table[i -> {}, {i, np}] // Association,
      labelnum2 = Table[i -> {}, {i, np}] // Association, factor = 1},
      massRev = If[OptionValue@explicitmass,
        (If[# == 0, 0, 1 / #])& /@ masses,
        (If[# == 0, 0, 1])& /@ masses
      ];
      amplist1 =
          amp //. {Times -> List, ab -> List, sb[i_, j_] -> {},
            Power[y_, z_] /; Element[z, PositiveIntegers] :>
                ConstantArray[y, z]} // Flatten;
      amplist2 =
          amp //. {Times -> List, ab[i_, j_] -> {}, sb -> List,
            Power[y_, z_] /; Element[z, PositiveIntegers] :>
                ConstantArray[y, z]} // Flatten;
      Do[If[ massRev[[i]] === 0,
        Continue[]
      ];
      labelnum1[i] = Count[amplist1, i];
      labelnum2[i] = Count[amplist2, i];
      If[ OptionValue[fund] === "\[Lambda]t",
        Do[factor *= -sb[i, 2 * np + 1 - i] * massRev[[i]],
          {j, labelnum1[i] - labelnum2[i]}],
        Do[factor *= ab[i, 2 * np + 1 - i] * massRev[[i]],
          {j, labelnum1[i] - labelnum2[i]}]
      ], {i, np}];
      Return[amp * factor];
    ];



(* ::Subsection:: *)
(*Reduce function*)


ReduceRules[Np_] :=
    Join[ruleP1[Np], ruleP2[Np], ruleP3[Np], ruleSchA, ruleSchS];

SetAttributes[InnerReduceDictPart, HoldFirst];
InnerReduceDictPart[dict_, amplst_, applyFun_] :=
    Module[ {i, factor, base, nextLevelAmpList, currentAmp, midResult, singleTermResult},
      If[ Length[amplst] === 1,
        (*init part start*)
        currentAmp = amplst[[1]];
        If[ FactorizeBracket@currentAmp //
            (factor = #[[1]];
            base = #[[2]];)&;
        dict ~ KeyExistsQ ~ base,
          Return[factor * dict[base] // Expand // List]
        ];
        nextLevelAmpList = applyFun@{currentAmp};
        (*init part end*)
        If[ Length[nextLevelAmpList] === 1,
          (* base part start *)
          (*reduce single term to right form*)
          (*single term may be reduced twice or more*)
          singleTermResult = nextLevelAmpList;
          While[
            midResult = applyFun@singleTermResult;
            midResult =!= singleTermResult,
            singleTermResult = midResult;
          ];
          FactorizeBracket@currentAmp
              // (factor = #[[1]]; base = #[[2]];)&;
          dict ~ AssociateTo ~ (base -> Expand[1 / factor * Total@singleTermResult]);
          Return[singleTermResult];
          (* base part end *)
          ,
          (*recursion for every term*)
          Return[Reap[Do[
            FactorizeBracket@currentAmp // (factor = #[[1]];
            base = #[[2]];)&;
            dict ~ AssociateTo ~ (base -> Expand[1 / factor *
                Total@Sow[InnerReduceDictPart[dict, {currentAmp}, applyFun]]])
            , {currentAmp, nextLevelAmpList}]] // Last // Flatten];
        ],
        (*recursion for every term*)
        Return[Reap[Do[
          FactorizeBracket@currentAmp // (factor = #[[1]];
          base = #[[2]];)&;
          dict ~ AssociateTo ~ (base -> Expand[1 / factor *
              Total@Sow[InnerReduceDictPart[dict, {currentAmp}, applyFun]]])
          , {currentAmp, amplst}]] // Last // Flatten];
      ]
    ];

SetAttributes[ReduceWithDict, HoldFirst];
If[!AssociationQ[globalReduceDict], globalReduceDict = <||>;];
IniGlobalReduceDict[np_] := (
  If[!AssociationQ[globalReduceDict], globalReduceDict = <||>;];
  If[!KeyExistsQ[globalReduceDict, np], globalReduceDict[np] = <||>;]);
ReduceWithDict[dict_?AssociationQ, np_Integer] := ReduceWithDict[dict, #, np]&;
ReduceWithDict[np_Integer] := (IniGlobalReduceDict[np];ReduceWithDict[globalReduceDict[np],
  #, np]&);
ReduceWithDict[amp_, np_Integer] := (IniGlobalReduceDict[np];ReduceWithDict[globalReduceDict[np],
  amp, np]);
ReduceWithDict[dict_, amp_Integer, np_Integer] := amp;
ReduceWithDict[dict_, amps_List, np_Integer] := ReduceWithDict[dict, #, np]& /@ amps;
ReduceWithDict[dict_, amp_, np_Integer] :=
    Module[ {F, dispRules, applyFun},
      dispRules = ReduceRules[np];
      applyFun = ( Plus @@ Map[(# /. dispRules) &, #] // Expand // Sum2List) &;
      F = InnerReduceDictPart[dict, Sum2List[Expand[amp]], applyFun] // Flatten // Total // Expand;
      Return[F];
    ];

(*TODO better mass options fit for all massive particle amounts*)
Options[ReduceSt] = {
  tryMax -> 30,
  parallelized -> False
};
ReduceSt[np_Integer, opts : OptionsPattern[]] := ReduceSt[# , np, FilterRules[{opts}, Options[ReduceSt]]]&;
ReduceSt[amp_Integer, np_Integer, OptionsPattern[]] := amp;
ReduceSt[amp_, np_Integer, OptionsPattern[]] :=
    Module[ {F = Expand@amp, F1, iter = 1, dispRules, applyFun},
      dispRules = ReduceRules[np];
      applyFun = (
        Plus @@ (Expand /@ ((If[! OptionValue[parallelized], Map, ParallelMap])
        [(# /. dispRules) &, Sum2List@#] ))) &;
      While[True,
        F1 = applyFun@F;
        If[ F1 === F,
          Break[],
          F = F1
        ];
        If[ iter >= OptionValue@tryMax,
          LogPri["err", "[reduce] too many reductions!"];
          LogPri[F];
          Break[],
          iter++
        ]];
      Return[F // Expand]
    ];


(* ::Section:: *)
(*coefficient matrix*)


FindCor[amp_, ampDbasis_] := FindCoordinate[amp, ampDbasis, !(MatchQ[#, _ab | _sb]) &];
FindCor[ampDbasis_] := FindCoordinate[#, ampDbasis, !(MatchQ[#, _ab | _sb]) &]&;



(* ::Section:: *)
(*obtain d-dim basis*)


$MaxKernelAmount = 4;
Options[ReduceToBH] = {
  minalParalledAmount -> 100,
  kernelAmount -> "Auto", log -> False, (*Global option*)
  withDict -> True, (*True to ModeII, False to ModeI *)
  externalReduceDict -> <||>, (*Mode II only*)
  synctask -> Infinity, synctime -> Infinity, (*Mode II only*)
  fund -> "\[Lambda]t", tryMax -> Infinity, maxntcount -> Infinity (*Mode I only*)
};
ReduceToBH[ampsFrom_List, bhBasis_List, np_Integer, opts : OptionsPattern[]] :=
    ReduceToBH[
      Table[ampsFrom[[i]] -> i, {i, Length@ampsFrom}] // Association
      , bhBasis, np, opts];
ReduceToBH[ampsFromDict_Association, bhBasis_List, np_Integer, OptionsPattern[]] :=
    Module[ {coorDict, reduceFun, amps = Keys@ampsFromDict, dealingAmp,
      separateAmpCalcList = {}, kernels = Length[Kernels[]], dictSync},
      If[Length@ampsFromDict < OptionValue@minalParalledAmount,
        Return[Table[
          k -> FindCor[bhBasis]@ReduceWithDict[np]@k,
          {k, Keys@ampsFromDict}] // Association]];
      coorDict = <||>;
      SetSharedVariable[coorDict];
      If[ kernels === "Auto",
        LaunchKernels[$MaxKernelAmount - kernels];
        kernels = Length[Kernels[]];
      ];
      If[ OptionValue @ kernelAmount != "Auto" && kernels < OptionValue @ kernelAmount,
        LaunchKernels[OptionValue @ kernelAmount - kernels];
        kernels = Length[Kernels[]];
      ];
      If[ OptionValue@withDict === False,
        If[OptionValue@log, LogPri["Direct decomposition..."];];
        reduceFun =
            FindCor[bhBasis]@
                ReduceSt[#, np, parallelized -> False, tryMax -> OptionValue@tryMax] &;
        (*SetSharedVariable[ampsFromDict, separateAmpCalcList, amps]*);
        If[OptionValue@log, LogPri["U(N) heads over ", OptionValue@maxntcount,
          " will be calculated separately."];];
        ParallelDo[
          dealingAmp = amps[[i]];
          If[CountHead[If[ OptionValue@fund === "\[Lambda]t",
            ab,
            sb
          ]]@dealingAmp <= OptionValue@maxntcount,
            coorDict ~ AssociateTo ~ (dealingAmp -> reduceFun@dealingAmp)
            ,
            separateAmpCalcList ~ AppendTo ~ dealingAmp;
          ], {i, Length[amps]}
          , DistributedContexts -> Automatic]
            // AbsoluteTiming // First
            // If[OptionValue@log, LogPri["part1 N=", Length[amps] - Length[separateAmpCalcList],
          " costs:", #]] &;
        reduceFun =
            FindCor[bhBasis]@
                ReduceSt[#, np, parallelized -> True, tryMax -> OptionValue@tryMax] &;
        Do[
          dealingAmp = separateAmpCalcList[[i]];
          coorDict ~ AssociateTo ~ (dealingAmp -> reduceFun@dealingAmp)
          , {i, Length[separateAmpCalcList]}]
            // AbsoluteTiming // First
            // If[OptionValue@log, LogPri["part2 N=", Length[separateAmpCalcList], " costs:", #];] &;
        ,
        If[OptionValue@log, LogPri["Dict decomposition..."];];
        (*Build parallelized fun : reduceFun*)
        reduceFun[dict_, amp_] :=
            coorDict ~ AssociateTo ~ (amp -> FindCor[bhBasis] @
                ReduceWithDict[dict, amp, np]);
        SetAttributes[reduceFun, HoldFirst];
        (*SetSharedVariable[ampsFromDict, dictSync]*);
        dictSync = OptionValue@externalReduceDict;
        (*Context must contains current package path*)
        SyncDataTask[dictSync, reduceFun, amps, synctask -> OptionValue@synctask,
          synctime -> OptionValue@synctime, context -> $ContextPath]
            // AbsoluteTiming
            // If[OptionValue@log, LogPri["dict reduction cost ", #[[1]]]]& ;
      ];
      Return[coorDict];
    ];

CalcNeededFakeDim[spins_List, physicalDim_Integer, massParm_ : All] := Module[
  {np = Length@spins, masses, dimFakeMinimal, dimMin, spinLeft, dims},
  masses = MassOption[massParm, np];
  dimFakeMinimal = np + Plus @@ Abs@spins;
  Return[Range[
    Max[
      dimFakeMinimal,
      If[OddQ[physicalDim - dimFakeMinimal], physicalDim + 1, physicalDim]
    ],
    If[OddQ[# - dimFakeMinimal], # - 1, #]&[physicalDim + Plus @@ MapThread[If[#2 =!= 0, 2 * #1, 0]&, {spins, masses}]]
    , 2]];
];

CalcFakeDim[codeDim_Integer, antispinor_List] := codeDim + Plus @@ antispinor;
CalcPhysicalDim[spins_List, codeDim_Integer, antispinor__List, massParm_ : All] :=
    codeDim - Plus @@ MapThread[
      If[#2 =!= 0 && #1 == 1 && #3 == 1, 1, 0]&,
      {spins, MassOption[massParm, Length@spins], antispinor}];

Options@ConstructCFIByFakeDim = Normal@Association@(Join @@ (Options /@
    {ConstructAmp, MatchCFDim, ReduceToBH}));
ConstructCFIByFakeDim[spins_, fakeDim_, opts : OptionsPattern[]] :=
    Module[
      {
        np, masses, constructOpts, reduceOpts, dimFakeMinimal,
        TimingTest, GenCFs, antiList, cfIndexList, bhs, cfsDict, cfsDictReverse, matchOpts,
        matchedCFCoordinateDict, totalCF, totalCoordinate, independentIndex, metaInfo},
      np = Length@spins;
      masses = MassOption[OptionValue@mass, np];
      constructOpts = FilterRules[{opts}, Options@ConstructAmp];
      matchOpts = FilterRules[{opts}, Options@MatchCFDim];
      reduceOpts = FilterRules[{opts}, Options@ReduceToBH];
      dimFakeMinimal = np + Plus @@ Abs@spins;

      If[fakeDim < dimFakeMinimal, Throw[{fakeDim, "Below minimal operator dimension!"}]];
      If[OddQ[fakeDim - dimFakeMinimal], Throw[{fakeDim, "Wrong fake dimension!"}]];

      TimingTest[message_] := (# // AbsoluteTiming //
          (If[OptionValue@log, LogPri[message, #[[1]]];];#[[2]])&)&;
      GenCFs[{codeDim_, antispinors_}] := ConstructAmp[spins, codeDim, antispinor -> antispinors, constructOpts];

      antiList = Fold[
        (Flatten[#, 1]&@
            Table[l ~ Append ~ i, {l, #1}, {i, 0,
              If[masses[[#2]] === 0, 0, 2 * spins[[#2]]]}]
        )&, {{}}, Range[np]] // DeleteCases[ConstantArray[0, np]];
      cfIndexList = Table[If[fakeDim - Plus @@ a >= dimFakeMinimal, {fakeDim - Plus @@ a, a}, Missing[]],
        {a, antiList}] // DeleteMissing;

      If[OptionValue@log,
        LogPri["Involved BH basis spins: ", spins, " @dim = " , fakeDim];
        LogPri["Involved CF basis : ", cfIndexList];];

      (
        bhs = ConstructAmp[spins, fakeDim, constructOpts];
        cfsDict = Association@Table[e -> GenCFs@e, {e, cfIndexList}];
        cfsDictReverse = ReverseDict@cfsDict;
        cfsDictReverse = cfsDictReverse // KeySortBy[
          CalcPhysicalDim[spins, cfsDictReverse[#][[1]], cfsDictReverse[#][[2]], masses]&];
      ) // TimingTest["Constructing amplitudes costs:"];

      If[Length[cfsDictReverse] == 0,
        If[Length@bhs == 0,
          Throw["No such operator!"];,
          metaInfo = {"spins" -> spins, "fakeDim" -> fakeDim,
            "mass" -> masses, "opts" -> {opts}} // Association;
          Return[
            {IdentityMatrix[Length@bhs],
              <|"basis" -> bhs, "cf" -> <||>, "bh" -> bhs, "metaInfo" -> metaInfo|>}
          ];
        ];
      ];

      If[OptionValue@log,
        LogPri["Involved CF(except BH) amplitude amount is ", cfsDictReverse // Length];
        LogPri["Involved BH amplitude amount is ", bhs // Length];];

      matchedCFCoordinateDict = ReduceToBH[MatchCFDim[np, matchOpts] /@ Keys@cfsDictReverse, bhs, np, reduceOpts] //
          TimingTest["Coefficients totally costs:"];

      totalCF = Keys@cfsDictReverse ~ Join ~ bhs;
      totalCoordinate = Join[
        matchedCFCoordinateDict[MatchCFDim[np, matchOpts]@#]& /@ Keys@cfsDictReverse,
        IdentityMatrix[Length@bhs]];
      independentIndex = FindIndependentBasisPos[totalCoordinate];
      metaInfo = {"spins" -> spins, "fakeDim" -> fakeDim,
        "mass" -> masses, "opts" -> {opts}} // Association;
      Return[{totalCoordinate[[independentIndex]],
        <|"basis" -> totalCF[[independentIndex]], "cf" -> cfsDict, "bh" -> bhs, "metaInfo" -> metaInfo|>}];
    ];

SeparateFakeResultPhysical[{iCFCoor_?MatrixQ, data_Association}] :=
    Module[{
      PhysicalCalc, DimCalc, icfs, bhs, cfs, fakeDim
    },
      fakeDim = data["metaInfo"]["fakeDim"];
      icfs = data["basis"];
      bhs = data["bh"];
      cfs = data["cf"] // ReverseDict;
      DimCalc[{codeDim_, antispinor_}] := CalcPhysicalDim[data["metaInfo"]["spins"], codeDim, antispinor,
        data["metaInfo"]["mass"]];
      PhysicalCalc[amp_] := If[MemberQ[bhs, amp], fakeDim, DimCalc[cfs[amp]]];
      Return[PositionIndex[PhysicalCalc /@ icfs]];
    ];
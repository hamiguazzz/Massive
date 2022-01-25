LogPri["Amplitude Loaded"];

(* ::Section:: *)
(*Construct Amplitude*)
MassOption[masses_List, np_] /; StringQ[masses[[1]]] := masses;
MassOption[massesless_List, np_] /; IntegerQ[massesless[[1]]] := Table[
  If[MemberQ[massesless, i], 0, "\!\(\*SubscriptBox[\(m\), \(" <> ToString@i <> "\)]\)"],
  {i, np}];
MassOption[All, np_] := Table["\!\(\*SubscriptBox[\(m\), \(" <> ToString@i <> "\)]\)", {i, np}];

Options[ConstructAmp] = {
  antispinor -> None,
  fund -> "\[Lambda]t",
  mass -> All};
ConstructAmp[spins_, ampDim_, OptionsPattern[]] :=
    Module[ {np = Length@spins, antispinors, para, yd, filling, amps, masses},
      If[np < 4, Return[Null]];
      masses = MassOption[OptionValue@mass, np];
      antispinors = If[OptionValue@antispinor === None, ConstantArray[0, np], OptionValue@antispinor];
      para = InnerConstructAmp[spins, antispinors, np, ampDim, masses];
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

FruleP1MLL[np_] := {
  sb[1, i_] * ab[1, j_] -> Sum[-sb[k, i] * ab[k, j], {k, 2, np}],
  sb[1, i_]^m_ * ab[1, j_] -> Sum[-sb[1, i]^(m - 1) * sb[k, i] * ab[k, j], {k, 2, np}],
  sb[1, i_] * ab[1, j_]^n_ -> Sum[-ab[1, j]^(n - 1) * sb[k, i] * ab[k, j], {k, 2, np}],
  sb[1, i_]^m_ * ab[1, j_]^n_ -> Sum[-sb[1, i]^(m - 1) * ab[1, j]^(n - 1) * sb[k, i] * ab[k, j], {k, 2, np}]};
FruleP3MLL[np_] := {
  sb[2, 3] * ab[2, 3] -> -1 / 2 * (Sum[sb[i, j] * ab[i, j], {i, 2, 3}, {j, 4, np}]
      + Sum[sb[i, j] * ab[i, j], {i, 4, np}, {j, i + 1, np}]),
  sb[2, 3]^m_ * ab[2, 3] -> -1 / 2 * sb[2, 3]^(m - 1) * (Sum[sb[i, j] * ab[i, j], {i, 2, 3}, {j, 4, np}]
      + Sum[sb[i, j] * ab[i, j], {i, 4, np}, {j, i + 1, np}]),
  sb[2, 3] * ab[2, 3]^n_ -> -1 / 2 * ab[2, 3]^(n - 1) * (Sum[sb[i, j] * ab[i, j], {i, 2, 3}, {j, 4, np}]
      + Sum[sb[i, j] * ab[i, j], {i, 4, np}, {j, i + 1, np}]),
  sb[2, 3]^m_ * ab[2, 3]^n_ -> -1 / 2 * sb[2, 3]^(m - 1) ab[2, 3]^(n - 1) * (Sum[sb[i, j] * ab[i, j], {i, 2, 3}, {j, 4, np}]
      + Sum[sb[i, j] * ab[i, j], {i, 4, np}, {j, i + 1, np}])
};
(*  sb[2, 3] * ab[2, 3] :> Sum[sb[i, j]ab[j, i], {i, 2, np}, {j, Max[i + 1, np], np}],*)
(*  sb[2, 3]^m_ * ab[2, 3] :> sb[2, 3]^(m - 1) Sum[sb[i, j]ab[j, i], {i, 2, np}, {j, Max[i + 1, np], np}],*)
(*  sb[2, 3] * ab[2, 3]^n_ :> ab[2, 3]^(n - 1) Sum[sb[i, j]ab[j, i], {i, 2, np}, {j, Max[i + 1, np], np}],*)
(*  sb[2, 3]^m_ * ab[2, 3]^n_ :> sb[2, 3]^(m - 1) ab[2, 3]^(n - 1) Sum[sb[i, j]ab[j, i], {i, 2, np}, {j, Max[i + 1, np], np}]};*)
ruleSchAMLL = {
  ab[i_, l_] * ab[j_, k_] /; Signature[{i, j}] > 0 && Signature[{k, l}] > 0
      :> -ab[i, j]ab[k, l] + ab[i, k]ab[j, l],
  ab[i_, l_]^m_ * ab[j_, k_] /; Signature[{i, j}] > 0 && Signature[{k, l}] > 0
      :> ab[i, l]^(m - 1) (-ab[i, j]ab[k, l] + ab[i, k]ab[j, l]),
  ab[i_, l_] * ab[j_, k_]^n_ /; Signature[{i, j}] > 0 && Signature[{k, l}] > 0
      :> ab[j, k]^(n - 1) (-ab[i, j]ab[k, l] + ab[i, k]ab[j, l]),
  ab[i_, l_]^m_ * ab[j_, k_]^n_ /; Signature[{i, j}] > 0 && Signature[{k, l}] > 0
      :> ab[i, l]^(m - 1) ab[j, k]^(n - 1) (-ab[i, j]ab[k, l] + ab[i, k]ab[j, l])};
ruleSchSMLL = ruleSchAMLL /. ab -> sb;


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

ReduceRules[np_] := Join[FruleP1MLL[np], FruleP3MLL[np], ruleSchSMLL, ruleSchAMLL];

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
      applyFun = (Map[(# /. dispRules) &, #]
          // Total // Expand // Sum2List) &;
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
    Module[ {F = amp, F1, iter = 1, dispRules, applyFun},
      dispRules = ReduceRules[np];
      applyFun = ((If[! OptionValue[parallelized], Map, ParallelMap])
      [(# /. dispRules) &, Sum2List[Expand[#]]] // Total // Expand) &;
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
        LogPri["Direct decomposition..."];
        reduceFun =
            FindCor[bhBasis]@
                ReduceSt[#, np, parallelized -> False, tryMax -> OptionValue@tryMax] &;
        (*SetSharedVariable[ampsFromDict, separateAmpCalcList, amps]*);
        LogPri["U(N) heads over ", OptionValue@maxntcount,
          " will be calculated separately."];
        ParallelDo[
          dealingAmp = amps[[i]];
          If[CountHead[If[ OptionValue@fund === "\[Lambda]t",
            ab,
            sb
          ]]@dealingAmp <= OptionValue@maxntcount,
            coorDict ~ AssociateTo ~ (dealingAmp -> reduceFun@dealingAmp)
                // AbsoluteTiming
                // If[OptionValue@log, LogPri[ampsFromDict[dealingAmp], " cost ", #[[1]]]&, Identity];
            ,
            separateAmpCalcList ~ AppendTo ~ dealingAmp;
          ], {i, Length[amps]}
          , DistributedContexts -> Automatic]
            // AbsoluteTiming // First
            // LogPri["part1 N=", Length[amps] - Length[separateAmpCalcList],
          " costs:", #] &;
        reduceFun =
            FindCor[bhBasis]@
                ReduceSt[#, np, parallelized -> True, tryMax -> OptionValue@tryMax] &;
        Do[
          dealingAmp = separateAmpCalcList[[i]];
          coorDict ~ AssociateTo ~ (dealingAmp -> reduceFun@dealingAmp) //
              AbsoluteTiming // If[OptionValue@log, LogPri[ampsFromDict[dealingAmp], " cost ", #[[1]]]&, Identity];
          , {i, Length[separateAmpCalcList]}]
            // AbsoluteTiming // First
            // LogPri["part2 N=", Length[separateAmpCalcList], " costs:", #] &;
        ,
        LogPri["Dict decomposition..."];
        (*Build parallelized fun : reduceFun*)
        reduceFun[dict_, amp_] :=
            coorDict ~ AssociateTo ~ (amp -> FindCor[bhBasis] @
                ReduceWithDict[dict, amp, np])
                // AbsoluteTiming
                // If[OptionValue@log, LogPri[ampsFromDict[amp], " cost ", #[[1]]]&, Identity];
        SetAttributes[reduceFun, HoldFirst];
        Options[reduceFun] = {
          log -> OptionValue@log
        };
        (*SetSharedVariable[ampsFromDict, dictSync]*);
        dictSync = OptionValue@externalReduceDict;
        (*Context must contains current package path*)
        SyncDataTask[dictSync, reduceFun, amps, synctask -> OptionValue@synctask,
          synctime -> OptionValue@synctime, context -> $ContextPath];
        Sow[dictSync, "reduceDict"];
      ];
      Return[coorDict];
    ];

Options[ConstructBasis] = {
  explicitmass -> False, fund -> "\[Lambda]t", mass -> All,
  withDict -> True, kernelAmount -> "Auto", log -> False,
  maxntcount -> Infinity, tryMax -> Infinity,
  synctask -> Infinity, synctime -> Infinity, externalReduceDict -> <||>};
ConstructBasis[spins_, operDim_, opts : OptionsPattern[]] :=
    Module[
      {
        metaInfo, masses = MassOption[OptionValue@mass, Length@spins],
        antiList, dimCodeMinimal, np = Length@spins,
        CalcOperatorDimContribute, nAMax, dimCFFrom, dimCFTo,
        GetNeededBHBasisDimList,
        NeededCFBasisQ,
        sortedBasis, sortedCFCoordinates,
        cfIndexList, bhDimList,
        cfBasisDict, bhBasisDict,
        matchedCFDict, reversedCFBasisDict, reducedAmpDict,
        cfCoordinateDict = <||>, bhBasis, reduceDict,
        constructOpts, reduceOpts,
        GenBHBasis, GenCFBasis,
        ZRank
      },
      (*Construct amplitude index*)
      CalcOperatorDimContribute[spin_] := Switch[spin, 0, 1, 1 / 2, 3 / 2, 1, 2,
        _, Throw[{spin, "No such spin"}]];
      nAMax = Count[spins, 1];
      dimCodeMinimal = Total[CalcOperatorDimContribute /@ spins];
      (*minimal operator dimension *)
      (*d_o = d_c - nA*)
      (*l -> 0,...,spin*2*)
      (*massive CF[d_c,sumL]->BH[d_c+sumL] & .. &BH[dimMin] *)
      (*MLL CF[d_c,sumL]->BH[dim+sumL]*)
      If[operDim < dimCodeMinimal - nAMax, Throw[{operDim, "Below minimal operator dimension!"}]];
      dimCFFrom = Max[dimCodeMinimal, operDim - 2 * Total[spins]];
      dimCFTo = operDim + nAMax;
      GetNeededBHBasisDimList[indexListInner_] :=
          PositionIndex@((#[[1]] + Total@#[[2]])& /@
              Cases[indexListInner, {dim_ /; (dim >= operDim && dim <= dimCFTo), _}]) // Keys;
      NeededCFBasisQ[dim_, antiSpinors_, includeLowerDim_ : False] :=
          (*check dim-nA===operDim*)
          If[includeLowerDim,
            ((dim -
                (ReleaseHold[HoldForm[#1 * #2] /. i_ /; i != 1 -> 0] // Total)&
            [spins, antiSpinors]) <= operDim) &&
                (*check (dim+sumS-dimMin)Even*)
                EvenQ[dim + Total[antiSpinors] - dimCodeMinimal],
            ((dim -
                (ReleaseHold[HoldForm[#1 * #2] /. i_ /; i != 1 -> 0] // Total)&
            [spins, antiSpinors]) == operDim) &&
                (*check (dim+sumS-dimMin)Even*)
                EvenQ[dim + Total[antiSpinors] - dimCodeMinimal]
          ]
      ;
      antiList = Fold[
        (Do[Do[Sow[l ~ Append ~ i], {i, 0, #2}], {l, #1}] // Reap // Last // First )&,
        {{}}, 2 * spins
      ] // GroupBy[#, Total]&;

      cfIndexList =
          Reap[Table[
            If[NeededCFBasisQ[dim, antiList[antiSum][[index]], True] ,
              Sow[{dim, antiList[antiSum][[index]]}]],
            {dim, dimCFFrom, dimCFTo}, {antiSum, 0, 2 * Total[spins]},
            {index, Length[antiList[antiSum]]}]] // Last;

      If[Length[cfIndexList] == 0,
        Throw["No such operator!"];
        ,
        cfIndexList = cfIndexList[[1]];
      ];
      bhDimList = GetNeededBHBasisDimList[cfIndexList];
      ZRank[matrix_] := If[matrix === {}, 0, MatrixRank@matrix];
      constructOpts = Association@ FilterRules[{opts}, Options[ConstructAmp]];
      constructOpts = Normal@AssociateTo[constructOpts, mass -> masses];

      cfIndexList = Cases[cfIndexList, {dim_, antiSpinors_} /;
          (MemberQ[bhDimList, dim + Total@antiSpinors])
      ];
      LogPri["Involved BH basis : ", bhDimList];
      LogPri["Involved CF basis : ", cfIndexList];
      GenBHBasis[dim_] := ConstructAmp[spins, dim, constructOpts];
      GenCFBasis[dim_, antispinorList_] := ConstructAmp[
        spins, dim, antispinor -> antispinorList, constructOpts];
      (
        bhBasisDict = ParallelMap[(# -> GenBHBasis@#)& , bhDimList ] // Association // KeySort;
        bhBasis = bhBasisDict // Values // Flatten;
        cfBasisDict = ParallelMap[(# -> GenCFBasis @@ #)& , cfIndexList] // Association;
        reversedCFBasisDict = ReverseDict[cfBasisDict];
      ) // AbsoluteTiming // LogPri["Constructing amplitudes costs ", #[[1]]]&;

      reduceOpts = Association@ FilterRules[{opts}, Options[ReduceToBH]];
      reduceOpts = If[OptionValue@withDict,
        reduceOpts // Normal,
        AssociateTo[reduceOpts, maxntcount ->
            If[ OptionValue@maxntcount == "Auto",
              Max[CountHead[If[ OptionValue@fund == "\[Lambda]t",
                ab, sb
              ]] /@ Keys[reversedCFBasisDict]] - 1,
              OptionValue@maxntcount
            ];
        ] // Normal;
      ];
      matchedCFDict = reducedAmpDict = <||>;
      Do[
        If[!KeyExistsQ[matchedCFDict, #],
          AssociateTo[matchedCFDict, # -> e];
          AssociateTo[reducedAmpDict, # -> reversedCFBasisDict[e]];
        ]&@MatchCFDim[e, np, FilterRules[{opts}, Options[MatchCFDim]]];
        , {e, Keys@reversedCFBasisDict}];

      cfCoordinateDict = ReduceToBH[
        reducedAmpDict, bhBasis, np, reduceOpts] // Reap
          // AbsoluteTiming
          // (LogPri["Coefficients totally costs:", #[[1]]]; #[[2]])& ;
      If[!OptionValue@withDict,
        cfCoordinateDict = cfCoordinateDict[[1]];,
        reduceDict = cfCoordinateDict[[2]][[1]][[1]];
        cfCoordinateDict = cfCoordinateDict[[1]];
      ];
      cfCoordinateDict = Association @ Table[matchedCFDict[e] -> cfCoordinateDict[e], {e, Keys@ reducedAmpDict}];
      LogPri["Involved CF amplitude amount is ", reversedCFBasisDict // Length];
      LogPri["Involved BH amplitude amount is ", bhBasis // Length];
      (*      LogPri["Involved BH amplitude amount is ",*)
      (*        Fold[Plus, ConstantArray[0, Length@bhBasis],*)
      (*          Map[((# == 0) /. {True -> 0, False -> 1}) &,*)
      (*            (Values@coordinateDict), {2}]]*)
      (*            // DeleteCases[#, 0] & // Length*)
      (*      ];*)
      LogPri["Coordinate rank is ", ZRank[Values@cfCoordinateDict]];
      (*Sort*)
      sortedBasis = Keys[cfCoordinateDict] //
          SortBy[(Total@Flatten@reversedCFBasisDict[matchedCFDict[#]])&];
      sortedCFCoordinates = cfCoordinateDict[#]& /@ sortedBasis;

      (*Get independent basis*)
      ((sortedBasis = sortedBasis[[#]]; sortedCFCoordinates = sortedCFCoordinates[[#]])&@
          Flatten[Position[#, Except[0, _?NumericQ], 1, 1] & /@
              RowReduce@Transpose@
                  ReplaceAll[sortedCFCoordinates, Table[If[e =!= 0, e -> 1], {e, masses}]]
          ]) // AbsoluteTiming //
          LogPri["Ranking costs ", #[[1]]]&;
      (*TODO reduce identical particles*)
      (*Select from minimal dimension*)
      (*This should not be done now.  Otherwise the permutation operator matrix will be wrong*)
      (*      index = Flatten@Position[permutedBasis,*)
      (*        e_ /; MemberQ[#, e], 1*)
      (*      ]&@Select[permutedBasis,*)
      (*        NeededCFBasisQ[reversedCFBasisDict[cfPermutedDict[#]][[1]], reversedCFBasisDict[cfPermutedDict[#]][[2]], False]&];*)
      (*      (permutedBasis = permutedBasis[[#]];*)
      (*      permutedBasisCoor = permutedBasisCoor[[#]];)&@index;*)
      (*      LogPri["Final basis amount is ", Length@permutedBasis];*)
      metaInfo = {"spins" -> spins, "operDim" -> operDim,
        "mass" -> masses, "explicitmass" -> OptionValue@explicitmass, "NeededCFBasisQ" -> NeededCFBasisQ} // Association;
      Return[{sortedCFCoordinates,
        <|"basis" -> sortedBasis, "coordinate" -> cfCoordinateDict,
          "cf" -> cfBasisDict, "bh" -> bhBasisDict, "reduceDict" -> reduceDict, "metaInfo" -> metaInfo
        |>}];
    ];

PositionOperatorPhysicalDim[constructBasisResult : {coor_List, constructBasisData_Association}] :=
    PositionOperatorPhysicalDim[constructBasisData];
PositionOperatorPhysicalDim[constructBasisData_Association] := Module[
  {NeededCFBasisQ, cfBasisDict, reverseBasisDict, basis, index},
  NeededCFBasisQ = constructBasisData["metaInfo"]["NeededCFBasisQ"];
  cfBasisDict = constructBasisData["cf"];
  basis = constructBasisData["basis"];
  reverseBasisDict = ReverseDict@cfBasisDict;
  index = (NeededCFBasisQ[#[[1]], #[[2]], False]&@reverseBasisDict[#]&@#)& /@ basis // PositionIndex;
  Return[index[True]];
];
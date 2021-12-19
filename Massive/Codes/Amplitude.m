(*TODO construct amplitude for all amounts*)

LogPri["Amplitude Loaded"];
(*TODO better mass options fit for all massive particle amounts*)
(* ::Subsection:: *)
(*Reduce function*)

Options[ReduceRules] = {
  fund -> "\[Lambda]t",
  mass -> {
    "\!\(\*SubscriptBox[\(m\), \(1\)]\)",
    "\!\(\*SubscriptBox[\(m\), \(2\)]\)",
    "\!\(\*SubscriptBox[\(m\), \(3\)]\)",
    "\!\(\*SubscriptBox[\(m\), \(4\)]\)"
  }};
ReduceRules[OptionsPattern[]] := Join[FruleP1MLL, FruleP3MLL, ruleSchSMLL, ruleSchAMLL];

(*TODO better mass options fit for all massive particle amounts*)
Options[FMreduceWithDict] = {
  fund -> "\[Lambda]t",
  mass -> {
    "\!\(\*SubscriptBox[\(m\), \(1\)]\)",
    "\!\(\*SubscriptBox[\(m\), \(2\)]\)",
    "\!\(\*SubscriptBox[\(m\), \(3\)]\)",
    "\!\(\*SubscriptBox[\(m\), \(4\)]\)"
  }};
SetAttributes[FMreducePart, HoldFirst];
FMreducePart[dict_, amplst_, applyFun_] :=
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
                Total@Sow[FMreducePart[dict, {currentAmp}, applyFun]]])
            , {currentAmp, nextLevelAmpList}]] // Last // Flatten];
        ],
        (*recursion for every term*)
        Return[Reap[Do[
          FactorizeBracket@currentAmp // (factor = #[[1]];
          base = #[[2]];)&;
          dict ~ AssociateTo ~ (base -> Expand[1 / factor *
              Total@Sow[FMreducePart[dict, {currentAmp}, applyFun]]])
          , {currentAmp, amplst}]] // Last // Flatten];
      ]
    ];

(*TODO better mass options fit for all massive particle amounts*)
Options[FMreduceWithDict] = {
  fund -> "\[Lambda]t",
  mass -> {
    "\!\(\*SubscriptBox[\(m\), \(1\)]\)",
    "\!\(\*SubscriptBox[\(m\), \(2\)]\)",
    "\!\(\*SubscriptBox[\(m\), \(3\)]\)",
    "\!\(\*SubscriptBox[\(m\), \(4\)]\)"
  }};
SetAttributes[FMreduceWithDict, HoldFirst];
If[!AssociationQ[globalReduceDict], globalReduceDict = <||>;];
FMreduceWithDict[amp_, OptionsPattern[]] := FMreduceWithDict[globalReduceDict, amp];
FMreduceWithDict[dict_?AssociationQ, OptionsPattern[]] := FMreduceWithDict[dict, #]&;
FMreduceWithDict[dict_, amp_Integer, OptionsPattern[]] := amp;
FMreduceWithDict[dict_, amp_, OptionsPattern[]] :=
    Module[ {F, dispRules, applyFun},
      dispRules = ReduceRules[fund -> OptionValue@fund, mass -> OptionValue@mass];
      applyFun = (Map[(# /. dispRules) &, #]
          // Total // Expand // Sum2List) &;
      F = FMreducePart[dict, Sum2List[Expand[amp]], applyFun] // Flatten // Total // Expand;
      Return[F];
    ];

(*TODO better mass options fit for all massive particle amounts*)
Options[FMreduce] = {
  tryMax -> 30,
  fund -> "\[Lambda]t",
  mass -> {
    "\!\(\*SubscriptBox[\(m\), \(1\)]\)",
    "\!\(\*SubscriptBox[\(m\), \(2\)]\)",
    "\!\(\*SubscriptBox[\(m\), \(3\)]\)",
    "\!\(\*SubscriptBox[\(m\), \(4\)]\)"},
  parallelized -> False
};
FMreduce[amp_Integer, OptionsPattern[]] := amp;
FMreduce[amp_, OptionsPattern[]] :=
    Module[ {F = amp, F1, iter = 1, dispRules, applyFun},
      dispRules = ReduceRules[fund -> OptionValue@fund, mass -> OptionValue@mass];
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

(* ::Section::Closed:: *)
(*obtain d-dim basis*)

Options[ReduceParallelized] = {
  fund -> Null, mass -> Null,
  explicitmass -> False,
  maxcount -> Infinity, tryMax -> Infinity, withDict -> "False",
  kernelAmount -> "Auto", synctask -> Infinity, synctime -> Infinity,
  externalReduceDict -> <||>, log -> True};
SetAttributes[ReduceParallelized, HoldFirst];
ReduceParallelized[ampcoorDict_, ampDict_, ampDbasis_, OptionsPattern[]] :=
    Module[ {reduceFun, ampDict2 = ampDict // ReverseDict, keys, key,
      separateList = {}, kernels = Length[Kernels[]], dictSync},
      keys = ampDict2 // Keys;
      If[ kernels === 0,
        LaunchKernels[4];
        kernels = Length[Kernels[]];
      ];
      If[ OptionValue @ kernelAmount != "Auto" && kernels < OptionValue @ kernelAmount,
        LaunchKernels[OptionValue @ kernelAmount - kernels];
        kernels = Length[Kernels[]];
      ];
      If[ OptionValue@withDict === False,
        LogPri["Direct decomposition..."];
        reduceFun =
            (FindCor[#, ampDbasis] &)@
                FMreduce[
                  MatchtoDdim[#, explicitmass -> OptionValue@explicitmass , mass -> OptionValue@mass],
                  mass -> OptionValue@mass,
                  fund -> OptionValue@fund,
                  parallelized -> False,
                  tryMax -> OptionValue@tryMax
                ] &;
        SetSharedVariable[ampDict2, separateList, keys, ampcoorDict];
        LogPri["U(N) heads over ", OptionValue@maxcount,
          " will be calculated separately."];
        ParallelDo[
          key = keys[[i]];
          If[CountHead[If[ OptionValue@fund === "\[Lambda]t",
            ab,
            sb
          ]]@key <= OptionValue@maxcount,
            ampcoorDict ~ AssociateTo ~ (key -> reduceFun@key)
                // AbsoluteTiming
                // If[OptionValue@log, LogPri[ampDict2[key], " cost ", #[[1]]]&, Identity];
            ,
            separateList ~ AppendTo ~ key;
          ], {i, Length[keys]}
          , DistributedContexts -> Automatic]
            // AbsoluteTiming // First
            // LogPri["part1 N=", Length[keys] - Length[separateList],
          " costs:", #] &;
        reduceFun =
            (FindCor[#, ampDbasis] &)@
                FMreduce[
                  MatchtoDdim[#],
                  mass -> OptionValue@mass,
                  fund -> OptionValue@fund,
                  parallelized -> True,
                  tryMax -> OptionValue@tryMax
                ] &;
        Do[
          key = separateList[[i]];
          ampcoorDict ~ AssociateTo ~ (key -> reduceFun@key) //
              AbsoluteTiming // If[OptionValue@log, LogPri[ampDict2[key], " cost ", #[[1]]]&, Identity];
          , {i, Length[separateList]}]
            // AbsoluteTiming // First
            // LogPri["part2 N=", Length[separateList], " costs:", #] &;
        ,
        LogPri["Dict decomposition..."];
        (*Build parallelized fun : reduceFun*)
        reduceFun[dict_, amp_] :=
            ampcoorDict ~ AssociateTo ~ ((amp -> FindCor[#, ampDbasis]) &@
                FMreduceWithDict[dict,
                  MatchtoDdim[amp],
                  mass -> OptionValue@mass,
                  fund -> OptionValue@fund])
                // AbsoluteTiming
                // If[OptionValue@log, LogPri[ampDict2[amp], " cost ", #[[1]]]&, Identity];
        SetAttributes[reduceFun, HoldFirst];
        Options[reduceFun] = {
          mass -> OptionValue@mass,
          fund -> OptionValue@fund,
          log -> OptionValue@log
        };
        SetSharedVariable[ampDict2, dictSync, ampcoorDict];
        dictSync = OptionValue@externalReduceDict;
        (*Context must contains current package path*)
        SyncDataTask[dictSync, reduceFun, keys, synctask -> OptionValue@synctask,
          synctime -> OptionValue@synctime, context -> $ContextPath];
        Return[dictSync];
      ];
    ];

(*TODO better mass options fit for all massive particle amounts*)
Options[ConstructBasis] = {
  (*only None, First, All are allowed*)
  permutation -> None,
  explicitmass -> False,
  fund -> "\[Lambda]t",
  mass -> {
    "\!\(\*SubscriptBox[\(m\), \(1\)]\)",
    "\!\(\*SubscriptBox[\(m\), \(2\)]\)",
    "\!\(\*SubscriptBox[\(m\), \(3\)]\)",
    "\!\(\*SubscriptBox[\(m\), \(4\)]\)"},
  singleCoreMaxHead -> "Auto", tryMax -> Infinity,
  withDict -> True, maxcount -> Infinity, tryMax -> Infinity,
  kernelAmount -> "Auto", log -> False,
  synctask -> Infinity, synctime -> Infinity, externalReduceDict -> <||>};
ConstructBasis[spins_, operDim_, OptionsPattern[]] :=
    Module[{
      metaInfo,
      antiList, dimCodeMinimal, Np, permutationRules,
      CalcOperatorDimContribute, nAMax, dimCFFrom, dimCFTo,
      GetNeededBHBasisDimList,
      NeededCFBasisQ, cfbasis,
      PermuteAmp, permutedBasis, permutedBasisCoor, index,
      cfIndexList, bhDimList,
      cfBasisDict, cfPermutedBasisDict, cfPermutedDict,
      bhBasisDict, reversedCFBasisDict,
      coordinateDict = <||>, bhBasis, reduceDict,
      opts, extOpts,
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
      opts = {
        mass -> OptionValue@mass,
        fund -> OptionValue@fund
      };
      extOpts = ((# -> OptionValue@#)& /@
          Complement[Keys@Association@Options@ReduceParallelized,
            Keys@Association@opts, {maxcount, singleCoreMaxHead}
          ]);

      cfIndexList = Cases[cfIndexList, {dim_, antiSpinors_} /;
          (MemberQ[bhDimList, dim + Total@antiSpinors])
      ];
      LogPri["Involved BH basis : ", bhDimList];
      LogPri["Involved CF basis : ", cfIndexList];
      GenBHBasis[dim_] := FptAmp @@ (spins ~ Join ~ {dim} ~ Join ~ opts);
      GenCFBasis[dim_, antispinorList_] := (FptAmp @@
          (spins ~ Join ~ {dim} ~ Join ~ {antispinor -> antispinorList} ~ Join ~ opts));
      (
        bhBasisDict = ParallelMap[(# -> GenBHBasis@#)& , bhDimList ] // Association // KeySort;
        bhBasis = bhBasisDict // Values // Flatten;
        cfBasisDict = ParallelMap[(# -> GenCFBasis @@ #)& , cfIndexList] // Association;
        reversedCFBasisDict = ReverseDict[cfBasisDict];
      ) // AbsoluteTiming // LogPri["Constructing amplitudes costs ", #[[1]]]&;
      extOpts = extOpts ~ Join ~
          {maxcount -> If[ OptionValue@singleCoreMaxHead == "Auto",
            Max[CountHead[If[ OptionValue@fund == "\[Lambda]t",
              ab,
              sb
            ]] /@ Keys[reversedCFBasisDict]] - 1,
            OptionValue@singleCoreMaxHead
          ]};

      (*Permute them*)
      Np = Length@spins;
      permutationRules = Switch[
        OptionValue@permutation,
        None, {},
        _List, OptionValue@permutation,
        (*Only for test*)
        First, {1 -> 2, 2 -> 1, 2 * Np -> 2 * Np - 1, 2 * Np - 1 -> 2 * Np},
        All, Table[i -> Mod[i, Np] + 1, {i, Np}] ~ Join ~ Table[2 * Np + 1 - i -> 2 * Np - Mod[i, Np], {i, Np}],
        23, {2 -> 3, 3 -> 2, 7 -> 6, 6 -> 7},
        _, Throw[{OptionValue@permutation, " not supported permutation"}];
      ];
      PermuteAmp[amp_] := Times @@ (Prod2List[amp] /. permutationRules);
      cfPermutedDict = Table[(PermuteAmp[e] -> e), {e, Keys@reversedCFBasisDict}] // Association;
      cfPermutedBasisDict = ParallelMap[PermuteAmp /@ #&, cfBasisDict];
      (*Print[cfPermutedDict]*);
      (*Return[{cfPermutedBasisDict, bhBasis}]*);
      reduceDict = Reap[ ReduceParallelized[
        coordinateDict, cfPermutedBasisDict, bhBasis, opts ~ Join ~ extOpts]
          // AbsoluteTiming
          // (Sow[# // Last];LogPri["Coefficients totally costs:", # // First]) &][[2]][[1]][[1]];

      LogPri["Involved CF amplitude amount is ", cfBasisDict // Values // Flatten // Length];
      LogPri["Involved CF amplitude amount is ", bhBasisDict // Values // Flatten // Length];
      (*      LogPri["Involved BH amplitude amount is ",*)
      (*        Fold[Plus, ConstantArray[0, Length@bhBasis],*)
      (*          Map[((# == 0) /. {True -> 0, False -> 1}) &,*)
      (*            (Values@coordinateDict), {2}]]*)
      (*            // DeleteCases[#, 0] & // Length*)
      (*      ];*)
      LogPri["Coordinate rank is ", ZRank[Values@coordinateDict]];

      (*Sort*)
      cfbasis = Keys[reversedCFBasisDict] //
          SortBy[(Total@Flatten@reversedCFBasisDict[#])&];
      permutedBasis = Keys[coordinateDict];
      (*TODO sort cf basis correctly*)
      permutedBasis = SortBy[permutedBasis, FirstPosition[cfbasis, cfPermutedDict[#], None, 1]&];
      permutedBasisCoor = coordinateDict[#]& /@ permutedBasis;

      (*Get independent basis*)
      ((permutedBasis = permutedBasis[[#]];permutedBasisCoor = permutedBasisCoor[[#]])&@
          Flatten[Position[#, Except[0, _?NumericQ], 1, 1] & /@
              RowReduce@Transpose@
                  ReplaceAll[permutedBasisCoor, Table[If[e =!= 0, e -> 1], {e, OptionValue@mass}]]
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
        "permutation" -> permutation,
        "mass" -> OptionValue@mass, "explicitmass" -> OptionValue@explicitmass, "NeededCFBasisQ" -> NeededCFBasisQ} // Association;
      Return[{permutedBasisCoor,
        <|"basis" -> permutedBasis, "coordinate" -> coordinateDict,
          "cf" -> cfBasisDict, "bh" -> bhBasisDict, "reduceDict" -> reduceDict, "metaInfo" -> metaInfo,
          "permutationRules" -> permutationRules
        |>}];
    ];

PositionOperatorPhysicalDim[ConstructBasisResult_] := Module[
  {NeededCFBasisQ, cfBasisDict, permutationRules, reverseBasisDict, basis, index},
  NeededCFBasisQ = ConstructBasisResult[[2]]["metaInfo"]["NeededCFBasisQ"];
  cfBasisDict = ConstructBasisResult[[2]]["cf"];
  permutationRules = ConstructBasisResult[[2]]["permutationRules"];
  reverseBasisDict = KeyMap[# /. permutationRules&, ReverseDict[cfBasisDict]];
  basis = ConstructBasisResult[[2]]["basis"];
  index = (NeededCFBasisQ[#[[1]], #[[2]], False]&@reverseBasisDict[#]&@#)& /@ basis // PositionIndex;
  Return[index[True]];
];
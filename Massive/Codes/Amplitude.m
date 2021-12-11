(*TODO construct amplitude for all amounts*)

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

SetAttributes[FMreducePart, HoldFirst];
FMreducePart[dict_, amplst_, applyFun_] :=
    Module[ {i, factor, base, amplsttemp, amptemp, amptemp2},
      If[ Length[amplst] === 1,
        (*init part start*)
        amptemp = amplst[[1]];
        If[ FactorizeBracket@amptemp // (factor = #[[1]];
        base = #[[2]];)&;
        dict ~ KeyExistsQ ~ base,
          Return[factor * dict[base]]
        ];
        amplsttemp = applyFun@amptemp;
        (*init part end*)
        If[ Length[amplsttemp] === 1,
          (* base part start *)
          amptemp = amplsttemp[[1]];
          (*reduce single term to right form*)
          (*Sometime need the following code to test if the reduction method is right*)
          (*In massive Single term may be reduced twice or more*)
          (*          If[canSingleTermBeReducedAnotherTime && amptemp =!= First@applyFun@amptemp,*)
          (*            Print[amptemp];Print[Total@applyFun@amptemp];*)
          (*            Print["Single term can be reduced back to poly by 2rd reduction!"];*)
          (*            Throw[{applyFun, amptemp}];*)
          (*          ];*)
          FactorizeBracket@amptemp // (factor = #[[1]];
          base = #[[2]];)&;
          dict ~ AssociateTo ~ (base -> 1 / factor * amptemp);
          Return[amplsttemp]          ;
          (* base part end *)
          ,
          (*recursion for every term*)
          Return[Reap[Do[
            amptemp = amplsttemp[[i]];
            FactorizeBracket@amptemp // (factor = #[[1]];
            base = #[[2]];)&;
            dict ~ AssociateTo ~ (base -> 1 / factor * Sow[FMreducePart[dict, {amptemp}, applyFun]])
            , {i, amplsttemp // Length}]] // Last // Flatten];
        ],
        (*recursion for every term*)
        Return[Reap[Do[
          amptemp = amplst[[i]];
          FactorizeBracket@amptemp // (factor = #[[1]];
          base = #[[2]];)&;
          dict ~ AssociateTo ~ (base -> 1 / factor * Sow[FMreducePart[dict, amptemp, applyFun]])
          , {i, amplst // Length}]] // Last // Flatten];
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
FMreduceWithDict[dict_, amp_, OptionsPattern[]] :=
    Module[ {F, dispRules, applyRules, applyFun},
      dispRules = ReduceRules[fund -> OptionValue@fund, mass -> OptionValue@mass];
      applyRules = (Map[(# /. dispRules)&, (Expand[{#}] // (# /. Plus :> List&) // Flatten)&@#] // # /. List :> Plus&)&;
      applyFun = ({Expand@applyRules@#} /. Plus -> List // Flatten)&;
      F = FMreducePart[dict, {amp}, applyFun] // Total;
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
FMreduce[amp_, OptionsPattern[]] :=
    Module[ {F = amp, F1, iter = 1, applyRules, dispRules, applyFun},
      dispRules = ReduceRules[fund -> OptionValue@fund, mass -> OptionValue@mass];
      applyRules = (If[ !OptionValue[parallelized],
        Map,
        ParallelMap
      ][(# /. dispRules)&, (Expand[{#}] // (# /. Plus :> List&) // Flatten)&@#] // # /. List :> Plus&)&;
      applyFun = Expand@applyRules@#&;
      While[True,
        F1 = applyFun@F;
        If[ F1 === F,
          Break[],
          F = F1
        ];
        If[ iter >= OptionValue@tryMax,
          Print["err", "[reduce] too many reductions!"];
          Print[F];
          Break[],
          iter++
        ]];
      Return[F // Expand]
    ];


(* ::Section:: *)
(*coefficient matrix*)

FindCor[amp_, ampDbasis_] := FindCoordinate[amp, ampDbasis, !(MatchQ[#, _ab | _sb]) &];

(* ::Section::Closed:: *)
(*obtain d-dim basis*)

Options[ReduceParallelized] = {fund->Null, mass->Null,
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
        Print["Direct decomposition..."];
        reduceFun =
            (FindCor[#, ampDbasis] &)@
                FMreduce[
                  MatchtoDdim[#],
                  mass -> OptionValue@mass,
                  fund -> OptionValue@fund,
                  parallelized -> False,
                  tryMax -> OptionValue@tryMax
                ] &;
        SetSharedVariable[ampDict2, separateList, keys, ampcoorDict];
        Print["U(N) heads over ", OptionValue@maxcount,
          " will be calculated separately."];
        ParallelDo[
          key = keys[[i]];
          If[CountHead[If[ OptionValue@fund === "\[Lambda]t",
            ab,
            sb
          ]]@key <= OptionValue@maxcount,
            ampcoorDict ~ AssociateTo ~ (key -> reduceFun@key)
                // AbsoluteTiming
                // If[OptionValue@log, Print[ampDict2[key], " cost ", #[[1]]]&, Identity];
            ,
            separateList ~ AppendTo ~ key;
          ], {i, Length[keys]}
          , DistributedContexts -> Automatic]
            // AbsoluteTiming // First
            // Print["part1 N=", Length[keys] - Length[separateList],
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
              AbsoluteTiming // If[OptionValue@log, Print[ampDict2[key], " cost ", #[[1]]]&, Identity];
          , {i, Length[separateList]}]
            // AbsoluteTiming // First
            // Print["part2 N=", Length[separateList], " costs:", #] &;
        ,
        Print["Dict decomposition..."];
        (*Build parallelized fun : reduceFun*)
        reduceFun[dict_, amp_] :=
            ampcoorDict ~ AssociateTo ~ ((amp -> FindCor[#, ampDbasis]) &@
                FMreduceWithDict[dict,
                  MatchtoDdim[amp],
                  mass -> OptionValue@mass,
                  fund -> OptionValue@fund])
                // AbsoluteTiming
                // If[OptionValue@log, Print[ampDict2[amp], " cost ", #[[1]]]&, Identity];
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
Options[ConstructIndependentOperatorBasis] = {
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
ConstructIndependentOperatorBasis[spins_, operDim_, OptionsPattern[]] :=
    Module[{
      antiList, dimCodeMinimal,
      CalcOperatorDimContribute, nAMax, dimCFFrom, dimCFTo,
      GetNeededBHBasisDimList,
      NeededCFBasisQ,
      basis, basisCoor, index,
      cfIndexList, bhDimList,
      cfBasisDict, bhBasisDict, reversedCFBasisDict,
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
          Complement[Keys@Association@Options@ConstructIndependentOperatorBasis,
            Keys@Association@opts, {maxcount, singleCoreMaxHead}
          ]);

      cfIndexList = Cases[cfIndexList, {dim_, antiSpinors_} /;
          (MemberQ[bhDimList, dim + Total@antiSpinors])
      ];
      Print["Involved BH basis : ", bhDimList];
      Print["Involved CF basis : ", cfIndexList];
      GenBHBasis[dim_] := FptAmp @@ (spins ~ Join ~ {dim} ~ Join ~ opts);
      GenCFBasis[dim_, antispinorList_] := FptAmp @@
          (spins ~ Join ~ {dim} ~ Join ~ {antispinor -> antispinorList} ~ Join ~ opts);
      (
        bhBasisDict = ParallelMap[(# -> GenBHBasis@#)& , bhDimList ] // Association;
        cfBasisDict = ParallelMap[(# -> GenCFBasis @@ #)& , cfIndexList] // Association;
      ) // AbsoluteTiming // Print["Constructing amplitudes costs ", #[[1]]]&;
      reversedCFBasisDict = ReverseDict[cfBasisDict];
      bhBasis = Do[Sow[bhBasisDict[e]], {e, bhBasisDict // Keys // Sort}] // Reap // Last // First // (Join @@ #)&;
      extOpts = extOpts ~ Join ~
          {maxcount -> If[ OptionValue@singleCoreMaxHead == "Auto",
            Max[CountHead[If[ OptionValue@fund == "\[Lambda]t",
              ab,
              sb
            ]] /@ Keys[reversedCFBasisDict]] - 1,
            OptionValue@singleCoreMaxHead
          ]};

      reduceDict = Reap[ ReduceParallelized[
        coordinateDict, cfBasisDict, bhBasis, opts ~ Join ~ extOpts]
          // AbsoluteTiming
          // (Sow[# // Last];Print["Coefficients totally costs:", # // First]) &][[2]][[1]][[1]];

      Print["Involved CF amplitude amount is ", cfBasisDict // Values // Flatten // Length];
      Print["Involved BH amplitude amount is ",
        Fold[Plus, ConstantArray[0, Length@bhBasis],
          Map[((# == 0) /. {True -> 0, False -> 1}) &,
            (Values@coordinateDict), {2}]]
            // DeleteCases[#, 0] & // Length
      ];
      Print["Coordinate rank is ", ZRank[Values@coordinateDict]];

      (*get independent basis*)

      basis = Keys[coordinateDict];
      (*TODO sort cf basis correctly*)
      basis = SortBy[basis, reversedCFBasisDict[#]&];
      basisCoor = coordinateDict[#]& /@ basis;
      ((basis = basis[[#]];basisCoor = basisCoor[[#]])&@
          Flatten[Position[#, Except[0, _?NumericQ], 1, 1] & /@
              RowReduce@Transpose@basisCoor]) // AbsoluteTiming //
          Print["Ranking costs ", #[[1]]]&;
      index = Flatten@Position[basis,
        e_ /; MemberQ[#, e], 1
      ]&@Select[basis,
        NeededCFBasisQ[reversedCFBasisDict[#][[1]], reversedCFBasisDict[#][[2]], False]&];
      (basis = basis[[#]];
      basisCoor = basisCoor[[#]];)&@index;
      Print["Final basis amount is ", Length@basis];
      (*TODO reduce identical particles*)
      Return[<|"basis" -> basis, "cf" -> cfBasisDict, "bh" -> bhBasisDict,
        "coordinate" -> coordinateDict, "reduceDict" -> reduceDict|>];
    ];
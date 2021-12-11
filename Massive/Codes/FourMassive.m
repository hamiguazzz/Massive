(* ::Package:: *)

Print["FourMassive Loaded"];

(*TODO particle over 4*)
reduce4pt[spin1_, spin2_, spin3_, spin4_, l1_, l2_, l3_, l4_, dim_, Nm_] :=
    Module[ {Left, Right, Num1, Num2, Num3, Num4, num1, num2, num3, num4},
      Right = (dim - 4 + spin1 + spin2 + spin3 + spin4 - l1 - l2 - l3 - l4) / 2;
      Left = (dim - 4 - spin1 - spin2 - spin3 - spin4 + l1 + l2 + l3 + l4) / 2;
      Num1 = If[ Nm > 0,
        Left - l1,
        Left + 2 spin1
      ];
      num1 = If[ Nm > 0,
        2spin1 - l1,
        0
      ];
      Num2 = If[ Nm > 3,
        Left - l2,
        Left + 2 spin2
      ];
      num2 = If[ Nm > 3,
        2spin2 - l2,
        0
      ];
      Num3 = If[ Nm > 2,
        Left - l3,
        Left + 2 spin3
      ];
      num3 = If[ Nm > 2,
        2spin3 - l3,
        0
      ];
      Num4 = If[ Nm > 1,
        Left - l4,
        Left + 2 spin4
      ];
      num4 = If[ Nm > 1,
        2spin4 - l4,
        0
      ];
      {Left, Right, Num1, Num2, Num3, Num4, num1, num2, num3, num4}
    ];


Options[FptAmp] = {
  antispinor -> {0, 0, 0, 0},
  fund -> "\[Lambda]t",
  mass -> {
    "\!\(\*SubscriptBox[\(m\), \(1\)]\)",
    "\!\(\*SubscriptBox[\(m\), \(2\)]\)",
    "\!\(\*SubscriptBox[\(m\), \(3\)]\)",
    "\!\(\*SubscriptBox[\(m\), \(4\)]\)"}};
FptAmp[spin1_, spin2_, spin3_, spin4_, Dim_, OptionsPattern[]] :=
    Module[ {Np = 4, para, yd, filling, amps, Nm},
      (*TODO extension particle number*)
      Nm = Np - Count[OptionValue[mass], 0];
      para = reduce4pt[spin1, spin2, spin3, spin4, #1, #2, #3, #4, Dim, Nm]& @@ OptionValue[antispinor];
      If[ Length@Select[para, Negative[#]&] != 0,
        Return[{}]
      ];
      yd = Table[0, 2, para[[1]] + para[[2]]];
      filling = Table[Table[i, para[[2 + i]]], {i, Np}]
          ~ Join ~ Table[Table[Np * 2 + 1 - i, para[[-(Np + 1 - i)]]], {i, Np}] // Flatten // Sort;
      amps = YTtoAmpmass[#, para[[1]], Range[Np],
        fund -> OptionValue[fund]]& /@
          StrangeSSYT[yd, filling, para[[1]], {5, 6, 7, 8}];
      Return[amps];
    ];

(* ::Section:: *)
(*decompose in basis*)


(* ::Subsection::Closed:: *)

(* ::Subsection:: *)

(*Massless limit reduce rules*)
(*In fact reduce faster by omitting these lower dimensions*)

FruleP1MLL = {
  sb[1, i_] * ab[1, j_] :> Sum[-sb[k, i]ab[k, j], {k, 2, 4}],
  sb[1, i_]^m_ * ab[1, j_] :> Sum[-sb[1, i]^(m - 1)sb[k, i]ab[k, j], {k, 2, 4}],
  sb[1, i_] * ab[1, j_]^n_ :> Sum[-ab[1, j]^(n - 1)sb[k, i]ab[k, j], {k, 2, 4}],
  sb[1, i_]^m_ * ab[1, j_]^n_ :> Sum[-sb[1, i]^(m - 1) ab[1, j]^(n - 1) sb[k, i]ab[k, j], {k, 2, 4}]};
FruleP3MLL = Join[{
  sb[2, 3] * ab[2, 3] :> Sum[sb[i, j]ab[j, i], {i, 2, 4}, {j, Max[i + 1, 4], 4}],
  sb[2, 3]^m_ * ab[2, 3] :> sb[2, 3]^(m - 1) Sum[sb[i, j]ab[j, i], {i, 2, 4}, {j, Max[i + 1, 4], 4}],
  sb[2, 3] * ab[2, 3]^n_ :> ab[2, 3]^(n - 1) Sum[sb[i, j]ab[j, i], {i, 2, 4}, {j, Max[i + 1, 4], 4}],
  sb[2, 3]^m_ * ab[2, 3]^n_ :> sb[2, 3]^(m - 1) ab[2, 3]^(n - 1) Sum[sb[i, j]ab[j, i], {i, 2, 4}, {j, Max[i + 1, 4], 4}]}];
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
(*TODO particle over 4*)

Options[MatchtoDdim] = {fund -> "\[Lambda]t",
  mass -> {"\!\(\*SubscriptBox[\(m\), \(1\)]\)",
    "\!\(\*SubscriptBox[\(m\), \(2\)]\)",
    "\!\(\*SubscriptBox[\(m\), \(3\)]\)",
    "\!\(\*SubscriptBox[\(m\), \(4\)]\)"}};
MatchtoDdim[amp_, OptionsPattern[]] :=
    Module[ {amplist1, amplist2,
      labelnum1 = <|1 -> {}, 2 -> {}, 3 -> {}, 4 -> {}|>,
      labelnum2 = <|1 -> {}, 2 -> {}, 3 -> {}, 4 -> {}|>, mfactor = 1},
      amplist1 =
          amp //. {Times -> List, ab -> List, sb[i_, j_] -> {},
            Power[y_, z_] /; Element[z, PositiveIntegers] :>
                ConstantArray[y, z]} // Flatten;
      amplist2 =
          amp //. {Times -> List, ab[i_, j_] -> {}, sb -> List,
            Power[y_, z_] /; Element[z, PositiveIntegers] :>
                ConstantArray[y, z]} // Flatten;
      Do[If[ OptionValue[mass][[i]] === 0,
        Continue[]
      ];
      labelnum1[i] = Count[amplist1, i];
      labelnum2[i] = Count[amplist2, i];
      If[ OptionValue[fund] === "\[Lambda]t",
        Do[mfactor *= -sb[i, 9 - i] / OptionValue[mass][[i]], {j, labelnum1[i] - labelnum2[i]}],
        Do[mfactor *= ab[i, 9 - i] / OptionValue[mass][[i]], {j, labelnum1[i] - labelnum2[i]}]
      ], {i, 4}];
      Return[amp * mfactor];
    ];

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

Options[ReduceParallelized] = {
  fund -> "\[Lambda]t",
  mass -> {"\!\(\*SubscriptBox[\(m\), \(1\)]\)",
    "\!\(\*SubscriptBox[\(m\), \(2\)]\)",
    "\!\(\*SubscriptBox[\(m\), \(3\)]\)",
    "\!\(\*SubscriptBox[\(m\), \(4\)]\)"},
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
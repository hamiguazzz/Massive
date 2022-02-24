LogPri["SU3 Loaded"];
(*Now only for SU3, to be expanded to SUN*)
(* ::Section:: *)
(*Step1 Specify indices and construct basis*)
(*Input: identical blocks shape, particle amount*)
(*Output: all particle indices dict*)

(*for gluon, convention tableaux is {{1,2},{3}}*)
su3ShapeDict = <|"" -> {}, "q" -> {1}, "aq" -> {1, 1}, "g" -> {2, 1}|>;

GetColorIndDict[shapes_List] := Module[{indAmountList, indDict, lastInd = 0
},
  indAmountList = Transpose@{Range[Length@shapes], Total /@ shapes} // SortBy[#, Last]&;
  indDict = Do[
    If[e[[2]] != 0 ,
      Sow[e[[1]] -> lastInd + Range[e[[2]]]];
      lastInd = lastInd + e[[2]];]
    , {e, indAmountList}] // Reap // Last // First // Association;
  Return[indDict];
];

ConstructColorBasis[nColumn_Integer] := GenerateStandardTableaux[ConstantArray[nColumn, 3]];

(* ::Section:: *)
(*Step2 Permute particles to form new young tableaux*)
GetPermuteColorIdenticalRules[identicalParticleList_List, colorIndDict_Association] := Module[
  {particleReplaceRules = GetMasslessIdenticalRules[identicalParticleList],
    ReplaceParticle2ColorRule},
  ReplaceParticle2ColorRule[n1_ -> n2_] := MapThread[#1 -> #2&, {colorIndDict[n1], colorIndDict[n2]}];
  Return[(ReplaceParticle2ColorRule /@ # // Flatten)& /@ particleReplaceRules]
];

GetPermuteColorInnerRules[colorIndDict_Association] := Module[
  {permutationColorRuleDict, GenColorRule},
  GenColorRule[inds_] := GetMasslessIdenticalRules@Switch[Length@inds, 1, {}, 2, inds ~ Append ~ {"A"}, 3, inds ~ Append ~ {"S"}];
  permutationColorRuleDict = GenColorRule /@ colorIndDict;
  Return[permutationColorRuleDict];
];
ReplaceColorTableauxNumber[rule_] := # /. rule&;

(* ::Section:: *)
(*Step3 Reduce any YT to standard YT*)
defaultYTHead = IYT;
WarpTableauxWithHead[tableaux_List, head_] := head[tableaux];
WarpTableauxWithHead[head_] := WarpTableauxWithHead[#, head]&;
WarpTableauxWithHead[] := WarpTableauxWithHead[defaultYTHead];
ReduceSU3YT[tableaux_List, h_ : defaultYTHead] := ReduceSU3YT[WarpTableauxWithHead[tableaux, h], h];
ReduceSU3YT[constant_, h_ : defaultYTHead] /; NumberQ@constant := constant;
ReduceSU3YT[expr_Plus, h_ : defaultYTHead] := ReduceSU3YT[#, h]& /@ Sum2List[expr] // Total;
ReduceSU3YT[expr_Times, h_ : defaultYTHead] := Times @@ (ReduceSU3YT[#, h]& /@ Prod2List[expr]);
ReduceSU3YT[warpedTableaux_, h_ : defaultYTHead] /; Head@warpedTableaux === h :=
    Module[
      {n = Length@warpedTableaux[[1]][[1]], totalFactor, tableaux, reduceAllOnce, lastExpr, result},
      {totalFactor, tableaux} = (YTSortColumnsFirst[#, h]&) @ (YTSortColumnInner[#, h]&)@warpedTableaux;
      reduceAllOnce = tableaux;
      While[lastExpr =!= reduceAllOnce,
        lastExpr = reduceAllOnce;
        Do[
          reduceAllOnce = YTSU3RepeatedShortenId[reduceAllOnce, {column1, column2} , h] // Expand;,
          {column1, 1, n}, {column2, column1 + 1 , n}
        ];
      ];
      result = totalFactor * reduceAllOnce // Return;
    ];
YTSortColumnsFirst[constant_, h_ : defaultYTHead] /; NumberQ@constant := constant;
YTSortColumnsFirst[factoredTableaux_List, h_ : defaultYTHead] /; NumberQ@factoredTableaux[[1]] :=
    YTSortColumnsFirst[#, h]& /@ factoredTableaux;
YTSortColumnsFirst[tableaux_List] := Transpose@SortBy[Transpose@tableaux, First];
YTSortColumnsFirst[warpedTableaux_, h_ : defaultYTHead] /; Head@warpedTableaux === h :=
    h[ YTSortColumnsFirst[warpedTableaux[[1]]] ];
YTSortColumnInner[tableaux_List, columnNumbers_List] := Module[
  {tTableaux = Transpose@tableaux, factor = 1},
  Do[
    factor *= Signature[tTableaux[[c]]];
    tTableaux[[c]] = Sort[tTableaux[[c]]];
    , {c, columnNumbers}];
  Return[{factor, Transpose@tTableaux}];
];
YTSortColumnInner[tableaux_List] := YTSortColumnInner[tableaux, Range@Length@tableaux[[1]]];
YTSortColumnInner[{{}}] := {{}};
YTSortColumnInner[warpedTableaux_, h_ : defaultYTHead] /; Head@warpedTableaux === h :=
    {#[[1]], h@#[[2]]}&@YTSortColumnInner[warpedTableaux[[1]]];
YTSortColumnInner[warpedTableaux_, columnNumbers_List , h_ : defaultYTHead] /; Head@warpedTableaux === h :=
    {#[[1]], h@#[[2]]}&@YTSortColumnInner[warpedTableaux[[1]], columnNumbers];
YTSortUseShortenId[warpedTableaux_, {column1_Integer, column2_Integer}, selectedReserve_Integer, h_ : defaultYTHead] /; Head@warpedTableaux === h :=
    YTSortUseShortenId[warpedTableaux[[1]], {column1, column2}, selectedReserve, h];
YTSortUseShortenId[tableaux_List, {column1_Integer, column2_Integer}, selectedReserve_Integer, h_ : defaultYTHead] := Module[
  {tTableaux = Transpose@tableaux, allPossibleTerms, allTableaux, factors, sortInnerResult},
  {factors, allPossibleTerms} = YTSortUseShortenId[tTableaux[[column1]], tTableaux[[column2]], selectedReserve];
  allTableaux = Transpose /@ MapThread[(tTableaux[[column1]] = #1;tTableaux[[column2]] = #2;tTableaux)&,
    Transpose @ allPossibleTerms];
  sortInnerResult = YTSortColumnInner[#, {column1, column2}]& /@ allTableaux // Transpose;
  MapThread[#1 * h[#2]&, {sortInnerResult[[1]] * factors, YTSortColumnsFirst /@ sortInnerResult[[2]]}] // Total //
      Return;
];
YTSortUseShortenId[column1List_List, column2List_List, selectedReserve_Integer] := Module[
  {leftTerms = Drop[column1List, {selectedReserve}],
    needPermutedTerms = Join[{column1List[[selectedReserve]]}, column2List], permuted,
    permutedResult, factors},
  If[Length@column1List != Length@column2List || Length@column1List < 2, Throw["Wrong shape"]];
  permuted = NestList[Permute[#, Cycles[{Range[Length@needPermutedTerms]}]] &, needPermutedTerms,
    Length@needPermutedTerms - 1][[2 ;; -1]];
  permutedResult = {leftTerms ~ Append ~ #[[1]], #[[2 ;; -1]]}& /@ permuted;
  factors = -1 * Signature[leftTerms ~ Append ~ column1List[[selectedReserve]]] * Signature[column1List]
      * Signature@needPermutedTerms * Signature /@ permuted;
  Return[{factors, permutedResult}];
];
YTSU3RepeatedShortenId[warpedTableaux_, {column1_Integer, column2_Integer}, h_ : defaultYTHead] := Module[
  {tTableaux = Transpose@warpedTableaux[[1]], a, b, c, d, e, f, temp, factors, exprs},
  {a, b, c} = tTableaux[[column1]];
  {d, e, f} = tTableaux[[column2]];
  If[b < e && c < f, Return[warpedTableaux]];
  If[b < e && c > f, Return@YTSortUseShortenId[warpedTableaux, {column1, column2}, 3, h]];
  If[b > e && c > f, Return@YTSortUseShortenId[warpedTableaux, {column1, column2}, 1, h]];
  If[b > e && c < f,
    temp = Prod2List /@ Sum2List@YTSortUseShortenId[warpedTableaux, {column1, column2}, 2, h];
    {factors, exprs} = If[Length@# == 1, {1} ~ Join ~ #, #]& /@ temp // Transpose;
    factors * (YTSU3RepeatedShortenId[#, {column1, column2}, h]& /@ exprs) // Total // Return;
  ];
];
YTSU3RepeatedShortenId[constant_, {column1_Integer, column2_Integer}, h_ : defaultYTHead] /; NumberQ@constant :=
    constant;
YTSU3RepeatedShortenId[expr_Plus, {column1_Integer, column2_Integer}, h_ : defaultYTHead] :=
    YTSU3RepeatedShortenId[#, {column1, column2}, h]& /@ Sum2List[expr] // Total;
YTSU3RepeatedShortenId[expr_Times, {column1_Integer, column2_Integer}, h_ : defaultYTHead] :=
    Times @@ (YTSU3RepeatedShortenId[#, {column1, column2}, h]& /@ Prod2List[expr]);

FindColorCor[warpedTableaux_List, warpedBasis_List] := FindColorCor[#, warpedBasis]& /@ warpedTableaux;
FindColorCor[warpedBasis_List] := FindColorCor[#, warpedBasis]&;
FindColorCor[warpedTableaux_, warpedBasis_List] := Module[
  {temp, factors, exprs, poss, vec},
  temp = Prod2List /@ Sum2List@ warpedTableaux;
  {factors, exprs} = If[Length@# == 1, {1} ~ Join ~ #, #]& /@ temp // Transpose;
  poss = Flatten@(FirstPosition[warpedBasis, #, {-1}]& /@ exprs);
  If[Length@Select[poss, Negative[#]&] != 0, Print["not found: ", warpedTableaux];Return[Null]];
  vec = ConstantArray[0, Length@warpedBasis];
  Table[
    vec[[poss[[i]]]] = factors[[i]];,
    {i, Length@poss}
  ];
  Return[vec];
];

(* ::Section:: *)
(*Step4 Get Color Operators*)
GetColorIdenticalPermutedOperatorDict[identicalParticleLists_List, colorIndDict_Association, genCoorsByRule_] :=
    Module[{operatorDict, rules, coors, PFirst, PAll},
      operatorDict = Table[identicalParticleList -> Null, {identicalParticleList, identicalParticleLists}] // Association;
      Do[
        rules = GetPermuteColorIdenticalRules[identicalParticleList, colorIndDict];
        coors = genCoorsByRule /@ rules;
        PFirst = coors[[2]];
        PAll = coors[[-1]];
        operatorDict[identicalParticleList] = {
          1 -> IdentityMatrix[Length@coors[[-1]]],
          symPermuteFirst -> PFirst,
          symPermuteAll[-1 + Length@identicalParticleList] -> PAll
        } // DeleteDuplicates;
        , {identicalParticleList, identicalParticleLists}];
      Return[operatorDict];
    ];

GetColorInnerPermutedOperatorDict[colorIndDict_Association, genCoorsByRule_] :=
    Module[{operatorDict, allRules, rules, coors, PFirst, PAll},
      operatorDict = <||>;
      allRules = GetPermuteColorInnerRules[colorIndDict];
      Do[
        rules = allRules[coloredParticle];
        coors = genCoorsByRule /@ rules;
        If[Length@coors != 1,
          PFirst = N@coors[[2]];
          PAll = N@coors[[-1]];
          AssociateTo[operatorDict,
            coloredParticle -> {
              1 -> N@IdentityMatrix[Length@coors[[1]]],
              symPermuteFirst -> PFirst
            } ~ Join ~
                If[Length@colorIndDict[coloredParticle] > 2,
                  {symPermuteAll[Length@colorIndDict[coloredParticle]] -> PAll},
                  {}
                ]
          ]
        ];
        , {coloredParticle, Keys@colorIndDict}];
      Return[operatorDict];
    ];

GetProjectInnerColorOp[colorIndDict_Association, operatorDict_Association] := Module[
  {polyDict, yt, poly},
  polyDict = <||>;
  Do[
    yt = Switch[Length@colorIndDict[particle],
      2, {1, 1},
      3, {2, 1},
      _, Throw["not suitable color indices " <> ToString@colorIndDict[particle]]
    ];
    (*By convention*)
    poly = GetPermutedPolyFromYT[yt] // First;
    AssociateTo[polyDict, particle -> poly];
    , {particle, Keys@operatorDict}];
  Dot @@ ParallelTable[polyDict[p] /. operatorDict[p], {p, Keys@polyDict}] // Return;
];


(* ::Section:: *)
(*Step5 Combine all*)

Options[ConstructIndependentColoredBasis] = Join[{ythead -> defaultYTHead,
  allowedmemory -> 4 * 10^9,
  log -> False}, Options@ConstructBasis ,
  Options@AuxConstructIdenticalColorBasis] // DeleteDuplicates;
ConstructIndependentColoredBasis[spins_List, operDim_Integer,
  su3ShapeList_ : {},
  identicalParam_ : {},
  opts : OptionsPattern[]
] := ConstructIndependentColoredBasis[
  ConstructBasis[spins, operDim, FilterRules[{opts}, Options@ConstructBasis]],
  su3ShapeList, identicalParam, opts];
ConstructIndependentColoredBasis[result : {cfBasisCoordinates_List, data_Association},
  {},
  identicalParam_ : {},
  opts : OptionsPattern[]
] := ConstructIndependentBasis[result, identicalParam, FilterRules[{opts}, Options@ConstructIndependentBasis]];
ConstructIndependentColoredBasis[result : {cfBasisCoordinates_List, data_Association},
  su3ShapeList_ : {},
  identicalParam_ : {},
  opts : OptionsPattern[]
] := Module[
  {np, spins, identicalList, physicalBasisIndex,
    bhBasis, permutedBHs, coloredCfBasis, permutedBHCoorsDict, rulePermutedIdenticalCoorsDict,
    rulesPermutedIdentical, lorIdenticalOpDict, permuteIdenticalPolyDict, reducedTotalOperator,
    independentCfBasis, independentPermutedBasis, projectionOp,
    colorIndDict, colorBasis, colorIdenticalOpDict,
    colorOp, lorentzOp},

  (*Basis info*)
  spins = data["metaInfo"]["spins"];
  np = Length@spins;
  bhBasis = data["bh"] // Values // Flatten;
  independentCfBasis = data["basis"];
  physicalBasisIndex = PositionOperatorPhysicalDim[data];
  If[identicalParam === {},
    identicalList = {},
    identicalList = (# ~ Append ~ If[OddQ[2 * spins[[#[[1]]]]], "A", "S"])& /@ identicalParam;
  ];

  (*Calc Color Permutation*)
  {colorIndDict, colorBasis, colorIdenticalOpDict, projectionOp} =
      AuxConstructIdenticalColorBasis[su3ShapeList, identicalList,
        OptionValue@ythead, FilterRules[{opts}, Options@AuxConstructIdenticalColorBasis]];

  If[OptionValue@log, LogPri["involved color basis ", Length@ colorBasis];];

  (*Self color cancel*)
  If[MatrixRank@projectionOp == 0, Return[{}]];

  (*no identical*)
  If[identicalList === {},
    colorBasis = colorBasis[[#]]& /@
        Flatten[FirstPosition[#, Except[0, _?NumericQ], {}]& /@ projectionOp];
    independentCfBasis = independentCfBasis[[#]]& /@ physicalBasisIndex;
    Table[{color, amp}, {color, colorBasis}, {amp, independentCfBasis}] // Flatten[#, 1]& // Return;
  ];

  (*Expand basis*)
  coloredCfBasis = Table[{color, amp}, {color, colorBasis}, {amp, independentCfBasis}] // Flatten[#, 1]&;
  physicalBasisIndex = Flatten @ Table[physicalBasisIndex * i, {i, Length@colorBasis}];

  permuteIdenticalPolyDict = GetTotalPermutedPolyDict[identicalList];

  (*Calc Lorentz Permutation*)
  rulesPermutedIdentical = GetMassiveIdenticalRules[#, np]& /@ identicalList // Flatten[#, 1]& // DeleteDuplicates;
  permutedBHs = ParallelTable[ReplaceBraNumber[rule][b], {b, bhBasis}, {rule, rulesPermutedIdentical}] // Flatten;
  permutedBHCoorsDict = ReduceToBH[permutedBHs, bhBasis, np]
      // AbsoluteTiming // (If[OptionValue@log, LogPri["identical reduce cost ", #[[1]]]];#[[2]])&;
  rulePermutedIdenticalCoorsDict = Table[rule -> (permutedBHCoorsDict[#]&) /@ ReplaceBraNumber[rule] /@ bhBasis, {rule, rulesPermutedIdentical}]
      // Association;
  lorIdenticalOpDict = GetIndependentPermutedOperatorDict[identicalList, np, rulePermutedIdenticalCoorsDict[#]&];
  lorentzOp = (cfBasisCoordinates.(Dot @@ Table[permuteIdenticalPolyDict[id] /.
      lorIdenticalOpDict[id], {id, identicalList}]))
      // AbsoluteTiming // (If[OptionValue@log, LogPri["Lorentz matrix ",
    {Length@#[[2]], Length@#[[2]][[1]]}
    , " calc cost ", #[[1]]]];#[[2]])& // SparseArray;

  (*Calc direct product op*)
  colorOp = (Dot @@ Table[permuteIdenticalPolyDict[id] /. colorIdenticalOpDict[id], {id, identicalList}])
      .projectionOp // AbsoluteTiming // (If[OptionValue@log, LogPri["color matrix ",
    {Length@#[[2]], Length@#[[2]][[1]]}
    , " calc cost ", #[[1]]]];#[[2]])& // SparseArray;
  Sow[KroneckerProduct[colorOp, lorentzOp]];
  (MemoryConstrained[reducedTotalOperator = RowReduce@ Transpose@ KroneckerProduct[colorOp, lorentzOp];,
    OptionValue@allowedmemory,
    (Print["Not enough memory"];Abort[];)
  ]) // AbsoluteTiming // (If[OptionValue@log, LogPri["find independent basis cost ", #[[1]]]];#[[2]]) &;
  If[OptionValue@log, LogPri["dimension of total permutation op is ",
    {Length@reducedTotalOperator, Length@reducedTotalOperator[[1]]}];];
  independentPermutedBasis = coloredCfBasis[[#]]& /@
      Intersection[physicalBasisIndex,
        Flatten[FirstPosition[#, Except[0, _?NumericQ], {}]& /@
            reducedTotalOperator]];
  Return[independentPermutedBasis];
];

Options[AuxConstructIdenticalColorBasis] := {log -> False};
AuxConstructIdenticalColorBasis[su3ShapeList_, identicalList_, h_, OptionsPattern[]] := Module[
  {colorIndDict, maxInd, colorBasis, rulesIdentical, rulesInnerDict, ParaFindRuleMatrix, ruleIdenticalCoorsDict,
    ruleInnerCoorsDict, colorIdenticalOpDict, colorInnerOpDict, projectionOp, independentIndPosList},
  If[Sort@Keys@su3ShapeDict =!=
      Sort@DeleteDuplicates[su3ShapeList ~ Join ~ Keys@su3ShapeDict],
    Print["No such SU3 type"];Abort[];];
  colorIndDict = GetColorIndDict[su3ShapeDict[#]& /@ su3ShapeList];
  maxInd = colorIndDict // Values // Max;
  If[Mod[maxInd, 3] != 0, Throw["no SU3 singlet"]];
  colorBasis = WarpTableauxWithHead[h] /@ ConstructColorBasis[maxInd / 3];
  rulesIdentical = GetPermuteColorIdenticalRules[#, colorIndDict]& /@ identicalList // Flatten[#, 1]& //
      DeleteDuplicates;
  rulesInnerDict = GetPermuteColorInnerRules[colorIndDict];
  ParaFindRuleMatrix[paraRule_, basis_] := ParallelMap[
    FindColorCor[colorBasis]@ReduceSU3YT@#&,
    ReplaceColorTableauxNumber[paraRule] /@ basis];
  ParaFindRuleMatrix[{}, basis_] := DiagonalMatrix[ConstantArray[1, Length@basis]];
  ruleIdenticalCoorsDict = Table[
    rule -> ParaFindRuleMatrix[rule, colorBasis],
    {rule, rulesIdentical}] // Association
      // AbsoluteTiming // (If[OptionValue@log, LogPri["Reduce color basis1 cost ", #[[1]]]];#[[2]])&;
  ruleInnerCoorsDict = Table[
    rule -> ParaFindRuleMatrix[rule, colorBasis],
    {rule, rulesInnerDict // Values // Flatten[#, 1]& //
        DeleteDuplicates}] // Association
      // AbsoluteTiming // (If[OptionValue@log, LogPri["Reduce color basis2 cost ", #[[1]]]];#[[2]])&;
  colorIdenticalOpDict = GetColorIdenticalPermutedOperatorDict[identicalList, colorIndDict,
    ruleIdenticalCoorsDict[#]&];
  colorInnerOpDict = GetColorInnerPermutedOperatorDict[colorIndDict, ruleInnerCoorsDict[#]&];
  projectionOp = GetProjectInnerColorOp[colorIndDict, colorInnerOpDict];
  Return[{colorIndDict, colorBasis, colorIdenticalOpDict, projectionOp}]
];
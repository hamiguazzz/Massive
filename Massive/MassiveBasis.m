(* Wolfram Language Package *)

If[!Global`$DEBUG, BeginPackage["MassiveBasis`"];];
Print["Loading MassiveBasis..."];

{ConstructIndependentBasis};
{
  GetMassiveIdenticalRules,
  GetIndependentPermutedOperatorDict,
  GetTotalPermutedPolyDict
};
{ConstructBasis};
{ab, sb};
{MassOption, ConstructAmp , FindCor, MatchtoDdim, FMreduce, FMreduceWithDict};
{Sum2List, Prod2List, CountHead, FindCoordinate};

$MassiveVerbose = False;
LogPri[mess___] := If[$MassiveVerbose, Print[mess]];

If[!Global`$DEBUG, Begin["`Private`"]];
Do[Get[file], {file, Global`$CodeFiles}];

ConstructIndependentBasis[spins_, operDim_, identical_ : {}] :=
    Module[{
      np = Length@spins,
      identicalList, physicalBasisIndex, externalDict = <||>,
      getCoordinateMatrix, rules, result, matrixDict, operatorDict, exprDict, totalOperator,
      cfBasisCoordinates, cfBasis, totalCoordinates, permutedBasis, independentPermutedBasis
    },

      getCoordinateMatrix = ConstructBasis[spins, operDim, externalReduceDict -> externalDict, permutation -> #] &;
      (*No identical particles*)
      If[identical === {},
        result = getCoordinateMatrix[{}];
        physicalBasisIndex = PositionOperatorPhysicalDim[result];
        independentPermutedBasis = result[[2]]["basis"][[#]]& /@ physicalBasisIndex;
        Return[independentPermutedBasis];
      ];
      identicalList = (# ~ Append ~ If[OddQ[2 * spins[[#[[1]]]]], "A", "S"])& /@ identical;

      rules = GetMassiveIdenticalRules[#, np] & /@ identicalList //
          Flatten[#, 1] & // DeleteDuplicates;
      result = Table[rule -> Sow[getCoordinateMatrix@rule][[1]], {rule, rules}] //
          Reap;
      matrixDict = result[[1]] // Association;
      operatorDict =
          GetIndependentPermutedOperatorDict[identicalList, np, matrixDict[#] &];
      exprDict = GetTotalPermutedPolyDict[identicalList];
      totalOperator =
          Dot @@ Table[exprDict[id] /. operatorDict[id], {id, identicalList}];
      cfBasisCoordinates = result[[2]][[1]][[1]][[1]];
      cfBasis = result[[2]][[1]][[1]][[2]]["basis"];
      totalCoordinates = totalOperator . cfBasisCoordinates;
      permutedBasis = totalOperator . cfBasis;
      physicalBasisIndex = PositionOperatorPhysicalDim[result[[2]][[1]][[1]]];
      independentPermutedBasis =
          permutedBasis[[#]] & /@
              Intersection[physicalBasisIndex, Flatten[Position[#, Except[0, _?NumericQ], 1, 1] & /@
                  RowReduce@Transpose@totalCoordinates ]];
      Return[independentPermutedBasis];
    ];

If[!Global`$DEBUG, End[]];

If[!Global`$DEBUG, EndPackage[]];
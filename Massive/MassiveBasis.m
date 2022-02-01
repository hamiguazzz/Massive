(* Wolfram Language Package *)

If[!Global`$DEBUG, BeginPackage["MassiveBasis`"];];
Print["Loading MassiveBasis..."];

{ConvertMassiveId2Massless, ExportWelyOp2Tex, ExportSpinorObj2Tex};
{Amp2BrasList, Amp2MetaInfo, Amp2WeylOp, SpinorObj2FeynCalField, ConstructOpInSpinIndexSort};
{ConstructIndependentBasis, PositionOperatorPhysicalDim};
{ConstructBasis};
{MassOption, ConstructAmp , FindCor, MatchCFDim, ReduceSt, ReduceWithDict, ReduceToBH};
{ab, sb};
{Sum2List, Prod2List, CountHead, FactorizeBracket, FindCoordinate};

$MassiveVerbose = False;
LogPri[mess___] := If[$MassiveVerbose, Print[mess]];

If[!Global`$DEBUG, Begin["`Private`"]];
Do[Get[file], {file, Global`$CodeFiles}];

ConstructIndependentBasis[spins_List, operDim_Integer, identical_ : {}] :=
    ConstructIndependentBasis[ConstructBasis[spins, operDim], identical];
ConstructIndependentBasis[result : {cfBasisCoordinates_List, data_Association}, identical_ : {}] := Module[
  {np, spins, identicalList, physicalBasisIndex, dict,
    bh, permutedBHs, permutedBHCoorsDict, ruleCoorsDict,
    rules, operatorDict, exprDict, totalOperator, independentCfBasis, totalCoordinates, independentPermutedBasis},
  spins = data["metaInfo"]["spins"];
  np = Length@spins;
  independentCfBasis = data["basis"];
  physicalBasisIndex = PositionOperatorPhysicalDim[data];
  If[Flatten@identical === {}, Return[independentCfBasis[[#]]& /@ physicalBasisIndex]];
  bh = data["bh"] // Values // Flatten;
  identicalList = (# ~ Append ~ If[OddQ[2 * spins[[#[[1]]]]], "A", "S"])& /@ identical;
  rules = GetMassiveIdenticalRules[#, np]& /@ identicalList // Flatten[#, 1]& // DeleteDuplicates;
  dict = data["reduceDict"];
  permutedBHs = ParallelTable[ReplaceBraNumber[rule][b], {b, bh}, {rule, rules}] // Flatten;
  permutedBHCoorsDict = ReduceToBH[permutedBHs, bh, np]
      // AbsoluteTiming // (LogPri["identical reduce cost ", #[[1]]];#[[2]])&;
  ruleCoorsDict = Table[rule -> (permutedBHCoorsDict[#]&) /@ ReplaceBraNumber[rule] /@ bh, {rule, rules}]
      // Association;
  operatorDict = GetIndependentPermutedOperatorDict[identicalList, np, ruleCoorsDict[#]&];
  exprDict = GetTotalPermutedPolyDict[identicalList];
  totalOperator = Dot @@ Table[exprDict[id] /. operatorDict[id], {id, identicalList}];
  totalCoordinates = cfBasisCoordinates.Transpose@totalOperator;
  independentPermutedBasis = independentCfBasis[[#]]& /@
      Intersection[physicalBasisIndex,
        Flatten[Position[#, Except[0, _?NumericQ], 1, 1]& /@
            RowReduce@Transpose@totalCoordinates]];
  Return[independentPermutedBasis];
];

If[!Global`$DEBUG, End[]];

If[!Global`$DEBUG, EndPackage[]];

Print["Loaded MassiveBasis"];
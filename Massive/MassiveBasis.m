(* Wolfram Language Package *)

If[!Global`$DEBUG, BeginPackage["MassiveBasis`"];];
Print["Loading MassiveBasis..."];

{ExportSpinorObj2Tex};
{Amp2WeylOp};
{ConstructIndependentBasis, ConstructIndependentColoredBasis};
{ab, sb};
{Sum2List, Prod2List};
{ClearCache};

If[!BooleanQ[$MassiveVerbose],$MassiveVerbose = False;];
LogPri[mess___] := If[$MassiveVerbose, Print[mess]];

If[!Global`$DEBUG, Begin["`Private`"]];

Do[Get[file], {file, Global`$CodeFiles}];

If[!Global`$DEBUG, End[]];
ImportModel[FileNameJoin[{$MassiveDir, "Model", "default.json"}]];

(*Add cache*)
ClearCache[];
$MassiveCachedFunction = {
  ConstructCFIByFakeDim,
  CalcPermutationMatrixDictByFakeDim,
  ConstructIndependentBasis,
  AuxConstructIdenticalColorBasis,
  ConstructIndependentColoredBasis};
CacheFunction[$MassiveCachedFunction];

If[!Global`$DEBUG, EndPackage[]];

Print["Loaded MassiveBasis"];
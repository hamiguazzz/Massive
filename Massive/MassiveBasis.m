(* Wolfram Language Package *)

If[!Global`$DEBUG, BeginPackage["MassiveBasis`"];];
Print["Loading MassiveBasis..."];

{
  GetMassiveIdenticalRules,
  GetIndependentPermutedOperatorDict,
  GetTotalPermutedPolyDict
};
{ConstructBasis};
{ab, sb};
{FptAmp , FindCor, MatchtoDdim, FMreduce, FMreduceWithDict};
{Sum2List, Prod2List, CountHead, FindCoordinate};

$MassiveVerbose = False;
LogPri[mess___] := If[$MassiveVerbose, Print[mess]];

If[!Global`$DEBUG, Begin["`Private`"]];
Do[Get[file], {file, Global`$CodeFiles}];
If[!Global`$DEBUG, End[]];

If[!Global`$DEBUG, EndPackage[]];
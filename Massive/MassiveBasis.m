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

If[!Global`$DEBUG, End[]];
ImportModel[FileNameJoin[{$MassiveDir, "Model", "default.json"}]];

If[!Global`$DEBUG, EndPackage[]];

Print["Loaded MassiveBasis"];
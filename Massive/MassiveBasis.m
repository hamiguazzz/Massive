(* Wolfram Language Package *)

BeginPackage["MassiveBasis`"];
Print["Loading MassiveBasis..."];

{ConstructIndependentOperatorBasis}
{ab,sb}
{FptAmp , FindCor, MatchtoDdim, FMreduce, FMreduceWithDict}
{Sum2List, Prod2List, CountHead, FindCoordinate}


If[!Global`$DEBUG, Begin["`Private`"]];
Do[Get[file], {file, Global`$CodeFiles}];
If[Global`$DEBUG, Print["Debug Mode"];Begin["`Private`"]];
End[];

EndPackage[]
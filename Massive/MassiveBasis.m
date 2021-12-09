(* Wolfram Language Package *)

BeginPackage["MassiveBasis`"];
Print["Loading MassiveBasis..."];

If[!Global`$DEBUG, Begin["`Private`"]];
Do[Get[file], {file, Global`$CodeFiles}];
If[Global`$DEBUG, Print["Debug Mode"];Begin["`Private`"]];
End[];

EndPackage[]
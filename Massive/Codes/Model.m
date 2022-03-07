(*Model file should be storaged as json*)
(*Model is an association of particle variable name->definition*)
(*particle definition is an association of
  spin,
  field name,
  field strength name,
  mass,
  color,
*)

(* ::Section:: *)
(* Control model *)
$currentModel = <||>;
SetSharedVariable[$currentModel];
modelDefaultProperties = <|
  "spin" -> 0,
  "field name" -> "\\phi",
  "field strength name" -> "",
  "mass" -> 0,
  "color" -> "",
  "charge" -> 0
|>;

ImportModel[fileName_String] := Module[{
  particlesDict, CheckProperty, CheckSpin, CheckMass, CheckCharge
},
  particlesDict = Association /@ Association@Import[fileName];
  CheckSpin[spinIn_] := Switch[spinIn,
    0 | "0" | 0.0, 0,
    0.5 | N@0.5 | "0.5" | "1/2" | 1 / 2 , Rational[1, 2],
    1 | "1" | 1.0, 1,
    _, Throw["No such spin"]
  ];
  CheckMass[massIn_] := Switch[massIn,
    0 | "0", 0,
    _, "m" <> ToString@massIn
  ];
  CheckCharge[chargeIn_] := If[
    NumberQ@ToExpression@ToString@chargeIn,
    ToExpression@ToString@chargeIn,
    Throw["No such charge"]
  ];
  CheckProperty[associationInput_, propertyName_, checkFun_ : Null] :=
      Module[{re = associationInput, temp},
        Do[
          If[!KeyExistsQ[re[k], propertyName],
            temp = re[k];
            AssociateTo[temp, (propertyName -> modelDefaultProperties[propertyName])];
            re[k] = temp;
          ];
          If[checkFun =!= Null,
            re[k][propertyName] = checkFun[re[k][propertyName]];];
          , {k, re // Keys}
        ];
        Return[re]
      ];
  particlesDict = Fold[CheckProperty, particlesDict, modelDefaultProperties // Keys];
  particlesDict = CheckProperty[particlesDict, "mass", CheckMass];
  particlesDict = CheckProperty[particlesDict, "spin", CheckSpin];
  particlesDict = CheckProperty[particlesDict, "charge", CheckCharge];
  $currentModel = particlesDict;
  Return[$currentModel];
];

(* ::Section:: *)
(*Control basis construction*)

ClearSavedConstructBasis[] := (ClearAll[SavedConstructBasis]; InitialSavedConstructBasis[];);
InitialSavedConstructBasis[] := SavedConstructBasis[parameters___] :=
    SavedConstructBasis[parameters] = ConstructBasis[parameters];
InitialSavedConstructBasis[];

(*output mode: "amplitude", "operator", "feyncalc", "tex" *)
(*TODO deliver options*)
Options[BasisByModel] := {output -> "tex"};
BasisByModel[particlesParm_List, fromOpDim_, toOpDim_, OptionsPattern[]] := Module[
  {particles, np, spins, masses, colors, identicalList, externalDict, currentBasis, currentResult, resultDict},
  particles = Sort[particlesParm];
  If[Length@particles < 4 || Or @@ (!KeyExistsQ[$currentModel, #]& /@ particles),
    Print["particles are illegal!"];
    Return[];
  ];
  resultDict = Table[dim -> Null, {dim, fromOpDim, toOpDim}] // Association;
  spins = $currentModel[#]["spin"]& /@ particles;
  masses = $currentModel[#]["mass"]& /@ particles;
  If[
    OddQ[2 * Plus @@ spins]
        || 0 == Length@Select[masses, # =!= 0&]
        || 0 != Mod[Total[colors /. {"" -> 0, "q" -> 1, "aq" -> 2, "g" -> 3}], 3]
        || 0 != Total[$currentModel[#]["charge"]& /@ particles],
    Print["particles combination are illegal!"];
    Return[];
  ];
  np = Length@spins;
  colors = $currentModel[#]["color"]& /@ particles;
  identicalList = particles // PositionIndex // Values // Select[Length@# > 1 &];
  externalDict = Association@Table[ i ->
      If[$currentModel[particles[[i]]]["field strength name"] === "",
        {$currentModel[particles[[i]]]["field name"]},
        {$currentModel[particles[[i]]]["field name"], $currentModel[particles[[i]]]["field strength name"]}
      ]
    , {i, Length@particles}];

  LogPri["Spin:", spins, "\n", "Mass:", masses, "\n", "Color:", colors, "\n",
    "Identical:", identicalList, "\n", "Field:", externalDict];
  Do[
    currentBasis = {};
    Catch[currentBasis = SavedConstructBasis[spins, dim, mass -> masses];];
    If[currentBasis == {}, Continue[];];
    If[0 == Length@Select[colors, # =!= ""&],
      currentResult = ConstructIndependentBasis[currentBasis, identicalList, mass -> masses];
      resultDict[dim] = Switch[ToLowerCase@OptionValue@output,
        "amplitude" | "amp", currentResult,
        "operator" | "op", Amp2WeylOp[np, mass -> masses] /@ currentResult,
        (*TODO feyncalc*)
        "tex" | "latex", ExportSpinorObj2Tex[#, external -> externalDict] & /@
            Amp2WeylOp[np, mass -> masses] /@ currentResult // ExportTexList2Array,
        _, Null
      ];
      ,
      currentResult = ConstructIndependentColoredBasis[currentBasis, colors, identicalList];
      resultDict[dim] = Switch[ToLowerCase@OptionValue@output,
        "amplitude" | "amp", currentResult,
        "operator" | "op", Amp2WeylOp[np, colorType -> colors, mass -> masses] /@ currentResult,
        (*TODO feyncalc*)
        "tex" | "latex", ExportSpinorObj2Tex[#, external -> externalDict] & /@
            Amp2WeylOp[np, colorType -> colors, mass -> masses] /@ currentResult // ExportTexList2Array,
        _, Null
      ];
    ];
    , {dim, fromOpDim, toOpDim}
  ];
  Return[resultDict /. Null -> {}];
];

Options[OrganizeStringAssociation] = {
  sectionfun -> (StringJoin["\\subsection{ Dimension = ", ToString@#, "}"]&),
  heading -> "", exportPath -> "", delimiter -> "\n"};
OrganizeStringAssociation[texDict_?AssociationQ,
  OptionsPattern[]] := Module[
  {
    keys = texDict // Keys // Sort,
    endLine = OptionValue@delimiter,
    result = OptionValue@heading <> OptionValue@delimiter,
    fun = OptionValue@sectionfun
  },
  result = result <> StringJoin @@ ((
    fun@# <> endLine
        <> "$$" <> endLine
        <> ToString@texDict[#]
        <> "$$" <> endLine
  )& /@ keys);
  If[OptionValue@exportPath =!= "",
    If[!FileExistsQ[OptionValue@exportPath],
      CreateFile[OptionValue@exportPath];
    ];
    Export[OptionValue@exportPath, result] // Return;
  ];
  Return[result];
];
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
  "particle name" -> "",
  "field name" -> "\\phi",
  "field strength name" -> "",
  "mass" -> 0,
  "color" -> "",
  "charge" -> 0,
  "antiparticle" -> False
|>;

ImportModel[fileName_String] := Module[{
  particlesDict, CheckProperty, CheckSpin, CheckMass, CheckCharge
},
  particlesDict = Association /@ Association@Import[fileName];
  CheckSpin[spinIn_] := Switch[spinIn,
    0 | "0" | 0.0, 0,
    0.5 | N@0.5 | "0.5" | "1/2" | 1 / 2 , Rational[1, 2],
    -0.5 | -N@0.5 | "-0.5" | "-1/2" | -1 / 2 , -Rational[1, 2],
    1 | "1" | 1.0, 1,
    -1 | "-1" | -1.0, -1,
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
  Do[If[particlesDict[p]["particle name"] == "", particlesDict[p]["particle name"] = p;];, {p, Keys@particlesDict}];
  $currentModel = particlesDict;
  Return[$currentModel];
];

(* ::Section:: *)

(*output mode: "amplitude", "operator", "feyncalc", "tex" *)
(*TODO deliver options*)
Options[BasisByModel] := {output -> "tex", log -> False, "form" -> String};
BasisByModel[particlesParm_List, fromOpDim_, toOpDim_, OptionsPattern[]] := Module[
  {particles, massivePos, masslessPos, np, spins, masses,
    antiparticles, colors, charges, identicalList,
    externalDict, currentBasis, currentResult, resultDict},
  particles = Sort[particlesParm, $currentModel[#]["spin"] & /@ # &];
  If[Length@particles < 4 || Or @@ (!KeyExistsQ[$currentModel, #]& /@ particles),
    Print["particles are illegal!"];
    Return[];
  ];
  resultDict = Table[dim -> Null, {dim, fromOpDim, toOpDim}] // Association;
  masses = $currentModel[#]["mass"]& /@ particles;
  masslessPos = Flatten@Position[masses, _?(# === 0&), 1];
  massivePos = Complement[Range@Length@particles, masslessPos];
  particles = particles[[massivePos ~ Join ~ masslessPos]];
  spins = $currentModel[#]["spin"]& /@ particles;
  np = Length@spins;
  masses = $currentModel[#]["mass"]& /@ particles;
  charges = $currentModel[#]["charge"]& /@ particles;
  colors = $currentModel[#]["color"]& /@ particles;
  If[Length@massivePos == 0, Print["at least one particle massive!"]; Return[];];
  If[
    OddQ[2 * Plus @@ spins]
        || 0 != Mod[Total[colors /. {"" -> 0, "q" -> 1, "aq" -> 2, "g" -> 3}], 3]
        || 0 != Total[charges],
    Print["particles combination are illegal!"];
    Return[];
  ];
  identicalList = particles // PositionIndex // Values // Select[Length@# > 1 &];
  externalDict = Association@Table[ i ->
      If[$currentModel[particles[[i]]]["field strength name"] === "",
        {$currentModel[particles[[i]]]["field name"]},
        {$currentModel[particles[[i]]]["field name"], $currentModel[particles[[i]]]["field strength name"]}
      ]
    , {i, Length@particles}];
  antiparticles = Table[If[
    $currentModel[particles[[i]]]["antiparticle"],
    i , Missing[]], {i, Length@particles}] // DeleteMissing;

  If[OptionValue@log, LogPri["Spin:", spins, "\n", "Mass:", masses, "\n", "Color:", colors, "\n",
    "Identical:", identicalList, "\n", "Field:", externalDict, "\n", "Antiparticles", antiparticles];];

  Do[
    currentBasis = {};
    If[0 == Length@Select[colors, # =!= ""&],
      currentResult = ConstructIndependentBasis[spins, dim, identicalList, mass -> masses, log -> OptionValue@log];
      resultDict[dim] = Switch[ToLowerCase@OptionValue@output,
        "amplitude" | "amp", currentResult,
        "operator" | "op", Amp2WeylOp[np, mass -> masses] /@ currentResult,
        (*TODO feyncalc*)
        "tex" | "latex", ExportSpinorObj2Tex[#, "form" -> OptionValue@"form", external -> externalDict, antiPaticleList -> antiparticles] & /@
            Amp2WeylOp[np, mass -> masses] /@ currentResult,
        _, Null
      ];
      ,
      currentResult = ConstructIndependentColoredBasis[spins, dim, colors, identicalList, mass -> masses, log -> OptionValue@log];
      resultDict[dim] = Switch[ToLowerCase@OptionValue@output,
        "amplitude" | "amp", currentResult,
        "operator" | "op", Amp2WeylOp[np, colorType -> colors, mass -> masses] /@ currentResult,
        (*TODO feyncalc*)
        "tex" | "latex", ExportSpinorObj2Tex[#, "form" -> OptionValue@"form", external -> externalDict, antiPaticleList -> antiparticles] & /@
            Amp2WeylOp[np, colorType -> colors, mass -> masses] /@ currentResult,
        _, Null
      ];
    ];
    , {dim, fromOpDim, toOpDim}
  ];
  Return[resultDict /. Null -> {}];
];

Options[OrganizeResultTexDict] := {heading -> "", delimiter -> "\n", exportPath -> "", equstart -> "\\[", equend -> "\\]"};
OrganizeResultTexDict[texDict_?AssociationQ, OptionsPattern[]] := Module[
  {
    EquLine, DimHeadLine,
    keys = texDict // Keys // Sort,
    endLine = OptionValue@delimiter,
    result
  },
  EquLine[key_] := If[
    Length@texDict[key] > 0 && texDict[key][[1]] =!= "",
    (OptionValue@equstart <> endLine
        <> ToString@# <> endLine
        <> OptionValue@equend <> endLine <> endLine)& /@ texDict[key] // StringJoin,
    ""
  ];
  DimHeadLine[key_] := If[
    Length@texDict[key] > 0 && texDict[key][[1]] =!= "",
    StringJoin["\\subsection{Dimension ", ToString@key, " , ",
      "$\\mathcal{O}_{", ToString@key, "}^{",
      If[Length@texDict[key] > 1, "1\\sim " <> ToString@Length@texDict[key], "1"]
      , "}$}", endLine],
    ""
  ];
  result = OptionValue@heading <> StringJoin[(DimHeadLine[#] <> EquLine[#])& /@ keys];
  If[OptionValue@exportPath =!= "",
    If[!FileExistsQ[OptionValue@exportPath],
      CreateFile[OptionValue@exportPath];
    ];
    Export[OptionValue@exportPath, result] // Return;
  ];
  Return[result];
];


Options@BasisResultDict2JsonObj = {
  "headWrap" -> Default,
  "dimWrap" -> ("d" <> ToString@#&),
  "equWrap" -> (#&)
};
BasisResultDict2JsonObj[particles_List, texDict_?AssociationQ, OptionsPattern[]] := Module[
  {jsonObj = {}, head, dims, dimProps, nonOpDims = {}, fDim = OptionValue@"dimWrap", fEqu = OptionValue@"equWrap"},
  (*Head*)
  head = If[OptionValue@"headWrap" =!= Default, (OptionValue@"headWrap")[particles],
    StringRiffle[$currentModel[#]["particle name"]& /@ particles, " "]
  ];

  dims = Keys@texDict;
  nonOpDims = Select[dims, Length@texDict[#] == 0&];
  dims = Complement[dims, nonOpDims];
  AppendTo[jsonObj, "type" -> head];
  AppendTo[jsonObj, "dimensions" -> dims];

  Do[ AppendTo[jsonObj, fDim@d -> fEqu /@ texDict[d] ];, {d, dims}];
  Return[jsonObj];
]
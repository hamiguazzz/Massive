LogPri["FormatOutput Loaded"];
DisplayYT[warpedYt_, h_ : defaultYTHead] /; Head@warpedYt === h := DisplayYT[warpedYt[[1]]];
DisplayYT[yt_List] := Grid[yt, Frame -> {None, None,
  Flatten@Table[{i, j} -> True, {i, Length@yt}, {j,
    Length@yt[[i]]}]}];
DisplayYT[ytExpr_Plus, h_ : defaultYTHead] := DisplayYT[#, h]& /@ Sum2List[ytExpr] // Total;
DisplayYT[ytExpr_Times, h_ : defaultYTHead] := Times @@ (DisplayYT[#, h]& /@ Prod2List[ytExpr]);
DisplayYT[ytExpr_, h_ : defaultYTHead] /; NumberQ@ytExpr := ytExpr;

ConvertMassiveId2Massless[expr_, np_] := ReplaceBraNumber[expr, Table[np * 2 + 1 - i -> i, {i, np}]];

(*
\newcommand{\abk}[1] {\left\langle #1\right\rangle}
\newcommand{\sbk}[1] {\left[#1\right]}
*)
(*defaultAbkFun = "\\abk{" <> # <> "}"&;*)
(*defaultSbkFun = "\\sbk{" <> # <> "}"&;*)
(*TODO deal with minus*)
defaultAbkFun = "\\left\\langle " <> # <> "\\right\\rangle"&;
defaultSbkFun = "\\left[" <> # <> "\\right]"&;
ab /: ExportAmp2Tex[ab[i_, j_], abkFun_, sbkFun_] := abkFun[ToString@i <> ToString@j];
sb /: ExportAmp2Tex[sb[i_, j_], abkFun_, sbkFun_] := sbkFun[ToString@i <> ToString@j];
ExportAmp2Tex[n_?NumberQ, abkFun_, sbkFun_] := If[Denominator@n == 1, ToString@n,
  "\\frac{" <> ToString@Numerator@n <> "}{" <> ToString@Denominator@n <> "} "];
ExportAmp2Tex[l_List, abkFun_, sbkFun_] := ExportAmp2Tex[#, abkFun, sbkFun]& /@ l;
ExportAmp2Tex[expr_Times, abkFun_, sbkFun_] := StringJoin@ExportAmp2Tex[Prod2List[expr], abkFun, sbkFun];
ExportAmp2Tex[expr_Plus, abkFun_, sbkFun_] := ExportAmp2Tex[Sum2List@expr, abkFun, sbkFun] // StringRiffle[#, "+"]&;
ExportAmp2Tex[expr_] := ExportAmp2Tex[expr, defaultAbkFun, defaultSbkFun];

(*Label Section*)
(*Lorentz Label start with "LI"*)
allowedLorentz = {"\[Mu]", "\[Nu]", "\[Rho]", "\[Sigma]", "\[Xi]", "\[Tau]",
  "\[Zeta]", "\[Eta]", "\[Theta]", "\[Iota]", "\[Kappa]", "\[Lambda]"};
Number2Greek = ((If[#2 > 0, "{" <> ToString@TeXForm@#1 <> "_" <> ToString[#2 + 1] <> "}", ToString@TeXForm@#1]&)[
  allowedLorentz[[Mod[#, Length@allowedLorentz]]], Quotient[#, Length@allowedLorentz]]) &;
Number2Latin = ((If[#2 > 0, "{" <> ToString@#1 <> "_" <> ToString[#2 + 1] <> "}", ToString@#1]&)[
  Alphabet[][[Mod[0 + #, 26]]], Quotient[#, 26]]) &;
(*===TODO===remove letters not used for label ===TODO===*)
numberLorentzIndex[x_] := StringSplit[x, "LI"] // First // ToExpression;
numberColorIndex[x_] := StringSplit[x, "CI"] // First // ToExpression;
Index2Greek[x_] := x // ToString // numberLorentzIndex // Number2Greek;
Index2Latin[x_] := x // ToString // numberColorIndex // Number2Latin;

AddBrasToSpinorObjList[spinorOpList_List] := Module[
  {SpinorObjIsDQ, SpinorObjIsPsiQ, SpinorObjIsFieldQ,
    flag1, flag2, tempList, resultList, indexNow, op
  },
  SpinorObjIsDQ[singleOp_List] := MatchQ[singleOp, {"D", _Integer, _}];
  SpinorObjIsPsiQ[singleOp_List] := MatchQ[singleOp, {_Integer, 1 / 2 | -(1 / 2) | 1 / 2 I | -(1 / 2) I, ___}];
  SpinorObjIsFieldQ[singleOp_List] := MatchQ[singleOp, {"\[Phi]" | "A" | "F-" | "F+", ___}]
      || SpinorObjIsPsiQ[singleOp];
  (*D...F*)
  flag1 = 0;
  tempList = {};
  Do[
    If[flag1 == 0 && SpinorObjIsDQ@op,
      flag1 = 1;
      tempList ~ AppendTo ~ {"braDL"};
    ];
    tempList ~ AppendTo ~ op;
    If[flag1 != 0 && SpinorObjIsFieldQ@op,
      flag1 = 0;
      tempList ~ AppendTo ~ {"braR"};
    ];
    , {op, spinorOpList}];
  resultList = tempList;

  (*\[Psi]...\[Psi]*)
  flag1 = 0;
  tempList = {};
  Do[
    If[flag1 == 0 && SpinorObjIsPsiQ@op,
      flag1 = 1;
      tempList ~ AppendTo ~ {"braPL"};
      tempList ~ AppendTo ~ op;
      Continue[];
    ];
    tempList ~ AppendTo ~ op;
    If[flag1 != 0 && SpinorObjIsPsiQ@op,
      flag1 = 0;
      tempList ~ AppendTo ~ {"braR"};
    ];
    , {op, resultList}];
  resultList = tempList;
  (*Rearrange cross braDL,braPL*)
  flag1 = 0;
  flag2 = 0;
  tempList = {};
  Do[
    op = resultList[[i]];
    If[flag1 == 0 && op === {"braDL"},
      flag1 = 1; flag2 = 1 + Length@tempList;
    ];
    If[flag1 == 1 && op === {"braR"},
      flag1 = 0;
    ];
    If[flag1 == 1 && op === {"braPL"},
      tempList = Insert[tempList, {"braL"}, flag2];
      Continue[];
    ];
    tempList ~ AppendTo ~ op
    , {i, Length@resultList}];
  resultList = tempList /. {{"braDL"} -> {"braL"}, {"braPL"} -> {"braL"}};
  Return[resultList];
];

Options[ExportWelyOp2Tex] = Options[ExportSpinorObj2Tex];
ExportWelyOp2Tex[weylop_Plus, opts : OptionsPattern[]] := (ExportSpinorObj2Tex[#, opts])& /@ Sum2List[weylop] //
    StringRiffle[#, "+"]&;
ExportWelyOp2Tex[weylop_, opts : OptionsPattern[]] := ExportSpinorObj2Tex[#, opts]&@weylop;
(*Example external-><|1->{"W^+","W^+"},2->{"W^-","W^-"},3->{"g","G"},4->{"A","F"},5->{"\\nu_e"},6->{"e"}|>*)
Options[ExportSpinorObj2Tex] := {external -> "Default", addbra -> True};
ExportSpinorObj2Tex[spinorOpListParm_, OptionsPattern[]] := Module[{
  spinorOpList, innerRules, externalRules, FieldTranslationRule,
  opList, dic, curObj, outList, trList
},
  spinorOpList = If[OptionValue@addbra, AddBrasToSpinorObjList[spinorOpListParm], spinorOpListParm];
  innerRules = {
    {"braL"} -> "\\left(",
    {"braR"} -> "\\right)",
    {"D", n_, i_} :> "D_{" <> Index2Greek[i] <> "}",
    {"\[Sigma]", LI_, S1_, S2_} :> "\\sigma^{" <> Index2Greek[LI] <> "}",
    {"\[Sigma]Bar", LI_, S1_, S2_} :> "\\bar{\\sigma}^{" <> Index2Greek[LI] <> "}",
    {"\[Sigma]", L1_, L2_, S1_, S2_} :> "\\sigma^{" <> Index2Greek[L1] <> " " <> Index2Greek[L2] <> "}",
    {"\[Sigma]Bar", L1_, L2_, S1_, S2_} :> "\\bar{\\sigma}^{" <> Index2Greek[L1] <> " " <> Index2Greek[L2] <> "}",
    {"\[Epsilon]", i_, j_, k_} :> "\\epsilon^{" <> Index2Latin[i] <> " " <> Index2Latin[j] <> " " <> Index2Latin[k] <> "}",
    {"\[Epsilon]i", i_, j_, k_} :> "\\epsilon_{" <> Index2Latin[i] <> " " <> Index2Latin[j] <> " " <> Index2Latin[k] <> "}",
    {"TF", i_, j_, k_} :> "\\lambda ^{" <> Index2Latin[i] <> "\\ " <> Index2Latin[k] <> "}_" <> Index2Latin[j],
    SUNTF[i_, j_, k_] :> "(\\lambda ^{" <> ToString[Index2Latin /@ i] <> "})^{" <> "\\ " <> Index2Latin[k] <> "}_" <> Index2Latin[j],
    SUNT[SUNIndex[c_]] :> "T^" <> Index2Latin[c],
    SUND[i_, j_, k_] :> "d_{" <> Index2Latin[i] <> " " <> Index2Latin[j] <> " " <> Index2Latin[k] <> "}",
    SUNF[i_, j_, k_] :> "f_{" <> Index2Latin[i] <> " " <> Index2Latin[j] <> " " <> Index2Latin[k] <> "}"
  };

  FieldTranslationRule[number_Integer -> {name_String}] :=
      {
        {"\[Phi]", number} :> name,
        {number, 1 / 2, i_} :> "{" <> name <> "}_{R}",
        {number, -(1 / 2), i_} :> "{" <> name <> "}_{L}",
        (*with color index*)
        {number, 1 / 2, i_, j_} :> "{" <> name <> "}_{R}^{" <> Index2Latin[j] <> "}",
        {number, -(1 / 2), i_, j_} :> "{" <> name <> "}_{L}^{" <> Index2Latin[j] <> "}" ,
        {number, 1 / 2 I, i_, j_} :> "{" <> name <> "}_{R" <> " " <> Index2Latin[j] <> "}",
        {number, -(1 / 2) I, i_, j_} :> "{" <> name <> "}_{L" <> " " <> Index2Latin[j] <> "}"
      };

  FieldTranslationRule[number_Integer -> {field_String, strength_String}] :=
      {
        {"A", number, i_} :> "{" <> field <> "}" <> "_{" <> " " <> Index2Greek[i] <> "}",
        {"F+", number, i_, j_} :> "{" <> strength <> "}" <> "^{+}" <> "_{"
            <> " " <> Index2Greek[i] <> " " <> Index2Greek[j] <> "}",
        {"F-", number, i_, j_} :> "{" <> strength <> "}" <> "^{-}" <> "_{"
            <> " " <> Index2Greek[i] <> " " <> Index2Greek[j] <> "}",
        (*with color index*)
        (*adjoint*)
        {"F+", number, i_, j_, k_} :> "{" <> strength <> "}" <> "_{"
            <> " " <> Index2Greek[i] <> " " <> Index2Greek[j] <> "}^{+" <> Index2Latin[k] <> "}",
        {"F-", number, i_, j_, k_} :> "{" <> strength <> "}" <> "_{"
            <> " " <> Index2Greek[i] <> " " <> Index2Greek[j] <> "}^{-" <> Index2Latin[k] <> "}",
        {"A", number, i_, k_} :> "{" <> field <> "}" <>
            "_{" <> " " <> Index2Greek[i] <> "}^{" <> Index2Latin[k] <> "}",
        (*contracted generator*)
        {"F+", number, i_, j_, k_, l_} :> "{" <> strength <> "}" <> "_{"
            <> " " <> Index2Greek[i] <> " " <> Index2Greek[j] <> " " <> Index2Latin[k] <>
            "}^{+" <> Index2Latin[l] <> "}",
        {"F-", number, i_, j_, k_, l_} :> "{" <> strength <> "}" <> "_{"
            <> " " <> Index2Greek[i] <> " " <> Index2Greek[j] <> " " <> Index2Latin[k] <>
            "}^{-" <> Index2Latin[l] <> "}",
        {"A", number, i_, k_, l_} :> "{" <> field <> "}" <>
            "_{" <> Index2Greek[i] <> " " <> Index2Latin[k] <> "}^{" <> Index2Latin[l] <> "}"
      };

  If[OptionValue@external === "Default",
    externalRules = {
      {"\[Phi]", i_} :> "\\phi_" <> ToString[i],
      {n_Integer, 1 / 2, i_} :> "\\psi_{R" <> ToString[n] <> "}",
      {n_Integer, -(1 / 2), i_} :> "\\psi_{L" <> ToString[n] <> "}",
      {"A", n_, i_} :> "A_{" <> ToString[n] <> " " <> Index2Greek[i] <> "}",
      {"F+", n_, i_, j_} :> "{F}^{+}_{" <> ToString[n] <> " " <> Index2Greek[i] <> " " <> Index2Greek[j] <> "}",
      {"F-", n_, i_, j_} :> "{F}^{-}_{" <> ToString[n] <> " " <> Index2Greek[i] <> " " <> Index2Greek[j] <> "}",
      (*with color index*)
      {n_Integer, 1 / 2, i_, j_} :> "\\psi_{R" <> ToString[n] <> "}" <> "^{" <> Index2Latin[j] <> "}",
      {n_Integer, -(1 / 2), i_, j_} :> "\\psi_{L" <> ToString[n] <> "}" <> "^{" <> Index2Latin[j] <> "}" ,
      {n_Integer, 1 / 2 I, i_, j_} :> "\\bar{\\psi}_{R" <> ToString[n] <> " " <> Index2Latin[j] <> "}",
      {n_Integer, -(1 / 2) I, i_, j_} :> "\\bar{\\psi}_{L" <> ToString[n] <> " " <> Index2Latin[j] <> "}" ,

      {"F+", n_, i_, j_, k_} :> "{F}_{" <> ToString[n] <> " "
          <> Index2Greek[i] <> " " <> Index2Greek[j] <> "}^{+" <> Index2Latin[k] <> "}",
      {"F-", n_, i_, j_, k_} :> "{F}_{" <> ToString[n] <> " "
          <> Index2Greek[i] <> " " <> Index2Greek[j] <> "}^{-" <> Index2Latin[k] <> "}",
      {"A", n_, i_, k_} :> "A_{" <> ToString[n] <> " " <> Index2Greek[i] <> "}^{" <> Index2Latin[k] <> "}",
      {"F+", n_, i_, j_, k_, l_} :> "{F}_{" <> ToString@n <> " "
          <> Index2Greek[i] <> " " <> Index2Greek[j] <> " " <> Index2Latin[k] <>
          "}^{+" <> Index2Latin[l] <> "}",
      {"F-", n_, i_, j_, k_, l_} :> "{F}_{" <> ToString@n <> " "
          <> Index2Greek[i] <> " " <> Index2Greek[j] <> " " <> Index2Latin[k] <>
          "}^{-" <> Index2Latin[l] <> "}",
      {"A", n_, i_, k_, l_} :> "A" <>
          "_{" <> ToString@n <> " "
          <> Index2Greek[i] <> " " <> Index2Latin[k] <> "}^{" <> Index2Latin[l] <> "}"

    },
    externalRules = Join @@ (FieldTranslationRule /@ Normal@OptionValue@external);
  ];
  dic = Join[innerRules, externalRules];
  outList = {};
  curObj = spinorOpList[[1]];
  opList = Drop[spinorOpList, 1];
  If[(curObj // Head // ToString) != "List", (*only simplefied color term does not have list as head*)
    AppendTo[outList, "(" <> ((curObj //. dic) // ToString) <> ")"];
    curObj = opList[[1]];
    opList = Drop[opList, 1];
  ];
  While[curObj != {"Tr"},
    AppendTo[outList, curObj /. dic];
    If[Length[opList] == 0, Return[StringJoin[outList]]];
    curObj = opList[[1]];
    opList = Drop[opList, 1];
  ];
  While[Length[opList] != 0,
    trList = {};
    curObj = opList[[1]];
    opList = Drop[opList, 1];
    While[curObj != {"Tr"},
      AppendTo[trList, curObj /. dic];
      curObj = opList[[1]];
      opList = Drop[opList, 1];
      If[Length[opList] == 0, AppendTo[trList, curObj /. dic];
      Break[]]
    ];
    outList = Join[outList, {"\\operatorname{Tr}\\left("}, trList, {"\\right)"}];
  ];
  Return[StringJoin[outList]];
];


Options[ExportTexList2Array] = {
  env -> "array",
  param -> "l",
  option -> "",
  prefix -> "\t",
  suffix -> "\\\\\n"
};
ExportTexList2Array[{}, OptionsPattern[]] := "\\text{None}\n";
ExportTexList2Array[l_List, OptionsPattern[]] /; StringQ[l[[1]]] :=
    With[{},
      If[Length@l == 1,
        l[[1]] <> "\n"
        ,
        "\\begin{" <> OptionValue@env <> "}"
            <> If[OptionValue@param =!= "" && OptionValue@param =!= Null,
          "{" <> OptionValue@param <> "}", ""]
            <> If[OptionValue@option =!= "" && OptionValue@option =!= Null,
          "[" <> OptionValue@option <> "]\n", "\n"]
            <> StringJoin[(OptionValue@prefix <> # <> OptionValue@suffix)& /@ l]
            <> "\\end{" <> OptionValue@env <> "}\n"
      ]
    ];
(*Example: "\\begin{array}{c}\n \t" <>
     StringRiffle[#, "\\\\ \n\t"] &@(# /. TraditionalForm[x_] -> x &@
      ExportWelyOp2Tex /@ (Amp2WeylOp[4]@# & /@
       ConstructIndependentBasis[{1, 1, 0, 0},
        6, {{1, 2}, {3, 4}}])) <> "\n\\end{array}" // TraditionalForm*)
(*Example: "\\begin{array}{c}\n \t" <>
     StringRiffle[#, "\\\\ \n\t"] &@(# /. TraditionalForm[x_] -> x &@
      ExportWelyOp2Tex /@ (Amp2WeylOp[4]@# & /@
       ConstructIndependentBasis[{1, 1, 0, 0},
        6, {{1, 2}, {3, 4}}])) <> "\n\\end{array}" // TraditionalForm*)
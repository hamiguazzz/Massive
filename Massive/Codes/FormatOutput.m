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
defaultAbkFun = "\\left\\langle " <> # <> "\\right\\rangle"&;
defaultSbkFun = "\\left[" <> # <> "\\right]"&;
ab /: ExportAmp2Tex[ab[i_, j_], abkFun_, sbkFun_] := abkFun[ToString@i <> ToString@j];
sb /: ExportAmp2Tex[sb[i_, j_], abkFun_, sbkFun_] := sbkFun[ToString@i <> ToString@j];
ExportAmp2Tex[n_?NumberQ, abkFun_, sbkFun_] := ToString@n;
ExportAmp2Tex[l_List, abkFun_, sbkFun_] := ExportAmp2Tex[#, abkFun, sbkFun]& /@ l;
ExportAmp2Tex[expr_Times, abkFun_, sbkFun_] := StringJoin@ExportAmp2Tex[Prod2List[expr], abkFun, sbkFun];
ExportAmp2Tex[expr_Plus, abkFun_, sbkFun_] := ExportAmp2Tex[Sum2List@expr, abkFun, sbkFun] // StringRiffle[#, "+"]&;
ExportAmp2Tex[expr_] := ExportAmp2Tex[expr, defaultAbkFun, defaultSbkFun];


(*Label Section*)
(*Lorentz Label start with "LI"*)
Number2Greek = If[#2 > 0, #1 <> ToString[#2], #1] &[Alphabet["Greek"][[Mod[11 + #, 24]]], Quotient[#, 24]] &;
(*===TODO===remove letters not used for label ===TODO===*)
numberLorentzIndex[x_] := StringSplit[x, "LI"] // First // ToExpression;
Index2Greek[x_] := x // ToString // numberLorentzIndex // Number2Greek // TeXForm // ToString[#]&;

ExportWelyOp2Tex[weylop_Plus] := (ExportSpinorObj2Tex@#)& /@ Sum2List[weylop] // StringRiffle[#, "+"]&;
ExportWelyOp2Tex[weylop_] := ExportSpinorObj2Tex@weylop;
ExportSpinorObj2Tex[SpinorOpList_] := Module[{
  opList, dic, curObj, outList, trList
},
  dic = {
    {n_Integer, 1 / 2, i_} :> "\\psi^+_" <> ToString[n],
    {n_Integer, -(1 / 2), i_} :> "\\psi^-_" <> ToString[n],
    {"D", n_, i_} :> "D_{" <> Index2Greek[i] <> "}",
    {"A", n_, i_} :> "A_{" <> ToString[n] <> " " <> Index2Greek[i] <> "}",
    {"\[Sigma]", LI_, S1_, S2_} :> "\\gamma^{" <> Index2Greek[LI] <> "}",
    {"\[Sigma]Bar", LI_, S1_, S2_} :> "\\gamma^{" <> Index2Greek[LI] <> "}",
    {"\[Sigma]", L1_, L2_, S1_, S2_} :> "\\frac{i}{2} (\\gamma^{" <> Index2Greek[L1] <> "} \\gamma^{" <> Index2Greek[L2] <> "} - \\gamma^{" <> Index2Greek[L2] <> "} \\gamma^{" <> Index2Greek[L1] <> "})",
    {"\[Sigma]Bar", L1_, L2_, S1_, S2_} :> "\\frac{i}{2} (\\gamma^{" <> Index2Greek[L2] <> "} \\gamma^{" <> Index2Greek[L1] <> "} - \\gamma^{" <> Index2Greek[L1] <> "} \\gamma^{" <> Index2Greek[L2] <> "})",
    {"F+", n_, i_, j_} :> "F^+_{" <> ToString[n] <> " " <> Index2Greek[i] <> " " <> Index2Greek[j] <> "}",
    {"F-", n_, i_, j_} :> "F^-_{" <> ToString[n] <> " " <> Index2Greek[i] <> " " <> Index2Greek[j] <> "}",
    {"\[Phi]", i_} :> "\\phi_" <> ToString[i]
  };
  outList = {};
  curObj = SpinorOpList[[1]];
  opList = Drop[SpinorOpList, 1];
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

(*Example: "\\begin{array}{c}\n \t" <>
     StringRiffle[#, "\\\\ \n\t"] &@(# /. TraditionalForm[x_] -> x &@
      ExportWelyOp2Tex /@ (Amp2WeylOp[4]@# & /@
       ConstructIndependentBasis[{1, 1, 0, 0},
        6, {{1, 2}, {3, 4}}])) <> "\n\\end{array}" // TraditionalForm*)
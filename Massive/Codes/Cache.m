(*The file is designed to realize reflation and cache*)
LogPri["Cache Loaded"];

PatternRuleNames[funRule_HoldPattern :> ___] :=
    Cases[funRule, Verbatim[Pattern][name_, _] :> (HoldForm[name]), -1,
      Heads -> True];
HaveUnNamedOptionPatternQ[funRule_HoldPattern :> ___] :=
    MatchQ[funRule,
      Verbatim[HoldPattern][_[___, Verbatim[OptionsPattern][]]]];
HaveNamedOptionPatternQ[funRule_HoldPattern :> ___] :=
    If[MatchQ[funRule,
      Verbatim[HoldPattern][_[___,
        Verbatim[Pattern][_, Verbatim[OptionsPattern][]]]]],
      PatternRuleNames[funRule :> Null][[-1]], False];

CopyFunctionDesign[funFrom_Symbol, funTo_Symbol] :=
    (
      (*      Assert[!MemberQ[Attributes[funFrom], Protected]];*)
      (*      Assert[{}*)
      (*          === Attributes[funTo]*)
      (*          === Options@funTo*)
      (*          === DownValues@funTo*)
      (*          === UpValues@funTo*)
      (*      ];*)
      Options@funTo = Options@funFrom;
      DownValues@funTo = DownValues@funFrom /. funFrom -> funTo;
      Attributes[funTo] = Attributes[funFrom];
      UpValues@funTo = UpValues@funFrom /. funFrom -> funTo;
      LogPri["Copy def from ", SymbolName@funFrom , " to ", SymbolName@funTo];
    );

If[!ListQ[$MassiveCachedFunction],
  $MassiveCachedFunction = {};
];

If[!ListQ[shiftedDefinition],
  shiftedDefinition = {};
];

ClearCache[] := (
  If[ListQ[shiftedDefinition],
    ClearCache /@ Evaluate /@ Symbol /@ StringTake[#, {StringLength@"Shifted" + 1, -1}]&
        /@ SymbolName /@ shiftedDefinition
  ];
  shiftedDefinition = {};
);
ClearCache[functionName_Symbol] := (
  ClearAll[Evaluate@functionName];
  CopyFunctionDesign[Symbol["Shifted" <> SymbolName[functionName]] , functionName];
  ClearAll[Evaluate@Symbol["Shifted" <> SymbolName[functionName]]];
  shiftedDefinition = DeleteCases[shiftedDefinition, Symbol["Shifted" <> SymbolName[functionName]]];
  LogPri["Clear Cached ", SymbolName@functionName];
);

CacheFunction[funList_List] /; And@@(Head@# === Symbol& /@ funList) := CacheFunction /@ funList;
CacheFunction[functionName_Symbol] := (
  CopyFunctionDesign[functionName, Symbol["Shifted" <> SymbolName[functionName]]];
  DownValues@functionName = {HoldPattern[functionName[para___]] :>
      (functionName[para] = Symbol["Shifted" <> SymbolName[functionName]][para])};
  AppendTo[shiftedDefinition, Symbol["Shifted" <> SymbolName[functionName]]];
  LogPri["Cached ", SymbolName@functionName];
);

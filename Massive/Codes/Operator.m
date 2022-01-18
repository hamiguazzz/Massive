(* ::Package:: *)
LogPri["Operator Loaded"];

Amp2BrasList[amp_] :=
    Module[ {factor, totalFactor = 1, bras},
      {factor, bras} = GroupBy[Prod2List@amp, MatchQ[_sb | _ab]][#]& /@ {False, True};
      If[!ListQ[factor], factor = {}];
      totalFactor = Times @@ factor;
      {bras, factor} = # /. Times[c_, b_ab | b_sb] :> (Sow[c];b)& /@ bras // Reap;
      totalFactor *= Times @@ Flatten @ factor;
      Return[{totalFactor, bras}]
    ];
BreakBracket[bra_] := {bra[[0]], bra[[1]], bra[[2]]};
(*Free sb = spin*2-antispinor*)
(*Free ab = antispinor*)
Amp2MetaInfo[amp_, np_Integer] := Module[{rule, braList , particleList, massiveParticleList, spins, antispinors},
  braList = BreakBracket /@ Amp2BrasList[amp][[2]];
  rule[type_, ind_] := {type, ind, _} | {type, _, ind};
  particleList = Table[{Count[braList, rule[sb, i]] , Count[braList, rule[ab, i]]}, {i, np}];
  massiveParticleList = Table[Count[braList, rule[sb, i]], {i, Range[2 * np, np + 1, -1]}];
  {spins, antispinors} = Transpose@MapThread[{#2 + (#1[[2]] - #1[[1]]), #1[[2]] - #1[[1]]}&, {particleList, massiveParticleList}];
  If[Count[spins, Negative] + Count[antispinors, Negative] > 0, Return[Null]];
  Return[{spins / 2, antispinors}];
];

FindPsiChain[amp_, np_Integer] := Module[
  {
    FindNextHeadTarget, ExistNextTargetQ, ConsumeNextTarget, ExtendChainStep,
    FactorMatchQ,
    leftExternal,
    spins, antispinors,
    target, targetParticle = Null, targetBraType = Null,
    targetParticle2 = Null, targetBraType2 = Null,
    circleHead,
    chains = {},
    bras, factor, sigmas
  },
  {factor, bras} = Amp2BrasList[amp];
  If[Length@bras < 2,
    Return[{factor, bras, {1}}]
  ];
  {spins, antispinors} = Amp2MetaInfo[amp, np];
  bras = BreakBracket /@ bras;
  FactorMatchQ[bra_, matchrule_] :=
      If[ MatchQ[bra, matchrule],
        True,
        If[ MatchQ[{bra[[1]], bra[[3]], bra[[2]]}, matchrule],
          Sow[-1];
          True,
          False
        ]
      ];
  (*left amount {{8, 7, 6, ...},{1, 2, 3, ...}}*)
  leftExternal = Transpose @ Table[{2 * spins[[i]] - antispinors[[i]], antispinors[[i]]}, {i, np}];
  (*Get head*)
  FindNextHeadTarget[] := Block[{rule, externalIndex},
    While[True,
      externalIndex = FirstPosition[leftExternal[[1]], Except[0, _Integer], {-1}, 1][[1]];
      If[externalIndex != -1,
        leftExternal[[1]][[externalIndex]]--;
        targetBraType = sb;
        targetParticle = 2 * np + 1 - externalIndex;
        ,
        externalIndex = FirstPosition[leftExternal[[2]], Except[0, _Integer], {-1}, 1][[1]];
        If[externalIndex != -1,
          leftExternal[[2]][[externalIndex]]--;
          targetBraType = ab;
          targetParticle = externalIndex;
          ,
          targetBraType = targetParticle = Null;
          targetBraType2 = targetParticle2 = Null;
          Return[False];
        ];
      ];
      If[ExistNextTargetQ[targetBraType, targetParticle],
        chains ~ AppendTo ~ {targetBraType};
        Return[True];
      ]
    ];
  ];

  (*test whether exists next target bra, no side effect*)
  ExistNextTargetQ[targetBraTypeInner_, targetParticleInner_] := Block[{targetInner, rule, factorList},
    rule = {targetBraTypeInner, targetParticleInner, _};
    {targetInner, factorList} = SelectFirst[bras, FactorMatchQ[#, rule]&, Null] // Reap;
    Return[targetInner =!= Null];
  ];

  (*consume expected next target bra, change bras List and factor*)
  ConsumeNextTarget[targetBraTypeInner_, targetParticleInner_] := Block[{rule, factorList},
    rule = {targetBraTypeInner, targetParticleInner, _};
    {target, factorList} = SelectFirst[bras, FactorMatchQ[#, rule]&, Null] // Reap;
    If[target == Null, Return[False]];
    factor *= Times @@ Flatten @ factorList;
    bras = Drop[bras,
      FirstPosition[bras, target, Null, 1]
    ];
    Return[True];
  ];

  (*extend a head to tail*)
  ExtendChainStep[] :=
      If[ConsumeNextTarget[targetBraType, targetParticle],
        chains[[-1]] ~ AppendTo ~ targetParticle;
        targetBraType2 = targetBraType;
        targetBraType = Cases[{ab, sb}, Except[targetBraType2]][[1]];
        targetParticle = Cases[target, Except[targetBraType2 | targetParticle]][[1]];
        Return[True];
        ,
        chains[[-1]] ~ AppendTo ~ targetParticle;
        chains[[-1]] ~ AppendTo ~ targetBraType2;
        Return[False];
      ];

  (*All chain structure*)
  While[FindNextHeadTarget[],
    While[ExtendChainStep[]];
  ];

  While[Length@bras > 0,
    chains ~ AppendTo ~ {"circle"};
    targetBraType = bras[[1]][[1]];
    targetParticle = bras[[1]][[2]];
    circleHead = targetParticle;
    While[True,
      If[Length@bras == 0, Break[]];
      ExtendChainStep[];
      If[targetParticle == circleHead,
        Break[];
      ];
    ];
  ];

  (*Build sigma*)
  sigmas = Table[0, Length[chains]];
  Do[
    Switch[chains[[i]][[1]],
      ab, sigmas[[i]] = Length[chains[[i]]] - 4;,
      sb, sigmas[[i]] = -(Length[chains[[i]]] - 4);,
      "circle", sigmas[[i]] = (Length[chains[[i]]] - 1);,
      _, Throw[{chains[[i]][[1]], "Find Chain Error"}]
    ]
    , {i, Length[chains]}
  ];
  Return[{factor, chains, sigmas}]
];
FindPsiChain[np_Integer] := FindPsiChain[#, np]&;

(*For antispinor 1 (A case), use spin = -/+ 1 is fine in spins_List, \
as A is not determined from antispinor but from psiChain{ab,1,xx,8,sb} structure*)

ConstructOpInSpinIndex[amp_, np_Integer, spins_List] :=

    Module[
      {
        psiChain, chains, spInN, spinorIndex, SpinorObj, obj, index, findPtclSpin, opList, chain,
        DerPObj, DerMObj, FPObj, FMObj, APObj, AMObj, fPos, lorInN, lorIndex, lorIndexP,
        loopi, firstSpinorIndexN, firstSpinorObj, signFlipflop, testA,
        testAbSb
      },
      (*Make Psi chain*)
      psiChain = FindPsiChain[amp, np];
      (*Print["psiChian Found: ",psiChain];*)
      chains = psiChain[[2]];
      findPtclSpin[ptcl_] :=
          If[MemberQ[Range[np + 1, 2 * np], ptcl], spins[[-ptcl + 2 * np + 1]],
            spins[[ptcl]]];
      (*Make spinor index*)
      spInN = 1;
      spinorIndex[n_] := Symbol["SI" <> ToString[n]];
      lorInN = 1;
      lorIndex[n_] := Symbol["LI" <> ToString[n]];
      lorIndexP[n_] := Module[{}, lorInN++;Symbol["LI" <> ToString[n]]];
      (*SpinorObj is an object with 1 spinor index*)
      SpinorObj[obj_, sign_, index_, head___] := {obj, sign, index, head};
      obj[spinorObj_] := spinorObj[[1]];
      index[spinorObj_] := spinorObj[[3]];
      DerPObj[obj_, indexL_, indexR_] := {"D+", obj, indexL, indexR};
      DerMObj[obj_, indexL_, indexR_] := {"D-", obj, indexL, indexR};
      FPObj[obj_, indexL_, indexR_] := {"F+", obj, indexL, indexR};(*F+*)
      FMObj[obj_, indexL_, indexR_] := {"F-", obj, indexL, indexR};(*F-*)
      APObj[obj_, indexL_, indexR_] := {"A+", obj, indexL, indexR};
      AMObj[obj_, indexL_, indexR_] := {"A-", obj, indexL, indexR};(*A+ for >[ and A- for ]<*)
      (*make op List with D and spinorObj*)
      opList = {};
      Do[chain = chains[[i]];
      signFlipflop = If[psiChain[[3]][[i]] > 0, + 1, -1];
      testA == False;
      (*recored sigma or sigma bar*)
      If[ToString[chain[[1]]] == "circle", (*circle case*)
        chain = Drop[chain, 1];
        firstSpinorIndexN = spInN;
        firstSpinorObj = chain[[1]];
        (*spInN++;*)
        chain = Drop[chain, 1];
        While[Length[chain] != 0,
          If[signFlipflop == 1,
            AppendTo[opList, DerPObj[chain[[1]], spinorIndex[spInN], spinorIndex[spInN + 1]]],
            AppendTo[opList, DerMObj[chain[[1]], spinorIndex[spInN], spinorIndex[spInN + 1]]]];
          signFlipflop = -signFlipflop;
          spInN++;
          chain = Drop[chain, 1]
        ];
        If[signFlipflop == 1,
          AppendTo[opList, DerPObj[firstSpinorObj, spinorIndex[spInN], spinorIndex[firstSpinorIndexN]]],
          AppendTo[opList, DerMObj[firstSpinorObj, spinorIndex[spInN], spinorIndex[firstSpinorIndexN]]]];
        spInN++;
        , (*absb case*)
        testA = Evaluate[((ToString[chain[[1]]] != ToString[chain[[-1]]]) &&
            ((-chain[[2]] + 2 np + 1 == chain[[-2]]) || (chain[[2]] == -chain[[-2]] + 2 np + 1)))];
        testAbSb = If[(chain[[1]] // ToString) == "ab", -1, 1];
        chain = Drop[chain, 1];
        If[testA != False,
          firstSpinorIndexN = spInN,
          AppendTo[opList, SpinorObj[chain[[1]], If[findPtclSpin[chain[[1]]] == 1 || findPtclSpin[chain[[1]]] == -1,
            testAbSb, findPtclSpin[chain[[1]]]] , spinorIndex[spInN], 0]]
        ];
        While[(ToString[chain[[3]]] != ToString[ab]) && (ToString[chain[[3]]] != ToString[sb]),
          If[signFlipflop == 1,
            AppendTo[opList, DerPObj[chain[[2]], spinorIndex[spInN], spinorIndex[spInN + 1]]],
            AppendTo[opList, DerMObj[chain[[2]], spinorIndex[spInN], spinorIndex[spInN + 1]]]];
          signFlipflop = -signFlipflop;
          spInN++;
          chain = Drop[chain, 1]
        ];
        If[testA != False,
          If[signFlipflop == 1,
            AppendTo[opList, APObj[chain[[2]], spinorIndex[spInN], spinorIndex[firstSpinorIndexN]]],
            AppendTo[opList, AMObj[chain[[2]], spinorIndex[spInN], spinorIndex[firstSpinorIndexN]]]
          ];
          ,
          testAbSb = If[(chain[[-1]] // ToString) == "ab", -1, 1];
          AppendTo[opList, SpinorObj[chain[[2]], If[findPtclSpin[chain[[2]]] == 1 || findPtclSpin[chain[[2]]] == -1,
            testAbSb, findPtclSpin[chain[[2]]]], spinorIndex[spInN], 1]]];
        spInN++;
      ];
        , {i, Length[chains]}];
      (*Print["SpinorObj Done: ", opList];*)
      (*convert spin 1 spinObj to F and A*)
      Do[If[spins[[i]] == 1 || spins[[i]] == -1,
        fPos = Join[Position[opList, {i, 1, ___}, 1],
          Position[opList, {i, -1, ___}, 1],
          Position[opList, {-i + 2 np + 1, 1, ___}, 1],
          Position[opList, {-i + 2 np + 1, -1, ___}, 1]];
        If[OddQ[Length[fPos]], Throw[{opList, "Find F Error"}]];
        If[Length[fPos] != 0,
          If[Part[opList, fPos[[1]][[1]]][[2]] == Part[opList, fPos[[2]][[1]]][[2]],
            opList = Join[opList,
              {If[spins[[i]] == 1, FPObj, FMObj]
              [i, Part[opList, fPos[[1]][[1]]] // index, Part[opList, fPos[[2]][[1]]] // index]}];
            opList = Delete[opList, fPos]
            ,
            opList = Join[opList,
              {If[(Part[opList, fPos[[1]][[1]]][[-1]] == 1 && Part[opList, fPos[[1]][[1]]][[2]] == 1)
                  || (Part[opList, fPos[[1]][[1]]][[-1]] == -1 && Part[opList, fPos[[1]][[1]]][[2]] == 0),
                AMObj, APObj]
              [i, Part[opList, fPos[[1]][[1]]] // index, Part[opList, fPos[[2]][[1]]] // index]}];
            opList = Delete[opList, fPos]

          ]]
      ]
        , {i, Length[spins]}];
      (*convert F and D to {F sigma} and {D sigma}*)

      opList = opList /. {
        {n_Integer, 1 / 2, i_, _} :> {n, 1 / 2, i},
        {n_Integer, -1 / 2, i_, _} :> {n, -1 / 2, i},
        {"D+", i_, iL_, iR_} :> {{"D", i, lorIndex[lorInN]}, {"\[Sigma]", lorIndexP[lorInN], iL, iR}},
        {"D-", i_, iL_, iR_} :> {{"D", i, lorIndex[lorInN]}, {"\[Sigma]Bar", lorIndexP[lorInN], iL, iR}},
        {"A+", i_, iL_, iR_} :> {{"A", i, lorIndex[lorInN]}, {"\[Sigma]", lorIndexP[lorInN], iL, iR}},
        {"A-", i_, iL_, iR_} :> {{"A", i, lorIndex[lorInN]}, {"\[Sigma]Bar", lorIndexP[lorInN], iL, iR}},
        {"F+", i_, iL_, iR_} :> {{"F+", i, lorIndex[lorInN], lorIndex[lorInN + 1]},
          {"\[Sigma]Bar", lorIndexP[lorInN], lorIndexP[lorInN], iL, iR}},
        {"F-", i_, iL_, iR_} :> {{"F-", i, lorIndex[lorInN], lorIndex[lorInN + 1]},
          {"\[Sigma]", lorIndexP[lorInN], lorIndexP[lorInN], iL, iR}}};
      (*===TODO===check the F+F- sigma convention===TODO===*)
      (*flatten {X sigma}*)
      loopi = 1;
      While[loopi != Length[opList] + 1,
        If[Depth[opList[[loopi]]] == 3,
          opList = Join[opList, opList[[loopi]]];
          opList = Delete[opList, loopi];
          loopi = loopi - 1
        ];
        loopi++;
      ];
      Do[
        If[spins[[i]] == 0,
          AppendTo[opList, {"\[Phi]", i}]
        ],
        {i, Length[spins]}];
      (*Print["Op Done: ",opList];*)
      Append[opList, psiChain[[1]]]
    ];

ConstructOpInSpinIndex[amp_, np_Integer] :=
    ConstructOpInSpinIndex[amp, np, #[[1]] * (#[[2]] /. {1 -> -1, 2 -> -1, 0 -> 1}) &[Amp2MetaInfo[amp, np]]];


(*spinorObjOpForm is used to prevew spinorObj only*)
spinorObjOpForm[x_] := Module[{dic},
  dic = {
    {n_Integer, 1 / 2, i_} :> Subscript[Subscript[SuperPlus["\[Psi]"], n], i],
    {n_Integer, -1 / 2, i_} :> Subscript[Subscript[SuperMinus["\[Psi]"], n], i],
    {"D", n_, i_} :> Subscript[Subscript["D", n], i],
    {"A", n_, i_} :> Subscript[Subscript["A", n], i],
    {"\[Sigma]", LI_, S1_, S2_} :> Subscript[Superscript["\[Sigma]", LI], List[S1, S2]],
    {"\[Sigma]Bar", LI_, S1_, S2_} :> Subscript[Superscript[OverBar["\[Sigma]"], LI], List[S1, S2]],
    {"\[Sigma]", L1_, L2_, S1_, S2_} :> Subscript[Superscript["\[Sigma]", {L1, L2}], List[S1, S2]],
    {"\[Sigma]Bar", L1_, L2_, S1_, S2_} :> Subscript[Superscript[OverBar["\[Sigma]"], {L1, L2}], List[S1, S2]],
    {"F+", n_, i_, j_} :> Subscript[Subscript[SuperPlus["F"], n], {i, j}],
    {"F-", n_, i_, j_} :> Subscript[Subscript[SuperMinus["F"], n], {i, j}],
    {"\[Phi]", i_} :> Subscript["\[Phi]", i],
    {"Tr"} -> "Tr"};
  (x/.dic)];


(*WeylOp2spinorObj[op_] := Module[{oplist = Prod2List[op], dict, IndexSymbol2Int, fun},*)
(*  dict = {*)
(*    Subscript[Subscript[SuperPlus["\[Psi]"], n_], i_] :> {n, 1 / 2, i},*)
(*    Subscript[Subscript[SuperMinus["\[Psi]"], n_], i_] :> {n, -1 / 2, i},*)
(*    Subscript[Subscript["D", n_], i_] :> {"D", n, i},*)
(*    Subscript[Subscript["A", n_], i_] :> {"A", n, i},*)
(*    Subscript[Superscript["\[Sigma]", LI_], List[S1_, S2_]] :> {"\[Sigma]", LI, S1, S2},*)
(*    Subscript[Superscript[OverBar["\[Sigma]"], LI_], List[S1_, S2_]] :> {"\[Sigma]Bar", LI, S1, S2},*)
(*    Subscript[Superscript["\[Sigma]", {L1_, L2_}], List[S1_, S2_]] :> {"\[Sigma]", L1, L2, S1, S2},*)
(*    Subscript[Superscript[OverBar["\[Sigma]"], {L1_, L2_}], List[S1_, S2_]] :> {"\[Sigma]Bar", L1, L2, S1, S2},*)
(*    Subscript[Subscript[SuperPlus["F"], n_], {i_, j_}] :> {"F+", n, i, j},*)
(*    Subscript[Subscript[SuperMinus["F"], n_], {i_, j_}] :> {"F-", n, i, j},*)
(*    Subscript["\[Phi]", i_] :> {"\[Phi]", i},*)
(*    "Tr" -> {"Tr"}*)
(*  };*)
(*  IndexSymbol2Int[head_String, sym_List] := IndexSymbol2Int[head] /@ sym;*)
(*  IndexSymbol2Int[head_String] := IndexSymbol2Int[head, #]&;*)
(*  IndexSymbol2Int[head_String, sym_] :=*)
(*      If[StringMatchQ[ToString@sym, head ~~ _],*)
(*        ToExpression@StringReplace[ToString@sym, head ~~ i_ -> i],*)
(*        sym*)
(*      ];*)
(*  fun = Flatten @ IndexSymbol2Int["SI"] @ IndexSymbol2Int["LI"] @ (# /. dict)&;*)
(*  (fun /@ oplist) // Return;*)
(*];*)

(*Example: Dot@@(ConstructOpInSpinIndex[#,5]/.spinorObj2Op)&/@ConstructAmp[{1,1,1/2,1/2,0},10,antispinor->{0,1,0,1,0}]*)
ClearAll[sortSpinorIndex];
Options[sortSpinorIndex] = {factor -> False, traceLabel -> True};
sortSpinorIndex[opListIn_, np_Integer, OptionsPattern[]] :=
    Module[
      {
        opList, outList, DList, sigmaSwitch, fac, loopi, loopj,
        spinorIndex, spinorIndexN, SIList, curObj, fermionCainEnd,
        circleEnd
      },
      sigmaSwitch[sigmaObj_] := If[Length[sigmaObj] == 4,
        If[First[sigmaObj] == "\[Sigma]",
          {"\[Sigma]Bar", sigmaObj[[2]], sigmaObj[[4]], sigmaObj[[3]]},
          {"\[Sigma]", sigmaObj[[2]], sigmaObj[[4]], sigmaObj[[3]]}],
        If[First[sigmaObj] == "\[Sigma]",
          {"\[Sigma]Bar", sigmaObj[[2]], sigmaObj[[3]], sigmaObj[[5]], sigmaObj[[4]]},
          {"\[Sigma]", sigmaObj[[2]], sigmaObj[[3]], sigmaObj[[5]], sigmaObj[[4]]}]];(*flip sigma_ab to sigma bar_ba*)

      fac = opListIn[[-1]];
      opList = Drop[opListIn, -1];
      outList = {};
      DList = {};
      loopi = 1;
      spinorIndexN[n_] := Module[{}, Delete[SIList, Position[n]];Symbol["SI" <> ToString[n]]];
      spinorIndex[n_] := Symbol["SI" <> ToString[n]];
      While[loopi <
          Length[opList] + 1, (*add all object without Spinor Index except D*)
        If[opList[[loopi]][[1]] == "\[Phi]" || opList[[loopi]][[1]] == "A" ||
            StringMatchQ[ToString[opList[[loopi]][[1]]], "F*"],
          AppendTo[outList, opList[[loopi]]];
          opList = Delete[opList, loopi];
          loopi--
        ];
        loopi++
      ];
      loopi = 1;
      While[loopi < Length[opList] + 1, (*add D to DList*)
        If[opList[[loopi]][[1]] == "D",
          AppendTo[DList, opList[[loopi]]];
          opList = Delete[opList, loopi];
          loopi--
        ];
        loopi++
      ];
      loopi = 1;
      (*Now add object with spinor index,
      there are two case: {fermion sigmas fermion} and circle (all two index)*)
      While[loopi < Length[opList] + 1,
        curObj = opList[[loopi]];
        If[Length[curObj] == 3, (*femrion end case*)
          AppendTo[outList, curObj];
          opList = Delete[opList, loopi];
          loopj = 1;
          While[loopj < Length[opList] + 1,
            If[opList[[loopj]][[-2]] == outList[[-1]][[-1]],
              AppendTo[outList, opList[[loopj]]];
              opList = Delete[opList, loopj];
              loopj = 1;
              Goto[fermionCainEnd];
            ];
            If[opList[[loopj]][[-1]] == outList[[-1]][[-1]],
              If[Length[opList[[loopj]]] != 3,
                AppendTo[outList, sigmaSwitch[opList[[loopj]]]];
                opList = Delete[opList, loopj];
                loopj = 1;
                Goto[fermionCainEnd],
                (*ending fermion*)
                AppendTo[outList, opList[[loopj]]];
                opList = Delete[opList, loopj];
                Break[];
              ];
            ];
            loopj++;
            Label[fermionCainEnd]
          ];
        ];
        loopi++
      ];
      loopi = 1;
      If[Length[opList] != 0, (*circle case*)

        While[Length[opList] != 0,
          curObj = opList[[loopi]];
          If[OptionValue@traceLabel === True,
            AppendTo[outList, {"Tr"}]];
          AppendTo[outList, curObj];
          opList = Delete[opList, loopi];
          loopj = 1;
          While[loopj < Length[opList] + 1,
            If[opList[[loopj]][[-2]] == outList[[-1]][[-1]],
              AppendTo[outList, opList[[loopj]]];
              opList = Delete[opList, loopj];
              loopj = 1;
              Goto[circleEnd]
            ];
            If[opList[[loopj]][[-1]] == outList[[-1]][[-1]],
              AppendTo[outList, sigmaSwitch[opList[[loopj]]]];
              opList = Delete[opList, loopj];
              loopj = 1;
              Goto[circleEnd]
            ];
            loopj++;
            Label[circleEnd]
          ]
        ]
      ];
      (*Put D into Right Place*)
      Do[curObj = DList[[i]];
      Do[
        If[curObj[[2]] == outList[[j]][[If[IntegerQ[outList[[j]][[1]]], 1, 2]]] ||
            (-curObj[[2]] + 2 np + 1) == outList[[j]][[If[IntegerQ[outList[[j]][[1]]], 1, 2]]],
          outList = Insert[outList, curObj, j];
          Break[];
        ]
        , {j, Length[outList]}]
        , {i, Length[DList]}];
      ;
      (*factor seems not useful*)
      (*factors are used relatively in amp polynomials *)
      If[OptionValue@factor, AppendTo[outList, fac]];
      Return[outList];
    ];
Options[ConstructOpInSpinIndexSort] = {factor -> False, traceLabel -> True};
ConstructOpInSpinIndexSort[amp_, np_Integer, opts : OptionsPattern[]] :=
    If[OptionValue@traceLabel == True,
      sortSpinorIndex[ConstructOpInSpinIndex[amp, np], np, FilterRules[{opts}, Options[sortSpinorIndex]]]];

(*Example: (ConstructOpInSpinIndexSort[#,5]/.spinorObj2Op)&/@{ConstructAmp[{1,1,1/2,1/2,0},10,antispinor->{0,1,0,1,0}][[8]]}*)

SpinorObj2FeynCalField[opListIn_] :=
    Module[
      {
        opList, dic, curObj, outList, trList, corIndex, corInN
      },
      corInN = 1;
      corIndex[n_] := Module[{}, corInN++; Symbol["COR" <> ToString[n]]];
      dic = {
        {n_Integer, 1 / 2, i_} :> QuantumField[AntiQuarkField],
        {n_Integer, -(1 / 2), i_} :> QuantumField[QuarkField],
        {"D", n_, i_} :> CovariantD[i],
        {"A", n_, i_} :> QuantumField[GaugeField, {i}, {corIndex[corInN]}], (*CovariantD[i]*)
        {"\[Sigma]", LI_, S1_, S2_} :> GA[LI],
        {"\[Sigma]Bar", LI_, S1_, S2_} :> GA[LI],
        {"\[Sigma]", L1_, L2_, S1_, S2_} :> 1 / 2 I (GA[L1].GA[L2] - GA[L2].GA[L1]),
        {"\[Sigma]Bar", L1_, L2_, S1_, S2_} :> 1 / 2 I (GA[L1].GA[L2] - GA[L2].GA[L1]),
        {"F+", n_, i_, j_} :> FieldStrength[i, j, corIndex[corInN]], (*FieldStrength[i,j,c]+LC[i,j,k,l].FieldStrength[k,l,c]*)
        {"F-", n_, i_, j_} :> FieldStrength[i, j, corIndex[corInN]],
        {"\[Phi]", i_} :> QuantumField[\[Phi]]}; (*===TODO===Need to change for id ptcl===TODO===*)
      outList = {};
      curObj = opListIn[[1]];
      opList = Drop[opListIn, 1];
      While[curObj != {"Tr"},
        AppendTo[outList, curObj /. dic];
        If[Length[opList] == 0, Return[outList]];
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
        AppendTo[outList, Tr[Dot @@ trList]]
      ];
      outList
    ];
(*Example: (Dot @@ ((ConstructOpInSpinIndexSort[#, 5, traceLabel -> True] & /@
           {ConstructAmp[{1, 1, 1/2, 1/2, 0}, 10, antispinor -> {0, 1, 0, 1, 0}][[8]]})[[1]]
           // SpinorObj2FeynCalField)) // TraditionalForm*)

Options[Amp2WeylOp] = {factor -> False, traceLabel -> True};
Amp2WeylOp[amp_, np_Integer, opts : OptionsPattern[]] :=
        (ConstructOpInSpinIndexSort[amp, np, FilterRules[{opts}, Options@ConstructOpInSpinIndexSort]]);
Amp2WeylOp[amps_Plus, np_Integer, opts : OptionsPattern[]] := Amp2WeylOp[np, opts] /@ Sum2List[amps] // Total;
Amp2WeylOp[np_Integer, opts : OptionsPattern[]] := Amp2WeylOp[#, np, opts]&;
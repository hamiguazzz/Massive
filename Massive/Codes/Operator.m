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

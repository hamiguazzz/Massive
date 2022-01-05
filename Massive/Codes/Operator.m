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


(*For antispinor 1 (A case), use spin = -/+ 1 is fine in spins_List, as A is not determined from antispinor but from psiChain{ab,1,xx,8,sb} structure*)
ConstructOpInSpinIndex[amp_,np_Integer,spins_List]:=
Module[{psiChain,chains,spInN,spinorIndex,SpinorObj,obj,index,findPtclSpin,opList,chain,curSign,
DerPObj,DerMObj,FPObj,FMObj,APObj,AMObj,LI,RI,fPos,lorInN,lorIndex,lorIndexP,loopi,firstSpinorIndexN,signFlipflop,testA},
(*Make Psi chain*)
psiChain=FindPsiChain[amp,np];
Print["psiChian Found: ",psiChain];
chains=psiChain[[2]];
findPtclSpin[ptcl_]:=If[MemberQ[Range[np+1,2np],ptcl],spins[[-ptcl+2np+1]],spins[[ptcl]]];(*4pt*)
(*Make spinor index*)
spInN=1;
spinorIndex[n_]:=Symbol["SI"<>ToString[n]];
lorInN=1;
lorIndex[n_]:=Symbol["LI"<>ToString[n]];
lorIndexP[n_]:=Module[{},lorInN++;Symbol["LI"<>ToString[n]]];
(*SpinorObj is an object with 1 spinor index*)
SpinorObj[obj_,sign_,index_]:={obj,sign,index};
obj[spinorObj_]:=spinorObj[[1]];
index[spinorObj_]:=spinorObj[[3]];
DerPObj[obj_,indexL_,indexR_]:={"D+",obj,indexL,indexR};
DerMObj[obj_,indexL_,indexR_]:={"D-",obj,indexL,indexR};
FPObj[obj_,indexL_,indexR_]:={"F+",obj,indexL,indexR};(*F+*)
FMObj[obj_,indexL_,indexR_]:={"F-",obj,indexL,indexR};(*F-*)
APObj[obj_,indexL_,indexR_]:={"A+",obj,indexL,indexR};
AMObj[obj_,indexL_,indexR_]:={"A-",obj,indexL,indexR};(*A+ for >[ and A- for ]<*)
(*make op List with D and spinorObj*)
opList={};
Do[chain=chains[[i]];
signFlipflop=If[psiChain[[3]][[i]]>0,+1,-1];
testA==False;
(*recored sigma or sigma bar*)
If[ToString[chain[[1]]]=="circle",(*circle case*)
chain=Drop[chain,1];
firstSpinorIndexN=spInN;
spInN++;
chain=Drop[chain,1];
While[Length[chain]!=1,
If[signFlipflop==1,
AppendTo[opList,DerPObj[chain[[1]],spinorIndex[spInN],spinorIndex[spInN+1]]],
AppendTo[opList,DerMObj[chain[[1]],spinorIndex[spInN],spinorIndex[spInN+1]]]];
signFlipflop=-signFlipflop;
spInN++;
chain=Drop[chain,1]
];
If[signFlipflop==1,
AppendTo[opList,DerPObj[chain[[1]],spinorIndex[spInN],spinorIndex[firstSpinorIndexN]]],
AppendTo[opList,DerMObj[chain[[1]],spinorIndex[spInN],spinorIndex[firstSpinorIndexN]]]];
spInN++;
,(*absb case*)
testA=Evaluate[((ToString[chain[[1]]]!=ToString[chain[[-1]]])\[And]((-chain[[2]]+2np+1==chain[[-2]])\[Or](chain[[2]]==-chain[[-2]]+2np+1)))];
chain=Drop[chain,1];
If[testA!=False,
firstSpinorIndexN=spInN,
AppendTo[opList,SpinorObj[chain[[1]],findPtclSpin[chain[[1]]],spinorIndex[spInN]]]
];
While[(ToString[chain[[3]]]!=ToString[ab])\[And](ToString[chain[[3]]]!=ToString[sb]),
If[signFlipflop==1,
AppendTo[opList,DerPObj[chain[[2]],spinorIndex[spInN],spinorIndex[spInN+1]]],
AppendTo[opList,DerMObj[chain[[2]],spinorIndex[spInN],spinorIndex[spInN+1]]]];
signFlipflop=-signFlipflop;
spInN++;
chain=Drop[chain,1]
];
If[testA!=False,
If[signFlipflop==1,
AppendTo[opList,APObj[chain[[2]],spinorIndex[spInN],spinorIndex[firstSpinorIndexN]]],
AppendTo[opList,AMObj[chain[[2]],spinorIndex[spInN],spinorIndex[firstSpinorIndexN]]]
];
,
AppendTo[opList,SpinorObj[chain[[2]],findPtclSpin[chain[[2]]],spinorIndex[spInN]]]];
spInN++;
];
,{i,Length[chains]}];
(*Print["SpinorObj Done: ",opList];*)
(*convert spin 1 spinObj to F*)
Do[If[spins[[i]]==1\[Or]spins[[i]]==-1,
fPos=Join[Position[opList,{i,spins[[i]],_},1],Position[opList,{-i+2np+1,spins[[i]],_},1]];
If[Length[fPos]!=2\[And]Length[fPos]!=0,Throw[{opList, "Find F Error"}]];
If[Length[fPos]!=0,
opList=Join[opList,
{If[spins[[i]]==1,FPObj,FMObj][i,Part[opList,fPos[[1]][[1]]]//index,Part[opList,fPos[[2]][[1]]]//index]}];
opList=Delete[opList,fPos]]
]
,{i,Length[spins]}];
(*convert F and D to {F sigma} and {D sigma}*)
opList=opList/.{{"D+",i_,iL_,iR_}:>{{"D",i,lorIndex[lorInN]},{"\[Sigma]",lorIndexP[lorInN],iL,iR}},
{"D-",i_,iL_,iR_}:>{{"D",i,lorIndex[lorInN]},{"\[Sigma]Bar",lorIndexP[lorInN],iL,iR}},
{"A+",i_,iL_,iR_}:>{{"A",i,lorIndex[lorInN]},{"\[Sigma]",lorIndexP[lorInN],iL,iR}},
{"A-",i_,iL_,iR_}:>{{"A",i,lorIndex[lorInN]},{"\[Sigma]Bar",lorIndexP[lorInN],iL,iR}},
{"F+",i_,iL_,iR_}:>{{"F+",i,lorIndex[lorInN],lorIndex[lorInN+1]},{"\[Sigma]",lorIndexP[lorInN],lorIndexP[lorInN],iL,iR}},
{"F-",i_,iL_,iR_}:>{{"F-",i,lorIndex[lorInN],lorIndex[lorInN+1]},{"\[Sigma]Bar",lorIndexP[lorInN],lorIndexP[lorInN],iL,iR}}};
(*flatten {X sigma}*)
loopi=1;
While[loopi!=Length[opList]+1,
If[Depth[opList[[loopi]]]==3,
opList=Join[opList,opList[[loopi]]];
opList=Delete[opList,loopi];
loopi=loopi-1
];
loopi++;
];
Do[
If[spins[[i]] == 0,
AppendTo[opList,{"\[Phi]",i}]
],
{i,Length[spins]}];
(*Print["Op Done: ",opList];*)
Append[opList,psiChain[[1]]]
];
ConstructOpInSpinIndex[amp_,np_Integer]:=ConstructOpInSpinIndex[amp,np,#[[1]]*(#[[2]]/.{1->-1,2->-1,0->1})&[Amp2MetaInfo[amp,np]]];
spinorObj2Op={
{n_Integer,1/2,i_}:>\!\(\*
TagBox[
StyleBox[
RowBox[{"Subscript", "[", 
RowBox[{
RowBox[{"Subscript", "[", 
RowBox[{
RowBox[{"SuperPlus", "[", "\"\<\\[Psi]\>\"", "]"}], ",", "n"}], "]"}], ",", "i"}], "]"}],
ShowSpecialCharacters->False,
ShowStringCharacters->True,
NumberMarks->True],
FullForm]\),
{n_Integer,-1/2,i_}:>\!\(\*
TagBox[
StyleBox[
RowBox[{"Subscript", "[", 
RowBox[{
RowBox[{"Subscript", "[", 
RowBox[{
RowBox[{"SuperMinus", "[", "\"\<\\[Psi]\>\"", "]"}], ",", "n"}], "]"}], ",", "i"}], "]"}],
ShowSpecialCharacters->False,
ShowStringCharacters->True,
NumberMarks->True],
FullForm]\),
{"D",n_,i_}:>\!\(\*
TagBox[
StyleBox[
RowBox[{"Subscript", "[", 
RowBox[{
RowBox[{"Subscript", "[", 
RowBox[{"\"\<D\>\"", ",", "n"}], "]"}], ",", "i"}], "]"}],
ShowSpecialCharacters->False,
ShowStringCharacters->True,
NumberMarks->True],
FullForm]\),
{"A",n_,i_}:>\!\(\*
TagBox[
StyleBox[
RowBox[{"Subscript", "[", 
RowBox[{
RowBox[{"Subscript", "[", 
RowBox[{"\"\<A\>\"", ",", "n"}], "]"}], ",", "i"}], "]"}],
ShowSpecialCharacters->False,
ShowStringCharacters->True,
NumberMarks->True],
FullForm]\),
{"\[Sigma]",LI_,S1_,S2_}:>\!\(\*
TagBox[
StyleBox[
RowBox[{"Subscript", "[", 
RowBox[{
RowBox[{"Superscript", "[", 
RowBox[{"\"\<\\[Sigma]\>\"", ",", "LI"}], "]"}], ",", 
RowBox[{"List", "[", 
RowBox[{"S1", ",", "S2"}], "]"}]}], "]"}],
ShowSpecialCharacters->False,
ShowStringCharacters->True,
NumberMarks->True],
FullForm]\),
{"\[Sigma]Bar",LI_,S1_,S2_}:>\!\(\*
TagBox[
StyleBox[
RowBox[{"Subscript", "[", 
RowBox[{
RowBox[{"Superscript", "[", 
RowBox[{
RowBox[{"OverBar", "[", "\"\<\\[Sigma]\>\"", "]"}], ",", "LI"}], "]"}], ",", 
RowBox[{"List", "[", 
RowBox[{"S1", ",", "S2"}], "]"}]}], "]"}],
ShowSpecialCharacters->False,
ShowStringCharacters->True,
NumberMarks->True],
FullForm]\),
{"\[Sigma]",L1_,L2_,S1_,S2_}:>\!\(\*
TagBox[
StyleBox[
RowBox[{"Subscript", "[", 
RowBox[{
RowBox[{"Superscript", "[", 
RowBox[{"\"\<\\[Sigma]\>\"", ",", 
RowBox[{"{", 
RowBox[{"L1", ",", "L2"}], "}"}]}], "]"}], ",", 
RowBox[{"List", "[", 
RowBox[{"S1", ",", "S2"}], "]"}]}], "]"}],
ShowSpecialCharacters->False,
ShowStringCharacters->True,
NumberMarks->True],
FullForm]\),
{"\[Sigma]Bar",L1_,L2_,S1_,S2_}:>\!\(\*
TagBox[
StyleBox[
RowBox[{"Subscript", "[", 
RowBox[{
RowBox[{"Superscript", "[", 
RowBox[{
RowBox[{"OverBar", "[", "\"\<\\[Sigma]\>\"", "]"}], ",", 
RowBox[{"{", 
RowBox[{"L1", ",", "L2"}], "}"}]}], "]"}], ",", 
RowBox[{"List", "[", 
RowBox[{"S1", ",", "S2"}], "]"}]}], "]"}],
ShowSpecialCharacters->False,
ShowStringCharacters->True,
NumberMarks->True],
FullForm]\),
{"F+",n_,i_,j_}:>\!\(\*
TagBox[
StyleBox[
RowBox[{"Subscript", "[", 
RowBox[{
RowBox[{"Subscript", "[", 
RowBox[{
RowBox[{"SuperPlus", "[", "\"\<F\>\"", "]"}], ",", "n"}], "]"}], ",", 
RowBox[{"{", 
RowBox[{"i", ",", "j"}], "}"}]}], "]"}],
ShowSpecialCharacters->False,
ShowStringCharacters->True,
NumberMarks->True],
FullForm]\),
{"F-",n_,i_,j_}:>\!\(\*
TagBox[
StyleBox[
RowBox[{"Subscript", "[", 
RowBox[{
RowBox[{"Subscript", "[", 
RowBox[{
RowBox[{"SuperMinus", "[", "\"\<F\>\"", "]"}], ",", "n"}], "]"}], ",", 
RowBox[{"{", 
RowBox[{"i", ",", "j"}], "}"}]}], "]"}],
ShowSpecialCharacters->False,
ShowStringCharacters->True,
NumberMarks->True],
FullForm]\),
{"\[Phi]",i_}:>\!\(\*
TagBox[
StyleBox[
RowBox[{"Subscript", "[", 
RowBox[{"\"\<\\[Phi]\>\"", ",", "i"}], "]"}],
ShowSpecialCharacters->False,
ShowStringCharacters->True,
NumberMarks->True],
FullForm]\)};
(*Example: Dot@@(ConstructOpInSpinIndex[#,5]/.spinorObj2Op)&/@ConstructAmp[{1,1,1/2,1/2,0},10,antispinor->{0,1,0,1,0}]*)

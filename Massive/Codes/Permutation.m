(*
  The file should change
  input:({{1,3,A},{2,4,S})
  to
  output rule((1->3,3->1,2->4,4->2, .....)
  expr 1/4(1-x)(1+y)
  and give x,y matrix
*)
LogPri["Permutation Loaded"];

GetMassiveIdenticalRules;
GetIndependentPermutedOperatorDict;
GetTotalPermutedPolyDict;

(* ::Section:: *)
(*Step 1: separate particles*)
(*generate rules and reverse rules about transformation from outer indices like {2,3,5} to inner {1,2,3}*)

Outer2InnerMasslessIndexRules[identicalParticleList_List] := Module[
  {
    particleList, rules
  },
  If[Length@identicalParticleList < 2, Throw[{identicalParticleList, "no identical particle list error"}]];
  particleList =
      If[StringQ@identicalParticleList[[-1]], identicalParticleList[[;; -2]], identicalParticleList] // Sort;
  rules = MapThread[Rule, {particleList, Range[Length@particleList]}]
];

Inner2OuterMasslessIndexRules[identicalParticleList_List] := Module[
  {
    particleList, rules
  },
  If[Length@identicalParticleList < 2, Throw[{identicalParticleList, "no identical particle list error"}]];
  particleList =
      If[StringQ@identicalParticleList[[-1]], identicalParticleList[[;; -2]], identicalParticleList] // Sort;
  rules = MapThread[Rule, {Range[Length@particleList], particleList}]
];


(* ::Section:: *)
(*Step 2: generate cycles*)
(*Follow massless*)
(* ::Subsection:: *)
(* StandardYangTableaux:GenerateStandardTableaux*)
TransposeTableaux[tableaux_] := DeleteCases[Transpose[PadRight[#, Length[tableaux[[1]]], Null]& /@ tableaux], Null, -1];

InnerTransposePartition[partition_] := Module[
  {n1, n2, inverseP},
  If[partition === {}, Return[{}]];
  n1 = partition[[1]];
  n2 = Length[partition];
  inverseP = Count[partition, x_ /; x >= #]& /@ Range[n1];
  Return[inverseP];
];

(* Returns a Young tableaux with the entries filled with the maximum entry in each square, if the tableaux is to be standard *)
MaxIndex[partition_] := Module[
  {partitionT, result},
  partitionT = InnerTransposePartition[partition];
  result = Table[
    Total[partition] - Total[partition[[1 ;; i - 1]]] - Total[partitionT[[1 ;; j - 1]]] + (i - 1)(j - 1)
    , {i, Length[partition]}, {j, partition[[i]]}];
  result = Total[partition] + 1 - result;
  Return[result];
];

GenerateStandardTableaux[\[Lambda]_] := Module[
  {n, \[Lambda]T, canonicalTableaux, canonicalTableauxT, affectedByList, minIndTable, maxIndTable, result},
  If[\[Lambda] === {}, Return[{}]];

  n = Total[\[Lambda]];
  \[Lambda]T = InnerTransposePartition[\[Lambda]];
  canonicalTableaux = MapThread[Range, {Accumulate[\[Lambda]] - \[Lambda] + 1, Accumulate[\[Lambda]]}];
  canonicalTableauxT = TransposeTableaux[canonicalTableaux];

  affectedByList = ConstantArray[{}, n];

  Do[AppendTo[affectedByList[[canonicalTableaux[[i, j - 1]]]], canonicalTableaux[[i, j]]],
    {i, 1, Length[\[Lambda]]}, {j, 2, \[Lambda][[i]]}];
  Do[AppendTo[affectedByList[[canonicalTableauxT[[i, j - 1]]]], canonicalTableauxT[[i, j]]],
    {i, 1, Length[\[Lambda]T]}, {j, 2, \[Lambda]T[[i]]}];

  maxIndTable = Flatten[MaxIndex[\[Lambda]]];
  minIndTable = ConstantArray[1, n];

  result = GenerateStandardTableauxAux[ConstantArray[0, n], 1, affectedByList, minIndTable, maxIndTable];
  result = Transpose[MapThread[result[[All, #1 ;; #2]]&, {Accumulate[\[Lambda]] - \[Lambda] + 1, Accumulate[\[Lambda]]}]];

  Return[result];
];

(* Auxiliar function to GenerateStandardTableaux *)
GenerateStandardTableauxAux[incompleteList_, idxToFill_, affectedByList_, minIndTable_, maxIndTable_] := Module[{possibleFillings, aux, possibities, minIndTables, result},
  If[Abs[maxIndTable - minIndTable] =!= maxIndTable - minIndTable, Return[{}]];

  possibleFillings = Complement[Range[minIndTable[[idxToFill]], maxIndTable[[idxToFill]]], incompleteList[[1 ;; idxToFill - 1]]];
  possibities = Table[aux = incompleteList;aux[[idxToFill]] = i;aux,
    {i, possibleFillings}];
  minIndTables = Table[aux = minIndTable;aux[[affectedByList[[idxToFill]]]] =
      Table[Max[aux[[el]], i + 1], {el, affectedByList[[idxToFill]]}];aux,
    {i, possibleFillings}];

  If[idxToFill == Length[incompleteList],
    Return[possibities];
    ,
    result = Table[
      GenerateStandardTableauxAux[possibities[[i]], idxToFill + 1, affectedByList, minIndTables[[i]], maxIndTable],
      {i, Length[possibleFillings]}];
    Return[Flatten[result, 1]];
  ];
];

(* ::Subsection:: *)
(*GenerateYoungSymmetrizer *)
(* 2-element *)
PermExprProduct[a_, b_] := Module[{},
  Switch[Head[a],
    Plus, PermExprProduct[#, b]& /@ a,
    Times, Sum[MapAt[PermExprProduct[#, b]&, a, i], {i, Length[a]}],
    Cycles, Switch[Head[b],
    Plus, PermExprProduct[a, #]& /@ b,
    Times, Sum[MapAt[PermExprProduct[a, #]&, b, i], {i, Length[b]}],
    Cycles, PermutationProduct[b, a],
    _, 0
  ],
    _, 0
  ]
];

PermExprProduct[cyclesList_List] := If[Length[cyclesList] > 1, PermExprProduct[First[cyclesList], PermExprProduct[Rest[cyclesList]]], First[cyclesList]];

(*Given a tableau Generate List vertical cycle groups and horizontal cycle groups*)
GenerateCycleGauge[Tableau_] := Module[
  {len1 = Length[Tableau[[1]]], tTableVertical},
  tTableVertical = Cases[#, _Integer]& /@ Transpose[Join[#, Table["x", {i, 1, len1 - Length[#]}]]& /@ Tableau];
  Return[{Tableau, tTableVertical}];
];

(*Generate the list of permutations from the given array*)
GenerateCyclesFromList[l_] := # /. Cycles[x__] :> Cycles[Map[l[[#1]]&, x, {2}]]& /@ (GroupElements[SymmetricGroup[Length[l]]]);

(*function to calculate the parity of the Cycle*)
permutationSignature[perm_?PermutationCyclesQ] := Apply[Times, (-1)^(Length /@ First[perm] - 1)];

(*Generate irreducible Young Symmetrizer with given Tableau*)
GenerateYoungSymmetrizer[Tableau_] := Module[
  {cycleGroups = GenerateCycleGauge[Tableau], vgroup, hgroup, h, v},
  hgroup = GenerateCyclesFromList /@ cycleGroups[[1]];
  vgroup = GenerateCyclesFromList /@ cycleGroups[[2]];
  vgroup = vgroup * Map[permutationSignature[#]&, (vgroup), {2}];
  v = PermExprProduct[Total /@ vgroup];
  h = PermExprProduct[Total /@ hgroup];
  PermExprProduct[{h, v}]
];


(* ::Subsection:: *)
(* Break cycle expr to Swap cycle *)
BreakCycle[{first_, rest___}] := {first, #}& /@ {rest};
CycleToSwapCycle[Cycles[{}]] := {Cycles[{}]};
CycleToSwapCycle[perm_?PermutationCyclesQ] :=
    Cycles /@ List /@ Flatten[BreakCycle /@ First[perm], 1];


(* ::Section:: *)
(*Step 3: reduce cycles to (12) and (1..n) *)

(* ::Subsection:: *)
symPermuteFirst /: StandardForm[symPermuteFirst] := Subscript["P", "12"];
(*symPermuteFirst /: StandardForm[MatrixPower[symPermuteFirst,n_]] := Subsuperscript["P", "12", ToString@n];*)
symPermuteAll /: StandardForm[symPermuteAll[np_]] := Subscript["P", StringJoin[ToString /@ Range[np]]];
(*symPermuteAll /: StandardForm[MatrixPower[symPermuteAll[np_],n_]] := Subsuperscript["P", StringJoin[ToString /@ Range[np]], ToString@n];*)

symPermuteAll[2] := symPermuteFirst;
(* Change to (12) and (1...n) *)
(*a possible method: break all (a,b,c..) to (x,y)
  calc (a,a+1) .. (a,a+n)
  reduce result
*)
InitialSwapRepresentation[] := Block[{},
  ClearAll[SwapRepresentation];
  LogPri["Initial SwapRepresentation."];
  SwapRepresentation[cyclesExpr_Plus, np_Integer] := SwapRepresentation[#, np]& /@ cyclesExpr;
  SwapRepresentation[cyclesExpr_Times, np_Integer] := SwapRepresentation[#, np]& /@ cyclesExpr;
  SwapRepresentation[cyclesExpr_?NumberQ, np_Integer] := cyclesExpr;
  SwapRepresentation[Cycles[{l___}], np_Integer] /; Length[List[l]] > 1 := Dot @@ (SwapRepresentation[#, np]& /@ CycleToSwapCycle[Cycles[{l}]]);
  SwapRepresentation[Cycles[{{l___}}], np_Integer] /; Length[List[l]] > 2 := Dot @@ (SwapRepresentation[#, np]& /@ CycleToSwapCycle[Cycles[{{l}}]]);
  SwapRepresentation[Cycles[{{}}], np_Integer] := 1;
  SwapRepresentation[Cycles[{{a_Integer, b_Integer}}], np_Integer] /; a > b :=
      SwapRepresentation[Cycles[{{a, b}}], np] =
          SwapRepresentation[Cycles[{{b, a}}], np];
  SwapRepresentation[Cycles[{{a_Integer, b_Integer}}], np_Integer] /; b == a + 1 :=
      MatrixPower[symPermuteAll[np], (np - (a - 1))].symPermuteFirst.MatrixPower[symPermuteAll[np], (a - 1)];
  SwapRepresentation[Cycles[{{a_Integer, b_Integer}}], np_Integer] /; a < b :=
      SwapRepresentation[Cycles[{{a, b}}], np] =
          SwapRepresentation[Cycles[{{b - 1, b}}], np].
              SwapRepresentation[Cycles[{{a, b - 1}}], np].
              SwapRepresentation[Cycles[{{b - 1, b}}], np];
];
InitialSwapRepresentation[];

(* ::Subsection:: *)
(*Simplify Result*)
SimplifySwapRepresentationPoly[poly_?NumberQ] := poly;
SimplifySwapRepresentationPoly[poly_Dot] :=
    poly //.
        {
          Dot[a___, 1, b___] :> Dot[a, b],
          Dot[a___, x_, MatrixPower[x_, n_], b___] :> Dot[a, MatrixPower[x, n + 1], b],
          Dot[a___, MatrixPower[x_, n_], x_, b___] :> Dot[a, MatrixPower[x, n + 1], b],
          Dot[a___, MatrixPower[x_, n1_], MatrixPower[x_, n2_], b___] :> Dot[a, MatrixPower[x, n1 + n2], b],
          MatrixPower[a_, n_] /; n == 1 :> a,
          MatrixPower[a_, n_] /; n == 0 :> 1,
          MatrixPower[symPermuteFirst, n_] :> MatrixPower[symPermuteFirst, Mod[n, 2]],
          MatrixPower[symPermuteAll[np_], n_] /; n >= np :> MatrixPower[symPermuteAll[np], Mod[n, np]]
        };
SetAttributes[SimplifySwapRepresentationPoly, Listable];
SimplifySwapRepresentationPoly[poly_List] :=
    SimplifySwapRepresentationPoly /@ poly;
SimplifySwapRepresentationPoly[poly_Plus] :=
    SimplifySwapRepresentationPoly /@ poly;
SimplifySwapRepresentationPoly[poly_Times] :=
    SimplifySwapRepresentationPoly /@ poly;


(* ::Section:: *)
(*Step 4: generate independent rule of (12)'s and (1..n)'s *)
GenerateMasslessRule[symPermuteFirst] := {1 -> 2, 2 -> 1};
GenerateMasslessRule[symPermuteAll[np_]] := Table[i -> Mod[i, np] + 1, {i, np}];

(*Only from this part , the massive part is considered*)
(*Follow massless and add n+1...2n rules*)
Massless2MassiveRules[masslessRules_List, npTotal_Integer] :=
    masslessRules ~ Join ~ (masslessRules /. {(n1_ -> n2_) :> (2 * npTotal + 1 - n1 -> 2 * npTotal + 1 - n2)});

GetMasslessIdenticalRules[identicalParticleList_List] := Module[
  {
    np = -1 + Length@identicalParticleList
  },
  If[np < 2, Return[{{}}]];
  If[np == 2,
    Return[ {{}} ~ Join ~ {GenerateMasslessRule[symPermuteFirst]
        /. Inner2OuterMasslessIndexRules[identicalParticleList]}];
  ];
  Return[
    {{}} ~ Join ~ ({GenerateMasslessRule[symPermuteFirst], GenerateMasslessRule[symPermuteAll[np]]}
        /. Inner2OuterMasslessIndexRules[identicalParticleList])
  ];
];

GetMassiveIdenticalRules[identicalParticleList_List, npTotal_Integer] :=
    Massless2MassiveRules[#, npTotal]& /@ GetMasslessIdenticalRules[identicalParticleList];



(* ::Section:: *)
(*Step 5: get matrix representation of independent matrix operator*)
(*Assume genCoorsByRule: {}->CoorsP0, P12->CoorsP12, Pall->CoorsPall*)
(*Used externally*)
GetIndependentPermutedOperatorDict[identicalParticleLists_List, nTotal_Integer, genCoorsByRule_] :=
    Module[{operatorDict, rules, coors, PFirst, PAll},
      operatorDict = Table[identicalParticleList -> Null, {identicalParticleList, identicalParticleLists}] // Association;
      Do[
        rules = GetMassiveIdenticalRules[identicalParticleList, nTotal];
        coors = genCoorsByRule /@ rules;
        If[Length@coors == 1,
          operatorDict[identicalParticleList] = {1 -> IdentityMatrix[Length@coors]}];
        PFirst = Transpose@LinearSolve[Transpose@coors[[1]], Transpose@coors[[2]]];
        PAll = Transpose@LinearSolve[Transpose@coors[[1]], Transpose@coors[[-1]]];
        operatorDict[identicalParticleList] = {
          1 -> IdentityMatrix[Length@coors[[1]]],
          symPermuteFirst -> PFirst,
          symPermuteAll[-1 + Length@identicalParticleList] -> PAll
        } // DeleteDuplicates;
        , {identicalParticleList, identicalParticleLists}];
      Return[operatorDict];
    ];
(* ::Section:: *)
(*Step 6: get total YO polynomial matrix representation*)
(*Direct replace {1->IdentityMatrix[Length@CoorsP12], symPermuteFirst->CoorsP12, symPermuteAll->CoorsPall}*)
GetTotalPermutedPolyDict[identicalParticleLists_List] := Module[
  {np, yt, polyDict, cycPoly, swapPoly},
  polyDict = Table[identicalParticleList -> Null, {identicalParticleList, identicalParticleLists}] // Association;
  Do[
    np = -1 + Length@identicalParticleList;
    yt = Switch[identicalParticleList[[-1]],
      "A" | "a", ConstantArray[1, np],
      "S" | "s", {np},
      _, Throw[{identicalParticleList, "no such identical particle error"}];
    ];
    (* (n,0) or (0,n) rep only one element*)
    polyDict[identicalParticleList] = GetPermutedPolyFromYT[yt] // First;
    , {identicalParticleList, identicalParticleLists}];
  Return[polyDict];
];

GetPermutedPolyFromYT[ytShape_List] := Module[
  {np = Total@ytShape, cycPolys, swapPolys, totalPolys},
  cycPolys = GenerateYoungSymmetrizer /@ GenerateStandardTableaux@ytShape;
  swapPolys = (SimplifySwapRepresentationPoly@SwapRepresentation[#, np]&) /@ cycPolys;
  totalPolys = (1 / (Length@#) * #)& /@ swapPolys;
  Return[totalPolys];
];

ReplaceBraNumber[expr_Power, rules_] :=
    Times @@ (ReplaceBraNumber[rules] /@ Prod2List[expr]);
ReplaceBraNumber[expr_Plus, rules_] :=
    Total@(ReplaceBraNumber[rules] /@ Sum2List[expr]);
ReplaceBraNumber[expr_Times, rules_] :=
    Times @@ (ReplaceBraNumber[rules] /@ Prod2List[expr]);
ReplaceBraNumber[rules_] := ReplaceBraNumber[#, rules] &;
ReplaceBraNumber[expr_List, rules_] := ReplaceBraNumber[rules] /@ expr;
ReplaceBraNumber[expr_, rules_] /; NumberQ[expr] := expr;
ReplaceBraNumber[expr_, rules_] := expr /. rules;
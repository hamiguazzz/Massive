LogPri["Tools Loaded"];

Sum2List[x_Plus] :=
    List @@ x;
Sum2List[x_ : Except[Plus]] :=
    List@x;
Prod2List[x_] :=
    Flatten[{x} /. {Power[y_, z_] /; Element[z, PositiveIntegers] :> ConstantArray[y, z], Times -> List}];

FactorizeHead[heads_?ListQ] :=
    ({
      Cases[#, Except[h_[___] /; MemberQ[heads, h]]] /. List -> Times,
      Cases[#, h_[___] /; MemberQ[heads, h]] /. List -> Times
    })&[Prod2List[#]]&;
FactorizeHead[head_] := FactorizeHead[{head}];
FactorizeHead[heads_, obj_] := FactorizeHead[heads][obj];
FactorizeBracket[amp_] := FactorizeHead[{ab, sb}, amp];

CountHead[head_] :=
    Module[ {list = # // Prod2List},
      Count[list, _head]
    ] &;

(*CountHead[head_] :=
    Module[ {list = {#} /. Times :> List // Flatten},
        Count[list, 
          head[a_, b_]] + (Cases[list, head[a_, b_]^n_] /. head[_, _]^n_ :> n //
        Total)
    ] &;*)

FindIndependentBasisPos[coordinateMatrix_?MatrixQ] := Flatten[FirstPosition[#, Except[0, _?NumericQ], {}]& /@
    RowReduce@Transpose@coordinateMatrix];

FindCoordinate[vector_, stBasis_?ListQ, coefficientQ_ : NumberQ] := Module[{
  coordinate = ConstantArray[0, Length@stBasis],
  factorizeCoeff = {
    Cases[#, _?coefficientQ] /. List -> Times,
    Cases[#, Except[_?coefficientQ]] /. List -> Times}
      &[Prod2List[#]]&,
  extractMinus
},
  extractMinus[blist_, clist_] := Do[If[MatchQ[blist[[i]], -_], blist[[i]] * -1;clist[[i]] * -1;], {i, Length@blist}];
  SetAttributes[extractMinus, HoldAll];
  If[Length@stBasis === Length[Flatten[Sum2List /@ stBasis]],
    Module[{
      basisList, basisCoeff,
      vectorCoeff, vectorList, pos},
      (vectorCoeff = First /@ #;vectorList = Last /@ #)&[factorizeCoeff /@ Sum2List[vector]];
      (basisCoeff = First /@ #;basisList = Last /@ #)&[(factorizeCoeff@Sum2List@#)& /@ stBasis];
      extractMinus[basisList, basisCoeff];
      extractMinus[vectorList, vectorCoeff];
      Do[
        pos = Position[vectorList, basisList[[i]], {}] // Cases[{_?NumberQ}];
        If[Length@pos > 0,
          coordinate[[i]] = Total[vectorCoeff[[Flatten@pos]]] / basisCoeff[[i]];
        ]
        , {i, Length[stBasis]}
      ];],
    Module[{transformMatrix, oldBasis = stBasis, newCoeff, newBasis, newStBasis},
      (newCoeff = First /@ #;newBasis = Last /@ #)&
      [factorizeCoeff /@ Flatten[Sum2List /@ oldBasis]];
      extractMinus[newBasis, newCoeff];
      newStBasis = DeleteDuplicates[newBasis];
      transformMatrix = FindCoordinate[#, newStBasis, coefficientQ]& /@ oldBasis;
      coordinate = LinearSolve[Transpose@transformMatrix, FindCoordinate[vector, newStBasis, coefficientQ]];
    ]
  ];

  If[Expand@vector === Expand@Total[stBasis * coordinate],
    Return[coordinate],
    (*    Print["FindCoordinate Error vector=\n",vector,*)
    (*      "\n Extra terms are\n", Simplify[vector-Total[coordinate*stBasis]]//Expand];*)
    Throw[{"no such solution", {Simplify[vector - Total[coordinate * stBasis]] // Expand, vector, stBasis}}];
  ];
];

Map2ListWithPosition[map_, sortedkeys_] :=
    Module[ {count = 0, le = 0, l, e},
      Reap[Reap[Do[le = Sow[Flatten[{map[sortedkeys[[i]]]}], e] // Length;
      Sow[sortedkeys[[i]] -> count + Range[le], l];
      count += le;, {i, Length @ sortedkeys}
      ], l], e] // {#[[2]] // Flatten, #[[1]][[2]] // Flatten}&
    ];

ReverseDict[dict_] :=
    With[ {keys = dict // Keys},
      Table[Sow[dict[keys[[i]]][[j]] -> keys[[i]]], {i, keys // Length}, {j, dict[keys[[i]]] // Length}] // Reap // Last // First // Association
    ];

Options[SyncDataTask] = {context -> Automatic, kernelAmount -> "Auto", synctask -> 20, synctime -> 10};
SetAttributes[SyncDataTask, HoldFirst];
SyncDataTask[syncedDict_, taskFun_, distributedData_, OptionsPattern[]] :=
    Module[ {kernels = Length[Kernels[]], n, index, data},
      If[ kernels === 0,
        LaunchKernels[4];
        kernels = Length[Kernels[]];
      ];
      If[ OptionValue @ kernelAmount != "Auto" && kernels < OptionValue @ kernelAmount,
        LaunchKernels[OptionValue @ kernelAmount - kernels];
        kernels = Length[Kernels[]];
      ];
      index = RandomSample[Range[Length[distributedData]]];
      n = Floor[Length[distributedData] / kernels];
      data = Table[i -> distributedData[[1 + n * (i - 1) ;; n * i]], {i, kernels}] // Association;
      Do[data[i] ~ AppendTo ~ distributedData[[n * kernels + i]], {i, Length[distributedData] - n * kernels}];
      If[ OptionValue@synctask == Infinity && OptionValue@synctime == Infinity,
        ParallelDo[
          Module[ {kernelOwnedData = data[k], kernelDict = syncedDict},
            Do[taskFun[kernelDict, kernelOwnedEle], {kernelOwnedEle, kernelOwnedData}];
            (*syncedDict ~ AssociateTo ~ kernelDict
                // AbsoluteTiming // First // If[# > 0.5, Print["locked copy ", #];]&*)
          ], {k, kernels}, DistributedContexts -> OptionValue@context],
        ParallelDo[
          Module[ {kernelOwnedData = data[k], kernelDict, taskcount = 0, timecount = 0, maxtask = OptionValue @ synctask, maxtime = OptionValue @ synctime},
            kernelDict = syncedDict;
            Do[
              If[ taskcount >= maxtask || timecount >= maxtime,
                (kernelDict = syncedDict) // AbsoluteTiming // First // If[ # > 0.5,
                  Print["locked copy ", #];
                ]&;
              ];
              timecount += taskFun[kernelDict, kernelOwnedData[[i]]] // AbsoluteTiming // First;
              If[ taskcount >= maxtask || timecount >= maxtime,
                syncedDict ~ AssociateTo ~ kernelDict // AbsoluteTiming // First // If[ # > 0.5,
                  Print["locked sync ", #];
                ]&
              ];
              taskcount++;, {i, Length[kernelOwnedData]}
            ];
            syncedDict ~ AssociateTo ~ kernelDict;
          ], {k, kernels}, DistributedContexts -> OptionValue@context]
      ]
    ]
 
(* ::Section:: *)
(* W^2 operator *)
(*Mostly following massless*)
BridgeQ[I_, i_, j_] := Xor[MemberQ[I, i], MemberQ[I, j]];
BridgeQ[I_] := BridgeQ[I, ##] &;
BridgeSign[I_, i_, j_] := If[BridgeQ[I, i, j], 1, -1];
MM[I_, i_, j_, k_, l_] :=
    -BridgeSign[I, i, k] *
        (ab[i, l] ab[j, k] + ab[i, k] ab[j, l]) / 4;
MbMb[I_, i_, j_, k_, l_] := -BridgeSign[I, i, k] *
    (sb[i, l] sb[j, k] + sb[i, k] sb[j, l]) / 4;
MMb[I_, MI_, i_, j_, k_, l_] :=
    BridgeSign[I ~ Join ~ MI, i, k] *
        Sum[
          (ab[m, i] ab[j, n] + ab[m, j] ab[i, n]) *
              (sb[m, k] sb[l, n] + sb[m, l] sb[k, n]),
          {m, I}, {n, I}] / 4 // Simplify;
s[i_, j_] := ab[i, j] * sb[j, i];
Mandelstam[I_] := (1 / 2) Sum[s[i, j], {i, I}, {j, I}];

W2[Ind_List, np_Integer] := W2[#, Ind, np] &;
W2[Amp_Plus, Ind_List, np_Integer] := W2[Ind, np] /@ Amp;
W2[Amp : Except[Plus], ind_List, np_Integer] :=
    Module[{
      massiveInd = ind /. i_Integer :> -i + 2 * np + 1,
      allInd,
      amp = Expand[Amp], list, ablist = {}, sblist = {},
      prefactor = 1, sf, sg, sfg},
      allInd = ind ~ Join ~ massiveInd;
      (*find bridges*)
      If[Head[amp] === Plus, Return[W2[amp, ind, np]],
        list = Prod2List[amp]];
      Map[Switch[Head[#],
        ab,
        If[BridgeQ[allInd] @@ #, AppendTo[ablist, #], prefactor *= #],
        sb,
        If[BridgeQ[allInd] @@ #, AppendTo[sblist, #], prefactor *= #],
        _,
        prefactor *= # (*other factors*)] &, list];
      (*calculations*)
      sf = -(3 / 4) Length[ablist] Times @@ ablist +
          2 Sum[MM[allInd, ablist[[i, 1]], ablist[[i, 2]], ablist[[j, 1]],
            ablist[[j, 2]]] Times @@ Delete[ablist, {{i}, {j}}], {j,
            Length[ablist]}, {i, j - 1}];
      sg = -(3 / 4) Length[sblist] Times @@ sblist +
          2 Sum[MbMb[allInd, sblist[[i, 1]], sblist[[i, 2]], sblist[[j, 1]],
            sblist[[j, 2]]] Times @@ Delete[sblist, {{i}, {j}}], {j,
            Length[sblist]}, {i, j - 1}];
      sfg = Sum[
        MMb[ind, massiveInd, ablist[[i, 1]], ablist[[i, 2]], sblist[[j, 1]],
          sblist[[j, 2]]] Times @@ Delete[ablist, i] Times @@
            Delete[sblist, j], {i, Length[ablist]}, {j, Length[sblist]}];
      Return[prefactor (Mandelstam[
        ind] (sf * (Times @@ sblist) + (Times @@ ablist) * sg) + sfg) //
          Simplify]];

(* Sometimes relation of W^2 Bi= Wij*s*Bj will be wrong*)
W2Matrix[spins_, bhDim_, ind_] := Module[
  {np = Length@spins, bhBasis, bhBasisHigher, mbhBasis, w2bhBasis, mbhBasisCoor, w2bhBasisCoor , rdict},
  bhBasis = ConstructAmp[spins, bhDim];
  bhBasisHigher = ConstructAmp[spins, bhDim + 2];
  rdict = <||>;
  mbhBasis = ReduceWithDict[rdict, Expand@#, np]& /@ (Mandelstam[ind] * bhBasis);
  w2bhBasis = ReduceWithDict[rdict, Expand@W2[#, ind, np], np]& /@ (bhBasis);
  mbhBasisCoor = FindCor[bhBasisHigher] /@ mbhBasis;
  w2bhBasisCoor = FindCor[bhBasisHigher] /@ w2bhBasis;
  Return[Transpose@LinearSolve[Transpose@mbhBasisCoor, Transpose@w2bhBasisCoor]];
];
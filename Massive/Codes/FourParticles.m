(*TODO generalize this file to all particle amounts and merge this with amplitude.m*)

(*TODO particle over 4*)
reduce4pt[spin1_, spin2_, spin3_, spin4_, l1_, l2_, l3_, l4_, dim_, Nm_] :=
    Module[ {Left, Right, Num1, Num2, Num3, Num4, num1, num2, num3, num4},
      Right = (dim - 4 + spin1 + spin2 + spin3 + spin4 - l1 - l2 - l3 - l4) / 2;
      Left = (dim - 4 - spin1 - spin2 - spin3 - spin4 + l1 + l2 + l3 + l4) / 2;
      Num1 = If[ Nm > 0,
        Left - l1,
        Left + 2 spin1
      ];
      num1 = If[ Nm > 0,
        2spin1 - l1,
        0
      ];
      Num2 = If[ Nm > 3,
        Left - l2,
        Left + 2 spin2
      ];
      num2 = If[ Nm > 3,
        2spin2 - l2,
        0
      ];
      Num3 = If[ Nm > 2,
        Left - l3,
        Left + 2 spin3
      ];
      num3 = If[ Nm > 2,
        2spin3 - l3,
        0
      ];
      Num4 = If[ Nm > 1,
        Left - l4,
        Left + 2 spin4
      ];
      num4 = If[ Nm > 1,
        2spin4 - l4,
        0
      ];
      {Left, Right, Num1, Num2, Num3, Num4, num1, num2, num3, num4}
    ];


Options[FptAmp] = {
  antispinor -> {0, 0, 0, 0},
  fund -> "\[Lambda]t",
  mass -> {
    "\!\(\*SubscriptBox[\(m\), \(1\)]\)",
    "\!\(\*SubscriptBox[\(m\), \(2\)]\)",
    "\!\(\*SubscriptBox[\(m\), \(3\)]\)",
    "\!\(\*SubscriptBox[\(m\), \(4\)]\)"}};
FptAmp[spin1_, spin2_, spin3_, spin4_, Dim_, OptionsPattern[]] :=
    Module[ {Np = 4, para, yd, filling, amps, Nm},
      (*TODO extension particle number*)
      Nm = Np - Count[OptionValue[mass], 0];
      para = reduce4pt[spin1, spin2, spin3, spin4, #1, #2, #3, #4, Dim, Nm]& @@ OptionValue[antispinor];
      If[ Length@Select[para, Negative[#]&] != 0,
        Return[{}]
      ];
      yd = Table[0, 2, para[[1]] + para[[2]]];
      filling = Table[Table[i, para[[2 + i]]], {i, Np}]
          ~ Join ~ Table[Table[Np * 2 + 1 - i, para[[-(Np + 1 - i)]]], {i, Np}] // Flatten // Sort;
      amps = YTtoAmpmass[#, para[[1]], Range[Np],
        fund -> OptionValue[fund]]& /@
          StrangeSSYT[yd, filling, para[[1]], {5, 6, 7, 8}];
      Return[amps];
    ];

(* ::Section:: *)
(*decompose in basis*)


(* ::Subsection::Closed:: *)

(* ::Subsection:: *)

(*Massless limit reduce rules*)
(*In fact reduce faster by omitting these lower dimensions*)

FruleP1MLL = {
  sb[1, i_] * ab[1, j_] :> Sum[-sb[k, i]ab[k, j], {k, 2, 4}],
  sb[1, i_]^m_ * ab[1, j_] :> Sum[-sb[1, i]^(m - 1)sb[k, i]ab[k, j], {k, 2, 4}],
  sb[1, i_] * ab[1, j_]^n_ :> Sum[-ab[1, j]^(n - 1)sb[k, i]ab[k, j], {k, 2, 4}],
  sb[1, i_]^m_ * ab[1, j_]^n_ :> Sum[-sb[1, i]^(m - 1) ab[1, j]^(n - 1) sb[k, i]ab[k, j], {k, 2, 4}]};
FruleP3MLL = Join[{
  sb[2, 3] * ab[2, 3] :> Sum[sb[i, j]ab[j, i], {i, 2, 4}, {j, Max[i + 1, 4], 4}],
  sb[2, 3]^m_ * ab[2, 3] :> sb[2, 3]^(m - 1) Sum[sb[i, j]ab[j, i], {i, 2, 4}, {j, Max[i + 1, 4], 4}],
  sb[2, 3] * ab[2, 3]^n_ :> ab[2, 3]^(n - 1) Sum[sb[i, j]ab[j, i], {i, 2, 4}, {j, Max[i + 1, 4], 4}],
  sb[2, 3]^m_ * ab[2, 3]^n_ :> sb[2, 3]^(m - 1) ab[2, 3]^(n - 1) Sum[sb[i, j]ab[j, i], {i, 2, 4}, {j, Max[i + 1, 4], 4}]}];
ruleSchAMLL = {
  ab[i_, l_] * ab[j_, k_] /; Signature[{i, j}] > 0 && Signature[{k, l}] > 0
      :> -ab[i, j]ab[k, l] + ab[i, k]ab[j, l],
  ab[i_, l_]^m_ * ab[j_, k_] /; Signature[{i, j}] > 0 && Signature[{k, l}] > 0
      :> ab[i, l]^(m - 1) (-ab[i, j]ab[k, l] + ab[i, k]ab[j, l]),
  ab[i_, l_] * ab[j_, k_]^n_ /; Signature[{i, j}] > 0 && Signature[{k, l}] > 0
      :> ab[j, k]^(n - 1) (-ab[i, j]ab[k, l] + ab[i, k]ab[j, l]),
  ab[i_, l_]^m_ * ab[j_, k_]^n_ /; Signature[{i, j}] > 0 && Signature[{k, l}] > 0
      :> ab[i, l]^(m - 1) ab[j, k]^(n - 1) (-ab[i, j]ab[k, l] + ab[i, k]ab[j, l])};
ruleSchSMLL = ruleSchAMLL /. ab -> sb;


(* ::Section:: *)
(*matching mass dimension*)
(*TODO particle over 4*)

Options[MatchtoDdim] = {fund -> "\[Lambda]t",
  mass -> {"\!\(\*SubscriptBox[\(m\), \(1\)]\)",
    "\!\(\*SubscriptBox[\(m\), \(2\)]\)",
    "\!\(\*SubscriptBox[\(m\), \(3\)]\)",
    "\!\(\*SubscriptBox[\(m\), \(4\)]\)"}};
MatchtoDdim[amp_, OptionsPattern[]] :=
    Module[ {amplist1, amplist2,
      labelnum1 = <|1 -> {}, 2 -> {}, 3 -> {}, 4 -> {}|>,
      labelnum2 = <|1 -> {}, 2 -> {}, 3 -> {}, 4 -> {}|>, mfactor = 1},
      amplist1 =
          amp //. {Times -> List, ab -> List, sb[i_, j_] -> {},
            Power[y_, z_] /; Element[z, PositiveIntegers] :>
                ConstantArray[y, z]} // Flatten;
      amplist2 =
          amp //. {Times -> List, ab[i_, j_] -> {}, sb -> List,
            Power[y_, z_] /; Element[z, PositiveIntegers] :>
                ConstantArray[y, z]} // Flatten;
      Do[If[ OptionValue[mass][[i]] === 0,
        Continue[]
      ];
      labelnum1[i] = Count[amplist1, i];
      labelnum2[i] = Count[amplist2, i];
      If[ OptionValue[fund] === "\[Lambda]t",
        Do[mfactor *= -sb[i, 9 - i] / OptionValue[mass][[i]], {j, labelnum1[i] - labelnum2[i]}],
        Do[mfactor *= ab[i, 9 - i] / OptionValue[mass][[i]], {j, labelnum1[i] - labelnum2[i]}]
      ], {i, 4}];
      Return[amp * mfactor];
    ];
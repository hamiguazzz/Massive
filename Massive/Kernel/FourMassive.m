(* ::Package:: *)

Print["FourMassive Loaded"];

(* ::Section::Closed:: *)
(*FptAmp*)

(*test4pt[spin1_, spin2_, spin3_, spin4_, Dim_, Nm_] :=*)
(*    Module[ {Left, Right, Num1, Num2, Num3, Num4, num1, num2, num3, num4},*)
(*      Right = (Dim - 4 + spin1 + spin2 + spin3 + spin4) / 2;*)
(*      Left = (Dim - 4 - spin1 - spin2 - spin3 - spin4) / 2;*)
(*      Num1 = If[ Nm > 0,*)
(*        Left,*)
(*        Left + 2 spin1*)
(*      ];*)
(*      num1 = If[ Nm > 0,*)
(*        2spin1,*)
(*        0*)
(*      ];*)
(*      Num2 = If[ Nm > 3,*)
(*        Left,*)
(*        Left + 2 spin2*)
(*      ];*)
(*      num2 = If[ Nm > 3,*)
(*        2spin2,*)
(*        0*)
(*      ];*)
(*      Num3 = If[ Nm > 2,*)
(*        Left,*)
(*        Left + 2 spin3*)
(*      ];*)
(*      num3 = If[ Nm > 2,*)
(*        2spin3,*)
(*        0*)
(*      ];*)
(*      Num4 = If[ Nm > 1,*)
(*        Left,*)
(*        Left + 2 spin4*)
(*      ];*)
(*      num4 = If[ Nm > 1,*)
(*        2spin4,*)
(*        0*)
(*      ];*)
(*      {Left, Right, Num1, Num2, Num3, Num4, num1, num2, num3, num4}*)
(*    ];*)
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
  masslesslimit -> True,
  fund -> "\[Lambda]t",
  antispinor -> {0, 0, 0, 0},
  mass -> {
    "\!\(\*SubscriptBox[\(m\), \(1\)]\)",
    "\!\(\*SubscriptBox[\(m\), \(2\)]\)",
    "\!\(\*SubscriptBox[\(m\), \(3\)]\)",
    "\!\(\*SubscriptBox[\(m\), \(4\)]\)",
    False}};
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
        fund -> OptionValue[fund], masslesslimit -> OptionValue@masslesslimit]& /@
          StrangeSSYT[yd, filling, para[[1]], {5, 6, 7, 8}];
      If[ !OptionValue[masslesslimit],
        If[ OptionValue[antispinor] =!= ConstantArray[0, Np],
          amps = amps /. {
            8 -> Superscript[8, "I"],
            7 -> Superscript[7, "J"],
            6 -> Superscript[6, "K"],
            5 -> Superscript[5, "L"]};
          ,
          amps = (amps //. FruleMass[OptionValue[mass][[1 ;; Np]]])
              /. {8 -> Superscript[8, "I"],
            7 -> Superscript[7, "J"],
            6 -> Superscript[6, "K"],
            5 -> Superscript[5, "L"]};
          If[OptionValue[mass][[-1]] === True,
            amps = amps /. {8 -> 1, 7 -> 2, 6 -> 3, 5 -> 4};
          ]
        ];
      ];
      Return[amps];
    ];

(* ::Section:: *)
(*decompose in basis*)


(* ::Subsection::Closed:: *)
(*Massive reduce rules*)


FruleP1 = {sb[1, i_] * ab[1, j_] :> Sum[-sb[k, i]ab[k, j], {k, 2, 4}],
  sb[1, i_]^m_ * ab[1, j_] :> Sum[-sb[1, i]^(m - 1)sb[k, i]ab[k, j], {k, 2, 4}],
  sb[1, i_] * ab[1, j_]^n_ :> Sum[-ab[1, j]^(n - 1)sb[k, i]ab[k, j], {k, 2, 4}],
  sb[1, i_]^m_ * ab[1, j_]^n_ :> Sum[-sb[1, i]^(m - 1) ab[1, j]^(n - 1) sb[k, i]ab[k, j], {k, 2, 4}], (bra1 : ab | sb)[(head1 : Superscript | Subscript)[1, I1_], x_](bra2 : ab | sb)[(head2 : Superscript | Subscript)[1, I1_], y_] /; !(bra1 === bra2 || head1 === head2) :> Sum[-bra1[head1[i, I1], x]bra2[head2[i, I1], y], {i, 2, 4}], (bra1 : ab | sb)[x_, (head1 : Superscript | Subscript)[1, I1_]](bra2 : ab | sb)[(head2 : Superscript | Subscript)[1, I1_], y_] /; !(bra1 === bra2 || head1 === head2) :> Sum[-bra1[x, head1[i, I1]]bra2[head2[i, I1], y], {i, 2, 4}], (bra1 : ab | sb)[(head1 : Superscript | Subscript)[1, I1_], x_](bra2 : ab | sb)[y_, (head2 : Superscript | Subscript)[1, I1_]] /; !(bra1 === bra2 || head1 === head2) :> Sum[-bra1[head1[i, I1], x]bra2[y, head2[i, I1]], {i, 2, 4}], (bra1 : ab | sb)[x_, (head1 : Superscript | Subscript)[1, I1_]](bra2 : ab | sb)[y_, (head2 : Superscript | Subscript)[1, I1_]] /; !(bra1 === bra2 || head1 === head2) :> Sum[-bra1[head1[i, I1], x]bra2[head2[i, I1], y], {i, 2, 4}]};
FruleP3[mass_ : {"\!\(\*SubscriptBox[\(m\), \(1\)]\)", "\!\(\*SubscriptBox[\(m\), \(2\)]\)", "\!\(\*SubscriptBox[\(m\), \(3\)]\)", "\!\(\*SubscriptBox[\(m\), \(4\)]\)"}] :=
    Join[{(bra1 : ab | sb)[(head1 : Superscript | Subscript)[2, i2_], head1_[3, i3_]]
        * (bra2 : ab | sb)[(head2 : Superscript | Subscript)[2, i2_], head2_[3, i3_]] /; !(bra1 === bra2 || head1 === head2)
        :> -(Sum[bra1[head1[i, i2], head1[j, i3]]bra2[head2[i, i2], head2[j, i3]], {i, 2, 4}, {j, Max[i + 1, 4], 4}] + mass[[1]]^2 - mass[[2]]^2 - mass[[3]]^2 - mass[[4]]^2)},
      {(bra1 : ab | sb)[(head1 : Superscript | Subscript)[2, j1_], head1_[3, k1_]]
          * (bra2 : ab | sb)[(head2 : Superscript | Subscript)[2, j1_], head2_[3, k2_]]bra2_[head2_[3, k1_], x_] /; !(bra1 === bra2 || head1 === head2)
          :> bra1[head1[2, j1], head1[3, k1]]bra2[head2[2, j1], x]bra2[head2[3, k1], head2[3, k2]] + bra2[x, head2[3, k2]](Sum[bra1[head1[i, j1], head1[j, k1]]bra2[head2[i, j1], head2[j, k1]], {i, 2, 4}, {j, Max[i + 1, 4], 4}] + mass[[1]]^2 - mass[[2]]^2 - mass[[3]]^2 - mass[[4]]^2),
        (bra1 : ab | sb)[(head1 : Superscript | Subscript)[2, j1_], head1_[3, k1_]]
            * (bra2 : ab | sb)[(head2 : Superscript | Subscript)[2, j1_], head2_[3, k2_]]bra2_[x_, head2_[3, k1_]] /; !(bra1 === bra2 || head1 === head2)
            :> bra1[head1[2, j1], head1[3, k1]]bra2[x, head2[2, j1]]bra2[head2[3, k1], head2[3, k2]] + bra2[head2[3, k2], x](Sum[bra1[head1[i, j1], head1[j, k1]]bra2[head2[i, j1], head2[j, k1]], {i, 2, 4}, {j, Max[i + 1, 4], 4}] + mass[[1]]^2 - mass[[2]]^2 - mass[[3]]^2 - mass[[4]]^2),
        (bra1 : ab | sb)[(head1 : Superscript | Subscript)[2, j1_], head1_[3, k1_]]
            * (bra2 : ab | sb)[(head2 : Superscript | Subscript)[2, j2_], head2_[3, k1_]]bra2_[head2_[2, j1_], x_] /; !(bra1 === bra2 || head1 === head2)
            :> bra1[head1[2, j1], head1[3, k1]]bra2[head2[2, j1], head2[2, j2]]bra2[x, head2[3, k1]] + bra2[x, head2[2, j2]](Sum[bra1[head1[i, j1], head1[j, k1]]bra2[head2[i, j1], head2[j, k1]], {i, 2, 4}, {j, Max[i + 1, 4], 4}] + mass[[1]]^2 - mass[[2]]^2 - mass[[3]]^2 - mass[[4]]^2),
        (bra1 : ab | sb)[(head1 : Superscript | Subscript)[2, j1_], head1_[3, k1_]]
            * (bra2 : ab | sb)[(head2 : Superscript | Subscript)[2, j2_], head2_[3, k1_]]bra2_[x_, head2_[2, j1_]] /; !(bra1 === bra2 || head1 === head2)
            :> -bra1[head1[2, j1], head1[3, k1]]bra2[head2[2, j1], head2[2, j2]]bra2[x, head2[3, k1]] - bra2[x, head2[2, j2]](Sum[bra1[head1[i, j1], head1[j, k1]]bra2[head2[i, j1], head2[j, k1]], {i, 2, 4}, {j, Max[i + 1, 4], 4}] + mass[[1]]^2 - mass[[2]]^2 - mass[[3]]^2 - mass[[4]]^2)},
      {(bra1 : ab | sb)[(head1 : Superscript | Subscript)[2, j1_], head1_[3, k1_]]
          * (bra2 : ab | sb)[(head2 : Superscript | Subscript)[2, j2_], head2_[3, k2_]]bra2_[head2_[2, j1_], x_]bra2_[head2_[3, k1_], y_] /; !(bra1 === bra2 || head1 === head2)
          :> bra1[head1[2, j1], head1[3, k1]]bra2[head2[2, j1], head2[2, j2]]bra2[x, head2[3, k2]]bra2[head2[3, k1], y] + bra1[head1[2, j1], head1[3, k1]]bra2[head2[2, j2], x]bra2[head2[3, k2], head2[3, k1]]bra2[y, head2[2, j1]] - (Sum[bra1[head1[i, j1], head1[j, k1]]bra2[head2[i, j1], head2[j, k1]], {i, 2, 4}, {j, Max[i + 1, 4], 4}] + mass[[1]]^2 - mass[[2]]^2 - mass[[3]]^2 - mass[[4]]^2)bra2[head2[2, j2], x]bra2[head2[3, k2], y],
        (bra1 : ab | sb)[(head1 : Superscript | Subscript)[2, j1_], head1_[3, k1_]]
            * (bra2 : ab | sb)[(head2 : Superscript | Subscript)[2, j2_], head2_[3, k2_]]bra2_[x_, head2_[2, j1_]]bra2_[head2_[3, k1_], y_] /; !(bra1 === bra2 || head1 === head2)
            :> -bra1[head1[2, j1], head1[3, k1]]bra2[head2[2, j1], head2[2, j2]]bra2[x, head2[3, k2]]bra2[head2[3, k1], y] - bra1[head1[2, j1], head1[3, k1]]bra2[head2[2, j2], x]bra2[head2[3, k2], head2[3, k1]]bra2[y, head2[2, j1]] + (Sum[bra1[head1[i, j1], head1[j, k1]]bra2[head2[i, j1], head2[j, k1]], {i, 2, 4}, {j, Max[i + 1, 4], 4}] + mass[[1]]^2 - mass[[2]]^2 - mass[[3]]^2 - mass[[4]]^2)bra2[head2[2, j2], x]bra2[head2[3, k2], y],
        (bra1 : ab | sb)[(head1 : Superscript | Subscript)[2, j1_], head1_[3, k1_]]
            * (bra2 : ab | sb)[(head2 : Superscript | Subscript)[2, j2_], head2_[3, k2_]]bra2_[head2_[2, j1_], x_]bra2_[y_, head2_[3, k1_]] /; !(bra1 === bra2 || head1 === head2) :> -bra1[head1[2, j1], head1[3, k1]]bra2[head2[2, j1], head2[2, j2]]bra2[x, head2[3, k2]]bra2[head2[3, k1], y] - bra1[head1[2, j1], head1[3, k1]]bra2[head2[2, j2], x]bra2[head2[3, k2], head2[3, k1]]bra2[y, head2[2, j1]] + (Sum[bra1[head1[i, j1], head1[j, k1]]bra2[head2[i, j1], head2[j, k1]], {i, 2, 4}, {j, Max[i + 1, 4], 4}] + mass[[1]]^2 - mass[[2]]^2 - mass[[3]]^2 - mass[[4]]^2)bra2[head2[2, j2], x]bra2[head2[3, k2], y],
        (bra1 : ab | sb)[(head1 : Superscript | Subscript)[2, j1_], head1_[3, k1_]]
            * (bra2 : ab | sb)[(head2 : Superscript | Subscript)[2, j2_], head2_[3, k2_]]bra2_[x_, head2_[2, j1_]]bra2_[y_, head2_[3, k1_]] /; !(bra1 === bra2 || head1 === head2)
            :> bra1[head1[2, j1], head1[3, k1]]bra2[head2[2, j1], head2[2, j2]]bra2[x, head2[3, k2]]bra2[head2[3, k1], y] + bra1[head1[2, j1], head1[3, k1]]bra2[head2[2, j2], x]bra2[head2[3, k2], head2[3, k1]]bra2[y, head2[2, j1]] - (Sum[bra1[head1[i, j1], head1[j, k1]]bra2[head2[i, j1], head2[j, k1]], {i, 2, 4}, {j, Max[i + 1, 4], 4}] + mass[[1]]^2 - mass[[2]]^2 - mass[[3]]^2 - mass[[4]]^2)bra2[head2[2, j2], x]bra2[head2[3, k2], y]},
      {(bra1 : ab | sb)[(head1 : Superscript | Subscript)[2, j1_], head1_[3, k2_]]
          * (bra2 : ab | sb)[(head2 : Superscript | Subscript)[2, j2_], head2_[3, k1_]]bra2_[head2_[2, j1_], x_]bra1_[head1_[3, k1_], y_] /; !(bra1 === bra2 || head1 === head2)
          :> bra1[head1[2, j1], head1[3, k2]]bra1[head1[3, k1], y]bra2[Subscript[2, j1], Subscript[2, j2]]bra2[x, Subscript[3, k1]] + bra1[head1[2, j1], y]bra1[head1[3, k2], head1[3, k1]]bra2[Subscript[2, j2], x]bra2[Subscript[3, k1], Subscript[2, j1]] + bra1[y, head1[3, k2]]bra2[Subscript[2, j2], x](Sum[bra1[head1[i, j1], head1[j, k1]]bra2[head2[i, j1], head2[j, k1]], {i, 2, 4}, {j, Max[i + 1, 4], 4}] + mass[[1]]^2 - mass[[2]]^2 - mass[[3]]^2 - mass[[4]]^2), (bra1 : ab | sb)[(head1 : Superscript | Subscript)[2, j1_], head1_[3, k2_]](bra2 : ab | sb)[(head2 : Superscript | Subscript)[2, j2_], head2_[3, k1_]]bra2_[x_, head2_[2, j1_]]bra1_[head1_[3, k1_], y_] /; !(bra1 === bra2 || head1 === head2) :> -bra1[head1[2, j1], head1[3, k2]]bra1[head1[3, k1], y]bra2[Subscript[2, j1], Subscript[2, j2]]bra2[x, Subscript[3, k1]] - bra1[head1[2, j1], y]bra1[head1[3, k2], head1[3, k1]]bra2[Subscript[2, j2], x]bra2[Subscript[3, k1], Subscript[2, j1]] - bra1[y, head1[3, k2]]bra2[Subscript[2, j2], x](Sum[bra1[head1[i, j1], head1[j, k1]]bra2[head2[i, j1], head2[j, k1]], {i, 2, 4}, {j, Max[i + 1, 4], 4}] + mass[[1]]^2 - mass[[2]]^2 - mass[[3]]^2 - mass[[4]]^2), (bra1 : ab | sb)[(head1 : Superscript | Subscript)[2, j1_], head1_[3, k2_]](bra2 : ab | sb)[(head2 : Superscript | Subscript)[2, j2_], head2_[3, k1_]]bra2_[head2_[2, j1_], x_]bra1_[y_, head1_[3, k1_]] /; !(bra1 === bra2 || head1 === head2) :> -bra1[head1[2, j1], head1[3, k2]]bra1[head1[3, k1], y]bra2[Subscript[2, j1], Subscript[2, j2]]bra2[x, Subscript[3, k1]] - bra1[head1[2, j1], y]bra1[head1[3, k2], head1[3, k1]]bra2[Subscript[2, j2], x]bra2[Subscript[3, k1], Subscript[2, j1]] - bra1[y, head1[3, k2]]bra2[Subscript[2, j2], x](Sum[bra1[head1[i, j1], head1[j, k1]]bra2[head2[i, j1], head2[j, k1]], {i, 2, 4}, {j, Max[i + 1, 4], 4}] + mass[[1]]^2 - mass[[2]]^2 - mass[[3]]^2 - mass[[4]]^2), (bra1 : ab | sb)[(head1 : Superscript | Subscript)[2, j1_], head1_[3, k2_]](bra2 : ab | sb)[(head2 : Superscript | Subscript)[2, j2_], head2_[3, k1_]]bra2_[x_, head2_[2, j1_]]bra1_[y_, head1_[3, k1_]] /; !(bra1 === bra2 || head1 === head2) :> bra1[head1[2, j1], head1[3, k2]]bra1[head1[3, k1], y]bra2[Subscript[2, j1], Subscript[2, j2]]bra2[x, Subscript[3, k1]] + bra1[head1[2, j1], y]bra1[head1[3, k2], head1[3, k1]]bra2[Subscript[2, j2], x]bra2[Subscript[3, k1], Subscript[2, j1]] + bra1[y, head1[3, k2]]bra2[Subscript[2, j2], x](Sum[bra1[head1[i, j1], head1[j, k1]]bra2[head2[i, j1], head2[j, k1]], {i, 2, 4}, {j, Max[i + 1, 4], 4}] + mass[[1]]^2 - mass[[2]]^2 - mass[[3]]^2 - mass[[4]]^2)}];

ruleSchLG[spinor_] :=
    Module[ {headL, headR},
      Switch[spinor, "\[Lambda]t", headL = ab;
      headR = sb, "\[Lambda]", headR = ab;
      headL = sb, _, Print["input wrong representation of spinor"]];
      Join[{headL[a_[1, aa_], d_[4, dd_]] * ab[b_[2, bb_], c_[3, cc_]] :> -ab[a[1, aa], b[2, bb]] * ab[c[3, cc], d[4,
        dd]] + ab[a[1, aa], c[3, cc]] * ab[b[2, bb], d[4, dd]]}, {headR[i_, l_] * headR[j_, k_] /; Signature[{i, j}]
          > 0 && Signature[{k, l}] > 0 :> -headR[i, j]headR[k, l] + headR[i, k]headR[j, l], headR[i_, l_]^m_ headR[j_, k_] /; Signature[{i, j}] > 0 && Signature[{k, l}] > 0 :> headR[i, l]^(m - 1) (-headR[i, j]headR[k, l] + headR[i, k]headR[j, l]), headR[i_, l_]headR[j_, k_]^n_ /; Signature[{i, j}] > 0 && Signature[{k, l}] > 0 :> (-headR[i, j]headR[k, l] + headR[i, k]headR[j, l])headR[j, k]^(n - 1), headR[i_, l_]^m_ headR[j_, k_]^n_ /; Signature[{i, j}] > 0 && Signature[{k, l}] > 0 :> (-headR[i, j]headR[k, l] + headR[i, k]headR[j, l])headR[i, l]^(m - 1) headR[j, k]^(n - 1)}, {headR[Superscript[i_, ii_], Superscript[j_, j2_]]headR[Superscript[j_, j1_], Superscript[k_, kk_]] /; Signature[{j2, j1}] < 0 :> headR[Superscript[i, ii], Superscript[j, j1]]headR[Superscript[j, j2], Superscript[k, kk]] + headR[Superscript[i, ii], Superscript[k, kk]]headR[Superscript[j, j1], Superscript[j, j2]]}]
    ];

FruleMass[mass_ : {"\!\(\*SubscriptBox[\(m\), \(1\)]\)", "\!\(\*SubscriptBox[\(m\), \(2\)]\)", "\!\(\*SubscriptBox[\(m\), \(3\)]\)", "\!\(\*SubscriptBox[\(m\), \(4\)]\)"}] :=
    Dispatch@{
      Superscript[8, "I"] -> 8, Superscript[7, "J"] -> 7,
      Superscript[6, "K"] -> 6, Superscript[5, "L"] -> 5,
      ab[8, Superscript[1, i_]] :> mass[[1]] \[Epsilon][2, i, 8],
      ab[7, Superscript[2, i_]] :> mass[[2]] \[Epsilon][2, i, 7],
      ab[6, Superscript[3, i_]] :> mass[[3]] \[Epsilon][2, i, 6],
      ab[5, Superscript[4, i_]] :> mass[[4]] \[Epsilon][2, i, 5],
      sb[8, Superscript[1, i_]] :> mass[[1]] \[Epsilon][2, 8, i],
      sb[7, Superscript[2, i_]] :> mass[[2]] \[Epsilon][2, 7, i],
      sb[6, Superscript[3, i_]] :> mass[[3]] \[Epsilon][2, 6, i],
      sb[5, Superscript[4, i_]] :> mass[[4]] \[Epsilon][2, 5, i],
      \[Epsilon][2, a_, b_] * (bracket : ab | sb)[Subscript[i_, b_], j_] :> bracket[Superscript[i, a], j],
      \[Epsilon][2, a_, b_] * (bracket : ab | sb)[i_, Subscript[j_, b_]] :> bracket[i, Superscript[j, a]],
      \[Epsilon][2, a_, b_] * (bracket : ab | sb)[Subscript[i_, a_], j_] :> -bracket[Superscript[i, b], j],
      \[Epsilon][2, a_, b_] * (bracket : ab | sb)[i_, Subscript[j_, a_]] :> -bracket[i, Superscript[j, b]],
      Superscript[1, 8] -> 8,
      Superscript[2, 7] -> 7,
      Superscript[3, 6] -> 6,
      Superscript[4, 5] -> 5};
Contractbracket[mass_ : {"\!\(\*SubscriptBox[\(m\), \(1\)]\)", "\!\(\*SubscriptBox[\(m\), \(2\)]\)", "\!\(\*SubscriptBox[\(m\), \(3\)]\)", "\!\(\*SubscriptBox[\(m\), \(4\)]\)"}] :=
    {
      Subscript[\[Delta], a_ b_]\[Epsilon][p_Integer, b_, c_] :> \[Epsilon][p, a, c],
      Subscript[\[Delta], a_ b_]\[Epsilon][p_Integer, c_, b_] :> \[Epsilon][p, c, a],
      Subscript[\[Delta], a_ b_] Subscript[\[Delta], b_ c_] :> Subscript[\[Delta], a c],
      Subscript[\[Delta], a_ a_] :> 2, Subscript[\[Delta], a_ b_] Subscript[\[Delta], a_ b_] :> 2,
      Subscript[\[Delta], a_ b_](bracket : ab | sb)[Subscript[i_, b_], j_] :> bracket[Subscript[i, a], j],
      Subscript[\[Delta], a_ b_](bracket : ab | sb)[Superscript[i_, b_], j_] :> bracket[Superscript[i, a], j],
      Subscript[\[Delta], a_ b_](bracket : ab | sb)[i_, Subscript[j_, b_]] :> bracket[i, Subscript[j, a]],
      Subscript[\[Delta], a_ b_](bracket : ab | sb)[i_, Superscript[j_, b_]] :> bracket[i, Superscript[j, a]],
      \[Epsilon][2, a_, b_](bracket : ab | sb)[Subscript[i_, b_], j_] :> bracket[Superscript[i, a], j],
      \[Epsilon][1, a_, b_](bracket : ab | sb)[Superscript[i_, b_], j_] :> bracket[Subscript[i, a], j],
      \[Epsilon][2, a_, b_](bracket : ab | sb)[i_, Subscript[j_, b_]] :> bracket[i, Superscript[j, a]],
      \[Epsilon][1, a_, b_](bracket : ab | sb)[i_, Superscript[j_, b_]] :> bracket[i, Subscript[j, a]],
      \[Epsilon][2, a_, b_](bracket : ab | sb)[Subscript[i_, a_], j_] :> -bracket[Superscript[i, b], j],
      \[Epsilon][1, a_, b_](bracket : ab | sb)[Superscript[i_, a_], j_] :> -bracket[Subscript[i, b], j],
      \[Epsilon][2, a_, b_](bracket : ab | sb)[i_, Subscript[j_, a_]] :> -bracket[i, Superscript[j, b]],
      \[Epsilon][1, a_, b_](bracket : ab | sb)[i_, Superscript[j_, a_]] :> -bracket[i, Subscript[j, b]],
      \[Epsilon][p_Integer, a_, b_]\[Epsilon][q_Integer, b_, c_] :> Subscript[\[Delta], a c],
      \[Epsilon][p_Integer, a_, b_]\[Epsilon][q_Integer, c_, b_] :> -Subscript[\[Delta], a c],
      \[Epsilon][p_Integer, b_, a_]\[Epsilon][q_Integer, b_, c_] :> -Subscript[\[Delta], a c],
      \[Epsilon][p_Integer, b_, a_]\[Epsilon][q_Integer, c_, b_] :> Subscript[\[Delta], a c],
      (bracket : ab | sb)[i_, Subscript[k_, II_]] * bracket_[j_, Superscript[k_, II_]] :> sign[bracket]mass[[k]]bracket[i, j],
      (bracket : ab | sb)[i_, Subscript[k_, II_]] * bracket_[Superscript[k_, II_], j_] :> -sign[bracket]mass[[k]]bracket[i, j],
      (bracket : ab | sb)[Subscript[k_, II_], i_] * bracket_[j_, Superscript[k_, II_]] :> -sign[bracket]mass[[k]]bracket[i, j],
      (bracket : ab | sb)[Subscript[k_, II_], i_] * bracket_[Superscript[k_, II_], j_] :> sign[bracket]mass[[k]]bracket[i, j],
      (bracket : ab | sb)[Superscript[i_, I1_], Superscript[i_, I2_]] :> sign[bracket]mass[[i]]\[Epsilon][2, I1, I2],
      (bracket : ab | sb)[Subscript[i_, I1_], Superscript[i_, I2_]] :> sign[bracket]mass[[i]]Subscript[\[Delta], I1 I2],
      (bracket : ab | sb)[Superscript[i_, I1_], Subscript[i_, I2_]] :> -sign[bracket]mass[[i]]Subscript[\[Delta], I1 I2],
      (bracket : ab | sb)[Subscript[i_, I1_], Subscript[i_, I2_]] :> -sign[bracket]mass[[i]]\[Epsilon][1, I1, I2]
    };
sign[bracket_] :=
    Switch[bracket, ab, -1, sb, 1, \[Lambda], ab, \[Lambda]t, sb, _, Print["wrong bracket"]];
\[Epsilon][p_, b_, b_] :=
    0;
Options[labeladjust] = {fund -> "\[Lambda]t"};
labeladjust[amp_, ParticleNum_ : 4, OptionsPattern[]] :=
    Module[ {ii, label = Table[1, ParticleNum], replace = {}, halfamp, samebracket},
      Switch[amp[[0]], Plus, Return[labeladjust[#, ParticleNum, fund -> OptionValue[fund]]& /@ amp], Times, Null, _, Print["something miss, amp=", amp]];
      Switch[OptionValue[fund], "\[Lambda]", halfamp = Cases[amp, _sb], "\[Lambda]t", halfamp = Cases[amp, _ab]];
      halfamp = SortBy[halfamp, Map[#[[1]]&]];
      Do[samebracket = Position[halfamp, _[Subscript[ii[[1]], _], Subscript[ii[[2]], _]]] // Flatten;
      If[ Length[samebracket] > 1,
        halfamp = Join[halfamp[[;; samebracket[[1]] - 1]], Reverse@halfamp[[samebracket]], halfamp[[samebracket[[-1]] + 1 ;;]]]
      ], {ii, Subsets[Range[4], {2}]}];
      Do[replace = Join[replace, {halfamp[[ii, 1, 2]] -> If[ halfamp[[ii, 1, 1]] < 5,
        ToString[halfamp[[ii, 1, 1]]] <> "LG" <> ToString[label[[halfamp[[ii, 1, 1]]]]++],
        halfamp[[ii, 1, 2]]
      ], halfamp[[ii, 2, 2]] -> If[ halfamp[[ii, 2, 1]] < 5,
        ToString[halfamp[[ii, 2, 1]]] <> "LG" <> ToString[label[[halfamp[[ii, 2, 1]]]]++],
        halfamp[[ii, 2, 2]]
      ]}], {ii, Length[halfamp], 1, -1}];
      amp /. replace
    ];

FreeLGIndex[i_, updown_ : Superscript] :=
    Switch[i, 4 | 5, updown[5, "L"], 3 | 6, updown[6, "K"], 2 | 7, updown[7, "J"], 1 | 8, updown[8, "I"], _, Print["error to give a index"]];


(* ::Subsection:: *)
(*Massless limit reduce rules*)


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


Options[MatchtoDdimMassive] = {fund -> "\[Lambda]t",
  mass -> {"\!\(\*SubscriptBox[\(m\), \(1\)]\)",
    "\!\(\*SubscriptBox[\(m\), \(2\)]\)",
    "\!\(\*SubscriptBox[\(m\), \(3\)]\)",
    "\!\(\*SubscriptBox[\(m\), \(4\)]\)"}};
MatchtoDdimMassive[amp_, OptionsPattern[]] :=
    Module[ {amplist,
      label = <|1 -> {}, 2 -> {}, 3 -> {}, 4 -> {}, 5 -> "L", 6 -> "K",
        7 -> "J", 8 -> "I"|>,
      labelnum = <|1 -> {}, 2 -> {}, 3 -> {}, 4 -> {}|>, mfactor = 1},
      amplist =
          amp //. {Times -> List, ab -> List, sb -> List,
            Power[y_, z_] /; Element[z, PositiveIntegers] :>
                ConstantArray[y, z]} // Flatten;
      Do[If[ OptionValue[mass][[i]] === 0,
        Continue[]
      ];
      label[i] = Cases[amplist, _[i, _]] /. {_[i, la_] :> la};
      labelnum[i] = Count[label[i], #] & /@ label[i];
      If[ OptionValue[fund] === "\[Lambda]t",
        Do[mfactor *=
            -sb[
              Superscript[i,
                ToString[i] <> "LG" <>
                    ToString[Count[labelnum[i], 2] / 2 + j]],
              Superscript[9 - i, label[9 - i]]] /
                OptionValue[mass][[i]];
          ,
          {j, Count[labelnum[i], 1]}],
        Do[mfactor *=
            ab[Superscript[i,
              ToString[i] <> "LG" <>
                  ToString[Count[labelnum[i], 2] / 2 + j]],
              Superscript[9 - i, label[9 - i]]] / OptionValue[mass][[i]];
          ,
          {j, Count[labelnum[i], 1]}]
      ], {i, 4}];
      amp mfactor
    ];

Options[MatchtoDdimMasslesslimit] = {fund -> "\[Lambda]t",
  mass -> {"\!\(\*SubscriptBox[\(m\), \(1\)]\)",
    "\!\(\*SubscriptBox[\(m\), \(2\)]\)",
    "\!\(\*SubscriptBox[\(m\), \(3\)]\)",
    "\!\(\*SubscriptBox[\(m\), \(4\)]\)"}};
MatchtoDdimMasslesslimit[amp_, OptionsPattern[]] :=
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

Options[MatchtoDdim] = {
  masslesslimit -> True,
  fund -> "\[Lambda]t",
  mass -> {"\!\(\*SubscriptBox[\(m\), \(1\)]\)",
    "\!\(\*SubscriptBox[\(m\), \(2\)]\)",
    "\!\(\*SubscriptBox[\(m\), \(3\)]\)",
    "\!\(\*SubscriptBox[\(m\), \(4\)]\)"}};
MatchtoDdim[amp_, OptionsPattern[]] :=
    If[ OptionValue@masslesslimit,
      MatchtoDdimMasslesslimit,
      MatchtoDdimMassive
    ][amp, fund -> OptionValue@fund, mass -> OptionValue@mass];


(* ::Subsection:: *)
(*Reduce function*)


Options[ReduceRules] = {masslesslimit -> True, fund -> "\[Lambda]t", mass -> {"\!\(\*SubscriptBox[\(m\), \(1\)]\)", "\!\(\*SubscriptBox[\(m\), \(2\)]\)", "\!\(\*SubscriptBox[\(m\), \(3\)]\)", "\!\(\*SubscriptBox[\(m\), \(4\)]\)", False}};
ReduceRules[OptionsPattern[]] :=
    If[ OptionValue@masslesslimit,
      Join[FruleP1MLL, FruleP3MLL, ruleSchSMLL, ruleSchAMLL],
      Join[FruleP1, FruleP3[OptionValue[mass][[1 ;; 4]]], ruleSchLG[OptionValue[fund]]]
    ];


SetAttributes[FMreducePart, HoldFirst];
FMreducePart[dict_, amplst_, applyFun_, canSingleTermBeReducedAnotherTime_ : False] :=
    Module[ {i, factor, base, amplsttemp, amptemp, amptemp2},
      If[ Length[amplst] === 1,
        (*init part start*)
        amptemp = amplst[[1]];
        If[ FactorizeBracket@amptemp // (factor = #[[1]];
        base = #[[2]];)&;
        dict ~ KeyExistsQ ~ base,
          Return[factor * dict[base]]
        ];
        amplsttemp = applyFun@amptemp;
        (*init part end*)
        If[ Length[amplsttemp] === 1,
          (* base part start *)
          amptemp = amplsttemp[[1]];
          (*reduce single term to right form*)
          (*Sometime need the following code to test if the reduction method is right*)
          (*In massive Single term may be reduced twice or more*)
          (*          If[canSingleTermBeReducedAnotherTime && amptemp =!= First@applyFun@amptemp,*)
          (*            Print[amptemp];Print[Total@applyFun@amptemp];*)
          (*            Print["Single term can be reduced back to poly by 2rd reduction!"];*)
          (*            Throw[{applyFun, amptemp}];*)
          (*          ];*)
          FactorizeBracket@amptemp // (factor = #[[1]];
          base = #[[2]];)&;
          dict ~ AssociateTo ~ (base -> 1 / factor * amptemp);
          Return[amplsttemp]          ;
          (* base part end *)
          ,
          (*recursion for every term*)
          Return[Reap[Do[
            amptemp = amplsttemp[[i]];
            FactorizeBracket@amptemp // (factor = #[[1]];
            base = #[[2]];)&;
            dict ~ AssociateTo ~ (base -> 1 / factor * Sow[FMreducePart[dict, {amptemp}, applyFun]])
            , {i, amplsttemp // Length}]] // Last // Flatten];
        ],
        (*recursion for every term*)
        Return[Reap[Do[
          amptemp = amplst[[i]];
          FactorizeBracket@amptemp // (factor = #[[1]];
          base = #[[2]];)&;
          dict ~ AssociateTo ~ (base -> 1 / factor * Sow[FMreducePart[dict, amptemp, applyFun]])
          , {i, amplst // Length}]] // Last // Flatten];
      ]
    ];

Options[FMreduceWithDict] = {masslesslimit -> True, fund -> "\[Lambda]t", mass -> {"\!\(\*SubscriptBox[\(m\), \(1\)]\)", "\!\(\*SubscriptBox[\(m\), \(2\)]\)", "\!\(\*SubscriptBox[\(m\), \(3\)]\)", "\!\(\*SubscriptBox[\(m\), \(4\)]\)", False}};
SetAttributes[FMreduceWithDict, HoldFirst];
FMreduceWithDict[dict_, amp_, OptionsPattern[]] :=
    Module[ {F, dispRules, applyRules, applyFun},
      dispRules = ReduceRules[fund -> OptionValue@fund, mass -> OptionValue@mass, masslesslimit -> OptionValue@masslesslimit];
      applyRules = (Map[(# /. dispRules)&, (Expand[{#}] // (# /. Plus :> List&) // Flatten)&@#] // # /. List :> Plus&)&;
      applyFun =
          If[ OptionValue@masslesslimit,
            ({Expand@applyRules@#} /. Plus -> List // Flatten)&,
            ({(Expand@applyRules@(labeladjust[#, 4, fund -> OptionValue@fund]))
                //. Contractbracket[OptionValue[mass][[1 ;; 4]]]} /. Plus -> List // Flatten)&
          ];
      F = FMreducePart[dict, {amp}, applyFun, !OptionValue@masslesslimit] /. List -> Plus;
      If[ !OptionValue@masslesslimit,
        If[ !OptionValue[mass] === False,
          F = (F //. FruleMass[OptionValue[mass]]) //. {(bra : ab | sb)[(i : 5 | 6 | 7 | 8), x_] :> bra[FreeLGIndex[i], x], (bra : ab | sb)[x_, (i : 5 | 6 | 7 | 8)] :> bra[x, FreeLGIndex[i]]};
          If[ OptionValue[mass][[-1]],
            F = F /. {8 -> 1, 7 -> 2, 6 -> 3, 5 -> 4};
          ]
        ];
      ];
      Return[F]
    ];

Options[FMreduce] = {masslesslimit -> True, tryMax -> 30, fund -> "\[Lambda]t", mass -> {"\!\(\*SubscriptBox[\(m\), \(1\)]\)", "\!\(\*SubscriptBox[\(m\), \(2\)]\)", "\!\(\*SubscriptBox[\(m\), \(3\)]\)", "\!\(\*SubscriptBox[\(m\), \(4\)]\)", False}, parallelized -> False};
FMreduce[amp_, OptionsPattern[]] :=
    Module[ {F = amp, F1, iter = 1, applyRules, dispRules, applyFun},
      dispRules = ReduceRules[fund -> OptionValue@fund, mass -> OptionValue@mass, masslesslimit -> OptionValue@masslesslimit];
      applyRules = (If[ !OptionValue[parallelized],
        Map,
        ParallelMap
      ][(# /. dispRules)&, (Expand[{#}] // (# /. Plus :> List&) // Flatten)&@#] // # /. List :> Plus&)&;
      applyFun = If[ !OptionValue@masslesslimit,
        (Expand@applyRules@(labeladjust[#, 4, fund -> OptionValue[fund]])) //. Contractbracket[OptionValue[mass][[1 ;; 4]]]& // Expand,
        Expand@applyRules@#&
      ];
      While[True,
        F1 = applyFun@F;
        If[ F1 === F,
          Break[],
          F = F1
        ];
        If[ iter >= OptionValue@tryMax,
          Print["err", "[reduce] too many reductions!"];
          Print[F];
          Break[],
          iter++
        ]];
      If[ !OptionValue@masslesslimit,
        If[ !OptionValue[mass] === False,
          F = (F //. FruleMass[OptionValue[mass]]) //. {(bra : ab | sb)[(i : 5 | 6 | 7 | 8), x_] :> bra[FreeLGIndex[i], x], (bra : ab | sb)[x_, (i : 5 | 6 | 7 | 8)] :> bra[x, FreeLGIndex[i]]};
          If[ OptionValue[mass][[-1]],
            F = F /. {8 -> 1, 7 -> 2, 6 -> 3, 5 -> 4};
          ]
        ];
      ];
      Return[F // Expand]
    ];


(* ::Section:: *)
(*coefficient matrix*)

FindCor[amp_, ampDbasis_] := FindCoordinate[amp, ampDbasis, !(MatchQ[#, _ab | _sb]) &];

(* Separate numerical factors and symbolic factors of a monomial expression *)
(*Options[normalize] = {fund -> "\[Lambda]t",*)
(*  masslesslimit -> True,*)
(*  mass -> {"\!\(\*SubscriptBox[\(m\), \(1\)]\)", "\!\(\*SubscriptBox[\(m\), \(2\)]\)", "\!\(\*SubscriptBox[\(m\), \(3\)]\)", "\!\(\*SubscriptBox[\(m\), \(4\)]\)", False}};*)
(*Options[FindCor] = {fund -> "\[Lambda]t",*)
(*  masslesslimit -> True,*)
(*  mass -> {"\!\(\*SubscriptBox[\(m\), \(1\)]\)", "\!\(\*SubscriptBox[\(m\), \(2\)]\)", "\!\(\*SubscriptBox[\(m\), \(3\)]\)", "\!\(\*SubscriptBox[\(m\), \(4\)]\)", True}};*)
(*normalize[monoAmp_, OptionsPattern[]] :=*)
(*    Module[ {F, result, ma},*)
(*      F = Prod2List[monoAmp];*)
(*      *)(*result=Times@@@GatherBy[F,NumericQ ];*)
(*      result = {0, Times @@ Cases[F, _ab | _sb]};*)
(*      result[[1]] = monoAmp / result[[2]];*)

(*      If[ OptionValue[mass] === False, Return[result]];*)
(*      If[OptionValue@masslesslimit,*)
(*        If[monoAmp // MatchQ[Times[-1, ___]],*)
(*          Return[{-1, -monoAmp}],*)
(*          Return[{1, monoAmp}]*)
(*        ]*)
(*        ,*)
(*        Switch[OptionValue[fund],*)
(*          "\[Lambda]",*)
(*          ma = Count[F, sb[Superscript[8, "I"], Superscript[_, _]] | sb[_, Superscript[8, "I"]]];*)
(*          result = {result[[1]] / OptionValue[mass][[1]]^ma, result[[2]]OptionValue[mass][[1]]^ma};*)
(*          ma = Count[F, sb[Superscript[7, "J"], Superscript[_, _]] | sb[_, Superscript[7, "J"]]];*)
(*          result = {result[[1]] / OptionValue[mass][[2]]^ma, result[[2]]OptionValue[mass][[2]]^ma};*)
(*          ma = Count[F, sb[Superscript[6, "K"], Superscript[_, _]] | sb[_, Superscript[6, "K"]]];*)
(*          result = {result[[1]] / OptionValue[mass][[3]]^ma, result[[2]]OptionValue[mass][[3]]^ma};*)
(*          ma = Count[F, sb[Superscript[5, "L"], Superscript[_, _]] | sb[_, Superscript[5, "L"]]];*)
(*          result = {result[[1]] / OptionValue[mass][[4]]^ma, result[[2]]OptionValue[mass][[4]]^ma};,*)
(*          "\[Lambda]t",*)
(*          ma = Count[F, ab[Superscript[8, "I"], Superscript[_, _]] | ab[_, Superscript[8, "I"]]];*)
(*          result = {result[[1]] / OptionValue[mass][[1]]^ma, result[[2]]OptionValue[mass][[1]]^ma};*)
(*          ma = Count[F, ab[Superscript[7, "J"], Superscript[_, _]] | ab[_, Superscript[7, "J"]]];*)
(*          result = {result[[1]] / OptionValue[mass][[2]]^ma, result[[2]]OptionValue[mass][[2]]^ma};*)
(*          ma = Count[F, ab[Superscript[6, "K"], Superscript[_, _]] | ab[_, Superscript[6, "K"]]];*)
(*          result = {result[[1]] / OptionValue[mass][[3]]^ma, result[[2]]OptionValue[mass][[3]]^ma};*)
(*          ma = Count[F, ab[Superscript[5, "L"], Superscript[_, _]] | ab[_, Superscript[5, "L"]]];*)
(*          result = {result[[1]] / OptionValue[mass][[4]]^ma, result[[2]]OptionValue[mass][[4]]^ma};]*)
(*      ];*)
(*      Return[result];*)
(*      *)(*If[MatchQ[result\[LeftDoubleBracket]1\[RightDoubleBracket],_Complex],Return[{-I,I} result],Return[result]];*)
(*    ];*)



(* Find the coefficient list of an expression (e.g. an amplitude) in STANDARD FORM. *)
(*FindCor[Amp_, StBasis_, OptionsPattern[]] :=*)
(*    Module[ {F = Expand[Amp],*)
(*      normalize2 = normalize[#, OptionValue@masslesslimit]&,*)
(*      B, cor},*)
(*      B = normalize2 /@ StBasis;*)
(*      *)(* Amp: the expression,*)
(*      StBasis: the standard basis (monomials). *)
(*      cor = ConstantArray[0, Length[StBasis]];*)
(*      If[ F === 0,*)
(*        Return[cor]*)
(*      ];*)
(*      F = (normalize2 /@ Sum2List[F]) //. {{a___, {c1_, x_}, {c2_, x_}, b___} :> {a, {c1 + c2, x}, b}};*)
(*      Do[If[ MemberQ[B[[All, 2]], F[[i, 2]]],*)
(*        cor = ReplacePart[cor, Position[B[[All, 2]], F[[i, 2]]] -> F[[i, 1]]],*)
(*        Print["err", "[FindCor] Non-standard basis!"];*)
(*        Print[Amp];*)
(*        Print[F[[i]]]*)
(*      ], {i, Length[F]}];*)
(*      cor / B[[All, 1]]*)
(*    ];*)

(* ::Section::Closed:: *)
(*obtain d-dim basis*)

Options[ReduceParallelized] = {
  masslesslimit -> True,
  fund -> "\[Lambda]t",
  mass -> {"\!\(\*SubscriptBox[\(m\), \(1\)]\)",
    "\!\(\*SubscriptBox[\(m\), \(2\)]\)",
    "\!\(\*SubscriptBox[\(m\), \(3\)]\)",
    "\!\(\*SubscriptBox[\(m\), \(4\)]\)", False}, independentD -> True,
  maxcount -> Infinity, tryMax -> Infinity, withDict -> "False",
  kernelAmount -> "Auto", synctask -> Infinity, synctime -> Infinity,
  externalReduceDict -> <||>, log -> True};
SetAttributes[ReduceParallelized, HoldFirst];
ReduceParallelized[ampcoorDict_, ampDict_, ampDbasis_, OptionsPattern[]] :=
    Module[ {reduceFun, ampDict2 = ampDict // ReverseDict, keys, key,
      separateList = {}, kernels = Length[Kernels[]], dictSync},
      keys = ampDict2 // Keys;
      If[ kernels === 0,
        LaunchKernels[4];
        kernels = Length[Kernels[]];
      ];
      If[ OptionValue @ kernelAmount != "Auto" && kernels < OptionValue @ kernelAmount,
        LaunchKernels[OptionValue @ kernelAmount - kernels];
        kernels = Length[Kernels[]];
      ];
      If[ OptionValue@withDict === False,
        Print["Direct decomposition..."];
        reduceFun =
            (FindCor[#, ampDbasis] &)@
                FMreduce[
                  MatchtoDdim[#,
                    masslesslimit -> OptionValue@masslesslimit],
                  mass -> OptionValue@mass,
                  fund -> OptionValue@fund,
                  parallelized -> False,
                  tryMax -> OptionValue@tryMax,
                  masslesslimit -> OptionValue@masslesslimit] &;
        SetSharedVariable[ampDict2, separateList, keys, ampcoorDict];
        Print["U(N) heads over ", OptionValue@maxcount,
          " will be calculated separately."];
        ParallelDo[
          key = keys[[i]];
          If[CountHead[If[ OptionValue@fund === "\[Lambda]t",
            ab,
            sb
          ]]@key <= OptionValue@maxcount,
            ampcoorDict ~ AssociateTo ~ (key -> reduceFun@key)
                // AbsoluteTiming
                // If[OptionValue@log, Print[ampDict2[key], " cost ", #[[1]]]&, Identity];
            ,
            separateList ~ AppendTo ~ key;
          ], {i, Length[keys]}
          , DistributedContexts -> Automatic]
            // AbsoluteTiming // First
            // Print["part1 N=", Length[keys] - Length[separateList],
          " costs:", #] &;
        reduceFun =
            (FindCor[#, ampDbasis] &)@
                FMreduce[
                  MatchtoDdim[#, masslesslimit -> OptionValue@masslesslimit],
                  mass -> OptionValue@mass,
                  fund -> OptionValue@fund, parallelized -> True,
                  tryMax -> OptionValue@tryMax,
                  masslesslimit -> OptionValue@masslesslimit] &;
        Do[
          key = separateList[[i]];
          ampcoorDict ~ AssociateTo ~ (key -> reduceFun@key) //
              AbsoluteTiming // If[OptionValue@log, Print[ampDict2[key], " cost ", #[[1]]]&, Identity];
          , {i, Length[separateList]}]
            // AbsoluteTiming // First
            // Print["part2 N=", Length[separateList], " costs:", #] &;
        ,
        Print["Dict decomposition..."];
        (*Build parallelized fun : reduceFun*)
        reduceFun[dict_, amp_] :=
            ampcoorDict ~ AssociateTo ~ ((amp -> FindCor[#, ampDbasis]) &@
                FMreduceWithDict[dict,
                  MatchtoDdim[amp, masslesslimit -> OptionValue@masslesslimit],
                  mass -> OptionValue@mass,
                  fund -> OptionValue@fund,
                  masslesslimit -> OptionValue@masslesslimit])
                // AbsoluteTiming
                // If[OptionValue@log, Print[ampDict2[amp], " cost ", #[[1]]]&, Identity];
        SetAttributes[reduceFun, HoldFirst];
        Options[reduceFun] = {
          masslesslimit -> OptionValue@masslesslimit,
          mass -> OptionValue@mass,
          fund -> OptionValue@fund,
          log -> OptionValue@log
        };
        SetSharedVariable[ampDict2, dictSync, ampcoorDict];
        dictSync = OptionValue@externalReduceDict;
        (*Context must contains current package path*)
        SyncDataTask[dictSync, reduceFun, keys, synctask -> OptionValue@synctask,
          synctime -> OptionValue@synctime, context -> $ContextPath];
        Return[dictSync];
      ];
    ];

(*Options[MassivedBasis] = {*)
(*  masslesslimit -> True,*)
(*  fund -> "\[Lambda]t",*)
(*  mass -> {"\!\(\*SubscriptBox[\(m\), \(1\)]\)",*)
(*    "\!\(\*SubscriptBox[\(m\), \(2\)]\)",*)
(*    "\!\(\*SubscriptBox[\(m\), \(3\)]\)",*)
(*    "\!\(\*SubscriptBox[\(m\), \(4\)]\)", False}, independentD -> True,*)
(*  singleCoreMaxHead -> "Auto", tryMax -> Infinity, withDict -> False, maxcount -> Infinity, tryMax -> Infinity,*)
(*  kernelAmount -> "Auto",*)
(*  log -> False,*)
(*  synctask -> Infinity, synctime -> Infinity, externalReduceDict -> <||>};*)

(*MassivedBasis[spin1_, spin2_, spin3_, spin4_, dimmin_, dimmax_,*)
(*  OptionsPattern[]] :=*)
(*    Module[*)
(*      {ampbasiscoor, ampbasis, ampDbasis = {}, ampDbasisnum, antilist = {},*)
(*        amplist, ampcoor, rank, BHbasis, indexlist, ampDict, ampcoorDict, reduceDict},*)
(*      ampbasis =*)
(*          FptAmp[spin1, spin2, spin3, spin4, dimmin,*)
(*            dimension -> False,*)
(*            masslesslimit -> OptionValue@masslesslimit,*)
(*            fund -> OptionValue[fund],*)
(*            mass -> OptionValue[mass]];*)
(*      ampDbasisnum = <|dimmin - 2 -> {0}|>;*)
(*      BHbasis = <|dimmin -> ampbasis|>;*)
(*      SetSharedVariable[BHbasis];*)
(*      ParallelDo[*)
(*        BHbasis ~ AppendTo ~ (dim ->*)
(*            FptAmp[spin1, spin2, spin3, spin4, dim,*)
(*              dimension -> False,*)
(*              masslesslimit -> OptionValue@masslesslimit,*)
(*              fund -> OptionValue[fund],*)
(*              mass -> OptionValue[mass]]);,*)
(*        {dim, dimmin, dimmax + 2 spin1 + 2 spin2 + 2 spin3 + 2 spin4, 2}];*)
(*      (ampDbasis = #[[1]];*)
(*      ampDbasisnum ~ AssociateTo ~ #[[2]];) &@*)
(*          Map2ListWithPosition[BHbasis, Keys[BHbasis] // Sort];*)
(*      ampbasiscoor = ampDbasisnum;*)
(*      ampbasiscoor[[ ;; ]] = {};*)
(*      ampbasiscoor[dimmin - 2] =*)
(*          ampbasiscoor[dimmin] =*)
(*              FindCor[#, ampDbasis] & /@ ampbasis;*)
(*      If[ Det[ampbasiscoor[dimmin - 2] . Transpose[ampbasiscoor[dimmin - 2]]] ===*)
(*          0,*)
(*        Print["?"]*)
(*      ];*)
(*      Print["ampDbasis are ready"];*)
(*      *)(*zzz---This reduce error will be always triggered?*)(**)(*If[!FMreduce/@*)
(*ampDbasis===ampDbasis,Print["reduce error"]];*)
(*      antilist =*)
(*          Reap[Table[*)
(*            Sow[{i, j, k, l}], {l, 0, 2 spin4}, {k, 0, 2 spin3}, {j, 0,*)
(*              2 spin2}, {i, 0, 2 spin1}]] // Last // First;*)
(*      antilist =*)
(*          Reap[Table[*)
(*            Sow[anti -> Select[antilist, Plus @@ # === anti &]], {anti, 0,*)
(*              2 spin1 + 2 spin2 + 2 spin3 + 2 spin4}]] // Last // First //*)
(*              Association;*)
(*      indexlist =*)
(*          Reap[Table[*)
(*            If[ (antinum === 0 && dim === dimmin) ||*)
(*                OddQ[dim - dimmin + antinum],*)
(*              Null,*)
(*              Sow[{dim, antilist[antinum][[index]]}]*)
(*            ], {dim, dimmin,*)
(*              dimmax}, {antinum, 0,*)
(*              2 spin1 + 2 spin2 + 2 spin3 + 2 spin4}, {index,*)
(*              Length[antilist[antinum]]}]] // Last // First;*)
(*      ampDict = <||>;*)
(*      SetSharedVariable[ampDict];*)
(*      ParallelDo[*)
(*        amplist =*)
(*            FptAmp[spin1, spin2, spin3, spin4, indexlist[[i]][[1]],*)
(*              masslesslimit -> OptionValue@masslesslimit,*)
(*              dimension -> True,*)
(*              antispinor -> indexlist[[i]][[2]],*)
(*              fund -> OptionValue[fund],*)
(*              mass -> False];*)
(*        *)(*              mass -> OptionValue[mass]];*)
(*        *)
(*        ampDict ~ AssociateTo ~ (indexlist[[i]] -> amplist);, {i,*)
(*        Length[indexlist]}] // AbsoluteTiming // First //*)
(*          Print["Building anti-amp costs:", #] &;*)
(*      Print["Tasks amount:", ampDict // Values // Flatten // Length];*)
(*      ampcoorDict = <||>;*)
(*      SetSharedVariable[ampcoorDict];*)
(*      reduceDict = Reap[ ReduceParallelized[ampcoorDict, ampDict, ampDbasis,*)
(*        fund -> OptionValue@fund, mass -> OptionValue@mass,*)
(*        masslesslimit -> OptionValue@masslesslimit,*)
(*        tryMax -> OptionValue@tryMax,*)
(*        withDict -> OptionValue@withDict,*)
(*        kernelAmount -> OptionValue@kernelAmount,*)
(*        maxcount -> If[ OptionValue@singleCoreMaxHead == "Auto",*)
(*          (KeySelect[*)
(*            MatchQ[{dimmax,*)
(*              antilist[*)
(*                2 spin1 + 2 spin2 + 2 spin3 + 2 spin4][[1]]}]]@*)
(*              ampDict // Values // Flatten // First //*)
(*              CountHead[If[ OptionValue@fund == "\[Lambda]t",*)
(*                ab,*)
(*                sb*)
(*              ]]) - 1,*)
(*          OptionValue@singleCoreMaxHead*)
(*        ],*)
(*        synctask -> OptionValue@synctask,*)
(*        synctime -> OptionValue@synctime,*)
(*        externalReduceDict -> OptionValue@externalReduceDict,*)
(*        log -> OptionValue@log*)
(*      ] // AbsoluteTiming // (Sow[# // Last];*)
(*      Print["Coefficients totally costs:", # // First]) &*)
(*      ][[2]][[1]][[1]];*)
(*      If[ OptionValue[independentD],*)
(*        Do[If[ EvenQ[dim - dimmin],*)
(*          Do[Do[If[ antinum === 0 && dim === dimmin,*)
(*            Continue[]*)
(*          ];*)
(*          amplist =*)
(*              KeySelect[MatchQ[{dim, anti}]]@ampDict // Values // Flatten;*)
(*          ampcoor = KeyTake[ampcoorDict, amplist] // Values;*)(*If[!Plus@@@*)
(*                 ampcoor\[LeftDoubleBracket];;,ampDbasisnum[dim+*)
(*                 antinum+2]\[RightDoubleBracket]===ConstantArray[0,Length[ampcoor]],*)
(*                 Print["higher dimension"]];*)
(*          Do[rank =*)
(*              MatrixRank[*)
(*                Append[ampbasiscoor[dim + antinum],*)
(*                  ampcoor[[n, ampDbasisnum[dim + antinum]]]]];*)
(*          If[*)(*!Simplify[Append[ampbasiscoor,*)
(*                     ampcoor\[LeftDoubleBracket]n\[RightDoubleBracket]].Transpose[*)
(*                     Append[ampbasiscoor,*)
(*                     ampcoor\[LeftDoubleBracket]n\[RightDoubleBracket]]]]===0*)
(*            rank > Length[ampbasiscoor[dim + antinum]],*)
(*            *)(*Print[ampbasiscoor];*)
(*            AppendTo[ampbasiscoor[dim + antinum],*)
(*              ampcoor[[n, ampDbasisnum[dim + antinum]]]];*)
(*            AppendTo[ampbasiscoor[dimmin - 2], ampcoor[[n]]];*)
(*            AppendTo[ampbasis, amplist[[n]]]*)
(*          ],*)
(*            {n, Length@ampcoor}],*)
(*            {anti, antilist[antinum]}],*)
(*            {antinum, 0, 2 spin1 + 2 spin2 + 2 spin3 + 2 spin4, 2}],*)
(*          Do[Do[*)
(*            amplist =*)
(*                KeySelect[MatchQ[{dim, anti}]]@ampDict // Values // Flatten;*)
(*            ampcoor = KeyTake[ampcoorDict, amplist] // Values;*)
(*            If[ ! Plus @@@ ampcoor[[;; , ampDbasisnum[dim + antinum + 2]]] ===*)
(*                ConstantArray[0, Length[ampcoor]],*)
(*              Print["higher dimension"]*)
(*            ];*)
(*            Do[*)
(*              If[*)(*!Simplify[Append[ampbasiscoor,*)
(*               ampcoor\[LeftDoubleBracket]n\[RightDoubleBracket]].Transpose[*)
(*               Append[ampbasiscoor,*)
(*               ampcoor\[LeftDoubleBracket]n\[RightDoubleBracket]]]]===0*)
(*                MatrixRank[*)
(*                  Append[ampbasiscoor[dim + antinum],*)
(*                    ampcoor[[n, ampDbasisnum[dim + antinum]]]]] >*)
(*                    Length[ampbasiscoor[dim + antinum]],*)
(*                AppendTo[ampbasiscoor[dim + antinum],*)
(*                  ampcoor[[n, ampDbasisnum[dim + antinum]]]];*)
(*                AppendTo[ampbasiscoor[dimmin - 2], ampcoor[[n]]];*)
(*                AppendTo[ampbasis, amplist[[n]]]*)
(*              ],*)
(*              {n, Length@ampcoor}],*)
(*            {anti, antilist[antinum]}],*)
(*            {antinum, 1, 2 spin1 + 2 spin2 + 2 spin3 + 2 spin4 - 1, 2}]*)
(*        ],*)
(*          {dim, dimmin, dimmax}],*)
(*        *)(*******general method**********)
(*        Print["general method"];*)
(*        ampbasiscoor = {};*)
(*        Do[If[ EvenQ[dim - dimmin],*)
(*          Do[Do[If[ antinum === 0 && dim === dimmin,*)
(*            Continue[]*)
(*          ];*)
(*          amplist =*)
(*              KeySelect[MatchQ[{dim, anti}]]@ampDict // Values // Flatten;*)
(*          ampcoor = KeyTake[ampcoorDict, amplist] // Values;*)
(*          Do[rank = MatrixRank[Append[ampbasiscoor, ampcoor[[n]]]];*)
(*          If[*)(*!Simplify[Append[ampbasiscoor,*)
(*                     ampcoor\[LeftDoubleBracket]n\[RightDoubleBracket]].Transpose[*)
(*                     Append[ampbasiscoor,*)
(*                     ampcoor\[LeftDoubleBracket]n\[RightDoubleBracket]]]]===0*)
(*            rank > Length[ampbasiscoor], *)(*Print[ampbasiscoor];*)
(*            AppendTo[ampbasiscoor, ampcoor[[n]]];*)
(*            AppendTo[ampbasis, amplist[[n]]]*)
(*          ],*)
(*            {n, Length@ampcoor}],*)
(*            {anti, antilist[antinum]}],*)
(*            {antinum, 0, 2 spin1 + 2 spin2 + 2 spin3 + 2 spin4, 2}],*)
(*          Do[Do[*)
(*            amplist =*)
(*                KeySelect[MatchQ[{dim, anti}]]@ampDict // Values // Flatten;*)
(*            ampcoor = KeyTake[ampcoorDict, amplist] // Values;*)
(*            Do[*)
(*              If[*)(*!Simplify[Append[ampbasiscoor,*)
(*               ampcoor\[LeftDoubleBracket]n\[RightDoubleBracket]].Transpose[*)
(*               Append[ampbasiscoor,*)
(*               ampcoor\[LeftDoubleBracket]n\[RightDoubleBracket]]]]===0*)
(*                MatrixRank[Append[ampbasiscoor, ampcoor[[n]]]] >*)
(*                    Length[ampbasiscoor],*)
(*                AppendTo[ampbasiscoor, ampcoor[[n]]];*)
(*                AppendTo[ampbasis, amplist[[n]]]*)
(*              ],*)
(*              {n, Length@ampcoor}],*)
(*            {anti, antilist[antinum]}],*)
(*            {antinum, 1, 2 spin1 + 2 spin2 + 2 spin3 + 2 spin4 - 1, 2}]*)
(*        ],*)
(*          {dim, dimmin, dimmax}]*)
(*      ] // AbsoluteTiming // First //*)
(*          Print["Ranking costs:", #] &;*)
(*      If[ ampbasiscoor[[0]] === Association,*)
(*        ampbasiscoor = ampbasiscoor[dimmin - 2]*)
(*      ];*)
(*      <|"ampbasis" -> ampbasis, "ampcoor" -> ampbasiscoor,*)
(*        "ampDbasis" -> ampDbasis, "ampDict" -> ampDict , "reducedict" -> reduceDict|>*)
(*    ];*)

Options[ConstructIndependentOperatorBasis] = {
  masslesslimit -> True,
  fund -> "\[Lambda]t",
  mass -> {
    "\!\(\*SubscriptBox[\(m\), \(1\)]\)",
    "\!\(\*SubscriptBox[\(m\), \(2\)]\)",
    "\!\(\*SubscriptBox[\(m\), \(3\)]\)",
    "\!\(\*SubscriptBox[\(m\), \(4\)]\)"},
  singleCoreMaxHead -> "Auto", tryMax -> Infinity,
  withDict -> False, maxcount -> Infinity, tryMax -> Infinity,
  kernelAmount -> "Auto", log -> False,
  synctask -> Infinity, synctime -> Infinity, externalReduceDict -> <||>};
ConstructIndependentOperatorBasis[spins_, operDim_, OptionsPattern[]] :=
    Module[{
      antiList, dimCodeMinimal,
      CalcOperatorDimContribute, nAMax, dimCFFrom, dimCFTo,
      GetNeededBHBasisDimList,
      NeededCFBasisQ,
      basis, basisCoor, index,
      cfIndexList, bhDimList,
      cfBasisDict, bhBasisDict, reversedCFBasisDict,
      coordinateDict = <||>, bhBasis, reduceDict,
      opts, extOpts,
      GenBHBasis, GenCFBasis,
      ZRank
    },
      (*Construct amplitude index*)
      CalcOperatorDimContribute[spin_] := Switch[spin, 0, 1, 1 / 2, 3 / 2, 1, 2,
        _, Throw[{spin, "No such spin"}]];
      nAMax = Count[spins, 1];
      dimCodeMinimal = Total[CalcOperatorDimContribute /@ spins];
      (*minimal operator dimension *)
      (*d_o = d_c - nA*)
      (*l -> 0,...,spin*2*)
      (*massive CF[d_c,sumL]->BH[d_c+sumL] & .. &BH[dimMin] *)
      (*MLL CF[d_c,sumL]->BH[dim+sumL]*)
      If[operDim < dimCodeMinimal - nAMax, Throw[{operDim, "Below minimal operator dimension!"}]];
      dimCFFrom = If[OptionValue[masslesslimit], Max[dimCodeMinimal, operDim - 2 * Total[spins]], dimCodeMinimal];
      dimCFTo = operDim + nAMax;
      GetNeededBHBasisDimList[indexListInner_] :=
          If[OptionValue@masslesslimit,
            PositionIndex@((#[[1]] + Total@#[[2]])& /@ Cases[indexListInner, {dim_ /; (dim >= operDim && dim <= dimCFTo), _}]) // Keys
            ,
            Range[If[EvenQ[#2 - #1], #2, #2 - 1], If[EvenQ[#3 - #1], #3, #3 + 1],
              2]& @@
                {
                  dimCodeMinimal,
                  dimCodeMinimal,
                  (# + Max[Total /@ Cases[indexListInner, {#, l_} -> l]])&@Max[First /@ indexListInner]
                }
          ];
      NeededCFBasisQ[dim_, antiSpinors_, includeLowerDim_ : False] :=
          (*check dim-nA===operDim*)
          If[includeLowerDim,
            ((dim -
                (ReleaseHold[HoldForm[#1 * #2] /. i_ /; i != 1 -> 0] // Total)&
            [spins, antiSpinors]) <= operDim) &&
                (*check (dim+sumS-dimMin)Even*)
                EvenQ[dim + Total[antiSpinors] - dimCodeMinimal],
            ((dim -
                (ReleaseHold[HoldForm[#1 * #2] /. i_ /; i != 1 -> 0] // Total)&
            [spins, antiSpinors]) == operDim) &&
                (*check (dim+sumS-dimMin)Even*)
                EvenQ[dim + Total[antiSpinors] - dimCodeMinimal]
          ]
      ;
      (*      antiList =*)
      (*          Reap[Do[*)
      (*            Sow[{i, j, k, l}],*)
      (*            {l, 0, 2 spin4},*)
      (*            {k, 0, 2 spin3},*)
      (*            {j, 0, 2 spin2},*)
      (*            {i, 0, 2 spin1}]] // Last // First;*)
      antiList = Fold[
        (Do[Do[Sow[l ~ Append ~ i], {i, 0, #2}], {l, #1}] // Reap // Last // First )&,
        {{}}, 2 * spins
      ] // GroupBy[#, Total]&;

      cfIndexList =
          Reap[Table[
            If[NeededCFBasisQ[dim, antiList[antiSum][[index]], True] ,
              Sow[{dim, antiList[antiSum][[index]]}]],
            {dim, dimCFFrom, dimCFTo}, {antiSum, 0, 2 * Total[spins]},
            {index, Length[antiList[antiSum]]}]] // Last;

      If[Length[cfIndexList] == 0,
        Throw["No such operator!"];
        ,
        cfIndexList = cfIndexList[[1]];
      ];
      bhDimList = GetNeededBHBasisDimList[cfIndexList];
      (*      Return[<|"cf"->indexList, "bh"->neededBHBasisDim[indexList]|>];*)
      ZRank[matrix_] := If[matrix === {}, 0, MatrixRank@matrix];
      opts = {
        masslesslimit -> OptionValue@masslesslimit,
        mass -> OptionValue@mass ~ Append ~ False,
        fund -> OptionValue@fund
      };
      extOpts = ((# -> OptionValue@#)& /@
          Complement[Keys@Association@Options@ConstructIndependentOperatorBasis,
            Keys@Association@opts, {maxcount, singleCoreMaxHead}
          ]);
      If[OptionValue@masslesslimit,
        cfIndexList = Cases[cfIndexList, {dim_, antiSpinors_} /;
            (MemberQ[bhDimList, dim + Total@antiSpinors])
        ];
      ];
      Print[bhDimList, cfIndexList];
      GenBHBasis[dim_] := FptAmp @@ (spins ~ Join ~ {dim} ~ Join ~ opts);
      GenCFBasis[dim_, antispinorList_] := FptAmp @@
          (spins ~ Join ~ {dim} ~ Join ~ {antispinor -> antispinorList} ~ Join ~ opts);
      (
        bhBasisDict = ParallelMap[(# -> GenBHBasis@#)& , bhDimList ] // Association;
        cfBasisDict = ParallelMap[(# -> GenCFBasis @@ #)& , cfIndexList] // Association;
      ) // AbsoluteTiming // Print["Constructing amplitudes costs ", #[[1]]]&;
      reversedCFBasisDict = ReverseDict[cfBasisDict];
      bhBasis = Do[Sow[bhBasisDict[e]], {e, bhBasisDict // Keys // Sort}] // Reap // Last // First // (Join @@ #)&;
      extOpts = extOpts ~ Join ~
          {maxcount -> If[ OptionValue@singleCoreMaxHead == "Auto",
            Max[CountHead[If[ OptionValue@fund == "\[Lambda]t",
              ab,
              sb
            ]] /@ Keys[reversedCFBasisDict]] - 1,
            OptionValue@singleCoreMaxHead
          ]};

      reduceDict = Reap[ ReduceParallelized[
        coordinateDict, cfBasisDict, bhBasis, opts ~ Join ~ extOpts]
          // AbsoluteTiming
          // (Sow[# // Last];Print["Coefficients totally costs:", # // First]) &][[2]][[1]][[1]];

      Print["Involved CF amplitude amount is ", cfBasisDict // Values // Flatten // Length];
      Print["Involved BH amplitude amount is ",
        Fold[Plus, ConstantArray[0, Length@bhBasis],
          Map[((# == 0) /. {True -> 0, False -> 1}) &,
            (Values@coordinateDict), {2}]]
            // DeleteCases[#, 0] & // Length
      ];
      Print["Coordinate rank is ", ZRank[Values@coordinateDict]];

      (*get independent basis*)

      basis = Keys[coordinateDict];
      (*TODO sort cf basis correctly*)
      basis = SortBy[basis, reversedCFBasisDict[#]&];
      basisCoor = coordinateDict[#]& /@ basis;
      ((basis = basis[[#]];basisCoor = basisCoor[[#]])&@
          Flatten[Position[#, Except[0, _?NumericQ], 1, 1] & /@
              RowReduce@Transpose@basisCoor]) // AbsoluteTiming //
          Print["Ranking costs ", #[[1]]]&;
      (*      If[ZRank@basisCoor != ZRank[Values@coordinateDict], Print["?? Error"];Return[Null]];*)
      index = Flatten@Position[basis,
        e_ /; MemberQ[#, e], 1
      ]&@Select[basis,
        NeededCFBasisQ[reversedCFBasisDict[#][[1]], reversedCFBasisDict[#][[2]], False]&];
      (basis = basis[[#]];
      basisCoor = basisCoor[[#]];)&@index;
      Print["Final basis amount is ", Length@basis];
      Return[<|"basis" -> basis, "cf" -> cfBasisDict, "bh" -> bhBasisDict,
        "coordinate" -> coordinateDict, "reduceDict" -> reduceDict|>];
    ];

Print["SSYT Loaded"];

(* ::Section::Closed:: *)
(*SSYT*)


ClearAll[SSYT];
SSYT[A_, filling_, n_ : 1] :=
    Module[ {yt, pos, f, height = Length[A], list = {}},
      If[ n > Length[Flatten[A]],
        Return[{A}]
      ];
      f = filling[[n]];
      pos = FirstPosition[#, 0]& /@ A // Flatten;
      Do[
        If[ MissingQ[pos[[i]]],
          Continue[]
        ];
        If[ pos[[i]] > 1 && A[[i, pos[[i]] - 1]] > f,
          Continue[]
        ];
        If[ i > 1 && (A[[i - 1, pos[[i]]]] == 0 || A[[i - 1, pos[[i]]]] >= f),
          Continue[]
        ];
        yt = ReplacePart[A, {i, pos[[i]]} -> f];
        list = DeleteDuplicates@Join[list, SSYT[yt, filling, n + 1]],
        {i, height}];
      Return[list]
    ];

posi[NumInNt_, massivePart_] :=
    Position[NumInNt, #]& /@ massivePart;
StrangeSSYT[YoungD_, filling_, nt_, massivePart_] :=
    Module[ {ssyt, ntyt, sel},
      ssyt = SSYT[YoungD, filling];
      ntyt = Flatten /@ ssyt[[;;, ;;, ;; nt]];
      sel = Flatten /@ (posi[#, massivePart]& /@ ntyt);
      Delete[ssyt, Complement[Array[{#}&, Length[ssyt]], Position[sel, {}]]]
    ];



(* ::Section::Closed::*)
(* SSYT To Amp*)

ab[i_, j_] :=
    0 /; i == j;
ab[i_, j_] :=
    -ab[j, i] /; Signature[{i, j}] < 0;
sb[i_, j_] :=
    0 /; i == j;
sb[i_, j_] :=
    -sb[j, i] /; Signature[{i, j}] < 0;

Options[YTtoAmpmass] = {fund -> "\[Lambda]t"};
YTtoAmpmass[YT_, nt_, ParticleList_, OptionsPattern[]] :=
    Module[ {amp = 1, headL, headR,
      labelL = Table[1, Length[ParticleList]],
      labelR = Table[1, Length[ParticleList]]},
      If[ OptionValue[fund] === "\[Lambda]t",
        headL = ab;
        headR = sb; ,
        headL = sb;
        headR = ab;
      ];
      Do[
        amp *= headL @@ Complement[ParticleList, YT[[;;, ii]]];
        ,
        {ii, nt}];
      Do[
        amp *= headR @@ YT[[;; 2, ii]];
        ,
        {ii, nt + 1, Length[YT[[1]]]}];
      Return[amp];
    ];
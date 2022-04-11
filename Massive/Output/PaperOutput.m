(* ::Package:: *)

folderPath = FileNameDrop[If[$InputFileName === "", NotebookFileName[], $InputFileName], -2];
$DEBUG = False;
$MassiveVerbose = False;
Get[FileNameJoin[{folderPath, "Kernel", "init.m"}]];

$currentModel // Keys // Print;

dimFrom = 4;
dimTo = 8;

GenSection[particles_] :=
    OrganizeResultTexDict[
      BasisByModel[particles, dimFrom, dimTo, output -> "tex"],
      heading -> "\\section{Type:" <> StringJoin @@ particles <> "}\n\n",
      exportPath ->
          FileNameJoin[{$MassiveDir, "Output",
            ToString[$currentModel[#]["spin"] & /@ particles // Total],
            "result_" <> StringJoin @@ particles <> ".txt"}]] //
        ExpandFileName;


(* ::Section:: *)
(*0*)


(*0000*)
dimFrom = 5;
GenSection@{"h", "h", "h", "h"};


(* ::Section:: *)
(*1*)


(*1/2,1/2,0,0*)
dimFrom = 5;
GenSection@{"e-", "e+", "h", "h"};
GenSection@{"ve", "ve", "h", "h"};
GenSection@{"ve", "vmu", "h", "h"};
GenSection@{"u", "ubar", "h", "h"};

(*1,0,0,0*)
dimFrom = 6;
GenSection@{"Z", "h", "h", "h"};
(*GenSection@{"g", "h", "h", "h"};*)
GenSection@{"gamma", "h", "h", "h"};



(* ::Section:: *)
(*2*)


(*1,1,0,0*)
dimFrom = 4;
GenSection@{"Z", "Z", "h", "h"};
(*GenSection@{"Z", "g", "h", "h"};*)
GenSection@{"Z", "gamma", "h", "h"};
GenSection@{"g", "g", "h", "h"};
(*GenSection@{"g", "gamma", "h", "h"};*)
GenSection@{"gamma", "gamma", "h", "h"};
GenSection@{"W+", "W-", "h", "h"};

(*1/2,1/2,1/2,1/2*)
(*no charge*)
dimFrom = 6;
GenSection@{"ve", "vebar", "vmu", "vmubar"};
GenSection@{"ve", "ve", "vmu", "vmu"};
GenSection@{"ve", "ve", "ve", "vmu"};
GenSection@{"ve", "ve", "ve", "ve"};

(*charge 1/2+0*)
GenSection@{"e-", "e+", "ve", "vmu"};
GenSection@{"e-", "e+", "ve", "ve"};
(*charge 2/3+0*)
GenSection@{"u", "ubar", "ve", "vmu"};
GenSection@{"u", "ubar", "ve", "ve"};
(*charge 1/3+0 <==> 2/3+0*)
(*charge 1/2+1/2*)
GenSection@{"e-", "e+", "mu-", "mu+"};
GenSection@{"e-", "e+", "e-", "e+"};

(*charge 2/3+1/2*)
GenSection@{"u", "ubar", "e-", "e+"};

(*charge 2/3+2/3*)
GenSection@{"u", "ubar", "d", "dbar"};
GenSection@{"u", "ubar", "u", "ubar"};

(*charge -1/3*3+1*)
GenSection@{"d", "d", "d", "e+"};

(*1,1/2,1/2,0*)
dimFrom = 5;
GenSection@{"gamma", "ve", "vmu", "h"};
GenSection@{"Z", "ve", "vmu", "h"};
(*GenSection@{"g", "ve", "vmu", "h"};*)
GenSection@{"gamma", "ve", "ve", "h"};
GenSection@{"Z", "ve", "ve", "h"};
(*GenSection@{"g", "ve", "ve", "h"};*)

GenSection@{"gamma", "e-", "e+", "h"};
GenSection@{"Z", "e-", "e+", "h"};
(*GenSection@{"g", "e-", "e+", "h"};*)

GenSection@{"gamma", "u", "ubar", "h"};
GenSection@{"Z", "u", "ubar", "h"};
(*GenSection@{"g", "u", "ubar", "h"};*)


(* ::Section:: *)
(*3*)


(*1,1,1,0*)
dimFrom = 4;
GenSection@{"Z", "Z", "Z", "h"};
GenSection@{"g", "g", "g", "h"};
GenSection@{"gamma", "gamma", "gamma", "h"};

GenSection@{"Z", "Z", "gamma", "h"};
GenSection@{"Z", "gamma", "gamma", "h"};
(*GenSection@{"Z", "Z", "g", "h"};*)
GenSection@{"Z", "g", "g", "h"};
GenSection@{"g", "g", "gamma", "h"};
(*GenSection@{"g", "gamma", "gamma", "h"};*)

GenSection@{"W+", "W-", "Z", "h"};
(*GenSection@{"W+", "W-", "g", "h"};*)
GenSection@{"W+", "W-", "gamma", "h"};
(*GenSection@{"Z", "g", "gamma", "h"};*)

(*1,1,1/2,1/2*)
dimFrom = 5;
GenSection@{"Z", "Z", "ve", "vmu"};
GenSection@{"Z", "Z", "ve", "ve"};
GenSection@{"Z", "Z", "e-", "e+"};
GenSection@{"Z", "Z", "u", "ubar"};
GenSection@{"gamma", "gamma", "ve", "vmu"};
GenSection@{"gamma", "gamma", "ve", "ve"};
GenSection@{"gamma", "gamma", "e-", "e+"};
GenSection@{"gamma", "gamma", "u", "ubar"};
GenSection@{"g", "g", "ve", "vmu"};
GenSection@{"g", "g", "ve", "ve"};
GenSection@{"g", "g", "e-", "e+"};
GenSection@{"g", "g", "u", "ubar"};

(*GenSection@{"Z", "g", "ve", "vmu"};*)
(*GenSection@{"Z", "g", "ve", "ve"};*)
(*GenSection@{"Z", "g", "e-", "e+"};*)
(*GenSection@{"Z", "g", "u", "ubar"};*)
GenSection@{"Z", "gamma", "ve", "vmu"};
GenSection@{"Z", "gamma", "ve", "ve"};
GenSection@{"Z", "gamma", "e-", "e+"};
GenSection@{"Z", "gamma", "u", "ubar"};
(*GenSection@{"g", "gamma", "ve", "vmu"};*)
(*GenSection@{"g", "gamma", "ve", "ve"};*)
(*GenSection@{"g", "gamma", "e-", "e+"};*)
(*GenSection@{"g", "gamma", "u", "ubar"};*)
GenSection@{"W+", "W-", "ve", "vmu"};
GenSection@{"W+", "W-", "ve", "ve"};
GenSection@{"W+", "W-", "e-", "e+"};
GenSection@{"W+", "W-", "u", "ubar"};


(* ::Section:: *)
(*4*)


(*1,1,1,1*)
dimFrom = 4;
GenSection@{"Z", "Z", "Z", "Z"};
(*GenSection@{"g", "g", "g", "g"};*)
(*GenSection@{"gamma", "gamma", "gamma", "gamma"};*)

(*GenSection@{"Z", "Z", "Z", "g"};*)
GenSection@{"Z", "Z", "g", "g"};
GenSection@{"Z", "g", "g", "g"};
GenSection@{"Z", "Z", "Z", "gamma"};
GenSection@{"Z", "Z", "gamma", "gamma"};
GenSection@{"Z", "gamma", "gamma", "gamma"};
(*GenSection@{"g", "g", "g", "gamma"};*)
(*GenSection@{"g", "g", "gamma", "gamma"};*)
(*GenSection@{"g", "gamma", "gamma", "gamma"};*)

(*GenSection@{"Z", "Z", "g", "gamma"};*)
GenSection@{"g", "g", "Z", "gamma"};
(*GenSection@{"gamma", "gamma", "Z", "g"};*)

GenSection@{"W+", "W-", "W+", "W-"};
GenSection@{"W+", "W-", "Z", "Z"};
GenSection@{"W+", "W-", "g", "g"};
GenSection@{"W+", "W-", "gamma", "gamma"};
(*GenSection@{"W+", "W-", "Z", "g"};*)
GenSection@{"W+", "W-", "Z", "gamma"};
(*GenSection@{"W+", "W-", "g", "gamma"};*)

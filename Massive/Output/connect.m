(* ::Package:: *)

path=FileNameDrop[If[$InputFileName==="",NotebookFileName[],$InputFileName],-1];


re="";


If[Length@FileNames["result.txt",path]!=0,FileNameJoin[{path,"result.txt"}]//DeleteFile];
files=FileNames[__~~"txt",path,2];


rule={
"\\section{Type:"~~Shortest[e__]~~"}":>"\\section{Type: $"~~e~~"$}"};
(*"$$\n\\text{None}\n$$"\[Rule]"None\n",
"$$\n{}$$"\[Rule]"None\n",
"$$\n\\begin{array}{l}"\[Rule]"",
"\\end{array}\n$$"\[Rule]"",
"\t"~~Shortest[expr__]~~"\\\\":>"$$\n"<>expr<>"\n$$"};*)
rule2 = {
"$$\n$$"->"$$\n\n$$",
"vmubar"->" \\bar{\\nu}_\\mu ",
"vebar"->" \\bar{\\nu}_e ",
"e+"->" e^+ ",
"e-"->" e^- ",
"mu+"->"\\mu^+ ",
"mu-"->" \\mu^- ",
"W+"->" W^+ ",
"W-"->" W^- ",
"g+"->" g^+ ",
"g-"->" g^- ",
"gamma+"->" \\gamma^+ ",
"gamma-"->" \\gamma^- ",
"uubar"->" u\\bar{u} ",
"dbar"->" \\bar{d} ",
"ve"->" \\nu_e ",
"vmu"->" \\nu_\\mu "
};
rule3=RegularExpression["\\\\section\{.*\}\n+(\\\\section\{.*\})"]->"$1";


Do[
s=Import[f];
re=re<>StringReplace[StringReplace[s,rule],rule2];
,{f,files}];
fileOut = FileNameJoin[{path,"result.txt"}];
CreateFile[fileOut];
Export[fileOut,StringReplace[re,rule3]];

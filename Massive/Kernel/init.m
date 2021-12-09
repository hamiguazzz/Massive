(* ::Package:: *)
$DEBUG = True;
Print["initializing..."];
If[$DEBUG =!= True, $DEBUG = False;];
$MassiveDir = FileNameDrop[
  If[$InputFileName === "", NotebookFileName[], $InputFileName]
  , -2];
$CodeFiles = FileNames[__ ~~ ".m", FileNameJoin[{$MassiveDir, "Codes"}]];
Print["Codes Files:", $CodeFiles];
Get[FileNameJoin[{$MassiveDir, "MassiveBasis.m"}]]




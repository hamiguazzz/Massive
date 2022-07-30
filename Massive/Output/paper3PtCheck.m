(*Import*)
Check3PtPaperResult[spins_List,masses_,expection_Integer]:=(Print@(Length@#===expection);Print@MatrixForm@#;)&@Construct3PBasis[spins,mass->masses];

Check3PtPaperResult[{1/2,1/2,0},{1,2},2]

Check3PtPaperResult[{1/2,1/2,0},{3},1]

Check3PtPaperResult[{1/2,1/2,1},{1,2},1]

Check3PtPaperResult[{1/2,1/2,-1},{1,2},1]

Check3PtPaperResult[{1/2,1/2,-1},{1,2},1]

Check3PtPaperResult[{1/2,1/2,1},All,4]

Check3PtPaperResult[{1,1/2,1/2},{1,2},2]

Check3PtPaperResult[{1,1/2,-1/2},{1,2},2]

Check3PtPaperResult[{1,1/2,-1/2},{1},1]

Check3PtPaperResult[{1,1/2,1/2},{1},1]

Check3PtPaperResult[{0,1,1},{1},1]

Check3PtPaperResult[{0,-1,-1},{1},1]

Check3PtPaperResult[{1,0,1},{1,2},1]

Check3PtPaperResult[{1,1,0},All,3]

Check3PtPaperResult[{1,1,1},{1,2},2]

Check3PtPaperResult[{1,1,1},All,7]

ExportAmpMassive2Tex[3]/@Construct3PBasis[{1,1,1},mass->All]//ExportTexList2Array


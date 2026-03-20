(* ::Package:: *)

(* ::Input::Initialization:: *)
RealRepQ[{x_,y_,{z_}}]:=x==0&&(y==Reverse[y])&&EvenQ[z]
ConjugateRepUV[{u1s__,su3_,su2_,spin_}]:=Join[-1*{u1s},{Reverse[su3],su2,spin}]
ConjugateRepUV[fname_String]:=Switch[fname,"W"|"B"|"G",fname,_,StringReplace[fname<>"\[Dagger]","\[Dagger]\[Dagger]"->""]]
QNSMMap=<|{1/2,{0,0},{1},0}->"H",{-(1/2),{0,0},{1},0}->"H\[Dagger]",{1,{0,0},{0},1/2}->"ec",{-1,{0,0},{0},1/2}->"ec\[Dagger]",{-(1/3),{1,0},{0},1/2}->"dc\[Dagger]",{1/3,{0,1},{0},1/2}->"dc",{1/6,{1,0},{1},1/2}->"Q",{-(1/6),{0,1},{1},1/2}->"Q\[Dagger]",{0,{0,0},{0},1}->"B",{0,{0,0},{2},1}->"W",{0,{1,1},{0},1}->"G"|>;
Get[NotebookDirectory[]<>"Partitions.m"];
NonRe4ptQ[x_List]:=And@@(Cases[#/.{"H"->Nothing,"H\[Dagger]"->Nothing},_String]=={}&/@Select[x,Length[#]>=4&]);
ConjVertQ[vert1_,vert2_]:=Module[{tvert1=vert1/. Style[x_,__]:>x,tvert2=vert2/. Style[x_,__]:>x},Sort[tvert1]==Sort[tvert2]||Sort[tvert1]==Sort[ConjugateRepUV/@tvert2]]
CleanConjugateVert2[vertlist_]:=DeleteCases[DeleteDuplicates[vertlist/.{"WL"|"WR"->"W","BL"|"BR"->"B","GL"|"GR"->"G"},ConjVertQ],{"GL"|"WL"|"BL"|"GR"|"WR"|"BR"|"W"|"B"|"G",x__}/;ConjugateRepUV/@{x}==Reverse[{x}]]
MaxnptQ[partition_,npar_,n_]:=Module[{part,hcy=<||>},part=UnionFinder[parsePart[partition,npar]];
(HierarchyFinder[hcy,#1]&)/@part;
hcy=DeleteCases[hcy,{{_}}];
Sort[Length/@Append[KeyValueMap[Append[#2,#1]&,hcy],part[[1;;,1]]]][[-1]]<=n]


(* ::Input::Initialization:: *)
(*EOM related*)
ClearAll[GetUVsForAsso]
GetUVsForAsso[model_,asso_,type_]:=Module[{vertprop,tprop,verticeslist,UVs,SMUVlist,PureUVlist,SMUVsubsets,SMUVsubsetsMap,SMUVremainMap2,UVsEOM,verticeslistEOM,result},
vertprop=GetVerticesAll[model,asso,type];
verticeslist=Sort[Sort/@DeleteDuplicates[vertprop[[1]],#1==#2||Sort[#1]==Sort[ConjugateRepUV/@#2]&]];
UVs=Sort[DeleteDuplicates[vertprop[[2]]/.{w_,x_,y_,z_}:>{-w,Reverse[x],y,z}/;((OrderedQ[x]&&UnsameQ@@x)||(SameQ@@x&&w<0))]];
tprop=DeleteDuplicatesBy[Cases[Flatten[vertprop[[3]],1],_List],Last];
SMUVlist=Select[tprop,MemberQ[Keys@QNSMMap,#[[1]]]&];
SMUVsubsets=DeleteCases[Subsets[SMUVlist],{}|tprop];
UVsEOM=(Complement[tprop,#]&/@SMUVsubsets)/.{x_List,_Integer}->x;
If[UVsEOM=!={},
SMUVsubsetsMap=MapAt[Rule[#,QNSMMap[#[[1]]]]&,SMUVsubsets,{All,All}];
UVsEOM=Sort[#/.{w_,x_,y_,z_}:>{-w,Reverse[x],y,z}/;((OrderedQ[x]&&UnsameQ@@x)||(SameQ@@x&&w<0))]&/@(DeleteDuplicates[#,#1==#2||Sort[#1]==ConjugateRepUV[#2]&]&/@UVsEOM);
verticeslistEOM=((Sort/@#)&/@(DeleteCases[#,{_String..}]&/@((vertprop[[3]]/.#)&/@SMUVsubsetsMap)))/.{x_List,_Rational|_Integer}:>x;
Do[SMUVremainMap2=Rule[#,QNSMMap[#]]&/@Complement[Cases[Flatten[verticeslistEOM[[ith]],1],{_,{_,_},{_},_}],Flatten[{#,ConjugateRepUV[#]}&/@UVsEOM[[ith]],1]];
verticeslistEOM[[ith]]=Sort[Sort/@DeleteCases[verticeslistEOM[[ith]]/.SMUVremainMap2,{_String..}]];
,{ith,Length[UVsEOM]}];
verticeslistEOM=Sort/@(DeleteDuplicates[#,#1==#2||Sort[#1]==Sort[ConjugateRepUV/@#2]&]&/@verticeslistEOM);
(*verticeslistEOM=CleanConjugateVert2[verticeslistEOM];*)
result=Prepend[<|"New Fields"->Sort@#[[1]],"vertices"->CleanConjugateVert2[Sort[Sort/@#[[2]]]]|>&/@Transpose@{UVsEOM,verticeslistEOM},<|"New Fields"->UVs,"vertices"->CleanConjugateVert2[verticeslist]|>];,
result={<|"New Fields"->UVs,"vertices"->CleanConjugateVert2[verticeslist]|>};
];
(*MapAt[If[GetHelorSpin[model,#]\[LessEqual]0,#,Style[#,Red]]&,result,{All,2,All}]*)(*Print[result];*)
result
]
GetFbasisInd[jcoord_,BasisAll_,BasisNfSelect_,Kmp_,containrepeat_]:=Module[{lenlist,fbasisind,lenlist1,pospfmap,pospselmap},
If[(!containrepeat),Return[Union@Flatten[SparseArray[jcoord . Kmp]["AdjacencyLists"]]]];
lenlist=KeyValueMap[ConstantArray[(Times@@SnIrrepDim/@Association@#1),Length[#2]]&,BasisNfSelect["p-basis"]];
fbasisind=Range[Total[Length/@lenlist]];
lenlist1=Total/@lenlist;
pospfmap=Association@Thread[Rule[Range[Total[lenlist1]],Flatten[MapThread[ConstantArray[#1,#2]&,{fbasisind,Flatten[lenlist]}]]]];
pospselmap=Association@Thread[Rule[Flatten[Position[BasisAll["Kpm"],#]&/@BasisNfSelect["Kpm"]],Range[Length[BasisNfSelect["Kpm"]]]]];
Union[pospfmap/@(pospselmap/@Flatten[Intersection[Keys@pospselmap,Union@Flatten[SparseArray[jcoord . Kmp]["AdjacencyLists"]]]])]
]
GetHelorSpinAUX[model_,flist_]:=DimCoupling[Select[model[#]["helicity"]&/@flist,NumberQ],Cases[flist,_List][[All,-1]]]
Clear[GetHelorSpin]
GetHelorSpin[model_,flist_List]:=GetHelorSpin[model,flist]=Module[{tflist},
If[MemberQ[flist,"W"|"B"|"G"],tflist=Distribute[flist/.{x_,{y__},{z_},w_}:>protect[{x,{y},{z},w}]/.{"B"->{"BL","BR"},"W"->{"WL","WR"},"G"->{"GL","GR"}},List]/.protect->Identity;
Sort[GetHelorSpinAUX[model,#]&/@tflist][[1]]
,GetHelorSpinAUX[model,flist]
]]
GetHelorSpin[model_,Style[flist_,_]]:=GetHelorSpin[model,flist]
DimSelect[model_,verts_,dimop_]:=Module[{nprop,nfprop,dcp,dim},
nprop=Length[verts[[2]]];
nfprop=Count[verts[[2]],{__,j_/;!IntegerQ[j]}];
dcp=DimCoupling@@@(GetHelandSpin[SMEFT,#]&/@verts[[1]]);
dim=Total[dcp]+2nprop-nfprop;
{dimop-dim>=4,dcp}]


(* ::Input::Initialization:: *)
Clear[GetVerticesPrime]
GetVerticesPrime[partition_,tmaps_,npar_]:=Module[{tkey,part,hcy=<||>},
part=UnionFinder[parsePart[partition,npar]];
(HierarchyFinder[hcy,#1]&)/@part;
hcy=DeleteCases[hcy,{{_}}];
And@@(#=={}&/@(DeleteCases[Cases[#,_String],"H"|"H\[Dagger]"]&/@MapAt[tmaps,Select[DeleteCases[Append[KeyValueMap[Append[#2,#1]&,hcy],part[[1;;,1]]],{_,_}],Length[#]>=4&],{All,All}]))
]
Clear[SameUVQList];
SameUVQList[uv1_List,uv2_List]:=Module[{tuv1=uv1/.Style[x_,__]:>x,tuv2=uv2/.Style[x_,__]:>x},
tuv1==DeleteDuplicates[Join[tuv1,tuv2],#1==#2||(Sort[#1]==Sort[ConjugateRepUV/@#2])&]&&tuv2==DeleteDuplicates[Join[tuv2,tuv1],#1==#2||(Sort[#1]==Sort[ConjugateRepUV/@#2])&]]
ContainInvalidQ[model_,verts_]:=MemberQ[GetHelorSpin[model,#]&/@verts,DirectedInfinity[1]]
ClearAll[GetUVsForTypePartAux];
Options[GetUVsForTypePartAux]={Charges->{"U1y"}};
GetUVsForTypePartAux[model_,type_,part_,containrepeat_,lenfbasis_,BasisAll_,BasisNfSelect_,Kmp_,OptionsPattern[]]:=Module[{JbasisPart,tUVs,tfbasis,result,BasisAllmb,permutej},
result=Association@Thread[Rule[Range[lenfbasis],ConstantArray[{},lenfbasis]]];
JbasisPart=GetJBasisForType[model,type,part,Charges->OptionValue[Charges],SelectCoupling->True];
BasisAllmb=If[containrepeat,BasisAll["m-basis"],BasisAll[{}]];
permutej=FindPermutation[JbasisPart["basis"],BasisAllmb];
Do[
tUVs=GetUVsForAsso[model,KeyDrop[item[[1]],"allowed"],type];
tfbasis=GetFbasisInd[Permute[#,permutej]&/@item[[2]],BasisAll,BasisNfSelect,Kmp,containrepeat];
AppendTo[result[#],tUVs]&/@tfbasis;
,{item,Select[JbasisPart["j-basis"],(#[[1]]["allowed"])[[1]]==True&]}];
result
]
(*The Function that combine the result from all the partition*)
Options[GetUVsForType]={OneFlavor->False};
GetUVsForType[model_,type_,OptionsPattern[]]:=Module[{particles,npar,tmaps,ct,npt,nfield,partitionlist,partlen,BasisDeSym,BasisAll,BasisNfSelect,JbasisPart,lenfbasis,result,tUVs,Kmp,tfbasis,containrepeat},
ct=CheckType[model,type];
nfield=Total@ct[[All,2]];
If[nfield<8&&Total@Cases[ct,{"H\[Dagger]"|"H",x_}:>x]<=1,npt=3;
partitionlist=Partitions[npt,nfield];,
npt=4;
particles=CheckType[model,type,Counting->False];
npar=Length[particles];
tmaps=Association@MapThread[Rule[#1,#2]&,{Array[List,npar],particles}];
partitionlist=Select[Partitions[npt,nfield],GetVerticesPrime[#,tmaps,npar]&];
];
partlen=Length[partitionlist];
containrepeat=Length[ct[[All,2]]/.{1->Nothing}]>0;
BasisDeSym=If[containrepeat, Flatten[Thread[#,List,-1]&/@Normal[GetBasisForType[model,type]]],Flatten[Values@GetBasisForType[model,type]]];
lenfbasis=Length@BasisDeSym;If[lenfbasis==0,Return[]];
BasisAll=GetBasisForType[model,type,NfSelect->False,DeSym->False];
If[containrepeat,Kmp=Inverse@BasisAll["Kpm"];
BasisNfSelect=GetBasisForType[model,type,NfSelect->True,DeSym->False];,
Kmp=IdentityMatrix[lenfbasis];BasisNfSelect=BasisAll;];
(*Iterate over partitions*)
result=Monitor[Table[GetUVsForTypePartAux[model,type,partitionlist[[ith]],containrepeat,lenfbasis,BasisAll,BasisNfSelect,Kmp],{ith,1,partlen}],ToString[ith]<>"/"<>ToString[partlen]];
result=Flatten/@Merge[result,Identity];
result=(DeleteDuplicates[#]&/@result);
result=((DeleteDuplicates[#1,SameUVQList]&)/@#)&/@(GroupBy[#,First->Last]&/@result);
If[npt==4,result=DeleteCases[#,{}]&/@MapAt[Select[#,NonRe4ptQ]&,result,{All,All}],result];
result=KeyValueMap[<|"New Fields"->#1,"Vertices List"->#2|>&,#]&/@result;
(*Label the non-renormalizable vertex in Red color*)
result=MapAt[If[GetHelorSpin[model,#]<=0,#,Style[#,Red]]&,result,{All,All,2,All,All}];
result=<|"basis"->Association@MapThread[Rule[#1,#2]&,{Range[lenfbasis],BasisDeSym/.Rule[x1_,y1_]:>{x1,y1}}],"UVs"->result|>;
If[OptionValue[OneFlavor]&&containrepeat,
result["basis"]=Select[result["basis"],FreeQ[Length/@#[[1,1;;,2]],2]&];
result["UVs"]=KeyDrop[result["UVs"],Complement[Range[lenfbasis],Keys@result["basis"]]];
];
result
]


(* ::Input::Initialization:: *)
(*Minor modification of this core function to adapt the different method in computing y-basis in GetBasisForType and GetJBasisForType*)
LorentzJBasis[state_,k_,partition_]:=Module[{jEigen={},jbasisAll,jcomb,Num=Length[state],flip=1,ybasis,result},
If[{Num-2,2} . yngShape[state,k]>{Num-2,2} . yngShape[-state,k],flip=-flip];
ybasis=SSYT[flip state,k,OutMode->"amplitude"];
If[flip==-1,ybasis=ybasis/. {ab->sb,sb->ab};];
result=Association["basis"->ybasis];jbasisAll=(W2Diagonalize[state,k,#1,OutputFormat->"working"]&)/@partition;Do[AppendTo[jEigen,Map[jB["transfer"][[#1]]&,PositionIndex[jB["j"]],{2}]],{jB,jbasisAll}];jcomb=(AssociationThread[partition->#1]&)/@Distribute[Keys/@jEigen,List];Append[result,"jcoord"->Normal[DeleteCases[AssociationMap[LinearIntersection@@MapThread[#1[#2]&,{jEigen,Values[#1]}]&,jcomb],{}]]]]

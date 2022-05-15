(* ::Package:: *)

reduceObjects[objects_List, {}] := objects
reduceObjects[objects_List, objectEquivalences_List] := 
  reduceObjects[DeleteDuplicates[objects /. First[First[objectEquivalences]] -> Last[First[objectEquivalences]]], 
    Drop[DeleteDuplicates[objectEquivalences /. First[First[objectEquivalences]] -> Last[First[objectEquivalences]]], 
     1]] /; Length[objectEquivalences] > 0
reduceArrowsInitial[arrows_Association, {}] := arrows
reduceArrowsInitial[arrows_Association, arrowEquivalences_List] := 
  reduceArrowsInitial[Association[DeleteDuplicatesBy[Normal[arrows] /. First[First[arrowEquivalences]] -> 
        Last[First[arrowEquivalences]], First]], 
    Drop[DeleteDuplicates[arrowEquivalences /. First[First[arrowEquivalences]] -> Last[First[arrowEquivalences]]], 1]] /; 
   Length[arrowEquivalences] > 0
reduceArrowsFinal[arrows_Association, {}] := arrows
reduceArrowsFinal[arrows_Association, objectEquivalences_List] := 
  reduceArrowsFinal[Association[Normal[arrows] /. First[First[objectEquivalences]] -> Last[First[objectEquivalences]]], 
    Drop[DeleteDuplicates[objectEquivalences /. First[First[objectEquivalences]] -> Last[First[objectEquivalences]]], 
     1]] /; Length[objectEquivalences] > 0
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "Objects"] := Join[morphismDomains, {commonImage, pullbackSymbol @@ morphismDomains}]
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "ObjectCount"] := Length[Join[morphismDomains, {commonImage, pullbackSymbol @@ morphismDomains}]]
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "MorphismAssociation"] := 
  Association[Join[(morphismNames[[#1]] -> DirectedEdge[morphismDomains[[#1]], commonImage] & ) /@ 
     Range[Length[morphismDomains]], (projectionMorphismNames[[#1]] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
        morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
    (compositionSymbol[morphismNames[[#1]], projectionMorphismNames[[#1]]] -> 
       DirectedEdge[pullbackSymbol @@ morphismDomains, commonImage] & ) /@ Range[Length[morphismDomains]], 
    (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ morphismDomains, 
    {identitySymbol[commonImage] -> DirectedEdge[commonImage, commonImage], 
     identitySymbol[pullbackSymbol @@ morphismDomains] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
       pullbackSymbol @@ morphismDomains]}]]
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "MorphismNames"] := 
  First /@ Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[morphismDomains[[#1]], commonImage] & ) /@ 
       Range[Length[morphismDomains]], (projectionMorphismNames[[#1]] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
          morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
      (compositionSymbol[morphismNames[[#1]], projectionMorphismNames[[#1]]] -> 
         DirectedEdge[pullbackSymbol @@ morphismDomains, commonImage] & ) /@ Range[Length[morphismDomains]], 
      (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ morphismDomains, 
      {identitySymbol[commonImage] -> DirectedEdge[commonImage, commonImage], 
       identitySymbol[pullbackSymbol @@ morphismDomains] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
         pullbackSymbol @@ morphismDomains]}]]]
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "MorphismEdges"] := (DirectedEdge @@ Last[#1] & ) /@ 
   Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[morphismDomains[[#1]], commonImage] & ) /@ 
       Range[Length[morphismDomains]], (projectionMorphismNames[[#1]] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
          morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
      (compositionSymbol[morphismNames[[#1]], projectionMorphismNames[[#1]]] -> 
         DirectedEdge[pullbackSymbol @@ morphismDomains, commonImage] & ) /@ Range[Length[morphismDomains]], 
      (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ morphismDomains, 
      {identitySymbol[commonImage] -> DirectedEdge[commonImage, commonImage], 
       identitySymbol[pullbackSymbol @@ morphismDomains] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
         pullbackSymbol @@ morphismDomains]}]]]
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "MorphismCount"] := 
  Length[Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[morphismDomains[[#1]], commonImage] & ) /@ 
       Range[Length[morphismDomains]], (projectionMorphismNames[[#1]] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
          morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
      (compositionSymbol[morphismNames[[#1]], projectionMorphismNames[[#1]]] -> 
         DirectedEdge[pullbackSymbol @@ morphismDomains, commonImage] & ) /@ Range[Length[morphismDomains]], 
      (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ morphismDomains, 
      {identitySymbol[commonImage] -> DirectedEdge[commonImage, commonImage], 
       identitySymbol[pullbackSymbol @@ morphismDomains] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
         pullbackSymbol @@ morphismDomains]}]]]]
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "ReducedMorphismAssociation"] := 
  Association[Join[(morphismNames[[#1]] -> DirectedEdge[morphismDomains[[#1]], commonImage] & ) /@ 
     Range[Length[morphismDomains]], (projectionMorphismNames[[#1]] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
        morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
    {compositionSymbol[Last[morphismNames], Last[projectionMorphismNames]] -> 
      DirectedEdge[pullbackSymbol @@ morphismDomains, commonImage]}, (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ 
     morphismDomains, {identitySymbol[commonImage] -> DirectedEdge[commonImage, commonImage], 
     identitySymbol[pullbackSymbol @@ morphismDomains] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
       pullbackSymbol @@ morphismDomains]}]]
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "ReducedMorphismNames"] := 
  First /@ Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[morphismDomains[[#1]], commonImage] & ) /@ 
       Range[Length[morphismDomains]], (projectionMorphismNames[[#1]] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
          morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
      {compositionSymbol[Last[morphismNames], Last[projectionMorphismNames]] -> 
        DirectedEdge[pullbackSymbol @@ morphismDomains, commonImage]}, (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ 
       morphismDomains, {identitySymbol[commonImage] -> DirectedEdge[commonImage, commonImage], 
       identitySymbol[pullbackSymbol @@ morphismDomains] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
         pullbackSymbol @@ morphismDomains]}]]]
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "ReducedMorphismEdges"] := (DirectedEdge @@ Last[#1] & ) /@ 
   Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[morphismDomains[[#1]], commonImage] & ) /@ 
       Range[Length[morphismDomains]], (projectionMorphismNames[[#1]] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
          morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
      {compositionSymbol[Last[morphismNames], Last[projectionMorphismNames]] -> 
        DirectedEdge[pullbackSymbol @@ morphismDomains, commonImage]}, (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ 
       morphismDomains, {identitySymbol[commonImage] -> DirectedEdge[commonImage, commonImage], 
       identitySymbol[pullbackSymbol @@ morphismDomains] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
         pullbackSymbol @@ morphismDomains]}]]]
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "ReducedMorphismCount"] := 
  Length[Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[morphismDomains[[#1]], commonImage] & ) /@ 
       Range[Length[morphismDomains]], (projectionMorphismNames[[#1]] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
          morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
      {compositionSymbol[Last[morphismNames], Last[projectionMorphismNames]] -> 
        DirectedEdge[pullbackSymbol @@ morphismDomains, commonImage]}, (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ 
       morphismDomains, {identitySymbol[commonImage] -> DirectedEdge[commonImage, commonImage], 
       identitySymbol[pullbackSymbol @@ morphismDomains] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
         pullbackSymbol @@ morphismDomains]}]]]]
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "SimpleMorphismAssociation"] := 
  Association[Join[(morphismNames[[#1]] -> DirectedEdge[morphismDomains[[#1]], commonImage] & ) /@ 
     Range[Length[morphismDomains]], (projectionMorphismNames[[#1]] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
        morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
    {compositionSymbol[First[morphismNames], First[projectionMorphismNames]] -> 
      DirectedEdge[pullbackSymbol @@ morphismDomains, commonImage]}]]
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "SimpleMorphismNames"] := 
  First /@ Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[morphismDomains[[#1]], commonImage] & ) /@ 
       Range[Length[morphismDomains]], (projectionMorphismNames[[#1]] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
          morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
      {compositionSymbol[First[morphismNames], First[projectionMorphismNames]] -> 
        DirectedEdge[pullbackSymbol @@ morphismDomains, commonImage]}]]]
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "SimpleMorphismEdges"] := (DirectedEdge @@ Last[#1] & ) /@ 
   Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[morphismDomains[[#1]], commonImage] & ) /@ 
       Range[Length[morphismDomains]], (projectionMorphismNames[[#1]] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
          morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
      {compositionSymbol[First[morphismNames], First[projectionMorphismNames]] -> 
        DirectedEdge[pullbackSymbol @@ morphismDomains, commonImage]}]]]
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "SimpleMorphismCount"] := 
  Length[Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[morphismDomains[[#1]], commonImage] & ) /@ 
       Range[Length[morphismDomains]], (projectionMorphismNames[[#1]] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
          morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
      {compositionSymbol[First[morphismNames], First[projectionMorphismNames]] -> 
        DirectedEdge[pullbackSymbol @@ morphismDomains, commonImage]}]]]]
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "ReducedSimpleMorphismAssociation"] := 
  Association[Join[(morphismNames[[#1]] -> DirectedEdge[morphismDomains[[#1]], commonImage] & ) /@ 
     Range[Length[morphismDomains]], (projectionMorphismNames[[#1]] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
        morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
    {compositionSymbol[Last[morphismNames], Last[projectionMorphismNames]] -> 
      DirectedEdge[pullbackSymbol @@ morphismDomains, commonImage]}]]
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "ReducedSimpleMorphismNames"] := 
  First /@ Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[morphismDomains[[#1]], commonImage] & ) /@ 
       Range[Length[morphismDomains]], (projectionMorphismNames[[#1]] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
          morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
      {compositionSymbol[Last[morphismNames], Last[projectionMorphismNames]] -> 
        DirectedEdge[pullbackSymbol @@ morphismDomains, commonImage]}]]]
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "ReducedSimpleMorphismEdges"] := (DirectedEdge @@ Last[#1] & ) /@ 
   Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[morphismDomains[[#1]], commonImage] & ) /@ 
       Range[Length[morphismDomains]], (projectionMorphismNames[[#1]] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
          morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
      {compositionSymbol[Last[morphismNames], Last[projectionMorphismNames]] -> 
        DirectedEdge[pullbackSymbol @@ morphismDomains, commonImage]}]]]
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "ReducedSimpleMorphismCount"] := 
  Length[Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[morphismDomains[[#1]], commonImage] & ) /@ 
       Range[Length[morphismDomains]], (projectionMorphismNames[[#1]] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
          morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
      {compositionSymbol[Last[morphismNames], Last[projectionMorphismNames]] -> 
        DirectedEdge[pullbackSymbol @@ morphismDomains, commonImage]}]]]]
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalObjects"] := Join[morphismDomains, {commonImage, pullbackSymbol @@ morphismDomains, 
    Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]}]
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalObjectCount"] := Length[Join[morphismDomains, {commonImage, pullbackSymbol @@ morphismDomains, 
     Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]}]]
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalMorphismAssociation"] := 
  Association[Join[(morphismNames[[#1]] -> DirectedEdge[morphismDomains[[#1]], commonImage] & ) /@ 
     Range[Length[morphismDomains]], (projectionMorphismNames[[#1]] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
        morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
    (Subscript["\[ForAll]", ToString[universalMorphismNames[[#1]], StandardForm]] -> 
       DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], morphismDomains[[#1]]] & ) /@ 
     Range[Length[morphismDomains]], (compositionSymbol[morphismNames[[#1]], projectionMorphismNames[[#1]]] -> 
       DirectedEdge[pullbackSymbol @@ morphismDomains, commonImage] & ) /@ Range[Length[morphismDomains]], 
    (compositionSymbol[projectionMorphismNames[[#1]], uniqueMorphismName] -> 
       DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], morphismDomains[[#1]]] & ) /@ 
     Range[Length[morphismDomains]], (compositionSymbol[morphismNames[[#1]], universalMorphismNames[[#1]]] -> 
       DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], commonImage] & ) /@ 
     Range[Length[morphismDomains]], 
    (compositionSymbol[compositionSymbol[morphismNames[[#1]], projectionMorphismNames[[#1]]], uniqueMorphismName] -> 
       DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], commonImage] & ) /@ 
     Range[Length[morphismDomains]], (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ morphismDomains, 
    {identitySymbol[commonImage] -> DirectedEdge[commonImage, commonImage], 
     identitySymbol[pullbackSymbol @@ morphismDomains] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
       pullbackSymbol @@ morphismDomains], identitySymbol[universalObjectName] -> 
      DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], 
       Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]], 
     Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> 
      DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], pullbackSymbol @@ morphismDomains]}]]
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalMorphismNames"] := 
  First /@ Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[morphismDomains[[#1]], commonImage] & ) /@ 
       Range[Length[morphismDomains]], (projectionMorphismNames[[#1]] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
          morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
      (Subscript["\[ForAll]", ToString[universalMorphismNames[[#1]], StandardForm]] -> 
         DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], morphismDomains[[#1]]] & ) /@ 
       Range[Length[morphismDomains]], (compositionSymbol[morphismDomains[[#1]], projectionMorphismNames[[#1]]] -> 
         DirectedEdge[pullbackSymbol @@ morphismDomains, commonImage] & ) /@ Range[Length[morphismDomains]], 
      (compositionSymbol[projectionMorphismNames[[#1]], uniqueMorphismName] -> 
         DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], morphismDomains[[#1]]] & ) /@ 
       Range[Length[morphismDomains]], (compositionSymbol[morphismNames[[#1]], universalMorphismNames[[#1]]] -> 
         DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], commonImage] & ) /@ 
       Range[Length[morphismDomains]], 
      (compositionSymbol[compositionSymbol[morphismNames[[#1]], projectionMorphismNames[[#1]]], uniqueMorphismName] -> 
         DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], commonImage] & ) /@ 
       Range[Length[morphismDomains]], (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ morphismDomains, 
      {identitySymbol[commonImage] -> DirectedEdge[commonImage, commonImage], 
       identitySymbol[pullbackSymbol @@ morphismDomains] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
         pullbackSymbol @@ morphismDomains], identitySymbol[universalObjectName] -> 
        DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], 
         Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]], 
       Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> 
        DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], pullbackSymbol @@ morphismDomains]}]]]
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalMorphismEdges"] := (DirectedEdge @@ Last[#1] & ) /@ 
   Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[morphismDomains[[#1]], commonImage] & ) /@ 
       Range[Length[morphismDomains]], (projectionMorphismNames[[#1]] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
          morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
      (Subscript["\[ForAll]", ToString[universalMorphismNames[[#1]], StandardForm]] -> 
         DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], morphismDomains[[#1]]] & ) /@ 
       Range[Length[morphismDomains]], (compositionSymbol[morphismNames[[#1]], projectionMorphismNames[[#1]]] -> 
         DirectedEdge[pullbackSymbol @@ morphismDomains, commonImage] & ) /@ Range[Length[morphismDomains]], 
      (compositionSymbol[projectionMorphismNames[[#1]], uniqueMorphismName] -> 
         DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], morphismDomains[[#1]]] & ) /@ 
       Range[Length[morphismDomains]], (compositionSymbol[morphismNames[[#1]], universalMorphismNames[[#1]]] -> 
         DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], commonImage] & ) /@ 
       Range[Length[morphismDomains]], 
      (compositionSymbol[compositionSymbol[morphismNames[[#1]], projectionMorphismNames[[#1]]], uniqueMorphismName] -> 
         DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], commonImage] & ) /@ 
       Range[Length[morphismDomains]], (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ morphismDomains, 
      {identitySymbol[commonImage] -> DirectedEdge[commonImage, commonImage], 
       identitySymbol[pullbackSymbol @@ morphismDomains] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
         pullbackSymbol @@ morphismDomains], identitySymbol[universalObjectName] -> 
        DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], 
         Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]], 
       Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> 
        DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], pullbackSymbol @@ morphismDomains]}]]]
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalMorphismCount"] := 
  Length[Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[morphismDomains[[#1]], commonImage] & ) /@ 
       Range[Length[morphismDomains]], (projectionMorphismNames[[#1]] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
          morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
      (Subscript["\[ForAll]", ToString[universalMorphismNames[[#1]], StandardForm]] -> 
         DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], morphismDomains[[#1]]] & ) /@ 
       Range[Length[morphismDomains]], (compositionSymbol[morphismDomains[[#1]], projectionMorphismNames[[#1]]] -> 
         DirectedEdge[pullbackSymbol @@ morphismDomains, commonImage] & ) /@ Range[Length[morphismDomains]], 
      (compositionSymbol[projectionMorphismNames[[#1]], uniqueMorphismName] -> 
         DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], morphismDomains[[#1]]] & ) /@ 
       Range[Length[morphismDomains]], (compositionSymbol[morphismNames[[#1]], universalMorphismNames[[#1]]] -> 
         DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], commonImage] & ) /@ 
       Range[Length[morphismDomains]], 
      (compositionSymbol[compositionSymbol[morphismNames[[#1]], projectionMorphismNames[[#1]]], uniqueMorphismName] -> 
         DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], commonImage] & ) /@ 
       Range[Length[morphismDomains]], (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ morphismDomains, 
      {identitySymbol[commonImage] -> DirectedEdge[commonImage, commonImage], 
       identitySymbol[pullbackSymbol @@ morphismDomains] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
         pullbackSymbol @@ morphismDomains], identitySymbol[universalObjectName] -> 
        DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], 
         Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]], 
       Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> 
        DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], 
         pullbackSymbol @@ morphismDomains]}]]]]
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalReducedMorphismAssociation"] := 
  Association[Join[(morphismNames[[#1]] -> DirectedEdge[morphismDomains[[#1]], commonImage] & ) /@ 
     Range[Length[morphismDomains]], (projectionMorphismNames[[#1]] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
        morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
    {compositionSymbol[Last[morphismNames], Last[projectionMorphismNames]] -> 
      DirectedEdge[pullbackSymbol @@ morphismDomains, commonImage]}, 
    (compositionSymbol[projectionMorphismNames[[#1]], uniqueMorphismName] -> 
       DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], morphismDomains[[#1]]] & ) /@ 
     Range[Length[morphismDomains]], {compositionSymbol[compositionSymbol[Last[morphismNames], 
        Last[projectionMorphismNames]], uniqueMorphismName] -> 
      DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], commonImage]}, 
    (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ morphismDomains, 
    {identitySymbol[commonImage] -> DirectedEdge[commonImage, commonImage], 
     identitySymbol[pullbackSymbol @@ morphismDomains] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
       pullbackSymbol @@ morphismDomains], identitySymbol[universalObjectName] -> 
      DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], 
       Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]], 
     Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> 
      DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], pullbackSymbol @@ morphismDomains]}]]
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalReducedMorphismNames"] := 
  First /@ Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[morphismDomains[[#1]], commonImage] & ) /@ 
       Range[Length[morphismDomains]], (projectionMorphismNames[[#1]] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
          morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
      {compositionSymbol[Last[morphismNames], Last[projectionMorphismNames]] -> 
        DirectedEdge[pullbackSymbol @@ morphismDomains, commonImage]}, 
      (compositionSymbol[projectionMorphismNames[[#1]], uniqueMorphismName] -> 
         DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], morphismDomains[[#1]]] & ) /@ 
       Range[Length[morphismDomains]], {compositionSymbol[compositionSymbol[Last[morphismNames], 
          Last[projectionMorphismNames]], uniqueMorphismName] -> DirectedEdge[Subscript["\[ForAll]", 
          ToString[universalObjectName, StandardForm]], commonImage]}, (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ 
       morphismDomains, {identitySymbol[commonImage] -> DirectedEdge[commonImage, commonImage], 
       identitySymbol[pullbackSymbol @@ morphismDomains] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
         pullbackSymbol @@ morphismDomains], identitySymbol[universalObjectName] -> 
        DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], 
         Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]], 
       Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> 
        DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], pullbackSymbol @@ morphismDomains]}]]]
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalReducedMorphismEdges"] := (DirectedEdge @@ Last[#1] & ) /@ 
   Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[morphismDomains[[#1]], commonImage] & ) /@ 
       Range[Length[morphismDomains]], (projectionMorphismNames[[#1]] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
          morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
      {compositionSymbol[Last[morphismNames], Last[projectionMorphismNames]] -> 
        DirectedEdge[pullbackSymbol @@ morphismDomains, commonImage]}, 
      (compositionSymbol[projectionMorphismNames[[#1]], uniqueMorphismName] -> 
         DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], morphismDomains[[#1]]] & ) /@ 
       Range[Length[morphismDomains]], {compositionSymbol[compositionSymbol[Last[morphismNames], 
          Last[projectionMorphismNames]], uniqueMorphismName] -> DirectedEdge[Subscript["\[ForAll]", 
          ToString[universalObjectName, StandardForm]], commonImage]}, (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ 
       morphismDomains, {identitySymbol[commonImage] -> DirectedEdge[commonImage, commonImage], 
       identitySymbol[pullbackSymbol @@ morphismDomains] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
         pullbackSymbol @@ morphismDomains], identitySymbol[universalObjectName] -> 
        DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], 
         Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]], 
       Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> 
        DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], pullbackSymbol @@ morphismDomains]}]]]
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalReducedMorphismCount"] := 
  Length[Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[morphismDomains[[#1]], commonImage] & ) /@ 
       Range[Length[morphismDomains]], (projectionMorphismNames[[#1]] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
          morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
      {compositionSymbol[Last[morphismNames], Last[projectionMorphismNames]] -> 
        DirectedEdge[pullbackSymbol @@ morphismDomains, commonImage]}, 
      (compositionSymbol[projectionMorphismNames[[#1]], uniqueMorphismName] -> 
         DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], morphismDomains[[#1]]] & ) /@ 
       Range[Length[morphismDomains]], {compositionSymbol[compositionSymbol[Last[morphismNames], 
          Last[projectionMorphismNames]], uniqueMorphismName] -> DirectedEdge[Subscript["\[ForAll]", 
          ToString[universalObjectName, StandardForm]], commonImage]}, (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ 
       morphismDomains, {identitySymbol[commonImage] -> DirectedEdge[commonImage, commonImage], 
       identitySymbol[pullbackSymbol @@ morphismDomains] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
         pullbackSymbol @@ morphismDomains], identitySymbol[universalObjectName] -> 
        DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], 
         Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]], 
       Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> 
        DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], 
         pullbackSymbol @@ morphismDomains]}]]]]
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalSimpleMorphismAssociation"] := 
  Association[Join[(morphismNames[[#1]] -> DirectedEdge[morphismDomains[[#1]], commonImage] & ) /@ 
     Range[Length[morphismDomains]], (projectionMorphismNames[[#1]] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
        morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
    (Subscript["\[ForAll]", ToString[universalMorphismNames[[#1]], StandardForm]] -> 
       DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], morphismDomains[[#1]]] & ) /@ 
     Range[Length[morphismDomains]], {compositionSymbol[First[morphismNames], First[projectionMorphismNames]] -> 
      DirectedEdge[pullbackSymbol @@ morphismDomains, commonImage], 
     compositionSymbol[First[morphismNames], First[universalMorphismNames]] -> 
      DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], commonImage], 
     Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> 
      DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], pullbackSymbol @@ morphismDomains]}]]
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalSimpleMorphismNames"] := 
  First /@ Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[morphismDomains[[#1]], commonImage] & ) /@ 
       Range[Length[morphismDomains]], (projectionMorphismNames[[#1]] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
          morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
      (Subscript["\[ForAll]", ToString[universalMorphismNames[[#1]], StandardForm]] -> 
         DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], morphismDomains[[#1]]] & ) /@ 
       Range[Length[morphismDomains]], {compositionSymbol[First[morphismNames], First[projectionMorphismNames]] -> 
        DirectedEdge[pullbackSymbol @@ morphismDomains, commonImage], 
       compositionSymbol[First[morphismNames], First[universalMorphismNames]] -> 
        DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], commonImage], 
       Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> 
        DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], pullbackSymbol @@ morphismDomains]}]]]
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalSimpleMorphismEdges"] := (DirectedEdge @@ Last[#1] & ) /@ 
   Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[morphismDomains[[#1]], commonImage] & ) /@ 
       Range[Length[morphismDomains]], (projectionMorphismNames[[#1]] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
          morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
      (Subscript["\[ForAll]", ToString[universalMorphismNames[[#1]], StandardForm]] -> 
         DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], morphismDomains[[#1]]] & ) /@ 
       Range[Length[morphismDomains]], {compositionSymbol[First[morphismNames], First[projectionMorphismNames]] -> 
        DirectedEdge[pullbackSymbol @@ morphismDomains, commonImage], 
       compositionSymbol[First[morphismNames], First[universalMorphismNames]] -> 
        DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], commonImage], 
       Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> 
        DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], pullbackSymbol @@ morphismDomains]}]]]
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalSimpleMorphismCount"] := 
  Length[Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[morphismDomains[[#1]], commonImage] & ) /@ 
       Range[Length[morphismDomains]], (projectionMorphismNames[[#1]] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
          morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
      (Subscript["\[ForAll]", ToString[universalMorphismNames[[#1]], StandardForm]] -> 
         DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], morphismDomains[[#1]]] & ) /@ 
       Range[Length[morphismDomains]], {compositionSymbol[First[morphismNames], First[projectionMorphismNames]] -> 
        DirectedEdge[pullbackSymbol @@ morphismDomains, commonImage], 
       compositionSymbol[First[morphismNames], First[universalMorphismNames]] -> 
        DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], commonImage], 
       Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> 
        DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], 
         pullbackSymbol @@ morphismDomains]}]]]]
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalReducedSimpleMorphismAssociation"] := 
  Association[Join[(morphismNames[[#1]] -> DirectedEdge[morphismDomains[[#1]], commonImage] & ) /@ 
     Range[Length[morphismDomains]], (projectionMorphismNames[[#1]] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
        morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
    {compositionSymbol[Last[morphismNames], Last[projectionMorphismNames]] -> 
      DirectedEdge[pullbackSymbol @@ morphismDomains, commonImage]}, 
    (compositionSymbol[projectionMorphismNames[[#1]], uniqueMorphismName] -> 
       DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], morphismDomains[[#1]]] & ) /@ 
     Range[Length[morphismDomains]], {compositionSymbol[compositionSymbol[Last[morphismNames], 
        Last[projectionMorphismNames]], uniqueMorphismName] -> 
      DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], commonImage], 
     Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> 
      DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], pullbackSymbol @@ morphismDomains]}]]
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalReducedSimpleMorphismNames"] := 
  First /@ Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[morphismDomains[[#1]], commonImage] & ) /@ 
       Range[Length[morphismDomains]], (projectionMorphismNames[[#1]] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
          morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
      {compositionSymbol[Last[morphismNames], Last[projectionMorphismNames]] -> 
        DirectedEdge[pullbackSymbol @@ morphismDomains, commonImage]}, 
      (compositionSymbol[projectionMorphismNames[[#1]], uniqueMorphismName] -> 
         DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], morphismDomains[[#1]]] & ) /@ 
       Range[Length[morphismDomains]], {compositionSymbol[compositionSymbol[Last[morphismNames], 
          Last[projectionMorphismNames]], uniqueMorphismName] -> DirectedEdge[Subscript["\[ForAll]", 
          ToString[universalObjectName, StandardForm]], commonImage], 
       Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> 
        DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], pullbackSymbol @@ morphismDomains]}]]]
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalReducedSimpleMorphismEdges"] := (DirectedEdge @@ Last[#1] & ) /@ 
   Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[morphismDomains[[#1]], commonImage] & ) /@ 
       Range[Length[morphismDomains]], (projectionMorphismNames[[#1]] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
          morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
      {compositionSymbol[Last[morphismNames], Last[projectionMorphismNames]] -> 
        DirectedEdge[pullbackSymbol @@ morphismDomains, commonImage]}, 
      (compositionSymbol[projectionMorphismNames[[#1]], uniqueMorphismName] -> 
         DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], morphismDomains[[#1]]] & ) /@ 
       Range[Length[morphismDomains]], {compositionSymbol[compositionSymbol[Last[morphismNames], 
          Last[projectionMorphismNames]], uniqueMorphismName] -> DirectedEdge[Subscript["\[ForAll]", 
          ToString[universalObjectName, StandardForm]], commonImage], 
       Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> 
        DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], pullbackSymbol @@ morphismDomains]}]]]
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalReducedSimpleMorphismCount"] := 
  Length[Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[morphismDomains[[#1]], commonImage] & ) /@ 
       Range[Length[morphismDomains]], (projectionMorphismNames[[#1]] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
          morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
      {compositionSymbol[Last[morphismNames], Last[projectionMorphismNames]] -> 
        DirectedEdge[pullbackSymbol @@ morphismDomains, commonImage]}, 
      (compositionSymbol[projectionMorphismNames[[#1]], uniqueMorphismName] -> 
         DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], morphismDomains[[#1]]] & ) /@ 
       Range[Length[morphismDomains]], {compositionSymbol[compositionSymbol[Last[morphismNames], 
          Last[projectionMorphismNames]], uniqueMorphismName] -> DirectedEdge[Subscript["\[ForAll]", 
          ToString[universalObjectName, StandardForm]], commonImage], 
       Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> 
        DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], 
         pullbackSymbol @@ morphismDomains]}]]]]
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "PullbackSymbol"] := pullbackSymbol
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "CompositionSymbol"] := compositionSymbol
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "IdentitySymbol"] := identitySymbol
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "PullbackCategory"] := ResourceFunction["AbstractCategory"][Association["CompositionSymbol" -> compositionSymbol, 
    "IdentitySymbol" -> identitySymbol, "MorphismEquivalences" -> If[Length[morphismDomains] > 1, 
      (compositionSymbol[morphismNames[[#1]], projectionMorphismNames[[#1]]] == compositionSymbol[
          morphismNames[[#1 + 1]], projectionMorphismNames[[#1 + 1]]] & ) /@ Range[Length[morphismDomains] - 1], {}], 
    "ObjectEquivalences" -> {}, "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> {}, 
       "Arrows" -> Association[Join[(morphismNames[[#1]] -> DirectedEdge[morphismDomains[[#1]], commonImage] & ) /@ 
           Range[Length[morphismDomains]], (projectionMorphismNames[[#1]] -> DirectedEdge[pullbackSymbol @@ 
               morphismDomains, morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]]]], 
       "ObjectEquivalences" -> {}, "Objects" -> Join[morphismDomains, {commonImage, pullbackSymbol @@ 
           morphismDomains}]]]]]
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalPullbackCategory"] := ResourceFunction["AbstractCategory"][
   Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
    "MorphismEquivalences" -> If[Length[morphismDomains] > 1, 
      Join[(compositionSymbol[morphismNames[[#1]], projectionMorphismNames[[#1]]] == 
          compositionSymbol[morphismNames[[#1 + 1]], projectionMorphismNames[[#1 + 1]]] & ) /@ 
        Range[Length[morphismDomains] - 1], (compositionSymbol[morphismNames[[#1]], universalMorphismNames[[#1]]] == 
          compositionSymbol[morphismNames[[#1 + 1]], universalMorphismNames[[#1 + 1]]] & ) /@ 
        Range[Length[morphismDomains] - 1], (universalMorphismNames[[#1]] == compositionSymbol[
           projectionMorphismNames[[#1]], uniqueMorphismName] & ) /@ Range[Length[morphismDomains]], 
       {compositionSymbol[Last[morphismNames], compositionSymbol[Last[projectionMorphismNames], uniqueMorphismName]] == 
         compositionSymbol[compositionSymbol[Last[morphismNames], Last[projectionMorphismNames]], uniqueMorphismName]}], 
      {First[universalMorphismNames] == compositionSymbol[First[projectionMorphismNames], uniqueMorphismName], 
       compositionSymbol[First[morphismNames], compositionSymbol[First[projectionMorphismNames], uniqueMorphismName]] == 
        compositionSymbol[compositionSymbol[First[morphismNames], First[projectionMorphismNames]], uniqueMorphismName]}], 
    "ObjectEquivalences" -> {}, "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> {}, 
       "Arrows" -> Association[Join[(morphismNames[[#1]] -> DirectedEdge[morphismDomains[[#1]], commonImage] & ) /@ 
           Range[Length[morphismDomains]], (projectionMorphismNames[[#1]] -> DirectedEdge[pullbackSymbol @@ 
               morphismDomains, morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
          (universalMorphismNames[[#1]] -> DirectedEdge[universalObjectName, morphismDomains[[#1]]] & ) /@ 
           Range[Length[morphismDomains]], {uniqueMorphismName -> DirectedEdge[universalObjectName, 
             pullbackSymbol @@ morphismDomains]}]], "ObjectEquivalences" -> {}, 
       "Objects" -> Join[morphismDomains, {commonImage, pullbackSymbol @@ morphismDomains, universalObjectName}]]]]]
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "PullbackEquations"] := If[Length[morphismDomains] > 1, 
   (compositionSymbol[morphismNames[[#1]], projectionMorphismNames[[#1]]] == compositionSymbol[morphismNames[[#1 + 1]], 
       projectionMorphismNames[[#1 + 1]]] & ) /@ Range[Length[morphismDomains] - 1], {}]
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalPullbackEquations"] := If[Length[morphismDomains] > 1, 
   Join[(compositionSymbol[morphismNames[[#1]], projectionMorphismNames[[#1]]] == 
       compositionSymbol[morphismNames[[#1 + 1]], projectionMorphismNames[[#1 + 1]]] & ) /@ 
     Range[Length[morphismDomains] - 1], 
    (Module[{morphismIndex = #1}, ToExpression[StringJoin["HoldForm[ForAll[", ToString[universalMorphismNames, 
          StandardForm], ",Implies[", ToString[And @@ (compositionSymbol[morphismNames[[#1]], universalMorphismNames[[
                #1]]] == compositionSymbol[morphismNames[[#1 + 1]], projectionMorphismNames[[#1 + 1]]] & ) /@ 
            Range[Length[morphismDomains] - 1], StandardForm], ",Exists[", ToString[uniqueMorphismName, StandardForm], 
         ",", ToString[universalMorphismNames[[morphismIndex]] == compositionSymbol[projectionMorphismNames[[
             morphismIndex]], uniqueMorphismName], StandardForm], "]]]]"]]] & ) /@ Range[Length[morphismDomains]]], 
   {First[universalMorphismNames] == compositionSymbol[First[projectionMorphismNames], uniqueMorphismName]}]
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "FullLabeledGraph"] := EdgeTaggedGraph[Join[morphismDomains, {commonImage, pullbackSymbol @@ morphismDomains}], 
   (Labeled[DirectedEdge @@ Last[#1], Placed[First[#1], 0.5]] & ) /@ 
    Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[morphismDomains[[#1]], commonImage] & ) /@ 
        Range[Length[morphismDomains]], (projectionMorphismNames[[#1]] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
           morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
       (compositionSymbol[morphismNames[[#1]], projectionMorphismNames[[#1]]] -> 
          DirectedEdge[pullbackSymbol @@ morphismDomains, commonImage] & ) /@ Range[Length[morphismDomains]], 
       (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ morphismDomains, 
       {identitySymbol[commonImage] -> DirectedEdge[commonImage, commonImage], 
        identitySymbol[pullbackSymbol @@ morphismDomains] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
          pullbackSymbol @@ morphismDomains]}]]], VertexSize -> 0.3, 
   VertexStyle -> Directive[Transparent, EdgeForm[None]], VertexLabels -> Placed["Name", Center], 
   VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], EdgeStyle -> Directive[Black, Thick], 
   GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "FullUnlabeledGraph"] := EdgeTaggedGraph[Join[morphismDomains, {commonImage, pullbackSymbol @@ morphismDomains}], 
   (DirectedEdge @@ Last[#1] & ) /@ 
    Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[morphismDomains[[#1]], commonImage] & ) /@ 
        Range[Length[morphismDomains]], (projectionMorphismNames[[#1]] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
           morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
       (compositionSymbol[morphismNames[[#1]], projectionMorphismNames[[#1]]] -> 
          DirectedEdge[pullbackSymbol @@ morphismDomains, commonImage] & ) /@ Range[Length[morphismDomains]], 
       (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ morphismDomains, 
       {identitySymbol[commonImage] -> DirectedEdge[commonImage, commonImage], 
        identitySymbol[pullbackSymbol @@ morphismDomains] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
          pullbackSymbol @@ morphismDomains]}]]], VertexSize -> 0.3, 
   VertexStyle -> Directive[Transparent, EdgeForm[None]], VertexLabels -> Placed["Name", Center], 
   VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], EdgeStyle -> Directive[Black, Thick], 
   GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "ReducedLabeledGraph"] := EdgeTaggedGraph[Join[morphismDomains, {commonImage, pullbackSymbol @@ morphismDomains}], 
   (Labeled[DirectedEdge @@ Last[#1], Placed[First[#1], 0.5]] & ) /@ 
    Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[morphismDomains[[#1]], commonImage] & ) /@ 
        Range[Length[morphismDomains]], (projectionMorphismNames[[#1]] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
           morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
       {compositionSymbol[Last[morphismNames], Last[projectionMorphismNames]] -> 
         DirectedEdge[pullbackSymbol @@ morphismDomains, commonImage]}, 
       (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ morphismDomains, 
       {identitySymbol[commonImage] -> DirectedEdge[commonImage, commonImage], 
        identitySymbol[pullbackSymbol @@ morphismDomains] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
          pullbackSymbol @@ morphismDomains]}]]], VertexSize -> 0.3, 
   VertexStyle -> Directive[Transparent, EdgeForm[None]], VertexLabels -> Placed["Name", Center], 
   VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], EdgeStyle -> Directive[Black, Thick], 
   GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismName_List, "UniversalObjectName" -> universalObjectName_]][
   "ReducedUnlabeledGraph"] := EdgeTaggedGraph[Join[morphismDomains, {commonImage, pullbackSymbol @@ morphismDomains}], 
   (DirectedEdge @@ Last[#1] & ) /@ 
    Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[morphismDomains[[#1]], commonImage] & ) /@ 
        Range[Length[morphismDomains]], (projectionMorphismNames[[#1]] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
           morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
       {compositionSymbol[Last[morphismNames], Last[projectionMorphismNames]] -> 
         DirectedEdge[pullbackSymbol @@ morphismDomains, commonImage]}, 
       (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ morphismDomains, 
       {identitySymbol[commonImage] -> DirectedEdge[commonImage, commonImage], 
        identitySymbol[pullbackSymbol @@ morphismDomains] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
          pullbackSymbol @@ morphismDomains]}]]], VertexSize -> 0.3, 
   VertexStyle -> Directive[Transparent, EdgeForm[None]], VertexLabels -> Placed["Name", Center], 
   VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], EdgeStyle -> Directive[Black, Thick], 
   GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "SimpleLabeledGraph"] := EdgeTaggedGraph[Join[morphismDomains, {commonImage, pullbackSymbol @@ morphismDomains}], 
   (Labeled[DirectedEdge @@ Last[#1], Placed[First[#1], 0.5]] & ) /@ 
    Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[morphismDomains[[#1]], commonImage] & ) /@ 
        Range[Length[morphismDomains]], (projectionMorphismNames[[#1]] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
           morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
       {compositionSymbol[First[morphismNames], First[projectionMorphismNames]] -> 
         DirectedEdge[pullbackSymbol @@ morphismDomains, commonImage]}]]], VertexSize -> 0.3, 
   VertexStyle -> Directive[Transparent, EdgeForm[None]], VertexLabels -> Placed["Name", Center], 
   VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], EdgeStyle -> Directive[Black, Thick], 
   GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "SimpleUnlabeledGraph"] := EdgeTaggedGraph[Join[morphismDomains, {commonImage, pullbackSymbol @@ morphismDomains}], 
   (DirectedEdge @@ Last[#1] & ) /@ 
    Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[morphismDomains[[#1]], commonImage] & ) /@ 
        Range[Length[morphismDomains]], (projectionMorphismNames[[#1]] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
           morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
       {compositionSymbol[First[morphismNames], First[projectionMorphismNames]] -> 
         DirectedEdge[pullbackSymbol @@ morphismDomains, commonImage]}]]], VertexSize -> 0.3, 
   VertexStyle -> Directive[Transparent, EdgeForm[None]], VertexLabels -> Placed["Name", Center], 
   VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], EdgeStyle -> Directive[Black, Thick], 
   GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "ReducedSimpleLabeledGraph"] := EdgeTaggedGraph[Join[morphismDomains, 
    {commonImage, pullbackSymbol @@ morphismDomains}], (Labeled[DirectedEdge @@ Last[#1], Placed[First[#1], 0.5]] & ) /@ 
    Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[morphismDomains[[#1]], commonImage] & ) /@ 
        Range[Length[morphismDomains]], (projectionMorphismNames[[#1]] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
           morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
       {compositionSymbol[Last[morphismNames], Last[projectionMorphismNames]] -> 
         DirectedEdge[pullbackSymbol @@ morphismDomains, commonImage]}]]], VertexSize -> 0.3, 
   VertexStyle -> Directive[Transparent, EdgeForm[None]], VertexLabels -> Placed["Name", Center], 
   VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], EdgeStyle -> Directive[Black, Thick], 
   GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "ReducedSimpleUnlabeledGraph"] := EdgeTaggedGraph[Join[morphismDomains, 
    {commonImage, pullbackSymbol @@ morphismDomains}], (DirectedEdge @@ Last[#1] & ) /@ 
    Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[morphismDomains[[#1]], commonImage] & ) /@ 
        Range[Length[morphismDomains]], (projectionMorphismNames[[#1]] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
           morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
       {compositionSymbol[Last[morphismNames], Last[projectionMorphismNames]] -> 
         DirectedEdge[pullbackSymbol @@ morphismDomains, commonImage]}]]], VertexSize -> 0.3, 
   VertexStyle -> Directive[Transparent, EdgeForm[None]], VertexLabels -> Placed["Name", Center], 
   VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], EdgeStyle -> Directive[Black, Thick], 
   GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalFullLabeledGraph"] := EdgeTaggedGraph[Join[morphismDomains, {commonImage, pullbackSymbol @@ morphismDomains, 
     universalObjectName}], (Labeled[DirectedEdge @@ Last[#1], Placed[First[#1], 0.5]] & ) /@ 
    Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[morphismDomains[[#1]], commonImage] & ) /@ 
        Range[Length[morphismDomains]], (projectionMorphismNames[[#1]] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
           morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
       (Subscript["\[ForAll]", ToString[universalMorphismNames[[#1]], StandardForm]] -> DirectedEdge[universalObjectName, 
           morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
       (compositionSymbol[morphismNames[[#1]], projectionMorphismNames[[#1]]] -> 
          DirectedEdge[pullbackSymbol @@ morphismDomains, commonImage] & ) /@ Range[Length[morphismDomains]], 
       (compositionSymbol[projectionMorphismNames[[#1]], uniqueMorphismName] -> DirectedEdge[universalObjectName, 
           morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
       (compositionSymbol[morphismNames[[#1]], universalMorphismNames[[#1]]] -> DirectedEdge[universalObjectName, 
           commonImage] & ) /@ Range[Length[morphismDomains]], 
       (compositionSymbol[compositionSymbol[morphismNames[[#1]], projectionMorphismNames[[#1]]], uniqueMorphismName] -> 
          DirectedEdge[universalObjectName, commonImage] & ) /@ Range[Length[morphismDomains]], 
       (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ morphismDomains, 
       {identitySymbol[commonImage] -> DirectedEdge[commonImage, commonImage], 
        identitySymbol[pullbackSymbol @@ morphismDomains] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
          pullbackSymbol @@ morphismDomains], identitySymbol[universalObjectName] -> DirectedEdge[universalObjectName, 
          universalObjectName], Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> 
         DirectedEdge[universalObjectName, pullbackSymbol @@ morphismDomains]}]]], VertexSize -> 0.3, 
   VertexStyle -> Directive[Transparent, EdgeForm[None]], 
   VertexLabels -> {Placed["Name", Center], universalObjectName -> 
      Placed[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], Center]}, 
   VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
   EdgeStyle -> {Directive[Black, Thick], DirectedEdge[universalObjectName, pullbackSymbol @@ morphismDomains] -> 
      Dashed}, GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalFullUnlabeledGraph"] := EdgeTaggedGraph[Join[morphismDomains, 
    {commonImage, pullbackSymbol @@ morphismDomains, universalObjectName}], 
   (DirectedEdge @@ Last[#1] & ) /@ 
    Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[morphismDomains[[#1]], commonImage] & ) /@ 
        Range[Length[morphismDomains]], (projectionMorphismNames[[#1]] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
           morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
       (Subscript["\[ForAll]", ToString[universalMorphismNames[[#1]], StandardForm]] -> DirectedEdge[universalObjectName, 
           morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
       (compositionSymbol[morphismNames[[#1]], projectionMorphismNames[[#1]]] -> 
          DirectedEdge[pullbackSymbol @@ morphismDomains, commonImage] & ) /@ Range[Length[morphismDomains]], 
       (compositionSymbol[projectionMorphismNames[[#1]], uniqueMorphismName] -> DirectedEdge[universalObjectName, 
           morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
       (compositionSymbol[morphismNames[[#1]], universalMorphismNames[[#1]]] -> DirectedEdge[universalObjectName, 
           commonImage] & ) /@ Range[Length[morphismDomains]], 
       (compositionSymbol[compositionSymbol[morphismNames[[#1]], projectionMorphismNames[[#1]]], uniqueMorphismName] -> 
          DirectedEdge[universalObjectName, commonImage] & ) /@ Range[Length[morphismDomains]], 
       (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ morphismDomains, 
       {identitySymbol[commonImage] -> DirectedEdge[commonImage, commonImage], 
        identitySymbol[pullbackSymbol @@ morphismDomains] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
          pullbackSymbol @@ morphismDomains], identitySymbol[universalObjectName] -> DirectedEdge[universalObjectName, 
          universalObjectName], Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> 
         DirectedEdge[universalObjectName, pullbackSymbol @@ morphismDomains]}]]], VertexSize -> 0.3, 
   VertexStyle -> Directive[Transparent, EdgeForm[None]], 
   VertexLabels -> {Placed["Name", Center], universalObjectName -> 
      Placed[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], Center]}, 
   VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
   EdgeStyle -> {Directive[Black, Thick], DirectedEdge[universalObjectName, pullbackSymbol @@ morphismDomains] -> 
      Dashed}, GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalReducedLabeledGraph"] := EdgeTaggedGraph[Join[morphismDomains, 
    {commonImage, pullbackSymbol @@ morphismDomains, universalObjectName}], 
   (Labeled[DirectedEdge @@ Last[#1], Placed[First[#1], 0.5]] & ) /@ 
    Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[morphismDomains[[#1]], commonImage] & ) /@ 
        Range[Length[morphismDomains]], (projectionMorphismNames[[#1]] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
           morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
       {compositionSymbol[Last[morphismNames], Last[projectionMorphismNames]] -> 
         DirectedEdge[pullbackSymbol @@ morphismDomains, commonImage]}, 
       (compositionSymbol[projectionMorphismNames[[#1]], uniqueMorphismName] -> DirectedEdge[universalObjectName, 
           morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
       {compositionSymbol[compositionSymbol[Last[morphismNames], Last[projectionMorphismNames]], uniqueMorphismName] -> 
         DirectedEdge[universalObjectName, commonImage]}, (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ 
        morphismDomains, {identitySymbol[commonImage] -> DirectedEdge[commonImage, commonImage], 
        identitySymbol[pullbackSymbol @@ morphismDomains] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
          pullbackSymbol @@ morphismDomains], identitySymbol[universalObjectName] -> DirectedEdge[universalObjectName, 
          universalObjectName], Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> 
         DirectedEdge[universalObjectName, pullbackSymbol @@ morphismDomains]}]]], VertexSize -> 0.3, 
   VertexStyle -> Directive[Transparent, EdgeForm[None]], 
   VertexLabels -> {Placed["Name", Center], universalObjectName -> 
      Placed[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], Center]}, 
   VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
   EdgeStyle -> {Directive[Black, Thick], DirectedEdge[universalObjectName, pullbackSymbol @@ morphismDomains] -> 
      Dashed}, GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalReducedUnlabeledGraph"] := EdgeTaggedGraph[Join[morphismDomains, 
    {commonImage, pullbackSymbol @@ morphismDomains, universalObjectName}], 
   (DirectedEdge @@ Last[#1] & ) /@ 
    Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[morphismDomains[[#1]], commonImage] & ) /@ 
        Range[Length[morphismDomains]], (projectionMorphismNames[[#1]] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
           morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
       {compositionSymbol[Last[morphismNames], Last[projectionMorphismNames]] -> 
         DirectedEdge[pullbackSymbol @@ morphismDomains, commonImage]}, 
       (compositionSymbol[projectionMorphismNames[[#1]], uniqueMorphismName] -> DirectedEdge[universalObjectName, 
           morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
       {compositionSymbol[compositionSymbol[Last[morphismNames], Last[projectionMorphismNames]], uniqueMorphismName] -> 
         DirectedEdge[universalObjectName, commonImage]}, (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ 
        morphismDomains, {identitySymbol[commonImage] -> DirectedEdge[commonImage, commonImage], 
        identitySymbol[pullbackSymbol @@ morphismDomains] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
          pullbackSymbol @@ morphismDomains], identitySymbol[universalObjectName] -> DirectedEdge[universalObjectName, 
          universalObjectName], Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> 
         DirectedEdge[universalObjectName, pullbackSymbol @@ morphismDomains]}]]], VertexSize -> 0.3, 
   VertexStyle -> Directive[Transparent, EdgeForm[None]], 
   VertexLabels -> {Placed["Name", Center], universalObjectName -> 
      Placed[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], Center]}, 
   VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
   EdgeStyle -> {Directive[Black, Thick], DirectedEdge[universalObjectName, pullbackSymbol @@ morphismDomains] -> 
      Dashed}, GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalSimpleLabeledGraph"] := EdgeTaggedGraph[Join[morphismDomains, 
    {commonImage, pullbackSymbol @@ morphismDomains, universalObjectName}], 
   (Labeled[DirectedEdge @@ Last[#1], Placed[First[#1], 0.5]] & ) /@ 
    Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[morphismDomains[[#1]], commonImage] & ) /@ 
        Range[Length[morphismDomains]], (projectionMorphismNames[[#1]] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
           morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
       (Subscript["\[ForAll]", ToString[universalMorphismNames[[#1]], StandardForm]] -> DirectedEdge[universalObjectName, 
           morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
       {compositionSymbol[First[morphismNames], First[projectionMorphismNames]] -> 
         DirectedEdge[pullbackSymbol @@ morphismDomains, commonImage], compositionSymbol[First[morphismNames], 
          First[universalMorphismNames]] -> DirectedEdge[universalObjectName, commonImage], 
        Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> DirectedEdge[universalObjectName, 
          pullbackSymbol @@ morphismDomains]}]]], VertexSize -> 0.3, 
   VertexStyle -> Directive[Transparent, EdgeForm[None]], 
   VertexLabels -> {Placed["Name", Center], universalObjectName -> 
      Placed[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], Center]}, 
   VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
   EdgeStyle -> {Directive[Black, Thick], DirectedEdge[universalObjectName, pullbackSymbol @@ morphismDomains] -> 
      Dashed}, GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalSimpleUnlabeledGraph"] := EdgeTaggedGraph[Join[morphismDomains, 
    {commonImage, pullbackSymbol @@ morphismDomains, universalObjectName}], 
   (DirectedEdge @@ Last[#1] & ) /@ 
    Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[morphismDomains[[#1]], commonImage] & ) /@ 
        Range[Length[morphismDomains]], (projectionMorphismNames[[#1]] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
           morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
       (Subscript["\[ForAll]", ToString[universalMorphismNames[[#1]], StandardForm]] -> DirectedEdge[universalObjectName, 
           morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
       {compositionSymbol[First[morphismNames], First[projectionMorphismNames]] -> 
         DirectedEdge[pullbackSymbol @@ morphismDomains, commonImage], compositionSymbol[First[morphismNames], 
          First[universalMorphismNames]] -> DirectedEdge[universalObjectName, commonImage], 
        Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> DirectedEdge[universalObjectName, 
          pullbackSymbol @@ morphismDomains]}]]], VertexSize -> 0.3, 
   VertexStyle -> Directive[Transparent, EdgeForm[None]], 
   VertexLabels -> {Placed["Name", Center], universalObjectName -> 
      Placed[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], Center]}, 
   VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
   EdgeStyle -> {Directive[Black, Thick], DirectedEdge[universalObjectName, pullbackSymbol @@ morphismDomains] -> 
      Dashed}, GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalReducedSimpleLabeledGraph"] := EdgeTaggedGraph[Join[morphismDomains, 
    {commonImage, pullbackSymbol @@ morphismDomains, universalObjectName}], 
   (Labeled[DirectedEdge @@ Last[#1], Placed[First[#1], 0.5]] & ) /@ 
    Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[morphismDomains[[#1]], commonImage] & ) /@ 
        Range[Length[morphismDomains]], (projectionMorphismNames[[#1]] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
           morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
       {compositionSymbol[Last[morphismNames], Last[projectionMorphismNames]] -> 
         DirectedEdge[pullbackSymbol @@ morphismDomains, commonImage]}, 
       (compositionSymbol[projectionMorphismNames[[#1]], uniqueMorphismName] -> DirectedEdge[universalObjectName, 
           morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
       {compositionSymbol[compositionSymbol[Last[morphismNames], Last[projectionMorphismNames]], uniqueMorphismName] -> 
         DirectedEdge[universalObjectName, commonImage], Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> 
         DirectedEdge[universalObjectName, pullbackSymbol @@ morphismDomains]}]]], VertexSize -> 0.3, 
   VertexStyle -> Directive[Transparent, EdgeForm[None]], 
   VertexLabels -> {Placed["Name", Center], universalObjectName -> 
      Placed[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], Center]}, 
   VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
   EdgeStyle -> {Directive[Black, Thick], DirectedEdge[universalObjectName, pullbackSymbol @@ morphismDomains] -> 
      Dashed}, GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalReducedSimpleUnlabeledGraph"] := EdgeTaggedGraph[Join[morphismDomains, 
    {commonImage, pullbackSymbol @@ morphismDomains, universalObjectName}], 
   (DirectedEdge @@ Last[#1] & ) /@ 
    Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[morphismDomains[[#1]], commonImage] & ) /@ 
        Range[Length[morphismDomains]], (projectionMorphismNames[[#1]] -> DirectedEdge[pullbackSymbol @@ morphismDomains, 
           morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
       {compositionSymbol[Last[morphismNames], Last[projectionMorphismNames]] -> 
         DirectedEdge[pullbackSymbol @@ morphismDomains, commonImage]}, 
       (compositionSymbol[projectionMorphismNames[[#1]], uniqueMorphismName] -> DirectedEdge[universalObjectName, 
           morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
       {compositionSymbol[compositionSymbol[Last[morphismNames], Last[projectionMorphismNames]], uniqueMorphismName] -> 
         DirectedEdge[universalObjectName, commonImage], Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> 
         DirectedEdge[universalObjectName, pullbackSymbol @@ morphismDomains]}]]], VertexSize -> 0.3, 
   VertexStyle -> Directive[Transparent, EdgeForm[None]], 
   VertexLabels -> {Placed["Name", Center], universalObjectName -> 
      Placed[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], Center]}, 
   VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
   EdgeStyle -> {Directive[Black, Thick], DirectedEdge[universalObjectName, pullbackSymbol @@ morphismDomains] -> 
      Dashed}, GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "AssociationForm"] := Association["MorphismNames" -> morphismNames, "MorphismDomains" -> morphismDomains, 
   "CommonImage" -> commonImage, "PullbackSymbol" -> pullbackSymbol, "ProjectionMorphismNames" -> 
    projectionMorphismNames, "CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
   "UniversalObjectName" -> universalObjectName, "UniversalMorphismNames" -> universalMorphismNames, 
   "UniqueMorphismName" -> uniqueMorphismName]
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "Properties"] := {"Objects", "ObjectCount", "MorphismAssociation", "MorphismNames", "MorphismEdges", "MorphismCount", 
   "ReducedMorphismAssociation", "ReducedMorphismNames", "ReducedMorphismEdges", "ReducedMorphismCount", 
   "SimpleMorphismAssociation", "SimpleMorphismNames", "SimpleMorphismEdges", "SimpleMorphismCount", 
   "ReducedSimpleMorphismAssociation", "ReducedSimpleMorphismNames", "ReducedSimpleMorphismEdges", 
   "ReducedSimpleMorphismCount", "UniversalObjects", "UniversalObjectCount", "UniversalMorphismAssociation", 
   "UniversalMorphismNames", "UniversalMorphismEdges", "UniversalMorphismCount", "UniversalReducedMorphismAssociation", 
   "UniversalReducedMorphismNames", "UniversalReducedMorphismEdges", "UniversalReducedMorphismCount", 
   "UniversalSimpleMorphismAssociation", "UniversalSimpleMorphismNames", "UniversalSimpleMorphismEdges", 
   "UniversalSimpleMorphismCount", "UniversalReducedSimpleMorphismAssociation", "UniversalReducedSimpleMorphismNames", 
   "UniversalReducedSimpleMorphismEdges", "UniversalReducedSimpleMorphismCount", "PullbackSymbol", "CompositionSymbol", 
   "IdentitySymbol", "PullbackCategory", "UniversalPullbackCategory", "PullbackEquations", "UniversalPullbackEquations", 
   "FullLabeledGraph", "FullUnlabeledGraph", "ReducedLabeledGraph", "ReducedUnlabeledGraph", "SimpleLabeledGraph", 
   "SimpleUnlabeledGraph", "ReducedSimpleLabeledGraph", "ReducedSimpleUnlabeledGraph", "UniversalFullLabeledGraph", 
   "UniversalFullUnlabeledGraph", "UniversalReducedLabeledGraph", "UniversalReducedUnlabeledGraph", 
   "UniversalSimpleLabeledGraph", "UniversalSimpleUnlabeledGraph", "UniversalReducedSimpleLabeledGraph", 
   "UniversalReducedSimpleUnlabeledGraph", "AssociationForm", "Properties"}
AbstractPullback /: MakeBoxes[abstractPullback:AbstractPullback[Association["CommonImage" -> commonImage_, 
       "CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
       "MorphismDomains" -> morphismDomains_List, "MorphismNames" -> morphismNames_List, 
       "ProjectionMorphismNames" -> projectionMorphismNames_List, "PullbackSymbol" -> pullbackSymbol_, 
       "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
       "UniversalObjectName" -> universalObjectName_]], format_] := 
   Module[{icon}, icon = GraphPlot[EdgeTaggedGraph[Join[morphismDomains, {commonImage, 
          pullbackSymbol @@ morphismDomains}], (DirectedEdge @@ Last[#1] & ) /@ 
         Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[morphismDomains[[#1]], commonImage] & ) /@ 
             Range[Length[morphismDomains]], (projectionMorphismNames[[#1]] -> DirectedEdge[pullbackSymbol @@ 
                 morphismDomains, morphismDomains[[#1]]] & ) /@ Range[Length[morphismDomains]], 
            (compositionSymbol[projectionMorphismNames[[#1]], morphismNames[[#1]]] -> DirectedEdge[pullbackSymbol @@ 
                 morphismDomains, commonImage] & ) /@ Range[Length[morphismDomains]], 
            (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ morphismDomains, {identitySymbol[commonImage] -> 
              DirectedEdge[commonImage, commonImage], identitySymbol[pullbackSymbol @@ morphismDomains] -> 
              DirectedEdge[pullbackSymbol @@ morphismDomains, pullbackSymbol @@ morphismDomains]}]]], VertexSize -> 0.3, 
        VertexStyle -> Directive[Transparent, EdgeForm[None]], EdgeShapeFunction -> GraphElementData["ShortFilledArrow", 
          "ArrowSize" -> 0.05], EdgeStyle -> Black, GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]]; 
     BoxForm`ArrangeSummaryBox["AbstractPullback", abstractPullback, icon, 
      {{BoxForm`SummaryItem[{"Symbol: ", pullbackSymbol}], BoxForm`SummaryItem[{"Common Codomain: ", commonImage}]}, 
       {BoxForm`SummaryItem[{"Domains: ", morphismDomains}], BoxForm`SummaryItem[{"Arrows: ", morphismNames}]}}, {{}}, 
      format, "Interpretable" -> Automatic]]
AbstractPullback[cospan_Association] := AbstractPullback[Association["CommonImage" -> Last[Last[First[Normal[cospan]]]], 
     "CompositionSymbol" -> CircleDot, "IdentitySymbol" -> OverTilde, "MorphismDomains" -> 
      (First[Last[#1]] & ) /@ Normal[cospan], "MorphismNames" -> First /@ Normal[cospan], 
     "ProjectionMorphismNames" -> (Subscript["\[FormalP]", ToString[#1]] & ) /@ Range[Length[Normal[cospan]]], 
     "PullbackSymbol" -> Cross, "UniqueMorphismName" -> "\[FormalU]", "UniversalMorphismNames" -> 
      (Subscript["\[FormalQ]", ToString[#1]] & ) /@ Range[Length[Normal[cospan]]], "UniversalObjectName" -> "\[FormalCapitalQ]"]] /; 
    !KeyExistsQ[cospan, "CommonImage"] &&  !KeyExistsQ[cospan, "CompositionSymbol"] && 
     !KeyExistsQ[cospan, "IdentitySymbol"] &&  !KeyExistsQ[cospan, "MorphismDomains"] && 
     !KeyExistsQ[cospan, "MorphismNames"] &&  !KeyExistsQ[cospan, "ProjectionMorphismNames"] && 
     !KeyExistsQ[cospan, "PullbackSymbol"] &&  !KeyExistsQ[cospan, "UniqueMorphismName"] && 
     !KeyExistsQ[cospan, "UniversalMorphismNames"] &&  !KeyExistsQ[cospan, "UniversalObjectName"] && 
    Length[DeleteDuplicates[(Last[Last[#1]] & ) /@ Normal[cospan]]] == 1
AbstractPullback[cospan_Association, pullbackSymbol_] := 
  AbstractPullback[Association["CommonImage" -> Last[Last[First[Normal[cospan]]]], "CompositionSymbol" -> CircleDot, 
     "IdentitySymbol" -> OverTilde, "MorphismDomains" -> (First[Last[#1]] & ) /@ Normal[cospan], 
     "MorphismNames" -> First /@ Normal[cospan], "ProjectionMorphismNames" -> (Subscript["\[FormalP]", ToString[#1]] & ) /@ 
       Range[Length[Normal[cospan]]], "PullbackSymbol" -> pullbackSymbol, "UniqueMorphismName" -> "\[FormalU]", 
     "UniversalMorphismNames" -> (Subscript["\[FormalQ]", ToString[#1]] & ) /@ Range[Length[Normal[cospan]]], 
     "UniversalObjectName" -> "\[FormalCapitalQ]"]] /;  !ListQ[pullbackSymbol] && 
    Length[DeleteDuplicates[(Last[Last[#1]] & ) /@ Normal[cospan]]] == 1
AbstractPullback[cospan_Association, pullbackSymbol_, projectionMorphismNames_List] := 
  AbstractPullback[Association["CommonImage" -> Last[Last[First[Normal[cospan]]]], "CompositionSymbol" -> CircleDot, 
     "IdentitySymbol" -> OverTilde, "MorphismDomains" -> (First[Last[#1]] & ) /@ Normal[cospan], 
     "MorphismNames" -> First /@ Normal[cospan], "ProjectionMorphismNames" -> projectionMorphismNames, 
     "PullbackSymbol" -> pullbackSymbol, "UniqueMorphismName" -> "\[FormalU]", "UniversalMorphismNames" -> 
      (Subscript["\[FormalQ]", ToString[#1]] & ) /@ Range[Length[Normal[cospan]]], "UniversalObjectName" -> "\[FormalCapitalQ]"]] /; 
    !ListQ[pullbackSymbol] && Length[DeleteDuplicates[(Last[Last[#1]] & ) /@ Normal[cospan]]] == 1
AbstractPullback[cospan_Association, pullbackSymbol_, projectionMorphismNames_List, compositionSymbol_] := 
  AbstractPullback[Association["CommonImage" -> Last[Last[First[Normal[cospan]]]], 
     "CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> OverTilde, 
     "MorphismDomains" -> (First[Last[#1]] & ) /@ Normal[cospan], "MorphismNames" -> First /@ Normal[cospan], 
     "ProjectionMorphismNames" -> projectionMorphismNames, "PullbackSymbol" -> pullbackSymbol, 
     "UniqueMorphismName" -> "\[FormalU]", "UniversalMorphismNames" -> (Subscript["\[FormalQ]", ToString[#1]] & ) /@ 
       Range[Length[Normal[cospan]]], "UniversalObjectName" -> "\[FormalCapitalQ]"]] /; 
    !ListQ[pullbackSymbol] &&  !ListQ[compositionSymbol] && 
    Length[DeleteDuplicates[(Last[Last[#1]] & ) /@ Normal[cospan]]] == 1
AbstractPullback[cospan_Association, pullbackSymbol_, projectionMorphismNames_List, compositionSymbol_, 
   identitySymbol_] := AbstractPullback[Association["CommonImage" -> Last[Last[First[Normal[cospan]]]], 
     "CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
     "MorphismDomains" -> (First[Last[#1]] & ) /@ Normal[cospan], "MorphismNames" -> First /@ Normal[cospan], 
     "ProjectionMorphismNames" -> projectionMorphismNames, "PullbackSymbol" -> pullbackSymbol, 
     "UniqueMorphismName" -> "\[FormalU]", "UniversalMorphismNames" -> (Subscript["\[FormalQ]", ToString[#1]] & ) /@ 
       Range[Length[Normal[cospan]]], "UniversalObjectName" -> "\[FormalCapitalQ]"]] /; 
    !ListQ[pullbackSymbol] &&  !ListQ[compositionSymbol] &&  !ListQ[identitySymbol] && 
    Length[DeleteDuplicates[(Last[Last[#1]] & ) /@ Normal[cospan]]] == 1
AbstractPullback[cospan_Association, pullbackSymbol_, projectionMorphismNames_List, compositionSymbol_, identitySymbol_, 
   universalObjectName_] := AbstractPullback[Association["CommonImage" -> Last[Last[First[Normal[cospan]]]], 
     "CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
     "MorphismDomains" -> (First[Last[#1]] & ) /@ Normal[cospan], "MorphismNames" -> First /@ Normal[cospan], 
     "ProjectionMorphismNames" -> projectionMorphismNames, "PullbackSymbol" -> pullbackSymbol, 
     "UniqueMorphismName" -> "\[FormalU]", "UniversalMorphismNames" -> (Subscript["\[FormalQ]", ToString[#1]] & ) /@ 
       Range[Length[Normal[cospan]]], "UniversalObjectName" -> universalObjectName]] /; 
    !ListQ[pullbackSymbol] &&  !ListQ[compositionSymbol] &&  !ListQ[identitySymbol] && 
    Length[DeleteDuplicates[(Last[Last[#1]] & ) /@ Normal[cospan]]] == 1
AbstractPullback[cospan_Association, pullbackSymbol_, projectionMorphismNames_List, compositionSymbol_, identitySymbol_, 
   universalObjectName_, universalMorphismNames_List] := 
  AbstractPullback[Association["CommonImage" -> Last[Last[First[Normal[cospan]]]], 
     "CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
     "MorphismDomains" -> (First[Last[#1]] & ) /@ Normal[cospan], "MorphismNames" -> First /@ Normal[cospan], 
     "ProjectionMorphismNames" -> projectionMorphismNames, "PullbackSymbol" -> pullbackSymbol, 
     "UniqueMorphismName" -> "\[FormalU]", "UniversalMorphismNames" -> universalMorphismNames, 
     "UniversalObjectName" -> universalObjectName]] /;  !ListQ[pullbackSymbol] &&  !ListQ[compositionSymbol] && 
     !ListQ[identitySymbol] && Length[DeleteDuplicates[(Last[Last[#1]] & ) /@ Normal[cospan]]] == 1
AbstractPullback[cospan_Association, pullbackSymbol_, projectionMorphismNames_List, compositionSymbol_, identitySymbol_, 
   universalObjectName_, universalMorphismNames_List, uniqueMorphismName_] := 
  AbstractPullback[Association["CommonImage" -> Last[Last[First[Normal[cospan]]]], 
     "CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
     "MorphismDomains" -> (First[Last[#1]] & ) /@ Normal[cospan], "MorphismNames" -> First /@ Normal[cospan], 
     "ProjectionMorphismNames" -> projectionMorphismNames, "PullbackSymbol" -> pullbackSymbol, 
     "UniqueMorphismName" -> uniqueMorphismName, "UniversalMorphismNames" -> universalMorphismNames, 
     "UniversalObjectName" -> universalObjectName]] /;  !ListQ[pullbackSymbol] &&  !ListQ[compositionSymbol] && 
     !ListQ[identitySymbol] && Length[DeleteDuplicates[(Last[Last[#1]] & ) /@ Normal[cospan]]] == 1
AbstractPullback[cospan_Association, projectionMorphismNames_List] := 
  AbstractPullback[Association["CommonImage" -> Last[Last[First[Normal[cospan]]]], "CompositionSymbol" -> CircleDot, 
     "IdentitySymbol" -> OverTilde, "MorphismDomains" -> (First[Last[#1]] & ) /@ Normal[cospan], 
     "MorphismNames" -> First /@ Normal[cospan], "ProjectionMorphismNames" -> projectionMorphismNames, 
     "PullbackSymbol" -> Cross, "UniqueMorphismName" -> "\[FormalU]", "UniversalMorphismNames" -> 
      (Subscript["\[FormalQ]", ToString[#1]] & ) /@ Range[Length[Normal[cospan]]], "UniversalObjectName" -> "\[FormalCapitalQ]"]] /; 
   Length[DeleteDuplicates[(Last[Last[#1]] & ) /@ Normal[cospan]]] == 1
AbstractPullback[cospan_Association, projectionMorphismNames_List, compositionSymbol_] := 
  AbstractPullback[Association["CommonImage" -> Last[Last[First[Normal[cospan]]]], 
     "CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> OverTilde, 
     "MorphismDomains" -> (First[Last[#1]] & ) /@ Normal[cospan], "MorphismNames" -> First /@ Normal[cospan], 
     "ProjectionMorphismNames" -> projectionMorphismNames, "PullbackSymbol" -> Cross, "UniqueMorphismName" -> "\[FormalU]", 
     "UniversalMorphismNames" -> (Subscript["\[FormalQ]", ToString[#1]] & ) /@ Range[Length[Normal[cospan]]], 
     "UniversalObjectName" -> "\[FormalCapitalQ]"]] /; Length[DeleteDuplicates[(Last[Last[#1]] & ) /@ Normal[cospan]]] == 1
AbstractPullback[cospan_Association, projectionMorphismNames_List, compositionSymbol_, identitySymbol_] := 
  AbstractPullback[Association["CommonImage" -> Last[Last[First[Normal[cospan]]]], 
     "CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
     "MorphismDomains" -> (First[Last[#1]] & ) /@ Normal[cospan], "MorphismNames" -> First /@ Normal[cospan], 
     "ProjectionMorphismNames" -> projectionMorphismNames, "PullbackSymbol" -> Cross, "UniqueMorphismName" -> "\[FormalU]", 
     "UniversalMorphismNames" -> (Subscript["\[FormalQ]", ToString[#1]] & ) /@ Range[Length[Normal[cospan]]], 
     "UniversalObjectName" -> "\[FormalCapitalQ]"]] /; Length[DeleteDuplicates[(Last[Last[#1]] & ) /@ Normal[cospan]]] == 1
AbstractPullback[cospan_Association, pullbackSymbol_, compositionSymbol_] := 
  AbstractPullback[Association["CommonImage" -> Last[Last[First[Normal[cospan]]]], 
     "CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> OverTilde, 
     "MorphismDomains" -> (First[Last[#1]] & ) /@ Normal[cospan], "MorphismNames" -> First /@ Normal[cospan], 
     "ProjectionMorphismNames" -> (Subscript["\[FormalP]", ToString[#1]] & ) /@ Range[Length[Normal[cospan]]], 
     "PullbackSymbol" -> pullbackSymbol, "UniqueMorphismName" -> "\[FormalU]", "UniversalMorphismNames" -> 
      (Subscript["\[FormalQ]", ToString[#1]] & ) /@ Range[Length[Normal[cospan]]], "UniversalObjectName" -> "\[FormalCapitalQ]"]] /; 
    !ListQ[pullbackSymbol] &&  !ListQ[compositionSymbol] && 
    Length[DeleteDuplicates[(Last[Last[#1]] & ) /@ Normal[cospan]]] == 1
AbstractPullback[cospan_Association, pullbackSymbol_, compositionSymbol_, identitySymbol_] := 
  AbstractPullback[Association["CommonImage" -> Last[Last[First[Normal[cospan]]]], 
     "CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
     "MorphismDomains" -> (First[Last[#1]] & ) /@ Normal[cospan], "MorphismNames" -> First /@ Normal[cospan], 
     "ProjectionMorphismNames" -> (Subscript["\[FormalP]", ToString[#1]] & ) /@ Range[Length[Normal[cospan]]], 
     "PullbackSymbol" -> pullbackSymbol, "UniqueMorphismName" -> "\[FormalU]", "UniversalMorphismNames" -> 
      (Subscript["\[FormalQ]", ToString[#1]] & ) /@ Range[Length[Normal[cospan]]], "UniversalObjectName" -> "\[FormalCapitalQ]"]] /; 
    !ListQ[pullbackSymbol] &&  !ListQ[compositionSymbol] &&  !ListQ[identitySymbol] && 
    Length[DeleteDuplicates[(Last[Last[#1]] & ) /@ Normal[cospan]]] == 1
AbstractPullback[pullback_Association] := AbstractPullback[KeySort[pullback]] /; 
   KeyExistsQ[pullback, "CommonImage"] && KeyExistsQ[pullback, "CompositionSymbol"] && 
    KeyExistsQ[pullback, "IdentitySymbol"] && KeyExistsQ[pullback, "MorphismDomains"] && 
    KeyExistsQ[pullback, "MorphismNames"] && KeyExistsQ[pullback, "ProjectionMorphismNames"] && 
    KeyExistsQ[pullback, "PullbackSymbol"] && KeyExistsQ[pullback, "UniqueMorphismName"] && 
    KeyExistsQ[pullback, "UniversalMorphismNames"] && KeyExistsQ[pullback, "UniversalObjectName"] && 
    Keys[KeySort[pullback]] =!= Keys[pullback]
AbstractPullback[AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]], 
   newPullbackSymbol_] := AbstractPullback[Association["CommonImage" -> commonImage, 
    "CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, "MorphismDomains" -> morphismDomains, 
    "MorphismNames" -> morphismNames, "ProjectionMorphismNames" -> projectionMorphismNames, 
    "PullbackSymbol" -> newPullbackSymbol, "UniqueMorphismName" -> uniqueMorphismName, 
    "UniversalMorphismNames" -> universalMorphismNames, "UniversalObjectName" -> universalObjectName]]
AbstractPullback[AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]], 
   newPullbackSymbol_, newCompositionSymbol_] := AbstractPullback[Association["CommonImage" -> commonImage, 
    "CompositionSymbol" -> newCompositionSymbol, "IdentitySymbol" -> identitySymbol, 
    "MorphismDomains" -> morphismDomains, "MorphismNames" -> morphismNames, 
    "ProjectionMorphismNames" -> projectionMorphismNames, "PullbackSymbol" -> newPullbackSymbol, 
    "UniqueMorphismName" -> uniqueMorphismName, "UniversalMorphismNames" -> universalMorphismNames, 
    "UniversalObjectName" -> universalObjectName]]
AbstractPullback[AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]], 
   newPullbackSymbol_, newCompositionSymbol_, newIdentitySymbol_] := 
  AbstractPullback[Association["CommonImage" -> commonImage, "CompositionSymbol" -> newCompositionSymbol, 
    "IdentitySymbol" -> newIdentitySymbol, "MorphismDomains" -> morphismDomains, "MorphismNames" -> morphismNames, 
    "ProjectionMorphismNames" -> projectionMorphismNames, "PullbackSymbol" -> newPullbackSymbol, 
    "UniqueMorphismName" -> uniqueMorphismName, "UniversalMorphismNames" -> universalMorphismNames, 
    "UniversalObjectName" -> universalObjectName]]
AbstractPullback[Association["CommonImage" -> commonImage_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismDomains" -> morphismDomains_List, 
     "MorphismNames" -> morphismNames_List, "ProjectionMorphismNames" -> projectionMorphismNames_List, 
     "PullbackSymbol" -> pullbackSymbol_, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   (abstractCategory_)[Association["CompositionSymbol" -> categoryCompositionSymbol_, 
     "IdentitySymbol" -> categoryIdentitySymbol_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]] := Module[{morphismAssociation, compositions, reducedMorphismAssociation, 
     reducedCompositions, morphismEquivalenceGraph, newArrows, arrowCount, newMorphismEquivalences}, 
    morphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[categoryCompositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], categoryCompositionSymbol[First[Last[#1]], First[
                First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, 
      Length[objects]]; morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. categoryCompositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. categoryCompositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], categoryIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], categoryIdentitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ objects; reducedMorphismAssociation = 
      Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[arrows, arrowEquivalences], 
          quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[reducedCompositions = Select[Tuples[Normal[reducedMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[reducedMorphismAssociation], StringDelete[ToString[categoryCompositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          reducedMorphismAssociation = Association[Append[Normal[reducedMorphismAssociation], 
             categoryCompositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ reducedCompositions, 
      Length[reduceObjects[objects, quiverObjectEquivalences]]]; reducedMorphismAssociation = 
      Association[Select[Normal[reducedMorphismAssociation], 
        Length[Flatten[{First[#1] /. categoryCompositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. categoryCompositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[reducedMorphismAssociation], categoryIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        reducedMorphismAssociation = Association[Append[Normal[reducedMorphismAssociation], 
           categoryIdentitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[objects, quiverObjectEquivalences]; 
     morphismEquivalenceGraph = Graph[Join[EdgeList[TransitiveClosureGraph[
          Graph[Apply[UndirectedEdge, Join[arrowEquivalences, morphismEquivalences], {1}]]]], 
        (UndirectedEdge[#1, #1] & ) /@ First /@ Normal[morphismAssociation]]]; newArrows = {}; 
     newMorphismEquivalences = If[Length[morphismDomains] > 1, 
       (categoryCompositionSymbol[morphismNames[[#1]], projectionMorphismNames[[#1]]] == 
          categoryCompositionSymbol[morphismNames[[#1 + 1]], projectionMorphismNames[[#1 + 1]]] & ) /@ 
        Range[Length[reduceObjects[reduceObjects[morphismDomains, quiverObjectEquivalences], objectEquivalences]] - 1], 
       {}]; arrowCount = 0; (Module[{object = #1, isUniversalObject, universalMorphisms, projectionMorphisms}, 
        isUniversalObject = True; universalMorphisms = {}; projectionMorphisms = {}; 
         (Module[{pullbackObject = #1}, If[Length[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[
                   reducedMorphismAssociation, morphismEquivalences], objectEquivalences]], First[Last[#1]] === object && 
                  Last[Last[#1]] === pullbackObject & ]] == 0, isUniversalObject = False]] & ) /@ 
          reduceObjects[reduceObjects[morphismDomains, quiverObjectEquivalences], objectEquivalences]; 
         If[isUniversalObject, (Module[{pullbackObjectIndex = #1, pullbackObject, nextPullbackObject, morphism, 
              nextMorphism, projectionMorphism, nextProjectionMorphism, isCommutative}, 
             pullbackObject = morphismDomains[[pullbackObjectIndex]]; nextPullbackObject = morphismDomains[[
                pullbackObjectIndex + 1]]; morphism = morphismNames[[pullbackObjectIndex]]; nextMorphism = morphismNames[[
                pullbackObjectIndex + 1]]; projectionMorphism = projectionMorphismNames[[pullbackObjectIndex]]; 
              nextProjectionMorphism = projectionMorphismNames[[pullbackObjectIndex + 1]]; isCommutative = False; 
              (Module[{universalMorphism = #1}, (Module[{nextUniversalMorphism = #1}, If[MemberQ[VertexList[
                        morphismEquivalenceGraph], categoryCompositionSymbol[morphism, First[universalMorphism]]] && 
                      MemberQ[VertexList[morphismEquivalenceGraph], categoryCompositionSymbol[nextMorphism, 
                        First[nextUniversalMorphism]]], If[Length[FindShortestPath[morphismEquivalenceGraph, 
                         categoryCompositionSymbol[morphism, First[universalMorphism]], categoryCompositionSymbol[
                          nextMorphism, First[nextUniversalMorphism]]]] > 0, isCommutative = True; universalMorphisms = 
                        Join[universalMorphisms, {universalMorphism, nextUniversalMorphism}]; projectionMorphisms = 
                        Join[projectionMorphisms, {projectionMorphism, nextProjectionMorphism}]]]] & ) /@ 
                  Select[Normal[reduceArrowsFinal[reduceArrowsInitial[reducedMorphismAssociation, morphismEquivalences], 
                     objectEquivalences]], First[Last[#1]] === object && Last[Last[#1]] === 
                      nextPullbackObject & ]] & ) /@ Select[Normal[reduceArrowsFinal[reduceArrowsInitial[
                   reducedMorphismAssociation, morphismEquivalences], objectEquivalences]], First[Last[#1]] === object && 
                  Last[Last[#1]] === pullbackObject & ]; If[ !isCommutative, isUniversalObject = False]] & ) /@ 
           Range[Length[reduceObjects[reduceObjects[morphismDomains, quiverObjectEquivalences], objectEquivalences]] - 
             1]]; If[isUniversalObject, If[Length[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[
                 reducedMorphismAssociation, morphismEquivalences], objectEquivalences]], First[Last[#1]] === object && 
                Last[Last[#1]] === pullbackSymbol @@ morphismDomains & ]] == 0, arrowCount += 1; 
            newArrows = Append[newArrows, Subscript[uniqueMorphismName, ToString[arrowCount]] -> DirectedEdge[object, 
                pullbackSymbol @@ morphismDomains]]; (Module[{morphismIndex = #1}, newMorphismEquivalences = 
                Append[newMorphismEquivalences, First[universalMorphisms[[morphismIndex]]] == categoryCompositionSymbol[
                   projectionMorphisms[[morphismIndex]], Subscript[uniqueMorphismName, ToString[arrowCount]]]]] & ) /@ 
             Range[Length[universalMorphisms]]; newMorphismEquivalences = Append[newMorphismEquivalences, 
              categoryCompositionSymbol[Last[morphismNames], categoryCompositionSymbol[Last[projectionMorphismNames], 
                 Subscript[uniqueMorphismName, ToString[arrowCount]]]] == categoryCompositionSymbol[
                categoryCompositionSymbol[Last[morphismNames], Last[projectionMorphismNames]], Subscript[
                 uniqueMorphismName, ToString[arrowCount]]]]]]] & ) /@ 
      reduceObjects[reduceObjects[objects, quiverObjectEquivalences], objectEquivalences]; 
     ResourceFunction["AbstractCategory"][Association["CompositionSymbol" -> categoryCompositionSymbol, 
       "IdentitySymbol" -> categoryIdentitySymbol, "MorphismEquivalences" -> 
        DeleteDuplicates[Join[morphismEquivalences, newMorphismEquivalences]], "ObjectEquivalences" -> 
        objectEquivalences, "Quiver" -> ResourceFunction["AbstractQuiver"][
         Association["ArrowEquivalences" -> arrowEquivalences, "Arrows" -> Association[DeleteDuplicates[
             Join[Normal[arrows], (morphismNames[[#1]] -> DirectedEdge[morphismDomains[[#1]], commonImage] & ) /@ Range[
                Length[reduceObjects[reduceObjects[morphismDomains, quiverObjectEquivalences], objectEquivalences]]], 
              (projectionMorphismNames[[#1]] -> DirectedEdge[pullbackSymbol @@ morphismDomains, morphismDomains[[
                   #1]]] & ) /@ Range[Length[reduceObjects[reduceObjects[morphismDomains, quiverObjectEquivalences], 
                  objectEquivalences]]], newArrows]]], "ObjectEquivalences" -> quiverObjectEquivalences, 
          "Objects" -> DeleteDuplicates[Join[objects, morphismDomains, {commonImage, pullbackSymbol @@ 
               morphismDomains}]]]]]]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"

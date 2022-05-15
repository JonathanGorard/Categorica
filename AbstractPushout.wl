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
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["Objects"] := 
  Join[morphismImages, {commonDomain, pushoutSymbol @@ morphismImages}]
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["ObjectCount"] := 
  Length[Join[morphismImages, {commonDomain, pushoutSymbol @@ morphismImages}]]
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["MorphismAssociation"] := 
  Association[Join[(morphismNames[[#1]] -> DirectedEdge[commonDomain, morphismImages[[#1]]] & ) /@ 
     Range[Length[morphismImages]], (injectionMorphismNames[[#1]] -> DirectedEdge[morphismImages[[#1]], 
        pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
    (compositionSymbol[injectionMorphismNames[[#1]], morphismNames[[#1]]] -> DirectedEdge[commonDomain, 
        pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
    (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ morphismImages, 
    {identitySymbol[commonDomain] -> DirectedEdge[commonDomain, commonDomain], 
     identitySymbol[pushoutSymbol @@ morphismImages] -> DirectedEdge[pushoutSymbol @@ morphismImages, 
       pushoutSymbol @@ morphismImages]}]]
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["MorphismNames"] := 
  First /@ Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[commonDomain, morphismImages[[#1]]] & ) /@ 
       Range[Length[morphismImages]], (injectionMorphismNames[[#1]] -> DirectedEdge[morphismImages[[#1]], 
          pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
      (compositionSymbol[injectionMorphismNames[[#1]], morphismNames[[#1]]] -> DirectedEdge[commonDomain, 
          pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
      (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ morphismImages, 
      {identitySymbol[commonDomain] -> DirectedEdge[commonDomain, commonDomain], 
       identitySymbol[pushoutSymbol @@ morphismImages] -> DirectedEdge[pushoutSymbol @@ morphismImages, 
         pushoutSymbol @@ morphismImages]}]]]
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["MorphismEdges"] := 
  (DirectedEdge @@ Last[#1] & ) /@ 
   Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[commonDomain, morphismImages[[#1]]] & ) /@ 
       Range[Length[morphismImages]], (injectionMorphismNames[[#1]] -> DirectedEdge[morphismImages[[#1]], 
          pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
      (compositionSymbol[injectionMorphismNames[[#1]], morphismNames[[#1]]] -> DirectedEdge[commonDomain, 
          pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
      (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ morphismImages, 
      {identitySymbol[commonDomain] -> DirectedEdge[commonDomain, commonDomain], 
       identitySymbol[pushoutSymbol @@ morphismImages] -> DirectedEdge[pushoutSymbol @@ morphismImages, 
         pushoutSymbol @@ morphismImages]}]]]
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["MorphismCount"] := 
  Length[Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[commonDomain, morphismImages[[#1]]] & ) /@ 
       Range[Length[morphismImages]], (injectionMorphismNames[[#1]] -> DirectedEdge[morphismImages[[#1]], 
          pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
      (compositionSymbol[injectionMorphismNames[[#1]], morphismNames[[#1]]] -> DirectedEdge[commonDomain, 
          pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
      (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ morphismImages, 
      {identitySymbol[commonDomain] -> DirectedEdge[commonDomain, commonDomain], 
       identitySymbol[pushoutSymbol @@ morphismImages] -> DirectedEdge[pushoutSymbol @@ morphismImages, 
         pushoutSymbol @@ morphismImages]}]]]]
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["ReducedMorphismAssociation"] := 
  Association[Join[(morphismNames[[#1]] -> DirectedEdge[commonDomain, morphismImages[[#1]]] & ) /@ 
     Range[Length[morphismImages]], (injectionMorphismNames[[#1]] -> DirectedEdge[morphismImages[[#1]], 
        pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
    {compositionSymbol[Last[injectionMorphismNames], Last[morphismNames]] -> DirectedEdge[commonDomain, 
       pushoutSymbol @@ morphismImages]}, (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ morphismImages, 
    {identitySymbol[commonDomain] -> DirectedEdge[commonDomain, commonDomain], 
     identitySymbol[pushoutSymbol @@ morphismImages] -> DirectedEdge[pushoutSymbol @@ morphismImages, 
       pushoutSymbol @@ morphismImages]}]]
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["ReducedMorphismNames"] := 
  First /@ Normal[Association[(morphismNames[[#1]] -> DirectedEdge[commonDomain, morphismImages[[#1]]] & ) /@ 
      Range[Length[morphismImages]], (injectionMorphismNames[[#1]] -> DirectedEdge[morphismImages[[#1]], 
         pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
     {compositionSymbol[Last[injectionMorphismNames], Last[morphismNames]] -> DirectedEdge[commonDomain, 
        pushoutSymbol @@ morphismImages]}, (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ morphismImages, 
     {identitySymbol[commonDomain] -> DirectedEdge[commonDomain, commonDomain], 
      identitySymbol[pushoutSymbol @@ morphismImages] -> DirectedEdge[pushoutSymbol @@ morphismImages, 
        pushoutSymbol @@ morphismImages]}]]
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["ReducedMorphismEdges"] := 
  (DirectedEdge @@ Last[#1] & ) /@ 
   Normal[Association[(morphismNames[[#1]] -> DirectedEdge[commonDomain, morphismImages[[#1]]] & ) /@ 
      Range[Length[morphismImages]], (injectionMorphismNames[[#1]] -> DirectedEdge[morphismImages[[#1]], 
         pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
     {compositionSymbol[Last[injectionMorphismNames], Last[morphismNames]] -> DirectedEdge[commonDomain, 
        pushoutSymbol @@ morphismImages]}, (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ morphismImages, 
     {identitySymbol[commonDomain] -> DirectedEdge[commonDomain, commonDomain], 
      identitySymbol[pushoutSymbol @@ morphismImages] -> DirectedEdge[pushoutSymbol @@ morphismImages, 
        pushoutSymbol @@ morphismImages]}]]
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["ReducedMorphismCount"] := 
  Length[Normal[Association[(morphismNames[[#1]] -> DirectedEdge[commonDomain, morphismImages[[#1]]] & ) /@ 
      Range[Length[morphismImages]], (injectionMorphismNames[[#1]] -> DirectedEdge[morphismImages[[#1]], 
         pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
     {compositionSymbol[Last[injectionMorphismNames], Last[morphismNames]] -> DirectedEdge[commonDomain, 
        pushoutSymbol @@ morphismImages]}, (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ morphismImages, 
     {identitySymbol[commonDomain] -> DirectedEdge[commonDomain, commonDomain], 
      identitySymbol[pushoutSymbol @@ morphismImages] -> DirectedEdge[pushoutSymbol @@ morphismImages, 
        pushoutSymbol @@ morphismImages]}]]]
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["SimpleMorphismAssociation"] := 
  Association[Join[(morphismNames[[#1]] -> DirectedEdge[commonDomain, morphismImages[[#1]]] & ) /@ 
     Range[Length[morphismImages]], (injectionMorphismNames[[#1]] -> DirectedEdge[morphismImages[[#1]], 
        pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
    {compositionSymbol[First[injectionMorphismNames], First[morphismNames]] -> DirectedEdge[commonDomain, 
       pushoutSymbol @@ morphismImages]}]]
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["SimpleMorphismNames"] := 
  First /@ Normal[Association[(morphismNames[[#1]] -> DirectedEdge[commonDomain, morphismImages[[#1]]] & ) /@ 
      Range[Length[morphismImages]], (injectionMorphismNames[[#1]] -> DirectedEdge[morphismImages[[#1]], 
         pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
     {compositionSymbol[First[injectionMorphismNames], First[morphismNames]] -> DirectedEdge[commonDomain, 
        pushoutSymbol @@ morphismImages]}]]
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["SimpleMorphismEdges"] := 
  (DirectedEdge @@ Last[#1] & ) /@ 
   Normal[Association[(morphismNames[[#1]] -> DirectedEdge[commonDomain, morphismImages[[#1]]] & ) /@ 
      Range[Length[morphismImages]], (injectionMorphismNames[[#1]] -> DirectedEdge[morphismImages[[#1]], 
         pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
     {compositionSymbol[First[injectionMorphismNames], First[morphismNames]] -> DirectedEdge[commonDomain, 
        pushoutSymbol @@ morphismImages]}]]
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["SimpleMorphismCount"] := 
  Length[Normal[Association[(morphismNames[[#1]] -> DirectedEdge[commonDomain, morphismImages[[#1]]] & ) /@ 
      Range[Length[morphismImages]], (injectionMorphismNames[[#1]] -> DirectedEdge[morphismImages[[#1]], 
         pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
     {compositionSymbol[First[injectionMorphismNames], First[morphismNames]] -> DirectedEdge[commonDomain, 
        pushoutSymbol @@ morphismImages]}]]]
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["ReducedSimpleMorphismAssociation"] := 
  Association[Join[(morphismNames[[#1]] -> DirectedEdge[commonDomain, morphismImages[[#1]]] & ) /@ 
     Range[Length[morphismImages]], (injectionMorphismNames[[#1]] -> DirectedEdge[morphismImages[[#1]], 
        pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
    {compositionSymbol[Last[injectionMorphismNames], Last[morphismNames]] -> DirectedEdge[commonDomain, 
       pushoutSymbol @@ morphismImages]}]]
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["ReducedSimpleMorphismNames"] := 
  First /@ Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[commonDomain, morphismImages[[#1]]] & ) /@ 
       Range[Length[morphismImages]], (injectionMorphismNames[[#1]] -> DirectedEdge[morphismImages[[#1]], 
          pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
      {compositionSymbol[Last[injectionMorphismNames], Last[morphismNames]] -> DirectedEdge[commonDomain, 
         pushoutSymbol @@ morphismImages]}]]]
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["ReducedSimpleMorphismEdges"] := 
  (DirectedEdge @@ Last[#1] & ) /@ 
   Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[commonDomain, morphismImages[[#1]]] & ) /@ 
       Range[Length[morphismImages]], (injectionMorphismNames[[#1]] -> DirectedEdge[morphismImages[[#1]], 
          pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
      {compositionSymbol[Last[injectionMorphismNames], Last[morphismNames]] -> DirectedEdge[commonDomain, 
         pushoutSymbol @@ morphismImages]}]]]
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["ReducedSimpleMorphismCount"] := 
  Length[Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[commonDomain, morphismImages[[#1]]] & ) /@ 
       Range[Length[morphismImages]], (injectionMorphismNames[[#1]] -> DirectedEdge[morphismImages[[#1]], 
          pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
      {compositionSymbol[Last[injectionMorphismNames], Last[morphismNames]] -> DirectedEdge[commonDomain, 
         pushoutSymbol @@ morphismImages]}]]]]
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["UniversalObjects"] := 
  Join[morphismImages, {commonDomain, pushoutSymbol @@ morphismImages, 
    Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]}]
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["UniversalObjectCount"] := 
  Length[Join[morphismImages, {commonDomain, pushoutSymbol @@ morphismImages, 
     Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]}]]
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["UniversalMorphismAssociation"] := 
  Association[Join[(morphismNames[[#1]] -> DirectedEdge[commonDomain, morphismImages[[#1]]] & ) /@ 
     Range[Length[morphismImages]], (injectionMorphismNames[[#1]] -> DirectedEdge[morphismImages[[#1]], 
        pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
    (Subscript["\[ForAll]", ToString[universalMorphismNames[[#1]], StandardForm]] -> DirectedEdge[morphismImages[[#1]], 
        Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]] & ) /@ Range[Length[morphismImages]], 
    (compositionSymbol[injectionMorphismNames[[#1]], morphismNames[[#1]]] -> DirectedEdge[commonDomain, 
        pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
    (compositionSymbol[uniqueMorphismName, injectionMorphismNames[[#1]]] -> DirectedEdge[morphismImages[[#1]], 
        Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]] & ) /@ Range[Length[morphismImages]], 
    (compositionSymbol[universalMorphismNames[[#1]], morphismNames[[#1]]] -> DirectedEdge[commonDomain, 
        Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]] & ) /@ Range[Length[morphismImages]], 
    (compositionSymbol[compositionSymbol[uniqueMorphismName, injectionMorphismNames[[#1]]], morphismNames[[#1]]] -> 
       DirectedEdge[commonDomain, Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]] & ) /@ 
     Range[Length[morphismImages]], (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ morphismImages, 
    {identitySymbol[commonDomain] -> DirectedEdge[commonDomain, commonDomain], 
     identitySymbol[pushoutSymbol @@ morphismImages] -> DirectedEdge[pushoutSymbol @@ morphismImages, 
       pushoutSymbol @@ morphismImages], identitySymbol[universalObjectName] -> 
      DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], 
       Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]], 
     Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> DirectedEdge[pushoutSymbol @@ morphismImages, 
       Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]]}]]
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["UniversalMorphismNames"] := 
  First /@ Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[commonDomain, morphismImages[[#1]]] & ) /@ 
       Range[Length[morphismImages]], (injectionMorphismNames[[#1]] -> DirectedEdge[morphismImages[[#1]], 
          pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
      (Subscript["\[ForAll]", ToString[universalMorphismNames[[#1]], StandardForm]] -> DirectedEdge[morphismImages[[#1]], 
          Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]] & ) /@ Range[Length[morphismImages]], 
      (compositionSymbol[injectionMorphismNames[[#1]], morphismNames[[#1]]] -> DirectedEdge[commonDomain, 
          pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
      (compositionSymbol[uniqueMorphismName, injectionMorphismNames[[#1]]] -> DirectedEdge[morphismImages[[#1]], 
          Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]] & ) /@ Range[Length[morphismImages]], 
      (compositionSymbol[universalMorphismNames[[#1]], morphismNames[[#1]]] -> DirectedEdge[commonDomain, 
          Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]] & ) /@ Range[Length[morphismImages]], 
      (compositionSymbol[compositionSymbol[uniqueMorphismName, injectionMorphismNames[[#1]]], morphismNames[[#1]]] -> 
         DirectedEdge[commonDomain, Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]] & ) /@ 
       Range[Length[morphismImages]], (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ morphismImages, 
      {identitySymbol[commonDomain] -> DirectedEdge[commonDomain, commonDomain], 
       identitySymbol[pushoutSymbol @@ morphismImages] -> DirectedEdge[pushoutSymbol @@ morphismImages, 
         pushoutSymbol @@ morphismImages], identitySymbol[universalObjectName] -> 
        DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], 
         Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]], 
       Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> DirectedEdge[pushoutSymbol @@ morphismImages, 
         Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]]}]]]
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["UniversalMorphismEdges"] := 
  (DirectedEdge @@ Last[#1] & ) /@ 
   Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[commonDomain, morphismImages[[#1]]] & ) /@ 
       Range[Length[morphismImages]], (injectionMorphismNames[[#1]] -> DirectedEdge[morphismImages[[#1]], 
          pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
      (Subscript["\[ForAll]", ToString[universalMorphismNames[[#1]], StandardForm]] -> DirectedEdge[morphismImages[[#1]], 
          Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]] & ) /@ Range[Length[morphismImages]], 
      (compositionSymbol[injectionMorphismNames[[#1]], morphismNames[[#1]]] -> DirectedEdge[commonDomain, 
          pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
      (compositionSymbol[uniqueMorphismName, injectionMorphismNames[[#1]]] -> DirectedEdge[morphismImages[[#1]], 
          Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]] & ) /@ Range[Length[morphismImages]], 
      (compositionSymbol[universalMorphismNames[[#1]], morphismNames[[#1]]] -> DirectedEdge[commonDomain, 
          Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]] & ) /@ Range[Length[morphismImages]], 
      (compositionSymbol[compositionSymbol[uniqueMorphismName, injectionMorphismNames[[#1]]], morphismNames[[#1]]] -> 
         DirectedEdge[commonDomain, Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]] & ) /@ 
       Range[Length[morphismImages]], (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ morphismImages, 
      {identitySymbol[commonDomain] -> DirectedEdge[commonDomain, commonDomain], 
       identitySymbol[pushoutSymbol @@ morphismImages] -> DirectedEdge[pushoutSymbol @@ morphismImages, 
         pushoutSymbol @@ morphismImages], identitySymbol[universalObjectName] -> 
        DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], 
         Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]], 
       Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> DirectedEdge[pushoutSymbol @@ morphismImages, 
         Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]]}]]]
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["UniversalMorphismCount"] := 
  Length[Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[commonDomain, morphismImages[[#1]]] & ) /@ 
       Range[Length[morphismImages]], (injectionMorphismNames[[#1]] -> DirectedEdge[morphismImages[[#1]], 
          pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
      (Subscript["\[ForAll]", ToString[universalMorphismNames[[#1]], StandardForm]] -> DirectedEdge[morphismImages[[#1]], 
          Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]] & ) /@ Range[Length[morphismImages]], 
      (compositionSymbol[injectionMorphismNames[[#1]], morphismNames[[#1]]] -> DirectedEdge[commonDomain, 
          pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
      (compositionSymbol[uniqueMorphismName, injectionMorphismNames[[#1]]] -> DirectedEdge[morphismImages[[#1]], 
          Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]] & ) /@ Range[Length[morphismImages]], 
      (compositionSymbol[universalMorphismNames[[#1]], morphismNames[[#1]]] -> DirectedEdge[commonDomain, 
          Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]] & ) /@ Range[Length[morphismImages]], 
      (compositionSymbol[compositionSymbol[uniqueMorphismName, injectionMorphismNames[[#1]]], morphismNames[[#1]]] -> 
         DirectedEdge[commonDomain, Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]] & ) /@ 
       Range[Length[morphismImages]], (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ morphismImages, 
      {identitySymbol[commonDomain] -> DirectedEdge[commonDomain, commonDomain], 
       identitySymbol[pushoutSymbol @@ morphismImages] -> DirectedEdge[pushoutSymbol @@ morphismImages, 
         pushoutSymbol @@ morphismImages], identitySymbol[universalObjectName] -> 
        DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], 
         Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]], 
       Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> DirectedEdge[pushoutSymbol @@ morphismImages, 
         Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]]}]]]]
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["UniversalReducedMorphismAssociation"] := 
  Association[Join[(morphismNames[[#1]] -> DirectedEdge[commonDomain, morphismImages[[#1]]] & ) /@ 
     Range[Length[morphismImages]], (injectionMorphismNames[[#1]] -> DirectedEdge[morphismImages[[#1]], 
        pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
    {compositionSymbol[Last[injectionMorphismNames], Last[morphismNames]] -> DirectedEdge[commonDomain, 
       pushoutSymbol @@ morphismImages]}, (compositionSymbol[uniqueMorphismName, injectionMorphismNames[[#1]]] -> 
       DirectedEdge[morphismImages[[#1]], Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]] & ) /@ 
     Range[Length[morphismImages]], {compositionSymbol[compositionSymbol[uniqueMorphismName, 
        Last[injectionMorphismNames]], Last[morphismNames]] -> DirectedEdge[commonDomain, 
       Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]]}, 
    (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ morphismImages, 
    {identitySymbol[commonDomain] -> DirectedEdge[commonDomain, commonDomain], 
     identitySymbol[pushoutSymbol @@ morphismImages] -> DirectedEdge[pushoutSymbol @@ morphismImages, 
       pushoutSymbol @@ morphismImages], identitySymbol[universalObjectName] -> 
      DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], 
       Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]], 
     Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> DirectedEdge[pushoutSymbol @@ morphismImages, 
       Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]]}]]
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["UniversalReducedMorphismNames"] := 
  First /@ Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[commonDomain, morphismImages[[#1]]] & ) /@ 
       Range[Length[morphismImages]], (injectionMorphismNames[[#1]] -> DirectedEdge[morphismImages[[#1]], 
          pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
      {compositionSymbol[Last[injectionMorphismNames], Last[morphismNames]] -> DirectedEdge[commonDomain, 
         pushoutSymbol @@ morphismImages]}, (compositionSymbol[uniqueMorphismName, injectionMorphismNames[[#1]]] -> 
         DirectedEdge[morphismImages[[#1]], Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]] & ) /@ 
       Range[Length[morphismImages]], {compositionSymbol[compositionSymbol[uniqueMorphismName, 
          Last[injectionMorphismNames]], Last[morphismNames]] -> DirectedEdge[commonDomain, 
         Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]]}, 
      (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ morphismImages, 
      {identitySymbol[commonDomain] -> DirectedEdge[commonDomain, commonDomain], 
       identitySymbol[pushoutSymbol @@ morphismImages] -> DirectedEdge[pushoutSymbol @@ morphismImages, 
         pushoutSymbol @@ morphismImages], identitySymbol[universalObjectName] -> 
        DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], 
         Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]], 
       Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> DirectedEdge[pushoutSymbol @@ morphismImages, 
         Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]]}]]]
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["UniversalReducedMorphismEdges"] := 
  (DirectedEdge @@ Last[#1] & ) /@ 
   Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[commonDomain, morphismImages[[#1]]] & ) /@ 
       Range[Length[morphismImages]], (injectionMorphismNames[[#1]] -> DirectedEdge[morphismImages[[#1]], 
          pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
      {compositionSymbol[Last[injectionMorphismNames], Last[morphismNames]] -> DirectedEdge[commonDomain, 
         pushoutSymbol @@ morphismImages]}, (compositionSymbol[uniqueMorphismName, injectionMorphismNames[[#1]]] -> 
         DirectedEdge[morphismImages[[#1]], Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]] & ) /@ 
       Range[Length[morphismImages]], {compositionSymbol[compositionSymbol[uniqueMorphismName, 
          Last[injectionMorphismNames]], Last[morphismNames]] -> DirectedEdge[commonDomain, 
         Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]]}, 
      (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ morphismImages, 
      {identitySymbol[commonDomain] -> DirectedEdge[commonDomain, commonDomain], 
       identitySymbol[pushoutSymbol @@ morphismImages] -> DirectedEdge[pushoutSymbol @@ morphismImages, 
         pushoutSymbol @@ morphismImages], identitySymbol[universalObjectName] -> 
        DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], 
         Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]], 
       Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> DirectedEdge[pushoutSymbol @@ morphismImages, 
         Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]]}]]]
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["UniversalReducedMorphismCount"] := 
  Length[Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[commonDomain, morphismImages[[#1]]] & ) /@ 
       Range[Length[morphismImages]], (injectionMorphismNames[[#1]] -> DirectedEdge[morphismImages[[#1]], 
          pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
      {compositionSymbol[Last[injectionMorphismNames], Last[morphismNames]] -> DirectedEdge[commonDomain, 
         pushoutSymbol @@ morphismImages]}, (compositionSymbol[uniqueMorphismName, injectionMorphismNames[[#1]]] -> 
         DirectedEdge[morphismImages[[#1]], Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]] & ) /@ 
       Range[Length[morphismImages]], {compositionSymbol[compositionSymbol[uniqueMorphismName, 
          Last[injectionMorphismNames]], Last[morphismNames]] -> DirectedEdge[commonDomain, 
         Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]]}, 
      (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ morphismImages, 
      {identitySymbol[commonDomain] -> DirectedEdge[commonDomain, commonDomain], 
       identitySymbol[pushoutSymbol @@ morphismImages] -> DirectedEdge[pushoutSymbol @@ morphismImages, 
         pushoutSymbol @@ morphismImages], identitySymbol[universalObjectName] -> 
        DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], 
         Subscript["\[ForAll]", ToString[universalObjectName]]], 
       Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> DirectedEdge[pushoutSymbol @@ morphismImages, 
         Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]]}]]]]
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["UniversalSimpleMorphismAssociation"] := 
  Association[Join[(morphismNames[[#1]] -> DirectedEdge[commonDomain, morphismImages[[#1]]] & ) /@ 
     Range[Length[morphismImages]], (injectionMorphismNames[[#1]] -> DirectedEdge[morphismImages[[#1]], 
        pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
    (Subscript["\[ForAll]", ToString[universalMorphismNames[[#1]], StandardForm]] -> DirectedEdge[morphismImages[[#1]], 
        Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]] & ) /@ Range[Length[morphismImages]], 
    {compositionSymbol[First[injectionMorphismNames], First[morphismNames]] -> DirectedEdge[commonDomain, 
       pushoutSymbol @@ morphismImages], compositionSymbol[First[universalMorphismNames], First[morphismNames]] -> 
      DirectedEdge[commonDomain, Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]], 
     Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> DirectedEdge[pushoutSymbol @@ morphismImages, 
       Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]]}]]
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["UniversalSimpleMorphismNames"] := 
  First /@ Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[commonDomain, morphismImages[[#1]]] & ) /@ 
       Range[Length[morphismImages]], (injectionMorphismNames[[#1]] -> DirectedEdge[morphismImages[[#1]], 
          pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
      (Subscript["\[ForAll]", ToString[universalMorphismNames[[#1]], StandardForm]] -> DirectedEdge[morphismImages[[#1]], 
          Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]] & ) /@ Range[Length[morphismImages]], 
      {compositionSymbol[First[injectionMorphismNames], First[morphismNames]] -> DirectedEdge[commonDomain, 
         pushoutSymbol @@ morphismImages], compositionSymbol[First[universalMorphismNames], First[morphismNames]] -> 
        DirectedEdge[commonDomain, Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]], 
       Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> DirectedEdge[pushoutSymbol @@ morphismImages, 
         Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]]}]]]
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["UniversalSimpleMorphismEdges"] := 
  (DirectedEdge @@ Last[#1] & ) /@ 
   Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[commonDomain, morphismImages[[#1]]] & ) /@ 
       Range[Length[morphismImages]], (injectionMorphismNames[[#1]] -> DirectedEdge[morphismImages[[#1]], 
          pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
      (Subscript["\[ForAll]", ToString[universalMorphismNames[[#1]], StandardForm]] -> DirectedEdge[morphismImages[[#1]], 
          Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]] & ) /@ Range[Length[morphismImages]], 
      {compositionSymbol[First[injectionMorphismNames], First[morphismNames]] -> DirectedEdge[commonDomain, 
         pushoutSymbol @@ morphismImages], compositionSymbol[First[universalMorphismNames], First[morphismNames]] -> 
        DirectedEdge[commonDomain, Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]], 
       Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> DirectedEdge[pushoutSymbol @@ morphismImages, 
         Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]]}]]]
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["UniversalSimpleMorphismCount"] := 
  Length[Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[commonDomain, morphismImages[[#1]]] & ) /@ 
       Range[Length[morphismImages]], (injectionMorphismNames[[#1]] -> DirectedEdge[morphismImages[[#1]], 
          pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
      (Subscript["\[ForAll]", ToString[universalMorphismNames[[#1]], StandardForm]] -> DirectedEdge[morphismImages[[#1]], 
          Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]] & ) /@ Range[Length[morphismImages]], 
      {compositionSymbol[First[injectionMorphismNames], First[morphismNames]] -> DirectedEdge[commonDomain, 
         pushoutSymbol @@ morphismImages], compositionSymbol[First[universalMorphismNames], First[morphismNames]] -> 
        DirectedEdge[commonDomain, Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]], 
       Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> DirectedEdge[pushoutSymbol @@ morphismImages, 
         Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]]}]]]]
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["UniversalReducedSimpleMorphismAssociation"] := 
  Association[Join[(morphismNames[[#1]] -> DirectedEdge[commonDomain, morphismImages[[#1]]] & ) /@ 
     Range[Length[morphismImages]], (injectionMorphismNames[[#1]] -> DirectedEdge[morphismImages[[#1]], 
        pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
    {compositionSymbol[Last[injectionMorphismNames], Last[morphismNames]] -> DirectedEdge[commonDomain, 
       pushoutSymbol @@ morphismImages]}, (compositionSymbol[uniqueMorphismName, injectionMorphismNames[[#1]]] -> 
       DirectedEdge[morphismImages[[#1]], Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]] & ) /@ 
     Range[Length[morphismImages]], {compositionSymbol[compositionSymbol[uniqueMorphismName, 
        Last[injectionMorphismNames]], Last[morphismNames]] -> DirectedEdge[commonDomain, 
       Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]], 
     Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> DirectedEdge[pushoutSymbol @@ morphismImages, 
       Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]]}]]
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["UniversalReducedSimpleMorphismNames"] := 
  First /@ Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[commonDomain, morphismImages[[#1]]] & ) /@ 
       Range[Length[morphismImages]], (injectionMorphismNames[[#1]] -> DirectedEdge[morphismImages[[#1]], 
          pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
      {compositionSymbol[Last[injectionMorphismNames], Last[morphismNames]] -> DirectedEdge[commonDomain, 
         pushoutSymbol @@ morphismImages]}, (compositionSymbol[uniqueMorphismName, injectionMorphismNames[[#1]]] -> 
         DirectedEdge[morphismImages[[#1]], Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]] & ) /@ 
       Range[Length[morphismImages]], {compositionSymbol[compositionSymbol[uniqueMorphismName, 
          Last[injectionMorphismNames]], Last[morphismNames]] -> DirectedEdge[commonDomain, 
         Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]], 
       Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> DirectedEdge[pushoutSymbol @@ morphismImages, 
         Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]]}]]]
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["UniversalReducedSimpleMorphismEdges"] := 
  (DirectedEdge @@ Last[#1] & ) /@ 
   Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[commonDomain, morphismImages[[#1]]] & ) /@ 
       Range[Length[morphismImages]], (injectionMorphismNames[[#1]] -> DirectedEdge[morphismImages[[#1]], 
          pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
      {compositionSymbol[Last[injectionMorphismNames], Last[morphismNames]] -> DirectedEdge[commonDomain, 
         pushoutSymbol @@ morphismImages]}, (compositionSymbol[uniqueMorphismName, injectionMorphismNames[[#1]]] -> 
         DirectedEdge[morphismImages[[#1]], Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]] & ) /@ 
       Range[Length[morphismImages]], {compositionSymbol[compositionSymbol[uniqueMorphismName, 
          Last[injectionMorphismNames]], Last[morphismNames]] -> DirectedEdge[commonDomain, 
         Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]], 
       Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> DirectedEdge[pushoutSymbol @@ morphismImages, 
         Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]]}]]]
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["UniversalReducedSimpleMorphismCount"] := 
  Length[Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[commonDomain, morphismImages[[#1]]] & ) /@ 
       Range[Length[morphismImages]], (injectionMorphismNames[[#1]] -> DirectedEdge[morphismImages[[#1]], 
          pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
      {compositionSymbol[Last[injectionMorphismNames], Last[morphismNames]] -> DirectedEdge[commonDomain, 
         pushoutSymbol @@ morphismImages]}, (compositionSymbol[uniqueMorphismName, injectionMorphismNames[[#1]]] -> 
         DirectedEdge[morphismImages[[#1]], Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]] & ) /@ 
       Range[Length[morphismImages]], {compositionSymbol[compositionSymbol[uniqueMorphismName, 
          Last[injectionMorphismNames]], Last[morphismNames]] -> DirectedEdge[commonDomain, 
         Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]], 
       Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> DirectedEdge[pushoutSymbol @@ morphismImages, 
         Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]]}]]]]
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["PushoutSymbol"] := pushoutSymbol
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["CompositionSymbol"] := compositionSymbol
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["IdentitySymbol"] := identitySymbol
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["PushoutCategory"] := 
  ResourceFunction["AbstractCategory"][Association["CompositionSymbol" -> compositionSymbol, 
    "IdentitySymbol" -> identitySymbol, "MorphismEquivalences" -> If[Length[morphismImages] > 1, 
      (compositionSymbol[injectionMorphismNames[[#1]], morphismNames[[#1]]] == compositionSymbol[
          injectionMorphismNames[[#1 + 1]], morphismNames[[#1 + 1]]] & ) /@ Range[Length[morphismImages] - 1], {}], 
    "ObjectEquivalences" -> {}, "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> {}, 
       "Arrows" -> Association[Join[(morphismNames[[#1]] -> DirectedEdge[commonDomain, morphismImages[[#1]]] & ) /@ 
           Range[Length[morphismImages]], (injectionMorphismNames[[#1]] -> DirectedEdge[morphismImages[[#1]], 
              pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]]]], "ObjectEquivalences" -> {}, 
       "Objects" -> Join[morphismImages, {commonDomain, pushoutSymbol @@ morphismImages}]]]]]
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["UniversalPushoutCategory"] := 
  ResourceFunction["AbstractCategory"][Association["CompositionSymbol" -> compositionSymbol, 
    "IdentitySymbol" -> identitySymbol, "MorphismEquivalences" -> If[Length[morphismImages] > 1, 
      Join[(compositionSymbol[injectionMorphismNames[[#1]], morphismNames[[#1]]] == compositionSymbol[
           injectionMorphismNames[[#1 + 1]], morphismNames[[#1 + 1]]] & ) /@ Range[Length[morphismImages] - 1], 
       (universalMorphismNames[[#1]] == compositionSymbol[uniqueMorphismName, injectionMorphismNames[[#1]]] & ) /@ 
        Range[Length[morphismImages]], (compositionSymbol[compositionSymbol[uniqueMorphismName, 
            injectionMorphismNames[[#1]]], morphismNames[[#1]]] == compositionSymbol[uniqueMorphismName, 
           compositionSymbol[injectionMorphismNames[[#1]], morphismNames[[#1]]]] & ) /@ Range[Length[morphismImages]]], 
      {First[universalMorphismNames] == compositionSymbol[uniqueMorphismName, First[injectionMorphismNames]]}], 
    "ObjectEquivalences" -> {}, "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> {}, 
       "Arrows" -> Association[Join[(morphismNames[[#1]] -> DirectedEdge[commonDomain, morphismImages[[#1]]] & ) /@ 
           Range[Length[morphismImages]], (injectionMorphismNames[[#1]] -> DirectedEdge[morphismImages[[#1]], 
              pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
          (universalMorphismNames[[#1]] -> DirectedEdge[morphismImages[[#1]], universalObjectName] & ) /@ 
           Range[Length[morphismImages]], {uniqueMorphismName -> DirectedEdge[pushoutSymbol @@ morphismImages, 
             universalObjectName]}]], "ObjectEquivalences" -> {}, "Objects" -> Join[morphismImages, 
         {commonDomain, pushoutSymbol @@ morphismImages, universalObjectName}]]]]]
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["PushoutEquations"] := 
  If[Length[morphismImages] > 1, (compositionSymbol[injectionMorphismNames[[#1]], morphismNames[[#1]]] == 
      compositionSymbol[injectionMorphismNames[[#1 + 1]], morphismNames[[#1 + 1]]] & ) /@ 
    Range[Length[morphismImages] - 1], {}]
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["UniversalPushoutEquations"] := 
  If[Length[morphismImages] > 1, Join[(compositionSymbol[injectionMorphismNames[[#1]], morphismNames[[#1]]] == 
       compositionSymbol[injectionMorphismNames[[#1 + 1]], morphismNames[[#1 + 1]]] & ) /@ 
     Range[Length[morphismImages] - 1], 
    (Module[{morphismIndex = #1}, ToExpression[StringJoin["HoldForm[ForAll[", ToString[universalMorphismNames, 
          StandardForm], ",Implies[", ToString[And @@ (compositionSymbol[injectionMorphismNames[[#1]], morphismNames[[
                #1]]] == compositionSymbol[injectionMorphismNames[[#1 + 1]], morphismNames[[#1 + 1]]] & ) /@ 
            Range[Length[morphismImages] - 1], StandardForm], ",Exists[", ToString[uniqueMorphismName, StandardForm], 
         ",", ToString[universalMorphismNames[[morphismIndex]] == compositionSymbol[uniqueMorphismName, 
            injectionMorphismNames[[morphismIndex]]], StandardForm], "]]]]"]]] & ) /@ Range[Length[morphismImages]]], 
   {First[universalMorphismNames] == compositionSymbol[uniqueMorphismName, First[injectionMorphismNames]]}]
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["FullLabeledGraph"] := 
  EdgeTaggedGraph[Join[morphismImages, {commonDomain, pushoutSymbol @@ morphismImages}], 
   (Labeled[DirectedEdge @@ Last[#1], Placed[First[#1], 0.5]] & ) /@ 
    Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[commonDomain, morphismImages[[#1]]] & ) /@ 
        Range[Length[morphismImages]], (injectionMorphismNames[[#1]] -> DirectedEdge[morphismImages[[#1]], 
           pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
       (compositionSymbol[injectionMorphismNames[[#1]], morphismNames[[#1]]] -> DirectedEdge[commonDomain, 
           pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
       (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ morphismImages, 
       {identitySymbol[commonDomain] -> DirectedEdge[commonDomain, commonDomain], 
        identitySymbol[pushoutSymbol @@ morphismImages] -> DirectedEdge[pushoutSymbol @@ morphismImages, 
          pushoutSymbol @@ morphismImages]}]]], VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], 
   VertexLabels -> Placed["Name", Center], VertexLabelStyle -> Directive[Bold, 20], 
   EdgeLabelStyle -> Directive[Bold, 20], EdgeStyle -> Directive[Black, Thick], 
   GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["FullUnlabeledGraph"] := 
  EdgeTaggedGraph[Join[morphismImages, {commonDomain, pushoutSymbol @@ morphismImages}], 
   (DirectedEdge @@ Last[#1] & ) /@ 
    Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[commonDomain, morphismImages[[#1]]] & ) /@ 
        Range[Length[morphismImages]], (injectionMorphismNames[[#1]] -> DirectedEdge[morphismImages[[#1]], 
           pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
       (compositionSymbol[injectionMorphismNames[[#1]], morphismNames[[#1]]] -> DirectedEdge[commonDomain, 
           pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
       (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ morphismImages, 
       {identitySymbol[commonDomain] -> DirectedEdge[commonDomain, commonDomain], 
        identitySymbol[pushoutSymbol @@ morphismImages] -> DirectedEdge[pushoutSymbol @@ morphismImages, 
          pushoutSymbol @@ morphismImages]}]]], VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], 
   VertexLabels -> Placed["Name", Center], VertexLabelStyle -> Directive[Bold, 20], 
   EdgeLabelStyle -> Directive[Bold, 20], EdgeStyle -> Directive[Black, Thick], 
   GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["ReducedLabeledGraph"] := 
  EdgeTaggedGraph[Join[morphismImages, {commonDomain, pushoutSymbol @@ morphismImages}], 
   (Labeled[DirectedEdge @@ Last[#1], Placed[First[#1], 0.5]] & ) /@ 
    Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[commonDomain, morphismImages[[#1]]] & ) /@ 
        Range[Length[morphismImages]], (injectionMorphismNames[[#1]] -> DirectedEdge[morphismImages[[#1]], 
           pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
       {compositionSymbol[Last[injectionMorphismNames], Last[morphismNames]] -> DirectedEdge[commonDomain, 
          pushoutSymbol @@ morphismImages]}, (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ morphismImages, 
       {identitySymbol[commonDomain] -> DirectedEdge[commonDomain, commonDomain], 
        identitySymbol[pushoutSymbol @@ morphismImages] -> DirectedEdge[pushoutSymbol @@ morphismImages, 
          pushoutSymbol @@ morphismImages]}]]], VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], 
   VertexLabels -> Placed["Name", Center], VertexLabelStyle -> Directive[Bold, 20], 
   EdgeLabelStyle -> Directive[Bold, 20], EdgeStyle -> Directive[Black, Thick], 
   GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["ReducedUnlabeledGraph"] := 
  EdgeTaggedGraph[Join[morphismImages, {commonDomain, pushoutSymbol @@ morphismImages}], 
   (DirectedEdge @@ Last[#1] & ) /@ 
    Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[commonDomain, morphismImages[[#1]]] & ) /@ 
        Range[Length[morphismImages]], (injectionMorphismNames[[#1]] -> DirectedEdge[morphismImages[[#1]], 
           pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
       {compositionSymbol[Last[injectionMorphismNames], Last[morphismNames]] -> DirectedEdge[commonDomain, 
          pushoutSymbol @@ morphismImages]}, (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ morphismImages, 
       {identitySymbol[commonDomain] -> DirectedEdge[commonDomain, commonDomain], 
        identitySymbol[pushoutSymbol @@ morphismImages] -> DirectedEdge[pushoutSymbol @@ morphismImages, 
          pushoutSymbol @@ morphismImages]}]]], VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], 
   VertexLabels -> Placed["Name", Center], VertexLabelStyle -> Directive[Bold, 20], 
   EdgeLabelStyle -> Directive[Bold, 20], EdgeStyle -> Directive[Black, Thick], 
   GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["SimpleLabeledGraph"] := 
  EdgeTaggedGraph[Join[morphismImages, {commonDomain, pushoutSymbol @@ morphismImages}], 
   (Labeled[DirectedEdge @@ Last[#1], Placed[First[#1], 0.5]] & ) /@ 
    Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[commonDomain, morphismImages[[#1]]] & ) /@ 
        Range[Length[morphismImages]], (injectionMorphismNames[[#1]] -> DirectedEdge[morphismImages[[#1]], 
           pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
       {compositionSymbol[First[injectionMorphismNames], First[morphismNames]] -> DirectedEdge[commonDomain, 
          pushoutSymbol @@ morphismImages]}]]], VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], 
   VertexLabels -> Placed["Name", Center], VertexLabelStyle -> Directive[Bold, 20], 
   EdgeLabelStyle -> Directive[Bold, 20], EdgeStyle -> Directive[Black, Thick], 
   GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["SimpleUnlabeledGraph"] := 
  EdgeTaggedGraph[Join[morphismImages, {commonDomain, pushoutSymbol @@ morphismImages}], 
   (DirectedEdge @@ Last[#1] & ) /@ 
    Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[commonDomain, morphismImages[[#1]]] & ) /@ 
        Range[Length[morphismImages]], (injectionMorphismNames[[#1]] -> DirectedEdge[morphismImages[[#1]], 
           pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
       {compositionSymbol[First[injectionMorphismNames], First[morphismNames]] -> DirectedEdge[commonDomain, 
          pushoutSymbol @@ morphismImages]}]]], VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], 
   VertexLabels -> Placed["Name", Center], VertexLabelStyle -> Directive[Bold, 20], 
   EdgeLabelStyle -> Directive[Bold, 20], EdgeStyle -> Directive[Black, Thick], 
   GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["ReducedSimpleLabeledGraph"] := 
  EdgeTaggedGraph[Join[morphismImages, {commonDomain, pushoutSymbol @@ morphismImages}], 
   (Labeled[DirectedEdge @@ Last[#1], Placed[First[#1], 0.5]] & ) /@ 
    Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[commonDomain, morphismImages[[#1]]] & ) /@ 
        Range[Length[morphismImages]], (injectionMorphismNames[[#1]] -> DirectedEdge[morphismImages[[#1]], 
           pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
       {compositionSymbol[Last[injectionMorphismNames], Last[morphismNames]] -> DirectedEdge[commonDomain, 
          pushoutSymbol @@ morphismImages]}]]], VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], 
   VertexLabels -> Placed["Name", Center], VertexLabelStyle -> Directive[Bold, 20], 
   EdgeLabelStyle -> Directive[Bold, 20], EdgeStyle -> Directive[Black, Thick], 
   GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["ReducedSimpleUnlabeledGraph"] := 
  EdgeTaggedGraph[Join[morphismImages, {commonDomain, pushoutSymbol @@ morphismImages}], 
   (DirectedEdge @@ Last[#1] & ) /@ 
    Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[commonDomain, morphismImages[[#1]]] & ) /@ 
        Range[Length[morphismImages]], (injectionMorphismNames[[#1]] -> DirectedEdge[morphismImages[[#1]], 
           pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
       {compositionSymbol[Last[injectionMorphismNames], Last[morphismNames]] -> DirectedEdge[commonDomain, 
          pushoutSymbol @@ morphismImages]}]]], VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], 
   VertexLabels -> Placed["Name", Center], VertexLabelStyle -> Directive[Bold, 20], 
   EdgeLabelStyle -> Directive[Bold, 20], EdgeStyle -> Directive[Black, Thick], 
   GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["UniversalFullLabeledGraph"] := 
  EdgeTaggedGraph[Join[morphismImages, {commonDomain, pushoutSymbol @@ morphismImages, universalObjectName}], 
   (Labeled[DirectedEdge @@ Last[#1], Placed[First[#1], 0.5]] & ) /@ 
    Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[commonDomain, morphismImages[[#1]]] & ) /@ 
        Range[Length[morphismImages]], (injectionMorphismNames[[#1]] -> DirectedEdge[morphismImages[[#1]], 
           pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
       (Subscript["\[ForAll]", ToString[universalMorphismNames[[#1]], StandardForm]] -> DirectedEdge[morphismImages[[#1]], 
           universalObjectName] & ) /@ Range[Length[morphismImages]], 
       (compositionSymbol[injectionMorphismNames[[#1]], morphismNames[[#1]]] -> DirectedEdge[commonDomain, 
           pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
       (compositionSymbol[uniqueMorphismName, injectionMorphismNames[[#1]]] -> DirectedEdge[morphismImages[[#1]], 
           universalObjectName] & ) /@ Range[Length[morphismImages]], 
       (compositionSymbol[universalMorphismNames[[#1]], morphismNames[[#1]]] -> DirectedEdge[commonDomain, 
           universalObjectName] & ) /@ Range[Length[morphismImages]], 
       (compositionSymbol[compositionSymbol[uniqueMorphismName, injectionMorphismNames[[#1]]], morphismNames[[#1]]] -> 
          DirectedEdge[commonDomain, universalObjectName] & ) /@ Range[Length[morphismImages]], 
       (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ morphismImages, 
       {identitySymbol[commonDomain] -> DirectedEdge[commonDomain, commonDomain], 
        identitySymbol[pushoutSymbol @@ morphismImages] -> DirectedEdge[pushoutSymbol @@ morphismImages, 
          pushoutSymbol @@ morphismImages], identitySymbol[universalObjectName] -> DirectedEdge[universalObjectName, 
          universalObjectName], Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> 
         DirectedEdge[pushoutSymbol @@ morphismImages, universalObjectName]}]]], VertexSize -> 0.3, 
   VertexStyle -> Directive[Transparent, EdgeForm[None]], 
   VertexLabels -> {Placed["Name", Center], universalObjectName -> 
      Placed[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], Center]}, 
   VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
   EdgeStyle -> {Directive[Black, Thick], DirectedEdge[pushoutSymbol @@ morphismImages, universalObjectName] -> Dashed}, 
   GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["UniversalFullUnlabeledGraph"] := 
  EdgeTaggedGraph[Join[morphismImages, {commonDomain, pushoutSymbol @@ morphismImages, universalObjectName}], 
   (DirectedEdge @@ Last[#1] & ) /@ 
    Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[commonDomain, morphismImages[[#1]]] & ) /@ 
        Range[Length[morphismImages]], (injectionMorphismNames[[#1]] -> DirectedEdge[morphismImages[[#1]], 
           pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
       (Subscript["\[ForAll]", ToString[universalMorphismNames[[#1]], StandardForm]] -> DirectedEdge[morphismImages[[#1]], 
           universalObjectName] & ) /@ Range[Length[morphismImages]], 
       (compositionSymbol[injectionMorphismNames[[#1]], morphismNames[[#1]]] -> DirectedEdge[commonDomain, 
           pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
       (compositionSymbol[uniqueMorphismName, injectionMorphismNames[[#1]]] -> DirectedEdge[morphismImages[[#1]], 
           universalObjectName] & ) /@ Range[Length[morphismImages]], 
       (compositionSymbol[universalMorphismNames[[#1]], morphismNames[[#1]]] -> DirectedEdge[commonDomain, 
           universalObjectName] & ) /@ Range[Length[morphismImages]], 
       (compositionSymbol[compositionSymbol[uniqueMorphismName, injectionMorphismNames[[#1]]], morphismNames[[#1]]] -> 
          DirectedEdge[commonDomain, universalObjectName] & ) /@ Range[Length[morphismImages]], 
       (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ morphismImages, 
       {identitySymbol[commonDomain] -> DirectedEdge[commonDomain, commonDomain], 
        identitySymbol[pushoutSymbol @@ morphismImages] -> DirectedEdge[pushoutSymbol @@ morphismImages, 
          pushoutSymbol @@ morphismImages], identitySymbol[universalObjectName] -> DirectedEdge[universalObjectName, 
          universalObjectName], Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> 
         DirectedEdge[pushoutSymbol @@ morphismImages, universalObjectName]}]]], VertexSize -> 0.3, 
   VertexStyle -> Directive[Transparent, EdgeForm[None]], 
   VertexLabels -> {Placed["Name", Center], universalObjectName -> 
      Placed[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], Center]}, 
   VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
   EdgeStyle -> {Directive[Black, Thick], DirectedEdge[pushoutSymbol @@ morphismImages, universalObjectName] -> Dashed}, 
   GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["UniversalReducedLabeledGraph"] := 
  EdgeTaggedGraph[Join[morphismImages, {commonDomain, pushoutSymbol @@ morphismImages, universalObjectName}], 
   (Labeled[DirectedEdge @@ Last[#1], Placed[First[#1], 0.5]] & ) /@ 
    Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[commonDomain, morphismImages[[#1]]] & ) /@ 
        Range[Length[morphismImages]], (injectionMorphismNames[[#1]] -> DirectedEdge[morphismImages[[#1]], 
           pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
       {compositionSymbol[Last[injectionMorphismNames], Last[morphismNames]] -> DirectedEdge[commonDomain, 
          pushoutSymbol @@ morphismImages]}, (compositionSymbol[uniqueMorphismName, injectionMorphismNames[[#1]]] -> 
          DirectedEdge[morphismImages[[#1]], universalObjectName] & ) /@ Range[Length[morphismImages]], 
       {compositionSymbol[compositionSymbol[uniqueMorphismName, Last[injectionMorphismNames]], Last[morphismNames]] -> 
         DirectedEdge[commonDomain, universalObjectName]}, (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ 
        morphismImages, {identitySymbol[commonDomain] -> DirectedEdge[commonDomain, commonDomain], 
        identitySymbol[pushoutSymbol @@ morphismImages] -> DirectedEdge[pushoutSymbol @@ morphismImages, 
          pushoutSymbol @@ morphismImages], identitySymbol[universalObjectName] -> DirectedEdge[universalObjectName, 
          universalObjectName], Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> 
         DirectedEdge[pushoutSymbol @@ morphismImages, universalObjectName]}]]], VertexSize -> 0.3, 
   VertexStyle -> Directive[Transparent, EdgeForm[None]], 
   VertexLabels -> {Placed["Name", Center], universalObjectName -> 
      Placed[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], Center]}, 
   VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
   EdgeStyle -> {Directive[Black, Thick], DirectedEdge[pushoutSymbol @@ morphismImages, universalObjectName] -> Dashed}, 
   GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["UniversalReducedUnlabeledGraph"] := 
  EdgeTaggedGraph[Join[morphismImages, {commonDomain, pushoutSymbol @@ morphismImages, universalObjectName}], 
   (DirectedEdge @@ Last[#1] & ) /@ 
    Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[commonDomain, morphismImages[[#1]]] & ) /@ 
        Range[Length[morphismImages]], (injectionMorphismNames[[#1]] -> DirectedEdge[morphismImages[[#1]], 
           pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
       {compositionSymbol[Last[injectionMorphismNames], Last[morphismNames]] -> DirectedEdge[commonDomain, 
          pushoutSymbol @@ morphismImages]}, (compositionSymbol[uniqueMorphismName, injectionMorphismNames[[#1]]] -> 
          DirectedEdge[morphismImages[[#1]], universalObjectName] & ) /@ Range[Length[morphismImages]], 
       {compositionSymbol[compositionSymbol[uniqueMorphismName, Last[injectionMorphismNames]], Last[morphismNames]] -> 
         DirectedEdge[commonDomain, universalObjectName]}, (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ 
        morphismImages, {identitySymbol[commonDomain] -> DirectedEdge[commonDomain, commonDomain], 
        identitySymbol[pushoutSymbol @@ morphismImages] -> DirectedEdge[pushoutSymbol @@ morphismImages, 
          pushoutSymbol @@ morphismImages], identitySymbol[universalObjectName] -> DirectedEdge[universalObjectName, 
          universalObjectName], Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> 
         DirectedEdge[pushoutSymbol @@ morphismImages, universalObjectName]}]]], VertexSize -> 0.3, 
   VertexStyle -> Directive[Transparent, EdgeForm[None]], 
   VertexLabels -> {Placed["Name", Center], universalObjectName -> 
      Placed[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], Center]}, 
   VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
   EdgeStyle -> {Directive[Black, Thick], DirectedEdge[pushoutSymbol @@ morphismImages, universalObjectName] -> Dashed}, 
   GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["UniversalSimpleLabeledGraph"] := 
  EdgeTaggedGraph[Join[morphismImages, {commonDomain, pushoutSymbol @@ morphismImages, universalObjectName}], 
   (Labeled[DirectedEdge @@ Last[#1], Placed[First[#1], 0.5]] & ) /@ 
    Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[commonDomain, morphismImages[[#1]]] & ) /@ 
        Range[Length[morphismImages]], (injectionMorphismNames[[#1]] -> DirectedEdge[morphismImages[[#1]], 
           pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
       (Subscript["\[ForAll]", ToString[universalMorphismNames[[#1]], StandardForm]] -> DirectedEdge[morphismImages[[#1]], 
           universalObjectName] & ) /@ Range[Length[morphismImages]], 
       {compositionSymbol[First[injectionMorphismNames], First[morphismNames]] -> DirectedEdge[commonDomain, 
          pushoutSymbol @@ morphismImages], compositionSymbol[First[universalMorphismNames], First[morphismNames]] -> 
         DirectedEdge[commonDomain, universalObjectName], Subscript["\[Exists]!", ToString[uniqueMorphismName, 
           StandardForm]] -> DirectedEdge[pushoutSymbol @@ morphismImages, universalObjectName]}]]], VertexSize -> 0.3, 
   VertexStyle -> Directive[Transparent, EdgeForm[None]], 
   VertexLabels -> {Placed["Name", Center], universalObjectName -> 
      Placed[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], Center]}, 
   VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
   EdgeStyle -> {Directive[Black, Thick], DirectedEdge[pushoutSymbol @@ morphismImages, universalObjectName] -> Dashed}, 
   GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["UniversalSimpleUnlabeledGraph"] := 
  EdgeTaggedGraph[Join[morphismImages, {commonDomain, pushoutSymbol @@ morphismImages, universalObjectName}], 
   (DirectedEdge @@ Last[#1] & ) /@ 
    Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[commonDomain, morphismImages[[#1]]] & ) /@ 
        Range[Length[morphismImages]], (injectionMorphismNames[[#1]] -> DirectedEdge[morphismImages[[#1]], 
           pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
       (Subscript["\[ForAll]", ToString[universalMorphismNames[[#1]], StandardForm]] -> DirectedEdge[morphismImages[[#1]], 
           universalObjectName] & ) /@ Range[Length[morphismImages]], 
       {compositionSymbol[First[injectionMorphismNames], First[morphismNames]] -> DirectedEdge[commonDomain, 
          pushoutSymbol @@ morphismImages], compositionSymbol[First[universalMorphismNames], First[morphismNames]] -> 
         DirectedEdge[commonDomain, universalObjectName], Subscript["\[Exists]!", ToString[uniqueMorphismName, 
           StandardForm]] -> DirectedEdge[pushoutSymbol @@ morphismImages, universalObjectName]}]]], VertexSize -> 0.3, 
   VertexStyle -> Directive[Transparent, EdgeForm[None]], 
   VertexLabels -> {Placed["Name", Center], universalObjectName -> 
      Placed[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], Center]}, 
   VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
   EdgeStyle -> {Directive[Black, Thick], DirectedEdge[pushoutSymbol @@ morphismImages, universalObjectName] -> Dashed}, 
   GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["UniversalReducedSimpleLabeledGraph"] := 
  EdgeTaggedGraph[Join[morphismImages, {commonDomain, pushoutSymbol @@ morphismImages, universalObjectName}], 
   (Labeled[DirectedEdge @@ Last[#1], Placed[First[#1], 0.5]] & ) /@ 
    Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[commonDomain, morphismImages[[#1]]] & ) /@ 
        Range[Length[morphismImages]], (injectionMorphismNames[[#1]] -> DirectedEdge[morphismImages[[#1]], 
           pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
       {compositionSymbol[Last[injectionMorphismNames], Last[morphismNames]] -> DirectedEdge[commonDomain, 
          pushoutSymbol @@ morphismImages]}, (compositionSymbol[uniqueMorphismName, injectionMorphismNames[[#1]]] -> 
          DirectedEdge[morphismImages[[#1]], universalObjectName] & ) /@ Range[Length[morphismImages]], 
       {compositionSymbol[compositionSymbol[uniqueMorphismName, Last[injectionMorphismNames]], Last[morphismNames]] -> 
         DirectedEdge[commonDomain, universalObjectName], Subscript["\[Exists]!", ToString[uniqueMorphismName, 
           StandardForm]] -> DirectedEdge[pushoutSymbol @@ morphismImages, universalObjectName]}]]], VertexSize -> 0.3, 
   VertexStyle -> Directive[Transparent, EdgeForm[None]], 
   VertexLabels -> {Placed["Name", Center], universalObjectName -> 
      Placed[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], Center]}, 
   VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
   EdgeStyle -> {Directive[Black, Thick], DirectedEdge[pushoutSymbol @@ morphismImages, universalObjectName] -> Dashed}, 
   GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["UniversalReducedSimpleUnlabeledGraph"] := 
  EdgeTaggedGraph[Join[morphismImages, {commonDomain, pushoutSymbol @@ morphismImages, universalObjectName}], 
   (DirectedEdge @@ Last[#1] & ) /@ 
    Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[commonDomain, morphismImages[[#1]]] & ) /@ 
        Range[Length[morphismImages]], (injectionMorphismNames[[#1]] -> DirectedEdge[morphismImages[[#1]], 
           pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
       {compositionSymbol[Last[injectionMorphismNames], Last[morphismNames]] -> DirectedEdge[commonDomain, 
          pushoutSymbol @@ morphismImages]}, (compositionSymbol[uniqueMorphismName, injectionMorphismNames[[#1]]] -> 
          DirectedEdge[morphismImages[[#1]], universalObjectName] & ) /@ Range[Length[morphismImages]], 
       {compositionSymbol[compositionSymbol[uniqueMorphismName, Last[injectionMorphismNames]], Last[morphismNames]] -> 
         DirectedEdge[commonDomain, universalObjectName], Subscript["\[Exists]!", ToString[uniqueMorphismName, 
           StandardForm]] -> DirectedEdge[pushoutSymbol @@ morphismImages, universalObjectName]}]]], VertexSize -> 0.3, 
   VertexStyle -> Directive[Transparent, EdgeForm[None]], 
   VertexLabels -> {Placed["Name", Center], universalObjectName -> 
      Placed[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], Center]}, 
   VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
   EdgeStyle -> {Directive[Black, Thick], DirectedEdge[pushoutSymbol @@ morphismImages, universalObjectName] -> Dashed}, 
   GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["AssociationForm"] := 
  Association["MorphismNames" -> morphismNames, "MorphismImages" -> morphismImages, "CommonDomain" -> commonDomain, 
   "PushoutSymbol" -> pushoutSymbol, "InjectionMorphismNames" -> injectionMorphismNames, 
   "CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
   "UniversalObjectName" -> universalObjectName, "UniversalMorphismNames" -> universalMorphismNames, 
   "UniqueMorphismName" -> uniqueMorphismName]
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphisMNames_List, 
     "UniversalObjectName" -> universalObjectName_]]["Properties"] := {"Objects", "ObjectCount", "MorphismAssociation", 
   "MorphismNames", "MorphismEdges", "MorphismCount", "ReducedMorphismAssociation", "ReducedMorphismNames", 
   "ReducedMorphismEdges", "ReducedMorphismCount", "SimpleMorphismAssociation", "SimpleMorphismNames", 
   "SimpleMorphismEdges", "SimpleMorphismCount", "ReducedSimpleMorphismAssociation", "ReducedSimpleMorphismNames", 
   "ReducedSimpleMorphismEdges", "ReducedSimpleMorphismCount", "UniversalObjects", "UniversalObjectCount", 
   "UniversalMorphismAssociation", "UniversalMorphismNames", "UniversalMorphismEdges", "UniversalMorphismCount", 
   "UniversalReducedMorphismAssociation", "UniversalReducedMorphismNames", "UniversalReducedMorphismEdges", 
   "UniversalReducedMorphismCount", "UniversalSimpleMorphismAssociation", "UniversalSimpleMorphismNames", 
   "UniversalSimpleMorphismEdges", "UniversalSimpleMorphismCount", "UniversalReducedSimpleMorphismAssociation", 
   "UniversalReducedSimpleMorphismNames", "UniversalReducedSimpleMorphismEdges", "UniversalReducedSimpleMorphismCount", 
   "PushoutSymbol", "CompositionSymbol", "IdentitySymbol", "PushoutCategory", "UniversalPushoutCategory", 
   "PushoutEquations", "UniversalPushoutEquations", "FullLabeledGraph", "FullUnlabeledGraph", "ReducedLabeledGraph", 
   "ReducedUnlabeledGraph", "SimpleLabeledGraph", "SimpleUnlabeledGraph", "ReducedSimpleLabeledGraph", 
   "ReducedSimpleUnlabeledGraph", "UniversalFullLabeledGraph", "UniversalFullUnlabeledGraph", 
   "UniversalReducedLabeledGraph", "UniversalReducedUnlabeledGraph", "UniversalSimpleLabeledGraph", 
   "UniversalSimpleUnlabeledGraph", "UniversalReducedSimpleLabeledGraph", "UniversalReducedSimpleUnlabeledGraph", 
   "AssociationForm", "Properties"}
AbstractPushout /: MakeBoxes[abstractPushout:AbstractPushout[Association["CommonDomain" -> commonDomain_, 
       "CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
       "InjectionMorphismNames" -> injectionMorphismNames_List, "MorphismImages" -> morphismImages_List, 
       "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, "UniqueMorphismName" -> 
        uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
       "UniversalObjectName" -> universalObjectName_]], format_] := 
   Module[{icon}, icon = GraphPlot[EdgeTaggedGraph[Join[morphismImages, {commonDomain, pushoutSymbol @@ morphismImages}], 
        (DirectedEdge @@ Last[#1] & ) /@ Normal[Association[Join[(morphismNames[[#1]] -> DirectedEdge[commonDomain, 
                morphismImages[[#1]]] & ) /@ Range[Length[morphismImages]], 
            (injectionMorphismNames[[#1]] -> DirectedEdge[morphismImages[[#1]], pushoutSymbol @@ morphismImages] & ) /@ 
             Range[Length[morphismImages]], (compositionSymbol[injectionMorphismNames[[#1]], morphismNames[[#1]]] -> 
               DirectedEdge[commonDomain, pushoutSymbol @@ morphismImages] & ) /@ Range[Length[morphismImages]], 
            (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ morphismImages, {identitySymbol[commonDomain] -> 
              DirectedEdge[commonDomain, commonDomain], identitySymbol[pushoutSymbol @@ morphismImages] -> 
              DirectedEdge[pushoutSymbol @@ morphismImages, pushoutSymbol @@ morphismImages]}]]], VertexSize -> 0.3, 
        VertexStyle -> Directive[Transparent, EdgeForm[None]], EdgeShapeFunction -> GraphElementData["ShortFilledArrow", 
          "ArrowSize" -> 0.05], EdgeStyle -> Black, GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]]; 
     BoxForm`ArrangeSummaryBox["AbstractPushout", abstractPushout, icon, 
      {{BoxForm`SummaryItem[{"Symbol: ", pushoutSymbol}], BoxForm`SummaryItem[{"Common Domain: ", commonDomain}]}, 
       {BoxForm`SummaryItem[{"Codomains: ", morphismImages}], BoxForm`SummaryItem[{"Arrows: ", morphismNames}]}}, {{}}, 
      format, "Interpretable" -> Automatic]]
AbstractPushout[span_Association] := AbstractPushout[Association["CommonDomain" -> First[Last[First[Normal[span]]]], 
     "CompositionSymbol" -> CircleDot, "IdentitySymbol" -> OverTilde, "InjectionMorphismNames" -> 
      (Subscript["\[FormalI]", ToString[#1]] & ) /@ Range[Length[Normal[span]]], 
     "MorphismImages" -> (Last[Last[#1]] & ) /@ Normal[span], "MorphismNames" -> First /@ Normal[span], 
     "PushoutSymbol" -> Coproduct, "UniqueMorphismName" -> "\[FormalU]", "UniversalMorphismNames" -> 
      (Subscript["\[FormalJ]", ToString[#1]] & ) /@ Range[Length[span]], "UniversalObjectName" -> "\[FormalCapitalQ]"]] /; 
    !KeyExistsQ[span, "CommonDomain"] &&  !KeyExistsQ[span, "CompositionSymbol"] && 
     !KeyExistsQ[span, "IdentitySymbol"] &&  !KeyExistsQ[span, "InjectionMorphismNames"] && 
     !KeyExistsQ[span, "MorphismImages"] &&  !KeyExistsQ[span, "MorphismNames"] &&  !KeyExistsQ[span, "PushoutSymbol"] && 
     !KeyExistsQ[span, "UniqueMorphismName"] &&  !KeyExistsQ[span, "UniversalMorphismNames"] && 
     !KeyExistsQ[span, "UniversalObjectName"] && Length[DeleteDuplicates[(First[Last[#1]] & ) /@ Normal[span]]] == 1
AbstractPushout[span_Association, pushoutSymbol_] := 
  AbstractPushout[Association["CommonDomain" -> First[Last[First[Normal[span]]]], "CompositionSymbol" -> CircleDot, 
     "IdentitySymbol" -> OverTilde, "InjectionMorphismNames" -> (Subscript["\[FormalI]", ToString[#1]] & ) /@ 
       Range[Length[Normal[span]]], "MorphismImages" -> (Last[Last[#1]] & ) /@ Normal[span], 
     "MorphismNames" -> First /@ Normal[span], "PushoutSymbol" -> pushoutSymbol, "UniqueMorphismName" -> "\[FormalU]", 
     "UniversalMorphismNames" -> (Subscript["\[FormalJ]", ToString[#1]] & ) /@ Range[Length[span]], 
     "UniversalObjectName" -> "\[FormalCapitalQ]"]] /;  !ListQ[pushoutSymbol] && 
    Length[DeleteDuplicates[(First[Last[#1]] & ) /@ Normal[span]]] == 1
AbstractPushout[span_Association, pushoutSymbol_, injectionMorphismNames_List] := 
  AbstractPushout[Association["CommonDomain" -> First[Last[First[Normal[span]]]], "CompositionSymbol" -> CircleDot, 
     "IdentitySymbol" -> OverTilde, "InjectionMorphismNames" -> injectionMorphismNames, 
     "MorphismImages" -> (Last[Last[#1]] & ) /@ Normal[span], "MorphismNames" -> First /@ Normal[span], 
     "PushoutSymbol" -> pushoutSymbol, "UniqueMorphismName" -> "\[FormalU]", "UniversalMorphismNames" -> 
      (Subscript["\[FormalJ]", ToString[#1]] & ) /@ Range[Length[span]], "UniversalObjectName" -> "\[FormalCapitalQ]"]] /; 
    !ListQ[pushoutSymbol] && Length[DeleteDuplicates[(First[Last[#1]] & ) /@ Normal[span]]] == 1
AbstractPushout[span_Association, pushoutSymbol_, injectionMorphismNames_List, compositionSymbol_] := 
  AbstractPushout[Association["CommonDomain" -> First[Last[First[Normal[span]]]], 
     "CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> OverTilde, 
     "InjectionMorphismNames" -> injectionMorphismNames, "MorphismImages" -> (Last[Last[#1]] & ) /@ Normal[span], 
     "MorphismNames" -> First /@ Normal[span], "PushoutSymbol" -> pushoutSymbol, "UniqueMorphismName" -> "\[FormalU]", 
     "UniversalMorphismNames" -> (Subscript["\[FormalJ]", ToString[#1]] & ) /@ Range[Length[span]], 
     "UniversalObjectName" -> "\[FormalCapitalQ]"]] /;  !ListQ[pushoutSymbol] &&  !ListQ[compositionSymbol] && 
    Length[DeleteDuplicates[(First[Last[#1]] & ) /@ Normal[span]]] == 1
AbstractPushout[span_Association, pushoutSymbol_, injectionMorphismNames_List, compositionSymbol_, identitySymbol_] := 
  AbstractPushout[Association["CommonDomain" -> First[Last[First[Normal[span]]]], 
     "CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
     "InjectionMorphismNames" -> injectionMorphismNames, "MorphismImages" -> (Last[Last[#1]] & ) /@ Normal[span], 
     "MorphismNames" -> First /@ Normal[span], "PushoutSymbol" -> pushoutSymbol, "UniqueMorphismName" -> "\[FormalU]", 
     "UniversalMorphismNames" -> (Subscript["\[FormalJ]", ToString[#1]] & ) /@ Range[Length[span]], 
     "UniversalObjectName" -> "\[FormalCapitalQ]"]] /;  !ListQ[pushoutSymbol] &&  !ListQ[compositionSymbol] && 
     !ListQ[identitySymbol] && Length[DeleteDuplicates[(First[Last[#1]] & ) /@ Normal[span]]] == 1
AbstractPushout[span_Association, pushoutSymbol_, injectionMorphismNames_List, compositionSymbol_, identitySymbol_, 
   universalObjectName_] := AbstractPushout[Association["CommonDomain" -> First[Last[First[Normal[span]]]], 
     "CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
     "InjectionMorphismNames" -> injectionMorphismNames, "MorphismImages" -> (Last[Last[#1]] & ) /@ Normal[span], 
     "MorphismNames" -> First /@ Normal[span], "PushoutSymbol" -> pushoutSymbol, "UniqueMorphismName" -> "\[FormalU]", 
     "UniversalMorphismNames" -> (Subscript["\[FormalJ]", ToString[#1]] & ) /@ Range[Length[span]], 
     "UniversalObjectName" -> universalObjectName]] /;  !ListQ[pushoutSymbol] &&  !ListQ[compositionSymbol] && 
     !ListQ[identitySymbol] && Length[DeleteDuplicates[(First[Last[#1]] & ) /@ Normal[span]]] == 1
AbstractPushout[span_Association, pushoutSymbol_, injectionMorphismNames_List, compositionSymbol_, identitySymbol_, 
   universalObjectName_, universalMorphismNames_List] := 
  AbstractPushout[Association["CommonDomain" -> First[Last[First[Normal[span]]]], 
     "CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
     "InjectionMorphismNames" -> injectionMorphismNames, "MorphismImages" -> (Last[Last[#1]] & ) /@ Normal[span], 
     "MorphismNames" -> First /@ Normal[span], "PushoutSymbol" -> pushoutSymbol, "UniqueMorphismName" -> "\[FormalU]", 
     "UniversalMorphismNames" -> universalMorphismNames, "UniversalObjectName" -> universalObjectName]] /; 
    !ListQ[pushoutSymbol] &&  !ListQ[compositionSymbol] &&  !ListQ[identitySymbol] && 
    Length[DeleteDuplicates[(First[Last[#1]] & ) /@ Normal[span]]] == 1
AbstractPushout[span_Association, pushoutSymbol_, injectionMorphismNames_List, compositionSymbol_, identitySymbol_, 
   universalObjectName_, universalMorphismNames_List, uniqueMorphismName_] := 
  AbstractPushout[Association["CommonDomain" -> First[Last[First[Normal[span]]]], 
     "CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
     "InjectionMorphismNames" -> injectionMorphismNames, "MorphismImages" -> (Last[Last[#1]] & ) /@ Normal[span], 
     "MorphismNames" -> First /@ Normal[span], "PushoutSymbol" -> pushoutSymbol, 
     "UniqueMorphismName" -> uniqueMorphismName, "UniversalMorphismNames" -> universalMorphismNames, 
     "UniversalObjectName" -> universalObjectName]] /;  !ListQ[pushoutSymbol] &&  !ListQ[compositionSymbol] && 
     !ListQ[identitySymbol] && Length[DeleteDuplicates[(First[Last[#1]] & ) /@ Normal[span]]] == 1
AbstractPushout[span_Association, injectionMorphismNames_List] := 
  AbstractPushout[Association["CommonDomain" -> First[Last[First[Normal[span]]]], "CompositionSymbol" -> CircleDot, 
     "IdentitySymbol" -> OverTilde, "InjectionMorphismNames" -> injectionMorphismNames, 
     "MorphismImages" -> (Last[Last[#1]] & ) /@ Normal[span], "MorphismNames" -> First /@ Normal[span], 
     "PushoutSymbol" -> Coproduct, "UniqueMorphismName" -> "\[FormalU]", "UniversalMorphismNames" -> 
      (Subscript["\[FormalJ]", ToString[#1]] & ) /@ Range[Length[Normal[span]]], "UniversalObjectName" -> "\[FormalCapitalQ]"]] /; 
   Length[DeleteDuplicates[(First[Last[#1]] & ) /@ Normal[span]]] == 1
AbstractPushout[span_Association, injectionMorphismNames_List, compositionSymbol_] := 
  AbstractPushout[Association["CommonDomain" -> First[Last[First[Normal[span]]]], 
     "CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> OverTilde, 
     "InjectionMorphismNames" -> injectionMorphismNames, "MorphismImages" -> (Last[Last[#1]] & ) /@ Normal[span], 
     "MorphismNames" -> First /@ Normal[span], "PushoutSymbol" -> Coproduct, "UniqueMorphismName" -> "\[FormalU]", 
     "UniversalMorphismNames" -> (Subscript["\[FormalJ]", ToString[#1]] & ) /@ Range[Length[Normal[span]]], 
     "UniversalObjectName" -> "\[FormalCapitalQ]"]] /; Length[DeleteDuplicates[(First[Last[#1]] & ) /@ Normal[span]]] == 1
AbstractPushout[span_Association, injectionMorphismNames_List, compositionSymbol_, identitySymbol_] := 
  AbstractPushout[Association["CommonDomain" -> First[Last[First[Normal[span]]]], 
     "CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
     "InjectionMorphismNames" -> injectionMorphismNames, "MorphismImages" -> (Last[Last[#1]] & ) /@ Normal[span], 
     "MorphismNames" -> First /@ Normal[span], "PushoutSymbol" -> Coproduct, "UniqueMorphismName" -> "\[FormalU]", 
     "UniversalMorphismNames" -> (Subscript["\[FormalJ]", ToString[#1]] & ) /@ Range[Length[Normal[span]]], 
     "UniversalObjectName" -> "\[FormalCapitalQ]"]] /; Length[DeleteDuplicates[(First[Last[#1]] & ) /@ Normal[span]]] == 1
AbstractPushout[span_Association, pushoutSymbol_, compositionSymbol_] := 
  AbstractPushout[Association["CommonDomain" -> First[Last[First[Normal[span]]]], 
     "CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> OverTilde, 
     "InjectionMorphismNames" -> (Subscript["\[FormalI]", ToString[#1]] & ) /@ Range[Length[Normal[span]]], 
     "MorphismImages" -> (Last[Last[#1]] & ) /@ Normal[span], "MorphismNames" -> First /@ Normal[span], 
     "PushoutSymbol" -> pushoutSymbol, "UniqueMorphismName" -> "\[FormalU]", "UniversalMorphismNames" -> 
      (Subscript["\[FormalJ]", ToString[#1]] & ) /@ Range[Length[Normal[span]]], "UniversalObjectName" -> "\[FormalCapitalQ]"]] /; 
    !ListQ[pushoutSymbol] &&  !ListQ[compositionSymbol] && 
    Length[DeleteDuplicates[(First[Last[#1]] & ) /@ Normal[span]]] == 1
AbstractPushout[span_Association, pushoutSymbol_, compositionSymbol_, identitySymbol_] := 
  AbstractPushout[Association["CommonDomain" -> First[Last[First[Normal[span]]]], 
     "CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
     "InjectionMorphismNames" -> (Subscript["\[FormalI]", ToString[#1]] & ) /@ Range[Length[Normal[span]]], 
     "MorphismImages" -> (Last[Last[#1]] & ) /@ Normal[span], "MorphismNames" -> First /@ Normal[span], 
     "PushoutSymbol" -> pushoutSymbol, "UniqueMorphismName" -> "\[FormalU]", "UniversalMorphismNames" -> 
      (Subscript["\[FormalJ]", ToString[#1]] & ) /@ Range[Length[Normal[span]]], "UniversalObjectName" -> "\[FormalCapitalQ]"]] /; 
    !ListQ[pushoutSymbol] &&  !ListQ[compositionSymbol] &&  !ListQ[identitySymbol] && 
    Length[DeleteDuplicates[(First[Last[#1]] & ) /@ Normal[span]]] == 1
AbstractPushout[pushout_Association] := AbstractPushout[KeySort[pushout]] /; 
   KeyExistsQ[pushout, "CommonDomain"] && KeyExistsQ[pushout, "CompositionSymbol"] && 
    KeyExistsQ[pushout, "IdentitySymbol"] && KeyExistsQ[pushout, "InjectionMorphismNames"] && 
    KeyExistsQ[pushout, "MorphismImages"] && KeyExistsQ[pushout, "MorphismNames"] && 
    KeyExistsQ[pushout, "PushoutSymbol"] && KeyExistsQ[pushout, "UniqueMorphismName"] && 
    KeyExistsQ[pushout, "UniversalMorphismNames"] && KeyExistsQ[pushout, "UniversalObjectName"] && 
    Keys[KeySort[pushout]] =!= Keys[pushout]
AbstractPushout[AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]], newPushoutSymbol_] := 
  AbstractPushout[Association["CommonDomain" -> commonDomain, "CompositionSymbol" -> compositionSymbol, 
    "IdentitySymbol" -> identitySymbol, "InjectionMorphismNames" -> injectionMorphismNames, 
    "MorphismImages" -> morphismImages, "MorphismNames" -> morphismNames, "PushoutSymbol" -> newPushoutSymbol, 
    "UniqueMorphismName" -> uniqueMorphismName, "UniversalMorphismNames" -> universalMorphismNames, 
    "UniversalObjectName" -> universalObjectName]]
AbstractPushout[AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]], newPushoutSymbol_, newCompositionSymbol_] := 
  AbstractPushout[Association["CommonDomain" -> commonDomain, "CompositionSymbol" -> newCompositionSymbol, 
    "IdentitySymbol" -> identitySymbol, "InjectionMorphismNames" -> injectionMorphismNames, 
    "MorphismImages" -> morphismImages, "MorphismNames" -> morphismNames, "PushoutSymbol" -> newPushoutSymbol, 
    "UniqueMorphismName" -> uniqueMorphismName, "UniversalMorphismNames" -> universalMorphismNames, 
    "UniversalObjectName" -> universalObjectName]]
AbstractPushout[AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]], newPushoutSymbol_, newCompositionSymbol_, newIdentitySymbol_] := 
  AbstractPushout[Association["CommonDomain" -> commonDomain, "CompositionSymbol" -> newCompositionSymbol, 
    "IdentitySymbol" -> newIdentitySymbol, "InjectionMorphismNames" -> injectionMorphismNames, 
    "MorphismImages" -> morphismImages, "MorphismNames" -> morphismNames, "PushoutSymbol" -> newPushoutSymbol, 
    "UniqueMorphismName" -> uniqueMorphismName, "UniversalMorphismNames" -> universalMorphismNames, 
    "UniversalObjectName" -> universalObjectName]]
AbstractPushout[Association["CommonDomain" -> commonDomain_, "CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "MorphismImages" -> morphismImages_List, "MorphismNames" -> morphismNames_List, "PushoutSymbol" -> pushoutSymbol_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]][(abstractCategory_)[
    Association["CompositionSymbol" -> categoryCompositionSymbol_, "IdentitySymbol" -> categoryIdentitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
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
            DirectedEdge[#1, #1]]]] & )[objects]; reducedMorphismAssociation = 
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
     newMorphismEquivalences = If[Length[morphismImages] > 1, 
       (categoryCompositionSymbol[injectionMorphismNames[[#1]], morphismNames[[#1]]] == categoryCompositionSymbol[
           injectionMorphismNames[[#1 + 1]], morphismNames[[#1 + 1]]] & ) /@ 
        Range[Length[reduceObjects[reduceObjects[morphismImages, quiverObjectEquivalences], objectEquivalences]] - 1], 
       {}]; arrowCount = 0; (Module[{object = #1, isUniversalObject, universalMorphisms, injectionMorphisms}, 
        isUniversalObject = True; universalMorphisms = {}; injectionMorphisms = {}; 
         (Module[{pushoutObject = #1}, If[Length[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[
                   reducedMorphismAssociation, morphismEquivalences], objectEquivalences]], 
                First[Last[#1]] === pushoutObject && Last[Last[#1]] === object & ]] == 0, isUniversalObject = 
              False]] & ) /@ reduceObjects[reduceObjects[morphismImages, quiverObjectEquivalences], objectEquivalences]; 
         If[isUniversalObject, (Module[{pushoutObjectIndex = #1, pushoutObject, nextPushoutObject, morphism, 
              nextMorphism, injectionMorphism, nextInjectionMorphism, isCommutative}, 
             pushoutObject = morphismImages[[pushoutObjectIndex]]; nextPushoutObject = morphismImages[[
                pushoutObjectIndex + 1]]; morphism = morphismNames[[pushoutObjectIndex]]; nextMorphism = morphismNames[[
                pushoutObjectIndex + 1]]; injectionMorphism = injectionMorphismNames[[pushoutObjectIndex]]; 
              nextInjectionMorphism = injectionMorphismNames[[pushoutObjectIndex + 1]]; isCommutative = False; 
              (Module[{universalMorphism = #1}, (Module[{nextUniversalMorphism = #1}, If[MemberQ[VertexList[
                        morphismEquivalenceGraph], categoryCompositionSymbol[First[universalMorphism], morphism]] && 
                      MemberQ[VertexList[morphismEquivalenceGraph], categoryCompositionSymbol[First[
                         nextUniversalMorphism], nextMorphism]], If[Length[FindShortestPath[morphismEquivalenceGraph, 
                         categoryCompositionSymbol[First[universalMorphism], morphism], categoryCompositionSymbol[
                          First[nextUniversalMorphism], nextMorphism]]] > 0, isCommutative = True; universalMorphisms = 
                        Join[universalMorphisms, {universalMorphism, nextUniversalMorphism}]; injectionMorphisms = 
                        Join[injectionMorphisms, {injectionMorphism, nextInjectionMorphism}]]]] & ) /@ 
                  Select[Normal[reduceArrowsFinal[reduceArrowsInitial[reducedMorphismAssociation, morphismEquivalences], 
                     objectEquivalences]], First[Last[#1]] === nextPushoutObject && Last[Last[#1]] === object & ]] & ) /@ 
               Select[Normal[reduceArrowsFinal[reduceArrowsInitial[reducedMorphismAssociation, morphismEquivalences], 
                  objectEquivalences]], First[Last[#1]] === pushoutObject && Last[Last[#1]] === object & ]; 
              If[ !isCommutative, isUniversalObject = False]] & ) /@ 
           Range[Length[reduceObjects[reduceObjects[morphismImages, quiverObjectEquivalences], objectEquivalences]] - 
             1]]; If[isUniversalObject, If[Length[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[
                 reducedMorphismAssociation, morphismEquivalences], objectEquivalences]], 
              First[Last[#1]] === pushoutSymbol @@ morphismImages && Last[Last[#1]] === object & ]] == 0, 
           arrowCount += 1; newArrows = Append[newArrows, Subscript[uniqueMorphismName, ToString[arrowCount]] -> 
               DirectedEdge[pushoutSymbol @@ morphismImages, object]]; 
            (Module[{morphismIndex = #1}, newMorphismEquivalences = Append[newMorphismEquivalences, 
                  First[universalMorphisms[[morphismIndex]]] == categoryCompositionSymbol[Subscript[uniqueMorphismName, 
                     ToString[arrowCount]], injectionMorphisms[[morphismIndex]]]]; newMorphismEquivalences = 
                 Append[newMorphismEquivalences, categoryCompositionSymbol[categoryCompositionSymbol[Subscript[
                      uniqueMorphismName, ToString[arrowCount]], injectionMorphismNames[[morphismIndex]]], 
                    morphismNames[[morphismIndex]]] == categoryCompositionSymbol[Subscript[uniqueMorphismName, 
                     ToString[arrowCount]], categoryCompositionSymbol[injectionMorphismNames[[morphismIndex]], 
                     morphismNames[[morphismIndex]]]]]] & ) /@ Range[Length[universalMorphisms]]]]] & ) /@ 
      reduceObjects[reduceObjects[objects, quiverObjectEquivalences], objectEquivalences]; 
     ResourceFunction["AbstractCategory"][Association["CompositionSymbol" -> categoryCompositionSymbol, 
       "IdentitySymbol" -> categoryIdentitySymbol, "MorphismEquivalences" -> 
        DeleteDuplicates[Join[morphismEquivalences, newMorphismEquivalences]], "ObjectEquivalences" -> 
        objectEquivalences, "Quiver" -> ResourceFunction["AbstractQuiver"][
         Association["ArrowEquivalences" -> arrowEquivalences, "Arrows" -> Association[DeleteDuplicates[
             Join[Normal[arrows], (morphismNames[[#1]] -> DirectedEdge[commonDomain, morphismImages[[#1]]] & ) /@ Range[
                Length[reduceObjects[reduceObjects[morphismImages, quiverObjectEquivalences], objectEquivalences]]], 
              (injectionMorphismNames[[#1]] -> DirectedEdge[morphismImages[[#1]], pushoutSymbol @@ morphismImages] & ) /@ 
               Range[Length[reduceObjects[reduceObjects[morphismImages, quiverObjectEquivalences], objectEquivalences]]], 
              newArrows]]], "ObjectEquivalences" -> quiverObjectEquivalences, 
          "Objects" -> DeleteDuplicates[Join[objects, morphismImages, {commonDomain, pushoutSymbol @@ 
               morphismImages}]]]]]]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"

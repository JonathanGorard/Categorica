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
AbstractProduct[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "Objects" -> objects_List, "ProductSymbol" -> productSymbol_, "ProjectionMorphismNames" -> 
      projectionMorphismNames_List, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "Objects"] := Join[objects, {productSymbol @@ objects}]
AbstractProduct[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "Objects" -> objects_List, "ProductSymbol" -> productSymbol_, "ProjectionMorphismNames" -> 
      projectionMorphismNames_List, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "ObjectCount"] := Length[Join[objects, {productSymbol @@ objects}]]
AbstractProduct[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "Objects" -> objects_List, "ProductSymbol" -> productSymbol_, "ProjectionMorphismNames" -> 
      projectionMorphismNames_List, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "MorphismAssociation"] := 
  Association[Join[(projectionMorphismNames[[#1]] -> DirectedEdge[productSymbol @@ objects, objects[[#1]]] & ) /@ 
     Range[Length[objects]], (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ objects, 
    {identitySymbol[productSymbol @@ objects] -> DirectedEdge[productSymbol @@ objects, productSymbol @@ objects]}]]
AbstractProduct[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "Objects" -> objects_List, "ProductSymbol" -> productSymbol_, "ProjectionMorphismNames" -> 
      projectionMorphismNames_List, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "MorphismNames"] := 
  First /@ Normal[Association[Join[(projectionMorphismNames[[#1]] -> DirectedEdge[productSymbol @@ objects, 
          objects[[#1]]] & ) /@ Range[Length[objects]], (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ objects, 
      {identitySymbol[productSymbol @@ objects] -> DirectedEdge[productSymbol @@ objects, productSymbol @@ objects]}]]]
AbstractProduct[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "Objects" -> objects_List, "ProductSymbol" -> productSymbol_, "ProjectionMorphismNames" -> 
      projectionMorphismNames_List, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "MorphismEdges"] := (DirectedEdge @@ Last[#1] & ) /@ 
   Normal[Association[Join[(projectionMorphismNames[[#1]] -> DirectedEdge[productSymbol @@ objects, objects[[#1]]] & ) /@ 
       Range[Length[objects]], (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ objects, 
      {identitySymbol[productSymbol @@ objects] -> DirectedEdge[productSymbol @@ objects, productSymbol @@ objects]}]]]
AbstractProduct[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "Objects" -> objects_List, "ProductSymbol" -> productSymbol_, "ProjectionMorphismNames" -> 
      projectionMorphismNames_List, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "MorphismCount"] := 
  Length[Normal[Association[Join[(projectionMorphismNames[[#1]] -> DirectedEdge[productSymbol @@ objects, 
          objects[[#1]]] & ) /@ Range[Length[objects]], (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ objects, 
      {identitySymbol[productSymbol @@ objects] -> DirectedEdge[productSymbol @@ objects, productSymbol @@ objects]}]]]]
AbstractProduct[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "Objects" -> objects_List, "ProductSymbol" -> productSymbol_, "ProjectionMorphismNames" -> 
      projectionMorphismNames_List, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "SimpleMorphismAssociation"] := 
  Association[(projectionMorphismNames[[#1]] -> DirectedEdge[productSymbol @@ objects, objects[[#1]]] & ) /@ 
    Range[Length[objects]]]
AbstractProduct[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "Objects" -> objects_List, "ProductSymbol" -> productSymbol_, "ProjectionMorphismNames" -> 
      projectionMorphismNames_List, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "SimpleMorphismNames"] := 
  First /@ Normal[Association[(projectionMorphismNames[[#1]] -> DirectedEdge[productSymbol @@ objects, 
         objects[[#1]]] & ) /@ Range[Length[objects]]]]
AbstractProduct[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "Objects" -> objects_List, "ProductSymbol" -> productSymbol_, "ProjectionMorphismNames" -> 
      projectionMorphismNames_List, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "SimpleMorphismEdges"] := (DirectedEdge @@ Last[#1] & ) /@ 
   Normal[Association[(projectionMorphismNames[[#1]] -> DirectedEdge[productSymbol @@ objects, objects[[#1]]] & ) /@ 
      Range[Length[objects]]]]
AbstractProduct[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "Objects" -> objects_List, "ProductSymbol" -> productSymbol_, "ProjectionMorphismNames" -> 
      projectionMorphismNames_List, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "SimpleMorphismCount"] := 
  Length[Normal[Association[(projectionMorphismNames[[#1]] -> DirectedEdge[productSymbol @@ objects, 
         objects[[#1]]] & ) /@ Range[Length[objects]]]]]
AbstractProduct[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "Objects" -> objects_List, "ProductSymbol" -> productSymbol_, "ProjectionMorphismNames" -> 
      projectionMorphismNames_List, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalObjects"] := Join[objects, {productSymbol @@ objects, 
    Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]}]
AbstractProduct[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "Objects" -> objects_List, "ProductSymbol" -> productSymbol_, "ProjectionMorphismNames" -> 
      projectionMorphismNames_List, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalObjectCount"] := Length[Join[objects, {productSymbol @@ objects, 
     Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]}]]
AbstractProduct[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "Objects" -> objects_List, "ProductSymbol" -> productSymbol_, "ProjectionMorphismNames" -> 
      projectionMorphismNames_List, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalMorphismAssociation"] := 
  Association[Join[(projectionMorphismNames[[#1]] -> DirectedEdge[productSymbol @@ objects, objects[[#1]]] & ) /@ 
     Range[Length[objects]], (Subscript["\[ForAll]", ToString[universalMorphismNames[[#1]], StandardForm]] -> 
       DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], objects[[#1]]] & ) /@ 
     Range[Length[objects]], (compositionSymbol[projectionMorphismNames[[#1]], uniqueMorphismName] -> 
       DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], objects[[#1]]] & ) /@ 
     Range[Length[objects]], (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ objects, 
    {identitySymbol[productSymbol @@ objects] -> DirectedEdge[productSymbol @@ objects, productSymbol @@ objects], 
     identitySymbol[universalObjectName] -> DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], 
       Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]], 
     Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> 
      DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], productSymbol @@ objects]}]]
AbstractProduct[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "Objects" -> objects_List, "ProductSymbol" -> productSymbol_, "ProjectionMorphismNames" -> 
      projectionMorphismNames_List, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalMorphismNames"] := 
  First /@ Normal[Association[Join[(projectionMorphismNames[[#1]] -> DirectedEdge[productSymbol @@ objects, 
          objects[[#1]]] & ) /@ Range[Length[objects]], 
      (Subscript["\[ForAll]", ToString[universalMorphismNames[[#1]], StandardForm]] -> 
         DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], objects[[#1]]] & ) /@ 
       Range[Length[objects]], (compositionSymbol[projectionMorphismNames[[#1]], uniqueMorphismName] -> 
         DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], objects[[#1]]] & ) /@ 
       Range[Length[objects]], (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ objects, 
      {identitySymbol[productSymbol @@ objects] -> DirectedEdge[productSymbol @@ objects, productSymbol @@ objects], 
       identitySymbol[universalObjectName] -> DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], 
         Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]], 
       Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> 
        DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], productSymbol @@ objects]}]]]
AbstractProduct[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "Objects" -> objects_List, "ProductSymbol" -> productSymbol_, "ProjectionMorphismNames" -> 
      projectionMorphismNames_List, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalMorphismEdges"] := (DirectedEdge @@ Last[#1] & ) /@ 
   Normal[Association[Join[(projectionMorphismNames[[#1]] -> DirectedEdge[productSymbol @@ objects, objects[[#1]]] & ) /@ 
       Range[Length[objects]], (Subscript["\[ForAll]", ToString[universalMorphismNames[[#1]], StandardForm]] -> 
         DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], objects[[#1]]] & ) /@ 
       Range[Length[objects]], (compositionSymbol[projectionMorphismNames[[#1]], uniqueMorphismName] -> 
         DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], objects[[#1]]] & ) /@ 
       Range[Length[objects]], (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ objects, 
      {identitySymbol[productSymbol @@ objects] -> DirectedEdge[productSymbol @@ objects, productSymbol @@ objects], 
       identitySymbol[universalObjectName] -> DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], 
         Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]], 
       Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> 
        DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], productSymbol @@ objects]}]]]
AbstractProduct[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "Objects" -> objects_List, "ProductSymbol" -> productSymbol_, "ProjectionMorphismNames" -> 
      projectionMorphismNames_List, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalMorphismCount"] := 
  Length[Normal[Association[Join[(projectionMorphismNames[[#1]] -> DirectedEdge[productSymbol @@ objects, 
          objects[[#1]]] & ) /@ Range[Length[objects]], 
      (Subscript["\[ForAll]", ToString[universalMorphismNames[[#1]], StandardForm]] -> 
         DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], objects[[#1]]] & ) /@ 
       Range[Length[objects]], (compositionSymbol[projectionMorphismNames[[#1]], uniqueMorphismName] -> 
         DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], objects[[#1]]] & ) /@ 
       Range[Length[objects]], (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ objects, 
      {identitySymbol[productSymbol @@ objects] -> DirectedEdge[productSymbol @@ objects, productSymbol @@ objects], 
       identitySymbol[universalObjectName] -> DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], 
         Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]], 
       Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> 
        DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], productSymbol @@ objects]}]]]]
AbstractProduct[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "Objects" -> objects_List, "ProductSymbol" -> productSymbol_, "ProjectionMorphismNames" -> 
      projectionMorphismNames_List, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalReducedMorphismAssociation"] := 
  Association[Join[(projectionMorphismNames[[#1]] -> DirectedEdge[productSymbol @@ objects, objects[[#1]]] & ) /@ 
     Range[Length[objects]], (compositionSymbol[projectionMorphismNames[[#1]], uniqueMorphismName] -> 
       DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], objects[[#1]]] & ) /@ 
     Range[Length[objects]], (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ objects, 
    {identitySymbol[productSymbol @@ objects] -> DirectedEdge[productSymbol @@ objects, productSymbol @@ objects], 
     identitySymbol[universalObjectName] -> DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], 
       Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]], 
     Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> 
      DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], productSymbol @@ objects]}]]
AbstractProduct[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "Objects" -> objects_List, "ProductSymbol" -> productSymbol_, "ProjectionMorphismNames" -> 
      projectionMorphismNames_List, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalReducedMorphismNames"] := 
  First /@ Normal[Association[Join[(projectionMorphismNames[[#1]] -> DirectedEdge[productSymbol @@ objects, 
          objects[[#1]]] & ) /@ Range[Length[objects]], 
      (compositionSymbol[projectionMorphismNames[[#1]], uniqueMorphismName] -> 
         DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], objects[[#1]]] & ) /@ 
       Range[Length[objects]], (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ objects, 
      {identitySymbol[productSymbol @@ objects] -> DirectedEdge[productSymbol @@ objects, productSymbol @@ objects], 
       identitySymbol[universalObjectName] -> DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], 
         Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]], 
       Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> 
        DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], productSymbol @@ objects]}]]]
AbstractProduct[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "Objects" -> objects_List, "ProductSymbol" -> productSymbol_, "ProjectionMorphismNames" -> 
      projectionMorphismNames_List, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalReducedMorphismEdges"] := (DirectedEdge @@ Last[#1] & ) /@ 
   Normal[Association[Join[(projectionMorphismNames[[#1]] -> DirectedEdge[productSymbol @@ objects, objects[[#1]]] & ) /@ 
       Range[Length[objects]], (compositionSymbol[projectionMorphismNames[[#1]], uniqueMorphismName] -> 
         DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], objects[[#1]]] & ) /@ 
       Range[Length[objects]], (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ objects, 
      {identitySymbol[productSymbol @@ objects] -> DirectedEdge[productSymbol @@ objects, productSymbol @@ objects], 
       identitySymbol[universalObjectName] -> DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], 
         Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]], 
       Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> 
        DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], productSymbol @@ objects]}]]]
AbstractProduct[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "Objects" -> objects_List, "ProductSymbol" -> productSymbol_, "ProjectionMorphismNames" -> 
      projectionMorphismNames_List, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalReducedMorphismCount"] := 
  Length[Normal[Association[Join[(projectionMorphismNames[[#1]] -> DirectedEdge[productSymbol @@ objects, 
          objects[[#1]]] & ) /@ Range[Length[objects]], 
      (compositionSymbol[projectionMorphismNames[[#1]], uniqueMorphismName] -> 
         DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], objects[[#1]]] & ) /@ 
       Range[Length[objects]], (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ objects, 
      {identitySymbol[productSymbol @@ objects] -> DirectedEdge[productSymbol @@ objects, productSymbol @@ objects], 
       identitySymbol[universalObjectName] -> DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], 
         Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]], 
       Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> 
        DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], productSymbol @@ objects]}]]]]
AbstractProduct[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "Objects" -> objects_List, "ProductSymbol" -> productSymbol_, "ProjectionMorphismNames" -> 
      projectionMorphismNames_List, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalSimpleMorphismAssociation"] := 
  Association[Join[(projectionMorphismNames[[#1]] -> DirectedEdge[productSymbol @@ objects, objects[[#1]]] & ) /@ 
     Range[Length[objects]], (Subscript["\[ForAll]", ToString[universalMorphismNames[[#1]], StandardForm]] -> 
       DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], objects[[#1]]] & ) /@ 
     Range[Length[objects]], {Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> 
      DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], productSymbol @@ objects]}]]
AbstractProduct[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "Objects" -> objects_List, "ProductSymbol" -> productSymbol_, "ProjectionMorphismNames" -> 
      projectionMorphismNames_List, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalSimpleMorphismNames"] := 
  First /@ Normal[Association[Join[(projectionMorphismNames[[#1]] -> DirectedEdge[productSymbol @@ objects, 
          objects[[#1]]] & ) /@ Range[Length[objects]], 
      (Subscript["\[ForAll]", ToString[universalMorphismNames[[#1]], StandardForm]] -> 
         DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], objects[[#1]]] & ) /@ 
       Range[Length[objects]], {Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> 
        DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], productSymbol @@ objects]}]]]
AbstractProduct[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "Objects" -> objects_List, "ProductSymbol" -> productSymbol_, "ProjectionMorphismNames" -> 
      projectionMorphismNames_List, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalSimpleMorphismEdges"] := (DirectedEdge @@ Last[#1] & ) /@ 
   Normal[Association[Join[(projectionMorphismNames[[#1]] -> DirectedEdge[productSymbol @@ objects, objects[[#1]]] & ) /@ 
       Range[Length[objects]], (Subscript["\[ForAll]", ToString[universalMorphismNames[[#1]], StandardForm]] -> 
         DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], objects[[#1]]] & ) /@ 
       Range[Length[objects]], {Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> 
        DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], productSymbol @@ objects]}]]]
AbstractProduct[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "Objects" -> objects_List, "ProductSymbol" -> productSymbol_, "ProjectionMorphismNames" -> 
      projectionMorphismNames_List, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalSimpleMorphismCount"] := 
  Length[Normal[Association[Join[(projectionMorphismNames[[#1]] -> DirectedEdge[productSymbol @@ objects, 
          objects[[#1]]] & ) /@ Range[Length[objects]], 
      (Subscript["\[ForAll]", ToString[universalMorphismNames[[#1]], StandardForm]] -> 
         DirectedEdge[Subscript["\[ForAll]", ToString[universalMorphismNames[[#1]], StandardForm]], objects[[#1]]] & ) /@ 
       Range[Length[objects]], {Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> 
        DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], productSymbol @@ objects]}]]]]
AbstractProduct[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "Objects" -> objects_List, "ProductSymbol" -> productSymbol_, "ProjectionMorphismNames" -> 
      projectionMorphismNames_List, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalReducedSimpleMorphismAssociation"] := 
  Association[Join[(projectionMorphismNames[[#1]] -> DirectedEdge[productSymbol @@ objects, objects[[#1]]] & ) /@ 
     Range[Length[objects]], (compositionSymbol[projectionMorphismNames[[#1]], uniqueMorphismName] -> 
       DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], objects[[#1]]] & ) /@ 
     Range[Length[objects]], {Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> 
      DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], productSymbol @@ objects]}]]
AbstractProduct[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "Objects" -> objects_List, "ProductSymbol" -> productSymbol_, "ProjectionMorphismNames" -> 
      projectionMorphismNames_List, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalReducedSimpleMorphismNames"] := 
  First /@ Normal[Association[Join[(projectionMorphismNames[[#1]] -> DirectedEdge[productSymbol @@ objects, 
          objects[[#1]]] & ) /@ Range[Length[objects]], 
      (compositionSymbol[projectionMorphismNames[[#1]], uniqueMorphismName] -> 
         DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], objects[[#1]]] & ) /@ 
       Range[Length[objects]], {Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> 
        DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], productSymbol @@ objects]}]]]
AbstractProduct[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "Objects" -> objects_List, "ProductSymbol" -> productSymbol_, "ProjectionMorphismNames" -> 
      projectionMorphismNames_List, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalReducedSimpleMorphismEdges"] := (DirectedEdge @@ Last[#1] & ) /@ 
   Normal[Association[Join[(projectionMorphismNames[[#1]] -> DirectedEdge[productSymbol @@ objects, objects[[#1]]] & ) /@ 
       Range[Length[objects]], (compositionSymbol[projectionMorphismNames[[#1]], uniqueMorphismName] -> 
         DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], objects[[#1]]] & ) /@ 
       Range[Length[objects]], {Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> 
        DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], productSymbol @@ objects]}]]]
AbstractProduct[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "Objects" -> objects_List, "ProductSymbol" -> productSymbol_, "ProjectionMorphismNames" -> 
      projectionMorphismNames_List, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalReducedSimpleMorphismCount"] := 
  Length[Normal[Association[Join[(projectionMorphismNames[[#1]] -> DirectedEdge[productSymbol @@ objects, 
          objects[[#1]]] & ) /@ Range[Length[objects]], 
      (compositionSymbol[projectionMorphismNames[[#1]], uniqueMorphismName] -> 
         DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], objects[[#1]]] & ) /@ 
       Range[Length[objects]], {Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> 
        DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], productSymbol @@ objects]}]]]]
AbstractProduct[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "Objects" -> objects_List, "ProductSymbol" -> productSymbol_, "ProjectionMorphismNames" -> 
      projectionMorphismNames_List, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "ProductSymbol"] := productSymbol
AbstractProduct[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "Objects" -> objects_List, "ProductSymbol" -> productSymbol_, "ProjectionMorphismNames" -> 
      projectionMorphismNames_List, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "CompositionSymbol"] := compositionSymbol
AbstractProduct[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "Objects" -> objects_List, "ProductSymbol" -> productSymbol_, "ProjectionMorphismNames" -> 
      projectionMorphismNames_List, "UniqueMorphismName" -> universalMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "IdentitySymbol"] := identitySymbol
AbstractProduct[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "Objects" -> objects_List, "ProductSymbol" -> productSymbol_, "ProjectionMorphismNames" -> 
      projectionMorphismNames_List, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "ProductCategory"] := ResourceFunction["AbstractCategory"][Association["CompositionSymbol" -> compositionSymbol, 
    "IdentitySymbol" -> identitySymbol, "MorphismEquivalences" -> {}, "ObjectEquivalences" -> {}, 
    "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> {}, 
       "Arrows" -> Association[(projectionMorphismNames[[#1]] -> DirectedEdge[productSymbol @@ objects, 
             objects[[#1]]] & ) /@ Range[Length[objects]]], "ObjectEquivalences" -> {}, 
       "Objects" -> Join[objects, {productSymbol @@ objects}]]]]]
AbstractProduct[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "Objects" -> objects_List, "ProductSymbol" -> productSymbol_, "ProjectionMorphismNames" -> 
      projectionMorphismNames_List, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalProductCategory"] := ResourceFunction["AbstractCategory"][
   Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
    "MorphismEquivalences" -> (universalMorphismNames[[#1]] == compositionSymbol[projectionMorphismNames[[#1]], 
         uniqueMorphismName] & ) /@ Range[Length[objects]], "ObjectEquivalences" -> {}, 
    "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> {}, 
       "Arrows" -> Association[Join[(projectionMorphismNames[[#1]] -> DirectedEdge[productSymbol @@ objects, 
              objects[[#1]]] & ) /@ Range[Length[objects]], (universalMorphismNames[[#1]] -> 
             DirectedEdge[universalObjectName, objects[[#1]]] & ) /@ Range[Length[objects]], 
          {uniqueMorphismName -> DirectedEdge[universalObjectName, productSymbol @@ objects]}]], 
       "ObjectEquivalences" -> {}, "Objects" -> Join[objects, {productSymbol @@ objects, universalObjectName}]]]]]
AbstractProduct[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "Objects" -> objects_List, "ProductSymbol" -> productSymbol_, "ProjectionMorphismNames" -> 
      projectionMorphismNames_List, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalProductEquations"] := 
  (ToExpression[StringJoin["HoldForm[ForAll[", ToString[universalMorphismNames[[#1]], StandardForm], ",Exists[", 
      ToString[uniqueMorphismName, StandardForm], ",", ToString[universalMorphismNames[[#1]] == 
        compositionSymbol[projectionMorphismNames[[#1]], uniqueMorphismName], StandardForm], "]]]"]] & ) /@ 
   Range[Length[objects]]
AbstractProduct[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "Objects" -> objects_List, "ProductSymbol" -> productSymbol_, "ProjectionMorphismNames" -> 
      projectionMorphismNames_List, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "FullLabeledGraph"] := EdgeTaggedGraph[Join[objects, {productSymbol @@ objects}], 
   (Labeled[DirectedEdge @@ Last[#1], Placed[First[#1], 0.5]] & ) /@ 
    Normal[Association[Join[(projectionMorphismNames[[#1]] -> DirectedEdge[productSymbol @@ objects, 
           objects[[#1]]] & ) /@ Range[Length[objects]], (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ objects, 
       {identitySymbol[productSymbol @@ objects] -> DirectedEdge[productSymbol @@ objects, productSymbol @@ objects]}]]], 
   VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], VertexLabels -> Placed["Name", Center], 
   VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], EdgeStyle -> Directive[Black, Thick], 
   GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]
AbstractProduct[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "Objects" -> objects_List, "ProductSymbol" -> productSymbol_, "ProjectionMorphismNames" -> 
      projectionMorphismNames_List, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "FullUnlabeledGraph"] := EdgeTaggedGraph[Join[objects, {productSymbol @@ objects}], 
   (DirectedEdge @@ Last[#1] & ) /@ 
    Normal[Association[Join[(projectionMorphismNames[[#1]] -> DirectedEdge[productSymbol @@ objects, 
           objects[[#1]]] & ) /@ Range[Length[objects]], (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ objects, 
       {identitySymbol[productSymbol @@ objects] -> DirectedEdge[productSymbol @@ objects, productSymbol @@ objects]}]]], 
   VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], VertexLabels -> Placed["Name", Center], 
   VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], EdgeStyle -> Directive[Black, Thick], 
   GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]
AbstractProduct[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "Objects" -> objects_List, "ProductSymbol" -> productSymbol_, "ProjectionMorphismNames" -> 
      projectionMorphismNames_List, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "SimpleLabeledGraph"] := EdgeTaggedGraph[Join[objects, {productSymbol @@ objects}], 
   (Labeled[DirectedEdge @@ Last[#1], Placed[First[#1], 0.5]] & ) /@ 
    Normal[Association[(projectionMorphismNames[[#1]] -> DirectedEdge[productSymbol @@ objects, objects[[#1]]] & ) /@ 
       Range[Length[objects]]]], VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], 
   VertexLabels -> Placed["Name", Center], VertexLabelStyle -> Directive[Bold, 20], 
   EdgeLabelStyle -> Directive[Bold, 20], EdgeStyle -> Directive[Black, Thick], 
   GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]
AbstractProduct[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "Objects" -> objects_List, "ProductSymbol" -> productSymbol_, "ProjectionMorphismNames" -> 
      projectionMorphismNames_List, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "SimpleUnlabeledGraph"] := EdgeTaggedGraph[Join[objects, {productSymbol @@ objects}], 
   (DirectedEdge @@ Last[#1] & ) /@ 
    Normal[Association[(projectionMorphismNames[[#1]] -> DirectedEdge[productSymbol @@ objects, objects[[#1]]] & ) /@ 
       Range[Length[objects]]]], VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], 
   VertexLabels -> Placed["Name", Center], VertexLabelStyle -> Directive[Bold, 20], 
   EdgeLabelStyle -> Directive[Bold, 20], EdgeStyle -> Directive[Black, Thick], 
   GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]
AbstractProduct[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "Objects" -> objects_List, "ProductSymbol" -> productSymbol_, "ProjectionMorphismNames" -> 
      projectionMorphismNames_List, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalFullLabeledGraph"] := EdgeTaggedGraph[Join[objects, {productSymbol @@ objects, universalObjectName}], 
   (Labeled[DirectedEdge @@ Last[#1], Placed[First[#1], 0.5]] & ) /@ 
    Normal[Association[Join[(projectionMorphismNames[[#1]] -> DirectedEdge[productSymbol @@ objects, 
           objects[[#1]]] & ) /@ Range[Length[objects]], 
       (Subscript["\[ForAll]", ToString[universalMorphismNames[[#1]], StandardForm]] -> DirectedEdge[universalObjectName, 
           objects[[#1]]] & ) /@ Range[Length[objects]], 
       (compositionSymbol[projectionMorphismNames[[#1]], uniqueMorphismName] -> DirectedEdge[universalObjectName, 
           objects[[#1]]] & ) /@ Range[Length[objects]], (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ objects, 
       {identitySymbol[productSymbol @@ objects] -> DirectedEdge[productSymbol @@ objects, productSymbol @@ objects], 
        identitySymbol[universalObjectName] -> DirectedEdge[universalObjectName, universalObjectName], 
        Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> DirectedEdge[universalObjectName, 
          productSymbol @@ objects]}]]], VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], 
   VertexLabels -> {Placed["Name", Center], universalObjectName -> 
      Placed[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], Center]}, 
   VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
   EdgeStyle -> {Directive[Black, Thick], DirectedEdge[universalObjectName, productSymbol @@ objects] -> Dashed}, 
   GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]
AbstractProduct[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "Objects" -> objects_List, "ProductSymbol" -> productSymbol_, "ProjectionMorphismNames" -> 
      projectionMorphismNames_List, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalFullUnlabeledGraph"] := EdgeTaggedGraph[Join[objects, {productSymbol @@ objects, universalObjectName}], 
   (DirectedEdge @@ Last[#1] & ) /@ 
    Normal[Association[Join[(projectionMorphismNames[[#1]] -> DirectedEdge[productSymbol @@ objects, 
           objects[[#1]]] & ) /@ Range[Length[objects]], 
       (Subscript["\[ForAll]", ToString[universalMorphismNames[[#1]], StandardForm]] -> DirectedEdge[universalObjectName, 
           objects[[#1]]] & ) /@ Range[Length[objects]], 
       (compositionSymbol[projectionMorphismNames[[#1]], uniqueMorphismName] -> DirectedEdge[universalObjectName, 
           objects[[#1]]] & ) /@ Range[Length[objects]], (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ objects, 
       {identitySymbol[productSymbol @@ objects] -> DirectedEdge[productSymbol @@ objects, productSymbol @@ objects], 
        identitySymbol[universalObjectName] -> DirectedEdge[universalObjectName, universalObjectName], 
        Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> DirectedEdge[universalObjectName, 
          productSymbol @@ objects]}]]], VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], 
   VertexLabels -> {Placed["Name", Center], universalObjectName -> 
      Placed[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], Center]}, 
   VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
   EdgeStyle -> {Directive[Black, Thick], DirectedEdge[universalObjectName, productSymbol @@ objects] -> Dashed}, 
   GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]
AbstractProduct[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "Objects" -> objects_List, "ProductSymbol" -> productSymbol_, "ProjectionMorphismNames" -> 
      projectionMorphismNames_List, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalReducedLabeledGraph"] := EdgeTaggedGraph[Join[objects, {productSymbol @@ objects, universalObjectName}], 
   (Labeled[DirectedEdge @@ Last[#1], Placed[First[#1], 0.5]] & ) /@ 
    Normal[Association[Join[(projectionMorphismNames[[#1]] -> DirectedEdge[productSymbol @@ objects, 
           objects[[#1]]] & ) /@ Range[Length[objects]], 
       (compositionSymbol[projectionMorphismNames[[#1]], uniqueMorphismName] -> DirectedEdge[universalObjectName, 
           objects[[#1]]] & ) /@ Range[Length[objects]], (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ objects, 
       {identitySymbol[productSymbol @@ objects] -> DirectedEdge[productSymbol @@ objects, productSymbol @@ objects], 
        identitySymbol[universalObjectName] -> DirectedEdge[universalObjectName, universalObjectName], 
        Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> DirectedEdge[universalObjectName, 
          productSymbol @@ objects]}]]], VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], 
   VertexLabels -> {Placed["Name", Center], universalObjectName -> 
      Placed[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], Center]}, 
   VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
   EdgeStyle -> {Directive[Black, Thick], DirectedEdge[universalObjectName, productSymbol @@ objects] -> Dashed}, 
   GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]
AbstractProduct[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "Objects" -> objects_List, "ProductSymbol" -> productSymbol_, "ProjectionMorphismNames" -> 
      projectionMorphismNames_List, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalReducedUnlabeledGraph"] := EdgeTaggedGraph[Join[objects, {productSymbol @@ objects, universalObjectName}], 
   (DirectedEdge @@ Last[#1] & ) /@ 
    Normal[Association[Join[(projectionMorphismNames[[#1]] -> DirectedEdge[productSymbol @@ objects, 
           objects[[#1]]] & ) /@ Range[Length[objects]], 
       (compositionSymbol[projectionMorphismNames[[#1]], uniqueMorphismName] -> DirectedEdge[universalObjectName, 
           objects[[#1]]] & ) /@ Range[Length[objects]], (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ objects, 
       {identitySymbol[productSymbol @@ objects] -> DirectedEdge[productSymbol @@ objects, productSymbol @@ objects], 
        identitySymbol[universalObjectName] -> DirectedEdge[universalObjectName, universalObjectName], 
        Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> DirectedEdge[universalObjectName, 
          productSymbol @@ objects]}]]], VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], 
   VertexLabels -> {Placed["Name", Center], universalObjectName -> 
      Placed[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], Center]}, 
   VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
   EdgeStyle -> {Directive[Black, Thick], DirectedEdge[universalObjectName, productSymbol @@ objects] -> Dashed}, 
   GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]
AbstractProduct[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "Objects" -> objects_List, "ProductSymbol" -> productSymbol_, "ProjectionMorphismNames" -> 
      projectionMorphismNames_List, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalSimpleLabeledGraph"] := EdgeTaggedGraph[Join[objects, {productSymbol @@ objects, universalObjectName}], 
   (Labeled[DirectedEdge @@ Last[#1], Placed[First[#1], 0.5]] & ) /@ 
    Normal[Association[Join[(projectionMorphismNames[[#1]] -> DirectedEdge[productSymbol @@ objects, 
           objects[[#1]]] & ) /@ Range[Length[objects]], 
       (Subscript["\[ForAll]", ToString[universalMorphismNames[[#1]], StandardForm]] -> DirectedEdge[universalObjectName, 
           objects[[#1]]] & ) /@ Range[Length[objects]], 
       {Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> DirectedEdge[universalObjectName, 
          productSymbol @@ objects]}]]], VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], 
   VertexLabels -> {Placed["Name", Center], universalObjectName -> 
      Placed[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], Center]}, 
   VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
   EdgeStyle -> {Directive[Black, Thick], DirectedEdge[universalObjectName, productSymbol @@ objects] -> Dashed}, 
   GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]
AbstractProduct[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "Objects" -> objects_List, "ProductSymbol" -> productSymbol_, "ProjectionMorphismNames" -> 
      projectionMorphismNames_List, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalSimpleUnlabeledGraph"] := EdgeTaggedGraph[Join[objects, {productSymbol @@ objects, universalObjectName}], 
   (DirectedEdge @@ Last[#1] & ) /@ 
    Normal[Association[Join[(projectionMorphismNames[[#1]] -> DirectedEdge[productSymbol @@ objects, 
           objects[[#1]]] & ) /@ Range[Length[objects]], 
       (Subscript["\[ForAll]", ToString[universalMorphismNames[[#1]], StandardForm]] -> DirectedEdge[universalObjectName, 
           objects[[#1]]] & ) /@ Range[Length[objects]], 
       {Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> DirectedEdge[universalObjectName, 
          productSymbol @@ objects]}]]], VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], 
   VertexLabels -> {Placed["Name", Center], universalObjectName -> 
      Placed[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], Center]}, 
   VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
   EdgeStyle -> {Directive[Black, Thick], DirectedEdge[universalObjectName, productSymbol @@ objects] -> Dashed}, 
   GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]
AbstractProduct[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "Objects" -> objects_List, "ProductSymbol" -> productSymbol_, "ProjectionMorphismNames" -> 
      projectionMorphismNames_List, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalReducedSimpleLabeledGraph"] := EdgeTaggedGraph[
   Join[objects, {productSymbol @@ objects, universalObjectName}], 
   (Labeled[DirectedEdge @@ Last[#1], Placed[First[#1], 0.5]] & ) /@ 
    Normal[Association[Join[(projectionMorphismNames[[#1]] -> DirectedEdge[productSymbol @@ objects, 
           objects[[#1]]] & ) /@ Range[Length[objects]], 
       (compositionSymbol[projectionMorphismNames[[#1]], uniqueMorphismName] -> DirectedEdge[universalObjectName, 
           objects[[#1]]] & ) /@ Range[Length[objects]], 
       {Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> DirectedEdge[universalObjectName, 
          productSymbol @@ objects]}]]], VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], 
   VertexLabels -> {Placed["Name", Center], universalObjectName -> 
      Placed[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], Center]}, 
   VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
   EdgeStyle -> {Directive[Black, Thick], DirectedEdge[universalObjectName, productSymbol @@ objects] -> Dashed}, 
   GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]
AbstractProduct[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "Objects" -> objects_List, "ProductSymbol" -> productSymbol_, "ProjectionMorphismNames" -> 
      projectionMorphismNames_List, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalReducedSimpleUnlabeledGraph"] := 
  EdgeTaggedGraph[Join[objects, {productSymbol @@ objects, universalObjectName}], 
   (DirectedEdge @@ Last[#1] & ) /@ 
    Normal[Association[Join[(projectionMorphismNames[[#1]] -> DirectedEdge[productSymbol @@ objects, 
           objects[[#1]]] & ) /@ Range[Length[objects]], 
       (compositionSymbol[projectionMorphismNames[[#1]], uniqueMorphismName] -> DirectedEdge[universalObjectName, 
           objects[[#1]]] & ) /@ Range[Length[objects]], 
       {Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> DirectedEdge[universalObjectName, 
          productSymbol @@ objects]}]]], VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], 
   VertexLabels -> {Placed["Name", Center], universalObjectName -> 
      Placed[Subscript["\[ForAll]", ToString[universalObjectName]], Center]}, VertexLabelStyle -> Directive[Bold, 20], 
   EdgeLabelStyle -> Directive[Bold, 20], EdgeStyle -> {Directive[Black, Thick], 
     DirectedEdge[universalObjectName, productSymbol @@ objects] -> Dashed}, 
   GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]
AbstractProduct[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "Objects" -> objects_List, "ProductSymbol" -> productSymbol_, "ProjectionMorphismNames" -> 
      projectionMorphismNames_List, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "AssociationForm"] := Association["Objects" -> objects, "ProductSymbol" -> productSymbol, 
   "ProjectionMorphismNames" -> projectionMorphismNames, "CompositionSymbol" -> compositionSymbol, 
   "IdentitySymbol" -> identitySymbol, "UniversalObjectName" -> universalObjectName, 
   "UniversalMorphismNames" -> universalMorphismNames, "UniqueMorphismName" -> uniqueMorphismName]
AbstractProduct[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "Objects" -> objects_List, "ProductSymbol" -> productSymbol_, "ProjectionMorphismNames" -> 
      projectionMorphismNames_List, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "Properties"] := {"Objects", "ObjectCount", "MorphismAssociation", "MorphismNames", "MorphismEdges", "MorphismCount", 
   "SimpleMorphismAssociation", "SimpleMorphismNames", "SimpleMorphismEdges", "SimpleMorphismCount", "UniversalObjects", 
   "UniversalObjectCount", "UniversalMorphismAssociation", "UniversalMorphismNames", "UniversalMorphismEdges", 
   "UniversalMorphismCount", "UniversalReducedMorphismAssociation", "UniversalReducedMorphismNames", 
   "UniversalReducedMorphismEdges", "UniversalReducedMorphismCount", "UniversalSimpleMorphismAssociation", 
   "UniversalSimpleMorphismNames", "UniversalSimpleMorphismEdges", "UniversalSimpleMorphismCount", 
   "UniversalReducedSimpleMorphismAssociation", "UniversalReducedSimpleMorphismNames", 
   "UniversalReducedSimpleMorphismEdges", "UniversalReducedSimpleMorphismCount", "ProductSymbol", "CompositionSymbol", 
   "IdentitySymbol", "ProductCategory", "UniversalProductCategory", "UniversalProductEquations", "FullLabeledGraph", 
   "FullUnlabeledGraph", "SimpleLabeledGraph", "SimpleUnlabeledGraph", "UniversalFullLabeledGraph", 
   "UniversalFullUnlabeledGraph", "UniversalReducedLabeledGraph", "UniversalReducedUnlabeledGraph", 
   "UniversalSimpleLabeledGraph", "UniversalSimpleUnlabeledGraph", "UniversalReducedSimpleLabeledGraph", 
   "UniversalReducedSimpleUnlabeledGraph", "AssociationForm", "Properties"}
AbstractProduct /: MakeBoxes[abstractProduct:AbstractProduct[Association["CompositionSymbol" -> compositionSymbol_, 
       "IdentitySymbol" -> identitySymbol_, "Objects" -> objects_List, "ProductSymbol" -> productSymbol_, 
       "ProjectionMorphismNames" -> projectionMorphismNames_List, "UniqueMorphismName" -> uniqueMorphismName_, 
       "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]], 
    format_] := Module[{icon, objectCount}, 
    icon = GraphPlot[EdgeTaggedGraph[Join[objects, {productSymbol @@ objects}], (DirectedEdge @@ Last[#1] & ) /@ 
         Normal[Association[Join[(projectionMorphismNames[[#1]] -> DirectedEdge[productSymbol @@ objects, 
                objects[[#1]]] & ) /@ Range[Length[objects]], (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ objects, 
            {identitySymbol[productSymbol @@ objects] -> DirectedEdge[productSymbol @@ objects, productSymbol @@ 
                objects]}]]], VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], 
        EdgeShapeFunction -> GraphElementData["ShortFilledArrow", "ArrowSize" -> 0.05], EdgeStyle -> Black, 
        GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]]; objectCount = Length[objects]; 
     BoxForm`ArrangeSummaryBox["AbstractProduct", abstractProduct, icon, 
      {{BoxForm`SummaryItem[{"Objects: ", objectCount}]}, {BoxForm`SummaryItem[{"Symbol: ", productSymbol}]}}, {{}}, 
      format, "Interpretable" -> Automatic]]
AbstractProduct[objects_List] := AbstractProduct[Association["CompositionSymbol" -> CircleDot, 
    "IdentitySymbol" -> OverTilde, "Objects" -> objects, "ProductSymbol" -> Cross, 
    "ProjectionMorphismNames" -> (Subscript["\[FormalPi]", ToString[#1]] & ) /@ Range[Length[objects]], 
    "UniqueMorphismName" -> "\[FormalF]", "UniversalMorphismNames" -> (Subscript["\[FormalF]", ToString[#1]] & ) /@ 
      Range[Length[objects]], "UniversalObjectName" -> "\[FormalCapitalY]"]]
AbstractProduct[objects_List, productSymbol_] := 
  AbstractProduct[Association["CompositionSymbol" -> CircleDot, "IdentitySymbol" -> OverTilde, "Objects" -> objects, 
     "ProductSymbol" -> productSymbol, "ProjectionMorphismNames" -> (Subscript["\[FormalPi]", ToString[#1]] & ) /@ 
       Range[Length[objects]], "UniqueMorphismName" -> "\[FormalF]", "UniversalMorphismNames" -> 
      (Subscript["\[FormalF]", ToString[#1]] & ) /@ Range[Length[objects]], "UniversalObjectName" -> "\[FormalCapitalY]"]] /; 
    !ListQ[productSymbol]
AbstractProduct[objects_List, productSymbol_, projectionMorphismNames_List] := 
  AbstractProduct[Association["CompositionSymbol" -> CircleDot, "IdentitySymbol" -> OverTilde, "Objects" -> objects, 
     "ProductSymbol" -> productSymbol, "ProjectionMorphismNames" -> projectionMorphismNames, 
     "UniqueMorphismName" -> "\[FormalF]", "UniversalMorphismNames" -> (Subscript["\[FormalF]", ToString[#1]] & ) /@ 
       Range[Length[objects]], "UniversalObjectName" -> "\[FormalCapitalY]"]] /;  !ListQ[productSymbol]
AbstractProduct[objects_List, productSymbol_, projectionMorphismNames_List, compositionSymbol_] := 
  AbstractProduct[Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> OverTilde, 
     "Objects" -> objects, "ProductSymbol" -> productSymbol, "ProjectionMorphismNames" -> projectionMorphismNames, 
     "UniqueMorphismName" -> "\[FormalF]", "UniversalMorphismNames" -> (Subscript["\[FormalF]", ToString[#1]] & ) /@ 
       Range[Length[objects]], "UniversalObjectName" -> "\[FormalCapitalY]"]] /;  !ListQ[productSymbol] &&  !ListQ[compositionSymbol]
AbstractProduct[objects_List, productSymbol_, projectionMorphismNames_List, compositionSymbol_, identitySymbol_] := 
  AbstractProduct[Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
     "Objects" -> objects, "ProductSymbol" -> productSymbol, "ProjectionMorphismNames" -> projectionMorphismNames, 
     "UniqueMorphismName" -> "\[FormalF]", "UniversalMorphismNames" -> (Subscript["\[FormalF]", ToString[#1]] & ) /@ 
       Range[Length[objects]], "UniversalObjectName" -> "\[FormalCapitalY]"]] /;  !ListQ[productSymbol] && 
     !ListQ[compositionSymbol] &&  !ListQ[identitySymbol]
AbstractProduct[objects_List, productSymbol_, projectionMorphismNames_List, compositionSymbol_, identitySymbol_, 
   universalObjectName_] := AbstractProduct[Association["CompositionSymbol" -> compositionSymbol, 
     "IdentitySymbol" -> identitySymbol, "Objects" -> objects, "ProductSymbol" -> productSymbol, 
     "ProjectionMorphismNames" -> projectionMorphismNames, "UniqueMorphismName" -> "\[FormalF]", 
     "UniversalMorphismNames" -> (Subscript["\[FormalF]", ToString[#1]] & ) /@ Range[Length[objects]], 
     "UniversalObjectName" -> universalObjectName]] /;  !ListQ[productSymbol] &&  !ListQ[compositionSymbol] && 
     !ListQ[identitySymbol]
AbstractProduct[objects_List, productSymbol_, projectionMorphismNames_List, compositionSymbol_, identitySymbol_, 
   universalObjectName_, universalMorphismNames_List] := 
  AbstractProduct[Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
     "Objects" -> objects, "ProductSymbol" -> productSymbol, "ProjectionMorphismNames" -> projectionMorphismNames, 
     "UniqueMorphismName" -> "\[FormalF]", "UniversalMorphismNames" -> universalMorphismNames, 
     "UniversalObjectName" -> universalObjectName]] /;  !ListQ[productSymbol] &&  !ListQ[compositionSymbol] && 
     !ListQ[identitySymbol]
AbstractProduct[objects_List, productSymbol_, projectionMorphismNames_List, compositionSymbol_, identitySymbol_, 
   universalObjectName_, universalMorphismNames_List, uniqueMorphismName_] := 
  AbstractProduct[Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
     "Objects" -> objects, "ProductSymbol" -> productSymbol, "ProjectionMorphismNames" -> projectionMorphismNames, 
     "UniqueMorphismName" -> uniqueMorphismName, "UniversalMorphismNames" -> universalMorphismNames, 
     "UniversalObjectName" -> universalObjectName]] /;  !ListQ[productSymbol] &&  !ListQ[compositionSymbol] && 
     !ListQ[identitySymbol]
AbstractProduct[objects_List, projectionMorphismNames_List] := 
  AbstractProduct[Association["CompositionSymbol" -> CircleDot, "IdentitySymbol" -> OverTilde, "Objects" -> objects, 
    "ProductSymbol" -> Cross, "ProjectionMorphismNames" -> projectionMorphismNames, "UniqueMorphismName" -> "\[FormalF]", 
    "UniversalMorphismNames" -> (Subscript["\[FormalF]", ToString[#1]] & ) /@ Range[Length[objects]], 
    "UniversalObjectName" -> "\[FormalCapitalY]"]]
AbstractProduct[objects_List, projectionMorphismNames_List, compositionSymbol_] := 
  AbstractProduct[Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> OverTilde, 
    "Objects" -> objects, "ProductSymbol" -> Cross, "ProjectionMorphismNames" -> projectionMorphismNames, 
    "UniqueMorphismName" -> "\[FormalF]", "UniversalMorphismNames" -> (Subscript["\[FormalF]", ToString[#1]] & ) /@ 
      Range[Length[objects]], "UniversalObjectName" -> "\[FormalCapitalY]"]]
AbstractProduct[objects_List, projectionMorphismNames_List, compositionSymbol_, identitySymbol_] := 
  AbstractProduct[Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
    "Objects" -> objects, "ProductSymbol" -> Cross, "ProjectionMorphismNames" -> projectionMorphismNames, 
    "UniqueMorphismName" -> "\[FormalF]", "UniversalMorphismNames" -> (Subscript["\[FormalF]", ToString[#1]] & ) /@ 
      Range[Length[objects]], "UniversalObjectName" -> "\[FormalCapitalY]"]]
AbstractProduct[objects_List, productSymbol_, compositionSymbol_] := 
  AbstractProduct[Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> OverTilde, 
     "Objects" -> objects, "ProductSymbol" -> productSymbol, "ProjectionMorphismNames" -> 
      (Subscript["\[FormalPi]", ToString[#1]] & ) /@ Range[Length[objects]], "UniqueMorphismName" -> "\[FormalF]", 
     "UniversalMorphismNames" -> (Subscript["\[FormalF]", ToString[#1]] & ) /@ Range[Length[objects]], 
     "UniversalObjectName" -> "\[FormalCapitalY]"]] /;  !ListQ[productSymbol] &&  !ListQ[compositionSymbol]
AbstractProduct[objects_List, productSymbol_, compositionSymbol_, identitySymbol_] := 
  AbstractProduct[Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
     "Objects" -> objects, "ProductSymbol" -> productSymbol, "ProjectionMorphismNames" -> 
      (Subscript["\[FormalPi]", ToString[#1]] & ) /@ Range[Length[objects]], "UniqueMorphismName" -> "\[FormalF]", 
     "UniversalMorphismNames" -> (Subscript["\[FormalF]", ToString[#1]] & ) /@ Range[Length[objects]], 
     "UniversalObjectName" -> "\[FormalCapitalY]"]] /;  !ListQ[productSymbol] &&  !ListQ[compositionSymbol] &&  !ListQ[identitySymbol]
AbstractProduct[product_Association] := AbstractProduct[KeySort[product]] /; 
   KeyExistsQ[product, "CompositionSymbol"] && KeyExistsQ[product, "IdentitySymbol"] && KeyExistsQ[product, "Objects"] && 
    KeyExistsQ[product, "ProductSymbol"] && KeyExistsQ[product, "ProjectionMorphismNames"] && 
    KeyExistsQ[product, "UniqueMorphismName"] && KeyExistsQ[product, "UniversalMorphismNames"] && 
    KeyExistsQ[product, "UniversalObjectName"] && Keys[KeySort[product]] =!= Keys[product]
AbstractProduct[AbstractProduct[Association["CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "Objects" -> objects_List, "ProductSymbol" -> productSymbol_, 
     "ProjectionMorphismNames" -> projectionMorphismNames_List, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]], 
   newProductSymbol_] := AbstractProduct[Association["CompositionSymbol" -> compositionSymbol, 
    "IdentitySymbol" -> identitySymbol, "Objects" -> objects, "ProductSymbol" -> newProductSymbol, 
    "ProjectionMorphismNames" -> projectionMorphismNames, "UniqueMorphismName" -> uniqueMorphismName, 
    "UniversalMorphismNames" -> universalMorphismNames, "UniversalObjectName" -> universalObjectName]]
AbstractProduct[AbstractProduct[Association["CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "Objects" -> objects_List, "ProductSymbol" -> productSymbol_, 
     "ProjectionMorphismNames" -> projectionMorphismNames_List, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]], 
   newProductSymbol_, newCompositionSymbol_] := AbstractProduct[Association["CompositionSymbol" -> newCompositionSymbol, 
    "IdentitySymbol" -> identitySymbol, "Objects" -> objects, "ProductSymbol" -> newProductSymbol, 
    "ProjectionMorphismNames" -> projectionMorphismNames, "UniqueMorphismName" -> uniqueMorphismName, 
    "UniversalMorphismNames" -> universalMorphismNames, "UniversalObjectName" -> universalObjectName]]
AbstractProduct[AbstractProduct[Association["CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "Objects" -> objects_List, "ProductSymbol" -> productSymbol_, 
     "ProjectionMorphismNames" -> projectionMorphismNames_List, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]], 
   newProductSymbol_, newCompositionSymbol_, newIdentitySymbol_] := 
  AbstractProduct[Association["CompositionSymbol" -> newCompositionSymbol, "IdentitySymbol" -> newIdentitySymbol, 
    "Objects" -> objects, "ProductSymbol" -> newProductSymbol, "ProjectionMorphismNames" -> projectionMorphismNames, 
    "UniqueMorphismName" -> uniqueMorphismName, "UniversalMorphismNames" -> universalMorphismNames, 
    "UniversalObjectName" -> universalObjectName]]
AbstractProduct[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "Objects" -> objects_List, "ProductSymbol" -> productSymbol_, "ProjectionMorphismNames" -> 
      projectionMorphismNames_List, "UniqueMorphismName" -> uniqueMorphismName_, 
     "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   (abstractCategory_)[Association["CompositionSymbol" -> categoryCompositionSymbol_, 
     "IdentitySymbol" -> categoryIdentitySymbol_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> categoryObjects_List]]]]] := 
  Module[{morphismAssociation, compositions, newArrows, arrowCount, newMorphismEquivalences}, 
    morphismAssociation = Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[arrows, arrowEquivalences], 
          quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[categoryCompositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], categoryCompositionSymbol[First[Last[#1]], First[
                First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, 
      Length[reduceObjects[categoryObjects, quiverObjectEquivalences]]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. categoryCompositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. categoryCompositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], categoryIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], categoryIdentitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[categoryObjects, quiverObjectEquivalences]; newArrows = {}; 
     newMorphismEquivalences = {}; arrowCount = 0; 
     (Module[{object = #1, isUniversalObject}, isUniversalObject = True; 
         (Module[{productObject = #1}, If[Length[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[morphismAssociation, 
                   morphismEquivalences], objectEquivalences]], First[Last[#1]] === object && Last[Last[#1]] === 
                   productObject & ]] == 0, isUniversalObject = False]] & ) /@ 
          reduceObjects[reduceObjects[objects, quiverObjectEquivalences], objectEquivalences]; 
         If[isUniversalObject, If[Length[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[morphismAssociation, 
                 morphismEquivalences], objectEquivalences]], First[Last[#1]] === object && Last[Last[#1]] === 
                 productSymbol @@ objects & ]] == 0, arrowCount += 1; newArrows = Append[newArrows, 
              Subscript[uniqueMorphismName, ToString[arrowCount]] -> DirectedEdge[object, productSymbol @@ objects]]; 
            (Module[{productObjectIndex = #1, productObject}, productObject = reduceObjects[reduceObjects[objects, 
                    quiverObjectEquivalences], objectEquivalences][[productObjectIndex]]; newMorphismEquivalences = 
                 Join[newMorphismEquivalences, (First[#1] == categoryCompositionSymbol[projectionMorphismNames[[
                       productObjectIndex]], Subscript[uniqueMorphismName, ToString[arrowCount]]] & ) /@ 
                   Select[Normal[reduceArrowsFinal[reduceArrowsInitial[morphismAssociation, morphismEquivalences], 
                      objectEquivalences]], First[Last[#1]] === object && Last[Last[#1]] === productObject & ]]] & ) /@ 
             Range[Length[reduceObjects[reduceObjects[objects, quiverObjectEquivalences], objectEquivalences]]]]]] & ) /@ 
      reduceObjects[reduceObjects[categoryObjects, quiverObjectEquivalences], objectEquivalences]; 
     ResourceFunction["AbstractCategory"][Association["CompositionSymbol" -> categoryCompositionSymbol, 
       "IdentitySymbol" -> categoryIdentitySymbol, "MorphismEquivalences" -> 
        DeleteDuplicates[Join[morphismEquivalences, newMorphismEquivalences]], "ObjectEquivalences" -> 
        objectEquivalences, "Quiver" -> ResourceFunction["AbstractQuiver"][
         Association["ArrowEquivalences" -> arrowEquivalences, "Arrows" -> Association[DeleteDuplicates[
             Join[Normal[arrows], (projectionMorphismNames[[#1]] -> DirectedEdge[productSymbol @@ objects, 
                  objects[[#1]]] & ) /@ Range[Length[reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
                  objectEquivalences]]], newArrows]]], "ObjectEquivalences" -> quiverObjectEquivalences, 
          "Objects" -> DeleteDuplicates[Join[categoryObjects, objects, {productSymbol @@ objects}]]]]]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"

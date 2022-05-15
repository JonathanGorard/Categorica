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
AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol_, "CoproductSymbol" -> coproductSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "Objects" -> objects_List, "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> 
      universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]]["Objects"] := 
  Join[objects, {coproductSymbol @@ objects}]
AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol_, "CoproductSymbol" -> coproductSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "Objects" -> objects_List, "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> 
      universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]]["ObjectCount"] := 
  Length[Join[objects, {coproductSymbol @@ objects}]]
AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol_, "CoproductSymbol" -> coproductSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "Objects" -> objects_List, "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> 
      universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]]["MorphismAssociation"] := 
  Association[Join[(injectionMorphismNames[[#1]] -> DirectedEdge[objects[[#1]], coproductSymbol @@ objects] & ) /@ 
     Range[Length[objects]], (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ objects, 
    {identitySymbol[coproductSymbol @@ objects] -> DirectedEdge[coproductSymbol @@ objects, coproductSymbol @@ objects]}]]
AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol_, "CoproductSymbol" -> coproductSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "Objects" -> objects_List, "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> 
      universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]]["MorphismNames"] := 
  First /@ Normal[Association[Join[(injectionMorphismNames[[#1]] -> DirectedEdge[objects[[#1]], 
          coproductSymbol @@ objects] & ) /@ Range[Length[objects]], (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ 
       objects, {identitySymbol[coproductSymbol @@ objects] -> DirectedEdge[coproductSymbol @@ objects, 
         coproductSymbol @@ objects]}]]]
AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol_, "CoproductSymbol" -> coproductSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "Objects" -> objects_List, "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> 
      universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]]["MorphismEdges"] := 
  (DirectedEdge @@ Last[#1] & ) /@ 
   Normal[Association[Join[(injectionMorphismNames[[#1]] -> DirectedEdge[objects[[#1]], 
          coproductSymbol @@ objects] & ) /@ Range[Length[objects]], (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ 
       objects, {identitySymbol[coproductSymbol @@ objects] -> DirectedEdge[coproductSymbol @@ objects, 
         coproductSymbol @@ objects]}]]]
AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol_, "CoproductSymbol" -> coproductSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "Objects" -> objects_List, "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> 
      universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]]["MorphismCount"] := 
  Length[Normal[Association[Join[(injectionMorphismNames[[#1]] -> DirectedEdge[objects[[#1]], 
          coproductSymbol @@ objects] & ) /@ Range[Length[objects]], (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ 
       objects, {identitySymbol[coproductSymbol @@ objects] -> DirectedEdge[coproductSymbol @@ objects, 
         coproductSymbol @@ objects]}]]]]
AbstractCoproduct[Association["CompositionSymbol" -> compositionSymobl_, "CoproductSymbol" -> coproductSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "Objects" -> objects_List, "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> 
      universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]]["SimpleMorphismAssociation"] := 
  Association[(injectionMorphismNames[[#1]] -> DirectedEdge[objects[[#1]], coproductSymbol @@ objects] & ) /@ 
    Range[Length[objects]]]
AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol_, "CoproductSymbol" -> coproductSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "Objects" -> objects_List, "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> 
      universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]]["SimpleMorphismNames"] := 
  First /@ Normal[Association[(injectionMorphismNames[[#1]] -> DirectedEdge[objects[[#1]], 
         coproductSymbol @@ objects] & ) /@ Range[Length[objects]]]]
AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol_, "CoproductSymbol" -> coproductSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "Objects" -> objects_List, "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> 
      universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]]["SimpleMorphismEdges"] := 
  (DirectedEdge @@ Last[#1] & ) /@ 
   Normal[Association[(injectionMorphismNames[[#1]] -> DirectedEdge[objects[[#1]], coproductSymbol @@ objects] & ) /@ 
      Range[Length[objects]]]]
AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol_, "CoproductSymbol" -> coproductSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "Objects" -> objects_List, "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> 
      universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]]["SimpleMorphismCount"] := 
  Length[Normal[Association[(injectionMorphismNames[[#1]] -> DirectedEdge[objects[[#1]], 
         coproductSymbol @@ objects] & ) /@ Range[Length[objects]]]]]
AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol_, "CoproductSymbol" -> coproductSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "Objects" -> objects_List, "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> 
      universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]]["UniversalObjects"] := 
  Join[objects, {coproductSymbol @@ objects, Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]}]
AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol_, "CoproductSymbol" -> coproductSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "Objects" -> objects_List, "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> 
      universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]]["UniversalObjectCount"] := 
  Length[Join[objects, {coproductSymbol @@ objects, Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]}]]
AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol_, "CoproductSymbol" -> coproductSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "Objects" -> objects_List, "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> 
      universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]]["UniversalMorphismAssociation"] := 
  Association[Join[(injectionMorphismNames[[#1]] -> DirectedEdge[objects[[#1]], coproductSymbol @@ objects] & ) /@ 
     Range[Length[objects]], (Subscript["\[ForAll]", ToString[universalMorphismNames[[#1]], StandardForm]] -> 
       DirectedEdge[objects[[#1]], Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]] & ) /@ 
     Range[Length[objects]], (compositionSymbol[uniqueMorphismName, injectionMorphismNames[[#1]]] -> 
       DirectedEdge[objects[[#1]], Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]] & ) /@ 
     Range[Length[objects]], (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ objects, 
    {identitySymbol[coproductSymbol @@ objects] -> DirectedEdge[coproductSymbol @@ objects, coproductSymbol @@ objects], 
     identitySymbol[universalObjectName] -> DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], 
       Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]], 
     Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> DirectedEdge[coproductSymbol @@ objects, 
       Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]]}]]
AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol_, "CoproductSymbol" -> coproductSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "Objects" -> objects_List, "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> 
      universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]]["UniversalMorphismNames"] := 
  First /@ Normal[Association[Join[(injectionMorphismNames[[#1]] -> DirectedEdge[objects[[#1]], 
          coproductSymbol @@ objects] & ) /@ Range[Length[objects]], 
      (Subscript["\[ForAll]", ToString[universalMorphismNames[[#1]], StandardForm]] -> DirectedEdge[objects[[#1]], 
          Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]] & ) /@ Range[Length[objects]], 
      (compositionSymbol[uniqueMorphismName, injectionMorphismNames[[#1]]] -> DirectedEdge[objects[[#1]], 
          Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]] & ) /@ Range[Length[objects]], 
      (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ objects, {identitySymbol[coproductSymbol @@ objects] -> 
        DirectedEdge[coproductSymbol @@ objects, coproductSymbol @@ objects], identitySymbol[universalObjectName] -> 
        DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], 
         Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]], 
       Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> DirectedEdge[coproductSymbol @@ objects, 
         Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]]}]]]
AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol_, "CoproductSymbol" -> coproductSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "Objects" -> objects_List, "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> 
      universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]]["UniversalMorphismEdges"] := 
  (DirectedEdge @@ Last[#1] & ) /@ 
   Normal[Association[Join[(injectionMorphismNames[[#1]] -> DirectedEdge[objects[[#1]], 
          coproductSymbol @@ objects] & ) /@ Range[Length[objects]], 
      (Subscript["\[ForAll]", ToString[universalMorphismNames[[#1]], StandardForm]] -> DirectedEdge[objects[[#1]], 
          Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]] & ) /@ Range[Length[objects]], 
      (compositionSymbol[uniqueMorphismName, injectionMorphismNames[[#1]]] -> DirectedEdge[objects[[#1]], 
          Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]] & ) /@ Range[Length[objects]], 
      (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ objects, {identitySymbol[coproductSymbol @@ objects] -> 
        DirectedEdge[coproductSymbol @@ objects, coproductSymbol @@ objects], identitySymbol[universalObjectName] -> 
        DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], 
         Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]], 
       Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> DirectedEdge[coproductSymbol @@ objects, 
         Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]]}]]]
AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol_, "CoproductSymbol" -> coproductSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "Objects" -> objects_List, "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> 
      universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]]["UniversalMorphismCount"] := 
  Length[Normal[Association[Join[(injectionMorphismNames[[#1]] -> DirectedEdge[objects[[#1]], 
          coproductSymbol @@ objects] & ) /@ Range[Length[objects]], 
      (Subscript["\[ForAll]", ToString[universalMorphismNames[[#1]], StandardForm]] -> DirectedEdge[objects[[#1]], 
          Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]] & ) /@ Range[Length[objects]], 
      (compositionSymbol[uniqueMorphismName, injectionMorphismNames[[#1]]] -> DirectedEdge[objects[[#1]], 
          Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]] & ) /@ Range[Length[objects]], 
      (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ objects, {identitySymbol[coproductSymbol @@ objects] -> 
        DirectedEdge[coproductSymbol @@ objects, coproductSymbol @@ objects], identitySymbol[universalObjectName] -> 
        DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], 
         Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]], 
       Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> DirectedEdge[coproductSymbol @@ objects, 
         Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]]}]]]]
AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol_, "CoproductSymbol" -> coproductSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "Objects" -> objects_List, "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> 
      universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalReducedMorphismAssociation"] := 
  Association[Join[(injectionMorphismNames[[#1]] -> DirectedEdge[objects[[#1]], coproductSymbol @@ objects] & ) /@ 
     Range[Length[objects]], (compositionSymbol[uniqueMorphismName, injectionMorphismNames[[#1]]] -> 
       DirectedEdge[objects[[#1]], Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]] & ) /@ 
     Range[Length[objects]], (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ objects, 
    {identitySymbol[coproductSymbol @@ objects] -> DirectedEdge[coproductSymbol @@ objects, coproductSymbol @@ objects], 
     identitySymbol[universalObjectName] -> DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], 
       Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]], 
     Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> DirectedEdge[coproductSymbol @@ objects, 
       Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]]}]]
AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol_, "CoproductSymbol" -> coproductSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "Objects" -> objects_List, "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> 
      universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]]["UniversalReducedMorphismNames"] := 
  First /@ Normal[Association[Join[(injectionMorphismNames[[#1]] -> DirectedEdge[objects[[#1]], 
          coproductSymbol @@ objects] & ) /@ Range[Length[objects]], 
      (compositionSymbol[uniqueMorphismName, injectionMorphismNames[[#1]]] -> DirectedEdge[objects[[#1]], 
          Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]] & ) /@ Range[Length[objects]], 
      (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ objects, {identitySymbol[coproductSymbol @@ objects] -> 
        DirectedEdge[coproductSymbol @@ objects, coproductSymbol @@ objects], identitySymbol[universalObjectName] -> 
        DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], 
         Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]], 
       Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> DirectedEdge[coproductSymbol @@ objects, 
         Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]]}]]]
AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol_, "CoproductSymbol" -> coproductSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "Objects" -> objects_List, "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> 
      universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]]["UniversalReducedMorphismEdges"] := 
  (DirectedEdge @@ Last[#1] & ) /@ 
   Normal[Association[Join[(injectionMorphismNames[[#1]] -> DirectedEdge[objects[[#1]], 
          coproductSymbol @@ objects] & ) /@ Range[Length[objects]], 
      (compositionSymbol[uniqueMorphismName, injectionMorphismNames[[#1]]] -> DirectedEdge[objects[[#1]], 
          Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]] & ) /@ Range[Length[objects]], 
      (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ objects, {identitySymbol[coproductSymbol @@ objects] -> 
        DirectedEdge[coproductSymbol @@ objects, coproductSymbol @@ objects], identitySymbol[universalObjectName] -> 
        DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], 
         Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]], 
       Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> DirectedEdge[coproductSymbol @@ objects, 
         Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]]}]]]
AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol_, "CoproductSymbol" -> coproductSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "Objects" -> objects_List, "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> 
      universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]]["UniversalReducedMorphismCount"] := 
  Length[Normal[Association[Join[(injectionMorphismNames[[#1]] -> DirectedEdge[objects[[#1]], 
          coproductSymbol @@ objects] & ) /@ Range[Length[objects]], 
      (compositionSymbol[uniqueMorphismName, injectionMorphismNames[[#1]]] -> DirectedEdge[objects[[#1]], 
          Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]] & ) /@ Range[Length[objects]], 
      (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ objects, {identitySymbol[coproductSymbol @@ objects] -> 
        DirectedEdge[coproductSymbol @@ objects, coproductSymbol @@ objects], identitySymbol[universalObjectName] -> 
        DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], 
         Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]], 
       Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> DirectedEdge[coproductSymbol @@ objects, 
         Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]]}]]]]
AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol_, "CoproductSymbol" -> coproductSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "Objects" -> objects_List, "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> 
      universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalSimpleMorphismAssociation"] := 
  Association[Join[(injectionMorphismNames[[#1]] -> DirectedEdge[objects[[#1]], coproductSymbol @@ objects] & ) /@ 
     Range[Length[objects]], (Subscript["\[ForAll]", ToString[universalMorphismNames[[#1]], StandardForm]] -> 
       DirectedEdge[objects[[#1]], Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]] & ) /@ 
     Range[Length[objects]], {Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> 
      DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], coproductSymbol @@ objects]}]]
AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol_, "CoproductSymbol" -> coproductSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "Objects" -> objects_List, "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> 
      universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]]["UniversalSimpleMorphismNames"] := 
  First /@ Normal[Association[Join[(injectionMorphismNames[[#1]] -> DirectedEdge[objects[[#1]], 
          coproductSymbol @@ objects] & ) /@ Range[Length[objects]], 
      (Subscript["\[ForAll]", ToString[universalMorphismNames[[#1]], StandardForm]] -> DirectedEdge[objects[[#1]], 
          Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]] & ) /@ Range[Length[objects]], 
      {Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> 
        DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], coproductSymbol @@ objects]}]]]
AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol_, "CoproductSymbol" -> coproductSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "Objects" -> objects_List, "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> 
      universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]]["UniversalSimpleMorphismEdges"] := 
  (DirectedEdge @@ Last[#1] & ) /@ 
   Normal[Association[Join[(injectionMorphismNames[[#1]] -> DirectedEdge[objects[[#1]], 
          coproductSymbol @@ objects] & ) /@ Range[Length[objects]], 
      (Subscript["\[ForAll]", ToString[universalMorphismNames[[#1]], StandardForm]] -> DirectedEdge[objects[[#1]], 
          Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]] & ) /@ Range[Length[objects]], 
      {Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> 
        DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], coproductSymbol @@ objects]}]]]
AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol_, "CoproductSymbol" -> coproductSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "Objects" -> objects_List, "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> 
      universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]]["UniversalSimpleMorphismCount"] := 
  Length[Normal[Association[Join[(injectionMorphismNames[[#1]] -> DirectedEdge[objects[[#1]], 
          coproductSymbol @@ objects] & ) /@ Range[Length[objects]], 
      (Subscript["\[ForAll]", ToString[universalMorphismNames[[#1]], StandardForm]] -> DirectedEdge[objects[[#1]], 
          Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]] & ) /@ Range[Length[objects]], 
      {Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> 
        DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], coproductSymbol @@ objects]}]]]]
AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol_, "CoproductSymbol" -> coproductSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "Objects" -> objects_List, "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> 
      universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalReducedSimpleMorphismAssociation"] := 
  Association[Join[(injectionMorphismNames[[#1]] -> DirectedEdge[objects[[#1]], coproductSymbol @@ objects] & ) /@ 
     Range[Length[objects]], (compositionSymbol[uniqueMorphismName, injectionMorphismNames[[#1]]] -> 
       DirectedEdge[objects[[#1]], Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]] & ) /@ 
     Range[Length[objects]], {Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> 
      DirectedEdge[coproductSymbol @@ objects, Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]]}]]
AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol_, "CoproductSymbol" -> coproductSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "Objects" -> objects_List, "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> 
      universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalReducedSimpleMorphismNames"] := 
  First /@ Normal[Association[Join[(injectionMorphismNames[[#1]] -> DirectedEdge[objects[[#1]], 
          coproductSymbol @@ objects] & ) /@ Range[Length[objects]], 
      (compositionSymbol[uniqueMorphismName, injectionMorphismNames[[#1]]] -> DirectedEdge[objects[[#1]], 
          Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]] & ) /@ Range[Length[objects]], 
      {Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> DirectedEdge[coproductSymbol @@ objects, 
         Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]]}]]]
AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol_, "CoproductSymbol" -> coproductSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "Objects" -> objects_List, "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> 
      universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalReducedSimpleMorphismEdges"] := (DirectedEdge @@ Last[#1] & ) /@ 
   Normal[Association[Join[(injectionMorphismNames[[#1]] -> DirectedEdge[objects[[#1]], 
          coproductSymbol @@ objects] & ) /@ Range[Length[objects]], 
      (compositionSymbol[uniqueMorphismName, injectionMorphismNames[[#1]]] -> DirectedEdge[objects[[#1]], 
          Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]] & ) /@ Range[Length[objects]], 
      {Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> DirectedEdge[coproductSymbol @@ objects, 
         Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]]}]]]
AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol_, "CoproductSymbol" -> coproductSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "Objects" -> objects_List, "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> 
      universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalReducedSimpleMorphismCount"] := 
  Length[Normal[Association[Join[(injectionMorphismNames[[#1]] -> DirectedEdge[objects[[#1]], 
          coproductSymbol @@ objects] & ) /@ Range[Length[objects]], 
      (compositionSymbol[uniqueMorphismName, injectionMorphismNames[[#1]]] -> DirectedEdge[objects[[#1]], 
          Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]] & ) /@ Range[Length[objects]], 
      {Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> DirectedEdge[coproductSymbol @@ objects, 
         Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]]}]]]]
AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol_, "CoproductSymbol" -> coproductSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "Objects" -> objects_List, "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> 
      universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]]["CoproductSymbol"] := coproductSymbol
AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol_, "CoproductSymbol" -> coproductSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "Objects" -> objects_List, "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> 
      universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]]["CompositionSymbol"] := 
  compositionSymbol
AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol_, "CoproductSymbol" -> coproductSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "Objects" -> objects_List, "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> 
      universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]]["IdentitySymbol"] := identitySymbol
AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol_, "CoproductSymbol" -> coproductSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "Objects" -> objects_List, "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> 
      universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]]["CoproductCategory"] := 
  ResourceFunction["AbstractCategory"][Association["CompositionSymbol" -> compositionSymbol, 
    "IdentitySymbol" -> identitySymbol, "MorphismEquivalences" -> {}, "ObjectEquivalences" -> {}, 
    "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> {}, 
       "Arrows" -> Association[(injectionMorphismNames[[#1]] -> DirectedEdge[objects[[#1]], 
             coproductSymbol @@ objects] & ) /@ Range[Length[objects]]], "ObjectEquivalences" -> {}, 
       "Objects" -> Join[objects, {coproductSymbol @@ objects}]]]]]
AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol_, "CoproductSymbol" -> coproductSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "Objects" -> objects_List, "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> 
      universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]]["UniversalCoproductCategory"] := 
  ResourceFunction["AbstractCategory"][Association["CompositionSymbol" -> compositionSymbol, 
    "IdentitySymbol" -> identitySymbol, "MorphismEquivalences" -> 
     (universalMorphismNames[[#1]] == compositionSymbol[uniqueMorphismName, injectionMorphismNames[[#1]]] & ) /@ 
      Range[Length[objects]], "ObjectEquivalences" -> {}, "Quiver" -> ResourceFunction["AbstractQuiver"][
      Association["ArrowEquivalences" -> {}, "Arrows" -> Association[
         Join[(injectionMorphismNames[[#1]] -> DirectedEdge[objects[[#1]], coproductSymbol @@ objects] & ) /@ 
           Range[Length[objects]], (universalMorphismNames[[#1]] -> DirectedEdge[objects[[#1]], 
              universalObjectName] & ) /@ Range[Length[objects]], {uniqueMorphismName -> 
            DirectedEdge[coproductSymbol @@ objects, universalObjectName]}]], "ObjectEquivalences" -> {}, 
       "Objects" -> Join[objects, {coproductSymbol @@ objects, universalObjectName}]]]]]
AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol_, "CoproductSymbol" -> coproductSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "Objects" -> objects_List, "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> 
      universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]]["UniversalCoproductEquations"] := 
  (ToExpression[StringJoin["HoldForm[ForAll[", ToString[universalMorphismNames[[#1]], StandardForm], ",Exists[", 
      ToString[uniqueMorphismName, StandardForm], ",", ToString[universalMorphismNames[[#1]] == 
        compositionSymbol[uniqueMorphismName, injectionMorphismNames[[#1]]], StandardForm], "]]]"]] & ) /@ 
   Range[Length[objects]]
AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol_, "CoproductSymbol" -> coproductSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "Objects" -> objects_List, "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> 
      universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]]["FullLabeledGraph"] := 
  EdgeTaggedGraph[Join[objects, {coproductSymbol @@ objects}], 
   (Labeled[DirectedEdge @@ Last[#1], Placed[First[#1], 0.5]] & ) /@ 
    Normal[Association[Join[(injectionMorphismNames[[#1]] -> DirectedEdge[objects[[#1]], 
           coproductSymbol @@ objects] & ) /@ Range[Length[objects]], (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ 
        objects, {identitySymbol[coproductSymbol @@ objects] -> DirectedEdge[coproductSymbol @@ objects, 
          coproductSymbol @@ objects]}]]], VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], 
   VertexLabels -> Placed["Name", Center], VertexLabelStyle -> Directive[Bold, 20], 
   EdgeLabelStyle -> Directive[Bold, 20], EdgeStyle -> Directive[Black, Thick], 
   GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]
AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol_, "CoproductSymbol" -> coproductSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "Objects" -> objects_List, "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> 
      universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]]["FullUnlabeledGraph"] := 
  EdgeTaggedGraph[Join[objects, {coproductSymbol @@ objects}], (DirectedEdge @@ Last[#1] & ) /@ 
    Normal[Association[Join[(injectionMorphismNames[[#1]] -> DirectedEdge[objects[[#1]], 
           coproductSymbol @@ objects] & ) /@ Range[Length[objects]], (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ 
        objects, {identitySymbol[coproductSymbol @@ objects] -> DirectedEdge[coproductSymbol @@ objects, 
          coproductSymbol @@ objects]}]]], VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], 
   VertexLabels -> Placed["Name", Center], VertexLabelStyle -> Directive[Bold, 20], 
   EdgeLabelStyle -> Directive[Bold, 20], EdgeStyle -> Directive[Black, Thick], 
   GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]
AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol_, "CoproductSymbol" -> coproductSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "Objects" -> objects_List, "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> 
      universalMorphsmNames_List, "UniversalObjectName" -> universalObjectName_]]["SimpleLabeledGraph"] := 
  EdgeTaggedGraph[Join[objects, {coproductSymbol @@ objects}], 
   (Labeled[DirectedEdge @@ Last[#1], Placed[First[#1], 0.5]] & ) /@ 
    Normal[Association[(injectionMorphismNames[[#1]] -> DirectedEdge[objects[[#1]], coproductSymbol @@ objects] & ) /@ 
       Range[Length[objects]]]], VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], 
   VertexLabels -> Placed["Name", Center], VertexLabelStyle -> Directive[Bold, 20], 
   EdgeLabelStyle -> Directive[Bold, 20], EdgeStyle -> Directive[Black, Thick], 
   GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]
AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol_, "CoproductSymbol" -> coproductSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "Objects" -> objects_List, "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> 
      universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]]["SimpleUnlabeledGraph"] := 
  EdgeTaggedGraph[Join[objects, {coproductSymbol @@ objects}], (DirectedEdge @@ Last[#1] & ) /@ 
    Normal[Association[(injectionMorphismNames[[#1]] -> DirectedEdge[objects[[#1]], coproductSymbol @@ objects] & ) /@ 
       Range[Length[objects]]]], VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], 
   VertexLabels -> Placed["Name", Center], VertexLabelStyle -> Directive[Bold, 20], 
   EdgeLabelStyle -> Directive[Bold, 20], EdgeStyle -> Directive[Black, Thick], 
   GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]
AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol_, "CoproductSymbol" -> coproductSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "Objects" -> objects_List, "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> 
      universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]]["UniversalFullLabeledGraph"] := 
  EdgeTaggedGraph[Join[objects, {coproductSymbol @@ objects, universalObjectName}], 
   (Labeled[DirectedEdge @@ Last[#1], Placed[First[#1], 0.5]] & ) /@ 
    Normal[Association[Join[(injectionMorphismNames[[#1]] -> DirectedEdge[objects[[#1]], 
           coproductSymbol @@ objects] & ) /@ Range[Length[objects]], 
       (Subscript["\[ForAll]", ToString[universalMorphismNames[[#1]], StandardForm]] -> DirectedEdge[objects[[#1]], 
           universalObjectName] & ) /@ Range[Length[objects]], 
       (compositionSymbol[uniqueMorphismName, injectionMorphismNames[[#1]]] -> DirectedEdge[objects[[#1]], 
           universalObjectName] & ) /@ Range[Length[objects]], (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ 
        objects, {identitySymbol[coproductSymbol @@ objects] -> DirectedEdge[coproductSymbol @@ objects, 
          coproductSymbol @@ objects], identitySymbol[universalObjectName] -> DirectedEdge[universalObjectName, 
          universalObjectName], Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> 
         DirectedEdge[coproductSymbol @@ objects, universalObjectName]}]]], VertexSize -> 0.3, 
   VertexStyle -> Directive[Transparent, EdgeForm[None]], 
   VertexLabels -> {Placed["Name", Center], universalObjectName -> 
      Placed[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], Center]}, 
   VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
   EdgeStyle -> {Directive[Black, Thick], DirectedEdge[coproductSymbol @@ objects, universalObjectName] -> Dashed}, 
   GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]
AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol_, "CoproductSymbol" -> coproductSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "Objects" -> objects_List, "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> 
      universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]]["UniversalFullUnlabeledGraph"] := 
  EdgeTaggedGraph[Join[objects, {coproductSymbol @@ objects, universalObjectName}], 
   (DirectedEdge @@ Last[#1] & ) /@ 
    Normal[Association[Join[(injectionMorphismNames[[#1]] -> DirectedEdge[objects[[#1]], 
           coproductSymbol @@ objects] & ) /@ Range[Length[objects]], 
       (Subscript["\[ForAll]", ToString[universalMorphismNames[[#1]], StandardForm]] -> DirectedEdge[objects[[#1]], 
           universalObjectName] & ) /@ Range[Length[objects]], 
       (compositionSymbol[uniqueMorphismName, injectionMorphismNames[[#1]]] -> DirectedEdge[objects[[#1]], 
           universalObjectName] & ) /@ Range[Length[objects]], (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ 
        objects, {identitySymbol[coproductSymbol @@ objects] -> DirectedEdge[coproductSymbol @@ objects, 
          coproductSymbol @@ objects], identitySymbol[universalObjectName] -> DirectedEdge[universalObjectName, 
          universalObjectName], Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> 
         DirectedEdge[coproductSymbol @@ objects, universalObjectName]}]]], VertexSize -> 0.3, 
   VertexStyle -> Directive[Transparent, EdgeForm[None]], 
   VertexLabels -> {Placed["Name", Center], universalObjectName -> 
      Placed[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], Center]}, 
   VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
   EdgeStyle -> {Directive[Black, Thick], DirectedEdge[coproductSymbol @@ objects, universalObjectName] -> Dashed}, 
   GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]
AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol_, "CoproductSymbol" -> coproductSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "Objects" -> objects_List, "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> 
      universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]]["UniversalReducedLabeledGraph"] := 
  EdgeTaggedGraph[Join[objects, {coproductSymbol @@ objects, universalObjectName}], 
   (Labeled[DirectedEdge @@ Last[#1], Placed[First[#1], 0.5]] & ) /@ 
    Normal[Association[Join[(injectionMorphismNames[[#1]] -> DirectedEdge[objects[[#1]], 
           coproductSymbol @@ objects] & ) /@ Range[Length[objects]], 
       (compositionSymbol[uniqueMorphismName, injectionMorphismNames[[#1]]] -> DirectedEdge[objects[[#1]], 
           universalObjectName] & ) /@ Range[Length[objects]], (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ 
        objects, {identitySymbol[coproductSymbol @@ objects] -> DirectedEdge[coproductSymbol @@ objects, 
          coproductSymbol @@ objects], identitySymbol[universalObjectName] -> DirectedEdge[universalObjectName, 
          universalObjectName], Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> 
         DirectedEdge[coproductSymbol @@ objects, universalObjectName]}]]], VertexSize -> 0.3, 
   VertexStyle -> Directive[Transparent, EdgeForm[None]], 
   VertexLabels -> {Placed["Name", Center], universalObjectName -> 
      Placed[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], Center]}, 
   VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
   EdgeStyle -> {Directive[Black, Thick], DirectedEdge[coproductSymbol @@ objects, universalObjectName] -> Dashed}, 
   GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]
AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol_, "CoproductSymbol" -> coproductSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "Objects" -> objects_List, "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> 
      universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]]["UniversalReducedUnlabeledGraph"] := 
  EdgeTaggedGraph[Join[objects, {coproductSymbol @@ objects, universalObjectName}], 
   (DirectedEdge @@ Last[#1] & ) /@ 
    Normal[Association[Join[(injectionMorphismNames[[#1]] -> DirectedEdge[objects[[#1]], 
           coproductSymbol @@ objects] & ) /@ Range[Length[objects]], 
       (compositionSymbol[uniqueMorphismName, injectionMorphismNames[[#1]]] -> DirectedEdge[objects[[#1]], 
           universalObjectName] & ) /@ Range[Length[objects]], (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ 
        objects, {identitySymbol[coproductSymbol @@ objects] -> DirectedEdge[coproductSymbol @@ objects, 
          coproductSymbol @@ objects], identitySymbol[universalObjectName] -> DirectedEdge[universalObjectName, 
          universalObjectName], Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> 
         DirectedEdge[coproductSymbol @@ objects, universalObjectName]}]]], VertexSize -> 0.3, 
   VertexStyle -> Directive[Transparent, EdgeForm[None]], 
   VertexLabels -> {Placed["Name", Center], universalObjectName -> 
      Placed[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], Center]}, 
   VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
   EdgeStyle -> {Directive[Black, Thick], DirectedEdge[coproductSymbol @@ objects, universalObjectName] -> Dashed}, 
   GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]
AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol_, "CoproductSymbol" -> coproductSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "Objects" -> objects_List, "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> 
      universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]]["UniversalSimpleLabeledGraph"] := 
  EdgeTaggedGraph[Join[objects, {coproductSymbol @@ objects, universalObjectName}], 
   (Labeled[DirectedEdge @@ Last[#1], Placed[First[#1], 0.5]] & ) /@ 
    Normal[Association[Join[(injectionMorphismNames[[#1]] -> DirectedEdge[objects[[#1]], 
           coproductSymbol @@ objects] & ) /@ Range[Length[objects]], 
       (Subscript["\[ForAll]", ToString[universalMorphismNames[[#1]], StandardForm]] -> DirectedEdge[objects[[#1]], 
           universalObjectName] & ) /@ Range[Length[objects]], 
       {Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> DirectedEdge[coproductSymbol @@ objects, 
          universalObjectName]}]]], VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], 
   VertexLabels -> {Placed["Name", Center], universalObjectName -> 
      Placed[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], Center]}, 
   VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
   EdgeStyle -> {Directive[Black, Thick], DirectedEdge[coproductSymbol @@ objects, universalObjectName] -> Dashed}, 
   GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]
AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol_, "CoproductSymbol" -> coproductSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "Objects" -> objects_List, "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> 
      universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]]["UniversalSimpleUnlabeledGraph"] := 
  EdgeTaggedGraph[Join[objects, {coproductSymbol @@ objects, universalObjectName}], 
   (DirectedEdge @@ Last[#1] & ) /@ 
    Normal[Association[Join[(injectionMorphismNames[[#1]] -> DirectedEdge[objects[[#1]], 
           coproductSymbol @@ objects] & ) /@ Range[Length[objects]], 
       (Subscript["\[ForAll]", ToString[universalMorphismNames[[#1]], StandardForm]] -> DirectedEdge[objects[[#1]], 
           universalObjectName] & ) /@ Range[Length[objects]], 
       {Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> DirectedEdge[coproductSymbol @@ objects, 
          universalObjectName]}]]], VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], 
   VertexLabels -> {Placed["Name", Center], universalObjectName -> 
      Placed[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], Center]}, 
   VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
   EdgeStyle -> {Directive[Black, Thick], DirectedEdge[coproductSymbol @@ objects, universalObjectName] -> Dashed}, 
   GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]
AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol_, "CoproductSymbol" -> coproductSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "Objects" -> objects_List, "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> 
      universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalReducedSimpleLabeledGraph"] := EdgeTaggedGraph[
   Join[objects, {coproductSymbol @@ objects, universalObjectName}], 
   (Labeled[DirectedEdge @@ Last[#1], Placed[First[#1], 0.5]] & ) /@ 
    Normal[Association[Join[(injectionMorphismNames[[#1]] -> DirectedEdge[objects[[#1]], 
           coproductSymbol @@ objects] & ) /@ Range[Length[objects]], 
       (compositionSymbol[uniqueMorphismName, injectionMorphismNames[[#1]]] -> DirectedEdge[objects[[#1]], 
           universalObjectName] & ) /@ Range[Length[objects]], 
       {Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> DirectedEdge[coproductSymbol @@ objects, 
          universalObjectName]}]]], VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], 
   VertexLabels -> {Placed["Name", Center], universalObjectName -> 
      Placed[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], Center]}, 
   VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
   EdgeStyle -> {Directive[Black, Thick], DirectedEdge[coproductSymbol @@ objects, universalObjectName] -> Dashed}, 
   GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]
AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol_, "CoproductSymbol" -> coproductSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "Objects" -> objects_List, "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> 
      universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
   "UniversalReducedSimpleUnlabeledGraph"] := EdgeTaggedGraph[(DirectedEdge @@ Last[#1] & ) /@ 
    Normal[Association[Join[(injectionMorphismNames[[#1]] -> DirectedEdge[objects[[#1]], 
           coproductSymbol @@ objects] & ) /@ Range[Length[objects]], 
       (compositionSymbol[uniqueMorphismName, injectionMorphismNames[[#1]]] -> DirectedEdge[objects[[#1]], 
           universalObjectName] & ) /@ Range[Length[objects]], 
       {Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> DirectedEdge[coproductSymbol @@ objects, 
          universalObjectName]}]]], VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], 
   VertexLabels -> {Placed["Name", Center], universalObjectName -> 
      Placed[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], Center]}, 
   VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
   EdgeStyle -> {Directive[Black, Thick], DirectedEdge[coproductSymbol @@ objects, universalObjectName] -> Dashed}, 
   GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]
AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol_, "CoproductSymbol" -> coproductSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "Objects" -> objects_List, "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> 
      universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]]["AssociationForm"] := 
  Association["Objects" -> objects, "CoproductSymbol" -> coproductSymbol, 
   "InjectionMorphismNames" -> injectionMorphismNames, "CompositionSymbol" -> compositionSymbol, 
   "IdentitySymbol" -> identitySymbol, "UniversalObjectName" -> universalObjectName, 
   "UniversalMorphismNames" -> universalMorphismNames, "UniqueMorphismName" -> uniqueMorphismName]
AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol_, "CoproductSymbol" -> coproductSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "Objects" -> objects_List, "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> 
      universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]]["Properties"] := 
  {"Objects", "ObjectCount", "MorphismAssociation", "MorphismNames", "MorphismEdges", "MorphismCount", 
   "SimpleMorphismAssociation", "SimpleMorphismNames", "SimpleMorphismEdges", "SimpleMorphismCount", "UniversalObjects", 
   "UniversalObjectCount", "UniversalMorphismAssociation", "UniversalMorphismNames", "UniversalMorphismEdges", 
   "UniversalMorphismCount", "UniversalReducedMorphismAssociation", "UniversalReducedMorphismNames", 
   "UniversalReducedMorphismEdges", "UniversalReducedMorphismCount", "UniversalSimpleMorphismAssociation", 
   "UniversalSimpleMorphismNames", "UniversalSimpleMorphismEdges", "UniversalSimpleMorphismCount", 
   "UniversalReducedSimpleMorphismAssociation", "UniversalReducedSimpleMorphismNames", 
   "UniversalReducedSimpleMorphismEdges", "UniversalReducedSimpleMorphismCount", "CoproductSymbol", "CompositionSymbol", 
   "IdentitySymbol", "CoproductCategory", "UniversalCoproductCategory", "UniversalCoproductEquations", 
   "FullLabeledGraph", "FullUnlabeledGraph", "SimpleLabeledGraph", "SimpleUnlabeledGraph", "UniversalFullLabeledGraph", 
   "UniversalFullUnlabeledGraph", "UniversalReducedLabeledGraph", "UniversalReducedUnlabeledGraph", 
   "UniversalSimpleLabeledGraph", "UniversalSimpleUnlabeledGraph", "UniversalReducedSimpleLabeledGraph", 
   "UniversalReducedSimpleUnlabeledGraph", "AssociationForm", "Properties"}
AbstractCoproduct /: MakeBoxes[abstractCoproduct:AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol_, 
       "CoproductSymbol" -> coproductSymbol_, "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> 
        injectionMorphismNames_List, "Objects" -> objects_List, "UniqueMorphismName" -> uniqueMorphismName_, 
       "UniversalMorphismNames" -> universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]], 
    format_] := Module[{icon, objectCount}, 
    icon = GraphPlot[EdgeTaggedGraph[Join[objects, {coproductSymbol @@ objects}], (DirectedEdge @@ Last[#1] & ) /@ 
         Normal[Association[Join[(injectionMorphismNames[[#1]] -> DirectedEdge[objects[[#1]], coproductSymbol @@ 
                 objects] & ) /@ Range[Length[objects]], (identitySymbol[#1] -> DirectedEdge[#1, #1] & ) /@ objects, 
            {identitySymbol[coproductSymbol @@ objects] -> DirectedEdge[coproductSymbol @@ objects, coproductSymbol @@ 
                objects]}]]], VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], 
        EdgeShapeFunction -> GraphElementData["ShortFilledArrow", "ArrowSize" -> 0.05], EdgeStyle -> Black, 
        GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]]; objectCount = Length[objects]; 
     BoxForm`ArrangeSummaryBox["AbstractCoproduct", abstractCoproduct, icon, 
      {{BoxForm`SummaryItem[{"Objects: ", objectCount}]}, {BoxForm`SummaryItem[{"Symbol: ", coproductSymbol}]}}, {{}}, 
      format, "Interpretable" -> Automatic]]
AbstractCoproduct[objects_List] := AbstractCoproduct[Association["CompositionSymbol" -> CircleDot, 
    "CoproductSymbol" -> Coproduct, "IdentitySymbol" -> OverTilde, "InjectionMorphismNames" -> 
     (Subscript["\[FormalI]", ToString[#1]] & ) /@ Range[Length[objects]], "Objects" -> objects, "UniqueMorphismName" -> "\[FormalF]", 
    "UniversalMorphismNames" -> (Subscript["\[FormalF]", ToString[#1]] & ) /@ Range[Length[objects]], 
    "UniversalObjectName" -> "\[FormalCapitalY]"]]
AbstractCoproduct[objects_List, coproductSymbol_] := 
  AbstractCoproduct[Association["CompositionSymbol" -> CircleDot, "CoproductSymbol" -> coproductSymbol, 
     "IdentitySymbol" -> OverTilde, "InjectionMorphismNames" -> (Subscript["\[FormalI]", ToString[#1]] & ) /@ 
       Range[Length[objects]], "Objects" -> objects, "UniqueMorphismName" -> "\[FormalF]", 
     "UniversalMorphismNames" -> (Subscript["\[FormalF]", ToString[#1]] & ) /@ Range[Length[objects]], 
     "UniversalObjectName" -> "\[FormalCapitalY]"]] /;  !ListQ[coproductSymbol]
AbstractCoproduct[objects_List, coproductSymbol_, injectionMorphismNames_List] := 
  AbstractCoproduct[Association["CompositionSymbol" -> CircleDot, "CoproductSymbol" -> coproductSymbol, 
     "IdentitySymbol" -> OverTilde, "InjectionMorphismNames" -> injectionMorphismNames, "Objects" -> objects, 
     "UniqueMorphismName" -> "\[FormalF]", "UniversalMorphismNames" -> (Subscript["\[FormalF]", ToString[#1]] & ) /@ 
       Range[Length[objects]], "UniversalObjectName" -> "\[FormalCapitalY]"]] /;  !ListQ[coproductSymbol]
AbstractCoproduct[objects_List, coproductSymbol_, injectionMorphismNames_List, compositionSymbol_] := 
  AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol, "CoproductSymbol" -> coproductSymbol, 
     "IdentitySymbol" -> OverTilde, "InjectionMorphismNames" -> injectionMorphismNames, "Objects" -> objects, 
     "UniqueMorphismName" -> "\[FormalF]", "UniversalMorphismNames" -> (Subscript["\[FormalF]", ToString[#1]] & ) /@ 
       Range[Length[objects]], "UniversalObjectName" -> "\[FormalCapitalY]"]] /;  !ListQ[coproductSymbol] &&  !ListQ[compositionSymbol]
AbstractCoproduct[objects_List, coproductSymbol_, injectionMorphismNames_List, compositionSymbol_, identitySymbol_] := 
  AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol, "CoproductSymbol" -> coproductSymbol, 
     "IdentitySymbol" -> identitySymbol, "InjectionMorphismNames" -> injectionMorphismNames, "Objects" -> objects, 
     "UniqueMorphismName" -> "\[FormalF]", "UniversalMorphismNames" -> (Subscript["\[FormalF]", ToString[#1]] & ) /@ 
       Range[Length[objects]], "UniversalObjectName" -> "\[FormalCapitalY]"]] /;  !ListQ[coproductSymbol] && 
     !ListQ[compositionSymbol] &&  !ListQ[identitySymbol]
AbstractCoproduct[objects_List, coproductSymbol_, injectionMorphismNames_List, compositionSymbol_, identitySymbol_, 
   universalObjectName_] := AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol, 
     "CoproductSymbol" -> coproductSymbol, "IdentitySymbol" -> identitySymbol, 
     "InjectionMorphismNames" -> injectionMorphismNames, "Objects" -> objects, "UniqueMorphismName" -> "\[FormalF]", 
     "UniversalMorphismNames" -> (Subscript["\[FormalF]", ToString[#1]] & ) /@ Range[Length[objects]], 
     "UniversalObjectName" -> universalObjectName]] /;  !ListQ[coproductSymbol] &&  !ListQ[compositionSymbol] && 
     !ListQ[identitySymbol]
AbstractCoproduct[objects_List, coproductSymbol_, injectionMorphismNames_List, compositionSymbol_, identitySymbol_, 
   universalObjectName_, universalMorphismNames_List] := 
  AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol, "CoproductSymbol" -> coproductSymbol, 
     "IdentitySymbol" -> identitySymbol, "InjectionMorphismNames" -> injectionMorphismNames, "Objects" -> objects, 
     "UniqueMorphismName" -> "\[FormalF]", "UniversalMorphismNames" -> universalMorphismNames, 
     "UniversalObjectName" -> universalObjectName]] /;  !ListQ[coproductSymbol] &&  !ListQ[compositionSymbol] && 
     !ListQ[identitySymbol]
AbstractCoproduct[objects_List, coproductSymbol_, injectionMorphismNames_List, compositionSymbol_, identitySymbol_, 
   universalObjectName_, universalMorphismNames_List, uniqueMorphismName_] := 
  AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol, "CoproductSymbol" -> coproductSymbol, 
     "IdentitySymbol" -> identitySymbol, "InjectionMorphismNames" -> injectionMorphismNames, "Objects" -> objects, 
     "UniqueMorphismName" -> uniqueMorphismName, "UniversalMorphismNames" -> universalMorphismNames, 
     "UniversalObjectName" -> universalObjectName]] /;  !ListQ[coproductSymbol] &&  !ListQ[compositionSymbol] && 
     !ListQ[identitySymbol]
AbstractCoproduct[objects_List, injectionMorphismNames_List] := 
  AbstractCoproduct[Association["CompositionSymbol" -> CircleDot, "CoproductSymbol" -> Coproduct, 
    "IdentitySymbol" -> OverTilde, "InjectionMorphismNames" -> injectionMorphismNames, "Objects" -> objects, 
    "UniqueMorphismName" -> "\[FormalF]", "UniversalMorphismNames" -> (Subscript["\[FormalF]", ToString[#1]] & ) /@ 
      Range[Length[objects]], "UniversalObjectName" -> "\[FormalCapitalY]"]]
AbstractCoproduct[objects_List, injectionMorphismNames_List, compositionSymbol_] := 
  AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol, "CoproductSymbol" -> Coproduct, 
    "IdentitySymbol" -> OverTilde, "InjectionMorphismNames" -> injectionMorphismNames, "Objects" -> objects, 
    "UniqueMorphismName" -> "\[FormalF]", "UniversalMorphismNames" -> (Subscript["\[FormalF]", ToString[#1]] & ) /@ 
      Range[Length[objects]], "UniversalObjectName" -> "\[FormalCapitalY]"]]
AbstractCoproduct[objects_List, injectionMorphismNames_List, compositionSymbol_, identitySymbol_] := 
  AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol, "CoproductSymbol" -> Coproduct, 
    "IdentitySymbol" -> identitySymbol, "InjectionMorphismNames" -> injectionMorphismNames, "Objects" -> objects, 
    "UniqueMorphismName" -> "\[FormalF]", "UniversalMorphismNames" -> (Subscript["\[FormalF]", ToString[#1]] & ) /@ 
      Range[Length[objects]], "UniversalObjectName" -> "\[FormalCapitalY]"]]
AbstractCoproduct[objects_List, coproductSymbol_, compositionSymbol_] := 
  AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol, "CoproductSymbol" -> coproductSymbol, 
     "IdentitySymbol" -> OverTilde, "InjectionMorphismNames" -> (Subscript["\[FormalI]", ToString[#1]] & ) /@ 
       Range[Length[objects]], "Objects" -> objects, "UniqueMorphismName" -> "\[FormalF]", 
     "UniversalMorphismNames" -> (Subscript["\[FormalF]", ToString[#1]] & ) /@ Range[Length[objects]], 
     "UniversalObjectName" -> "\[FormalCapitalY]"]] /;  !ListQ[coproductSymbol] &&  !ListQ[compositionSymbol]
AbstractCoproduct[objects_List, coproductSymbol_, compositionSymbol_, identitySymbol_] := 
  AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol, "CoproductSymbol" -> coproductSymbol, 
     "IdentitySymbol" -> identitySymbol, "InjectionMorphismNames" -> (Subscript["\[FormalI]", ToString[#1]] & ) /@ 
       Range[Length[objects]], "Objects" -> objects, "UniqueMorphismName" -> "\[FormalF]", 
     "UniversalMorphismNames" -> (Subscript["\[FormalF]", ToString[#1]] & ) /@ Range[Length[objects]], 
     "UniversalObjectName" -> "\[FormalCapitalY]"]] /;  !ListQ[coproductSymbol] &&  !ListQ[compositionSymbol] &&  !ListQ[identitySymbol]
AbstractCoproduct[coproduct_Association] := AbstractCoproduct[KeySort[coproduct]] /; 
   KeyExistsQ[coproduct, "CompositionSymbol"] && KeyExistsQ[coproduct, "CoproductSymbol"] && 
    KeyExistsQ[coproduct, "IdentitySymbol"] && KeyExistsQ[coproduct, "InjectionMorphismNames"] && 
    KeyExistsQ[coproduct, "Objects"] && KeyExistsQ[coproduct, "UniqueMorphismName"] && 
    KeyExistsQ[coproduct, "UniversalMorphismNames"] && KeyExistsQ[coproduct, "UniversalObjectName"] && 
    Keys[KeySort[coproduct]] =!= Keys[coproduct]
AbstractCoproduct[AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol_, 
     "CoproductSymbol" -> coproductSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "InjectionMorphismNames" -> injectionMorphismNames_List, "Objects" -> objects_List, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]], newCoproductSymbol_] := 
  AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol, "CoproductSymbol" -> newCoproductSymbol, 
    "IdentitySymbol" -> identitySymbol, "InjectionMorphismNames" -> injectionMorphismNames, "Objects" -> objects, 
    "UniqueMorphismName" -> uniqueMorphismName, "UniversalMorphismNames" -> universalMorphismNames, 
    "UniversalObjectName" -> universalObjectName]]
AbstractCoproduct[AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol_, 
     "CoproductSymbol" -> coproductSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "InjectionMorphismNames" -> injectionMorphismNames_List, "Objects" -> objects_List, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]], newCoproductSymbol_, newCompositionSymbol_] := 
  AbstractCoproduct[Association["CompositionSymbol" -> newCompositionSymbol, "CoproductSymbol" -> newCoproductSymbol, 
    "IdentitySymbol" -> identitySymbol, "InjectionMorphismNames" -> injectionMorphismNames, "Objects" -> objects, 
    "UniqueMorphismName" -> uniqueMorphismName, "UniversalMorphismNames" -> universalMorphismNames, 
    "UniversalObjectName" -> universalObjectName]]
AbstractCoproduct[AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol_, 
     "CoproductSymbol" -> coproductSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "InjectionMorphismNames" -> injectionMorphismNames_List, "Objects" -> objects_List, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_List, 
     "UniversalObjectName" -> universalObjectName_]], newCoproductSymbol_, newCompositionSymbol_, newIdentitySymbol_] := 
  AbstractCoproduct[Association["CompositionSymbol" -> newCompositionSymbol, "CoproductSymbol" -> newCoproductSymbol, 
    "IdentitySymbol" -> newIdentitySymbol, "InjectionMorphismNames" -> injectionMorphismNames, "Objects" -> objects, 
    "UniqueMorphismName" -> uniqueMorphismName, "UniversalMorphismNames" -> universalMorphismNames, 
    "UniversalObjectName" -> universalObjectName]]
AbstractCoproduct[Association["CompositionSymbol" -> compositionSymbol_, "CoproductSymbol" -> coproductSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "InjectionMorphismNames" -> injectionMorphismNames_List, 
     "Objects" -> objects_List, "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> 
      universalMorphismNames_List, "UniversalObjectName" -> universalObjectName_]][
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
         (Module[{coproductObject = #1}, If[Length[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[
                   morphismAssociation, morphismEquivalences], objectEquivalences]], 
                First[Last[#1]] === coproductObject && Last[Last[#1]] === object & ]] == 0, isUniversalObject = 
              False]] & ) /@ reduceObjects[reduceObjects[objects, quiverObjectEquivalences], objectEquivalences]; 
         If[isUniversalObject, If[Length[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[morphismAssociation, 
                 morphismEquivalences], objectEquivalences]], First[Last[#1]] === coproductSymbol @@ objects && 
                Last[Last[#1]] === object & ]] == 0, arrowCount += 1; newArrows = Append[newArrows, 
              Subscript[uniqueMorphismName, ToString[arrowCount]] -> DirectedEdge[coproductSymbol @@ objects, object]]; 
            (Module[{coproductObjectIndex = #1, coproductObject}, coproductObject = reduceObjects[reduceObjects[objects, 
                    quiverObjectEquivalences], objectEquivalences][[coproductObjectIndex]]; newMorphismEquivalences = 
                 Join[newMorphismEquivalences, (First[#1] == categoryCompositionSymbol[Subscript[uniqueMorphismName, 
                       ToString[arrowCount]], injectionMorphismNames[[coproductObjectIndex]]] & ) /@ 
                   Select[Normal[reduceArrowsFinal[reduceArrowsInitial[morphismAssociation, morphismEquivalences], 
                      objectEquivalences]], First[Last[#1]] === coproductObject && Last[Last[#1]] === object & ]]] & ) /@ 
             Range[Length[reduceObjects[reduceObjects[objects, quiverObjectEquivalences], objectEquivalences]]]]]] & ) /@ 
      reduceObjects[reduceObjects[categoryObjects, quiverObjectEquivalences], objectEquivalences]; 
     ResourceFunction["AbstractCategory"][Association["CompositionSymbol" -> categoryCompositionSymbol, 
       "IdentitySymbol" -> categoryIdentitySymbol, "MorphismEquivalences" -> 
        DeleteDuplicates[Join[morphismEquivalences, newMorphismEquivalences]], "ObjectEquivalences" -> 
        objectEquivalences, "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> {}, 
          "Arrows" -> Association[DeleteDuplicates[Join[Normal[arrows], (injectionMorphismNames[[#1]] -> 
                 DirectedEdge[objects[[#1]], coproductSymbol @@ objects] & ) /@ Range[Length[reduceObjects[
                  reduceObjects[objects, quiverObjectEquivalences], objectEquivalences]]], newArrows]]], 
          "ObjectEquivalences" -> quiverObjectEquivalences, "Objects" -> DeleteDuplicates[Join[categoryObjects, objects, 
             {coproductSymbol @@ objects}]]]]]]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"

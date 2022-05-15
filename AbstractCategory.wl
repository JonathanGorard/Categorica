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
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["Objects"] := objects /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["ObjectCount"] := Length[objects] /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["MorphismAssociation"] := 
  Module[{morphismAssociation, compositions}, 
    morphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, Length[objects]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ objects; Association[(First[#1] -> DirectedEdge @@ Last[#1] & ) /@ 
       Normal[morphismAssociation]]] /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["MorphismNames"] := 
  Module[{morphismAssociation, compositions}, 
    morphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, Length[objects]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ objects; First /@ Normal[morphismAssociation]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["MorphismEdges"] := 
  Module[{morphismAssociation, compositions}, 
    morphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, Length[objects]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ objects; (DirectedEdge @@ Last[#1] & ) /@ Normal[morphismAssociation]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["MorphismCount"] := 
  Module[{morphismAssociation, compositions}, 
    morphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, Length[objects]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ objects; Length[Normal[morphismAssociation]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["ObjectEquivalences"] := Union[quiverObjectEquivalences, objectEquivalences] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["ObjectEquivalenceCount"] := 
  Length[Union[quiverObjectEquivalences, objectEquivalences]] /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["MorphismEquivalences"] := Union[arrowEquivalences, morphismEquivalences] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["MorphismEquivalenceCount"] := 
  Length[Union[arrowEquivalences, morphismEquivalences]] /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["ReducedObjects"] := 
  reduceObjects[reduceObjects[objects, quiverObjectEquivalences], objectEquivalences] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["ReducedObjectCount"] := 
  Length[reduceObjects[reduceObjects[objects, quiverObjectEquivalences], objectEquivalences]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["ReducedMorphismAssociation"] := 
  Module[{morphismAssociation, compositions}, 
    morphismAssociation = Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[arrows, arrowEquivalences], 
          quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, 
      Length[reduceObjects[objects, quiverObjectEquivalences]]]; morphismAssociation = 
      Association[Select[Normal[morphismAssociation], Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[objects, quiverObjectEquivalences]; 
     Association[(First[#1] -> DirectedEdge @@ Last[#1] & ) /@ 
       Normal[reduceArrowsFinal[reduceArrowsInitial[morphismAssociation, morphismEquivalences], objectEquivalences]]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["ReducedMorphismNames"] := 
  Module[{morphismAssociation, compositions}, 
    morphismAssociation = Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[arrows, arrowEquivalences], 
          quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, 
      Length[reduceObjects[objects, quiverObjectEquivalences]]]; morphismAssociation = 
      Association[Select[Normal[morphismAssociation], Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[objects, quiverObjectEquivalences]; 
     First /@ Normal[reduceArrowsFinal[reduceArrowsInitial[morphismAssociation, morphismEquivalences], 
        objectEquivalences]]] /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["ReducedMorphismEdges"] := 
  Module[{morphismAssociation, compositions}, 
    morphismAssociation = Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[arrows, arrowEquivalences], 
          quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, 
      Length[reduceObjects[objects, quiverObjectEquivalences]]]; morphismAssociation = 
      Association[Select[Normal[morphismAssociation], Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[objects, quiverObjectEquivalences]; 
     (DirectedEdge @@ Last[#1] & ) /@ Normal[reduceArrowsFinal[reduceArrowsInitial[morphismAssociation, 
         morphismEquivalences], objectEquivalences]]] /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["ReducedMorphismCount"] := 
  Module[{morphismAssociation, compositions}, 
    morphismAssociation = Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[arrows, arrowEquivalences], 
          quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, 
      Length[reduceObjects[objects, quiverObjectEquivalences]]]; morphismAssociation = 
      Association[Select[Normal[morphismAssociation], Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[objects, quiverObjectEquivalences]; 
     Length[Normal[reduceArrowsFinal[reduceArrowsInitial[morphismAssociation, morphismEquivalences], 
        objectEquivalences]]]] /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["SimpleMorphismAssociation"] := 
  Module[{morphismAssociation, compositions}, 
    morphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, Length[objects]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     Association[(First[#1] -> DirectedEdge @@ Last[#1] & ) /@ 
       Normal[Association[Select[DeleteDuplicatesBy[Normal[morphismAssociation], DirectedEdge @@ Last[#1] & ], 
          First[Last[#1]] =!= Last[Last[#1]] & ]]]]] /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["SimpleMorphismNames"] := 
  Module[{morphismAssociation, compositions}, 
    morphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, Length[objects]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     First /@ Normal[Association[Select[DeleteDuplicatesBy[Normal[morphismAssociation], DirectedEdge @@ Last[#1] & ], 
         First[Last[#1]] =!= Last[Last[#1]] & ]]]] /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["SimpleMorphismEdges"] := 
  Module[{morphismAssociation, compositions}, 
    morphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, Length[objects]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (DirectedEdge @@ Last[#1] & ) /@ Normal[Association[Select[DeleteDuplicatesBy[Normal[morphismAssociation], 
          DirectedEdge @@ Last[#1] & ], First[Last[#1]] =!= Last[Last[#1]] & ]]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["SimpleMorphismCount"] := 
  Module[{morphismAssociation, compositions}, 
    morphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, Length[objects]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     Length[Select[DeleteDuplicatesBy[Normal[morphismAssociation], DirectedEdge @@ Last[#1] & ], 
       First[Last[#1]] =!= Last[Last[#1]] & ]]] /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["ReducedSimpleMorphismAssociation"] := 
  Module[{morphismAssociation, compositions}, 
    morphismAssociation = Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[arrows, arrowEquivalences], 
          quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, 
      Length[reduceObjects[objects, quiverObjectEquivalences]]]; morphismAssociation = 
      Association[Select[Normal[morphismAssociation], Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     Association[(First[#1] -> DirectedEdge @@ Last[#1] & ) /@ 
       Normal[reduceArrowsFinal[reduceArrowsInitial[Association[Select[DeleteDuplicatesBy[Normal[morphismAssociation], 
             DirectedEdge @@ Last[#1] & ], First[Last[#1]] =!= Last[Last[#1]] & ]], morphismEquivalences], 
         objectEquivalences]]]] /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["ReducedSimpleMorphismNames"] := 
  Module[{morphismAssociation, compositions}, 
    morphismAssociation = Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[arrows, arrowEquivalences], 
          quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, 
      Length[reduceObjects[objects, quiverObjectEquivalences]]]; morphismAssociation = 
      Association[Select[Normal[morphismAssociation], Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     First /@ Normal[reduceArrowsFinal[reduceArrowsInitial[Association[
          Select[DeleteDuplicatesBy[Normal[morphismAssociation], DirectedEdge @@ Last[#1] & ], 
           First[Last[#1]] =!= Last[Last[#1]] & ]], morphismEquivalences], objectEquivalences]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["ReducedSimpleMorphismEdges"] := 
  Module[{morphismAssociation, compositions}, 
    morphismAssociation = Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[arrows, arrowEquivalences], 
          quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, 
      Length[reduceObjects[objects, quiverObjectEquivalences]]]; morphismAssociation = 
      Association[Select[Normal[morphismAssociation], Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (DirectedEdge @@ Last[#1] & ) /@ Normal[reduceArrowsFinal[reduceArrowsInitial[
         Association[Select[DeleteDuplicatesBy[Normal[morphismAssociation], DirectedEdge @@ Last[#1] & ], 
           First[Last[#1]] =!= Last[Last[#1]] & ]], morphismEquivalences], objectEquivalences]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["ReducedSimpleMorphismCount"] := 
  Module[{morphismAssociation, compositions}, 
    morphismAssociation = Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[arrows, arrowEquivalences], 
          quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, 
      Length[reduceObjects[objects, quiverObjectEquivalences]]]; morphismAssociation = 
      Association[Select[Normal[morphismAssociation], Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     Length[Normal[reduceArrowsFinal[reduceArrowsInitial[Association[Select[DeleteDuplicatesBy[
            Normal[morphismAssociation], DirectedEdge @@ Last[#1] & ], First[Last[#1]] =!= Last[Last[#1]] & ]], 
         morphismEquivalences], objectEquivalences]]]] /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["CompositionSymbol"] := 
  compositionSymbol /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["IdentitySymbol"] := 
  identitySymbol /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["DualCategory"] := 
  AbstractCategory[Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
     "MorphismEquivalences" -> (morphismEquivalences /. {compositionSymbol[x_, compositionSymbol[y_, z_]] :> 
         compositionSymbol[z, compositionSymbol[y, x]], compositionSymbol[compositionSymbol[x_, y_], z_] :> 
         compositionSymbol[compositionSymbol[z, y], x], compositionSymbol[x_, y_] :> compositionSymbol[y, x]}), 
     "ObjectEquivalences" -> objectEquivalences, "Quiver" -> ResourceFunction["AbstractQuiver"][
       Association["ArrowEquivalences" -> arrowEquivalences, "Arrows" -> 
         Association[(First[#1] -> Reverse[Last[#1]] & ) /@ Normal[arrows]], "ObjectEquivalences" -> objectEquivalences, 
        "Objects" -> objects]]]] /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["Quiver"] := 
  ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> arrowEquivalences, "Arrows" -> arrows, 
     "ObjectEquivalences" -> quiverObjectEquivalences, "Objects" -> objects]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["AssociativityEquations"] := 
  Module[{fullMorphismAssociation, compositions, associativityEquations}, 
    fullMorphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[fullMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[Normal[fullMorphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], fullMorphismAssociation = 
           Association[Append[Normal[fullMorphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, Length[objects]]; 
     fullMorphismAssociation = Association[Select[Normal[fullMorphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; associativityEquations = {}; 
     (Module[{morphismName = #1, equality}, equality = Select[First /@ Normal[fullMorphismAssociation], 
           StringDelete[ToString[morphismName], {"(", ")", " "}] === StringDelete[ToString[#1], {"(", ")", " "}] && 
             morphismName =!= #1 & ]; If[Length[equality] > 0, associativityEquations = 
           (Append[associativityEquations, morphismName == #1] & ) /@ equality]] & ) /@ 
      First /@ Normal[fullMorphismAssociation]; DeleteDuplicates[Sort /@ Flatten[associativityEquations]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["ReducedAssociativityEquations"] := 
  Module[{fullMorphismAssociation, compositions, associativityEquations}, 
    fullMorphismAssociation = Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[arrows, arrowEquivalences], 
          quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[fullMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[Normal[fullMorphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], fullMorphismAssociation = 
           Association[Append[Normal[fullMorphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, 
      Length[reduceObjects[objects, quiverObjectEquivalences]]]; fullMorphismAssociation = 
      Association[Select[Normal[fullMorphismAssociation], Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; associativityEquations = {}; 
     (Module[{morphismName = #1, equality}, 
        equality = Select[First /@ Normal[reduceArrowsFinal[reduceArrowsInitial[fullMorphismAssociation, 
               morphismEquivalences], objectEquivalences]], StringDelete[ToString[morphismName], {"(", ")", " "}] === 
              StringDelete[ToString[#1], {"(", ")", " "}] && morphismName =!= #1 & ]; If[Length[equality] > 0, 
          associativityEquations = (Append[associativityEquations, morphismName == #1] & ) /@ equality]] & ) /@ 
      First /@ Normal[reduceArrowsFinal[reduceArrowsInitial[fullMorphismAssociation, morphismEquivalences], 
         objectEquivalences]]; DeleteDuplicates[Sort /@ Flatten[associativityEquations]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["IdentityEquations"] := 
  Module[{morphismAssociation, compositions, identityEquations}, 
    morphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, Length[objects]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ objects; identityEquations = {}; 
     (Module[{identityMorphism = #1}, identityEquations = 
         (Append[identityEquations, compositionSymbol[First[#1], First[identityMorphism]] == First[#1]] & ) /@ 
          Select[Normal[morphismAssociation], First[Last[#1]] === First[Last[identityMorphism]] & ]] & ) /@ 
      Select[Normal[morphismAssociation], First[Last[#1]] === Last[Last[#1]] & ]; 
     (Module[{identityMorphism = #1}, identityEquations = 
         (Append[identityEquations, compositionSymbol[First[identityMorphism], First[#1]] == First[#1]] & ) /@ 
          Select[Normal[morphismAssociation], Last[Last[#1]] === Last[Last[identityMorphism]] & ]] & ) /@ 
      Select[Normal[morphismAssociation], First[Last[#1]] === Last[Last[#1]] & ]; 
     DeleteDuplicates[Sort /@ Flatten[identityEquations]]] /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["ReducedIdentityEquations"] := 
  Module[{morphismAssociation, compositions, identityEquations}, 
    morphismAssociation = Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[arrows, arrowEquivalences], 
          quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, 
      Length[reduceObjects[objects, quiverObjectEquivalences]]]; morphismAssociation = 
      Association[Select[Normal[morphismAssociation], Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[objects, quiverObjectEquivalences]; identityEquations = {}; 
     (Module[{identityMorphism = #1}, identityEquations = 
         (Append[identityEquations, compositionSymbol[First[#1], First[identityMorphism]] == First[#1]] & ) /@ 
          Select[Normal[reduceArrowsFinal[reduceArrowsInitial[morphismAssociation, morphismEquivalences], 
             objectEquivalences]], First[Last[#1]] === First[Last[identityMorphism]] & ]] & ) /@ 
      Select[Normal[reduceArrowsFinal[reduceArrowsInitial[morphismAssociation, morphismEquivalences], 
         objectEquivalences]], First[Last[#1]] === Last[Last[#1]] & ]; 
     (Module[{identityMorphism = #1}, identityEquations = 
         (Append[identityEquations, compositionSymbol[First[identityMorphism], First[#1]] == First[#1]] & ) /@ 
          Select[Normal[reduceArrowsFinal[reduceArrowsInitial[morphismAssociation, morphismEquivalences], 
             objectEquivalences]], Last[Last[#1]] === Last[Last[identityMorphism]] & ]] & ) /@ 
      Select[Normal[reduceArrowsFinal[reduceArrowsInitial[morphismAssociation, morphismEquivalences], 
         objectEquivalences]], First[Last[#1]] === Last[Last[#1]] & ]; 
     DeleteDuplicates[Sort /@ Flatten[identityEquations]]] /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["CommutativeDiagramQ"] := 
  Module[{morphismAssociation, compositions}, 
    morphismAssociation = Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[arrows, arrowEquivalences], 
          quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, 
      Length[reduceObjects[objects, quiverObjectEquivalences]]]; morphismAssociation = 
      Association[Select[Normal[morphismAssociation], Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[objects, quiverObjectEquivalences]; 
     AllTrue[Normal[CountsBy[Normal[reduceArrowsFinal[reduceArrowsInitial[morphismAssociation, morphismEquivalences], 
          objectEquivalences]], DirectedEdge @@ Last[#1] & ]], Last[#1] == 1 & ]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["CommutativityEquations"] := 
  Module[{morphismAssociation, compositions}, 
    morphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, Length[objects]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ objects; 
     Flatten[(EdgeList[TransitiveReductionGraph[Graph[Apply[UndirectedEdge, Tuples[First /@ #1, 2], {1}]]]] /. 
         UndirectedEdge -> Equal & ) /@ Select[GatherBy[(First[#1] -> DirectedEdge @@ Last[#1] & ) /@ 
          Normal[morphismAssociation], Last], Length[#1] > 1 & ]]] /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["ReducedCommutativityEquations"] := 
  Module[{morphismAssociation, compositions}, 
    morphismAssociation = Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[arrows, arrowEquivalences], 
          quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, 
      Length[reduceObjects[objects, quiverObjectEquivalences]]]; morphismAssociation = 
      Association[Select[Normal[morphismAssociation], Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[objects, quiverObjectEquivalences]; 
     Flatten[(EdgeList[TransitiveReductionGraph[Graph[Apply[UndirectedEdge, Tuples[First /@ #1, 2], {1}]]]] /. 
         UndirectedEdge -> Equal & ) /@ Select[GatherBy[(First[#1] -> DirectedEdge @@ Last[#1] & ) /@ 
          Normal[reduceArrowsFinal[reduceArrowsInitial[morphismAssociation, morphismEquivalences], objectEquivalences]], 
         Last], Length[#1] > 1 & ]]] /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["Monomorphisms"] := 
  Module[{morphismAssociation, compositions, objectEquivalenceGraph, morphismEquivalenceGraph, monomorphisms}, 
    morphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, Length[objects]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ objects; objectEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Join[quiverObjectEquivalences, 
             objectEquivalences], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ objects]]; 
     morphismEquivalenceGraph = Graph[Join[EdgeList[TransitiveClosureGraph[
          Graph[Apply[UndirectedEdge, Join[arrowEquivalences, morphismEquivalences], {1}]]]], 
        (UndirectedEdge[#1, #1] & ) /@ First /@ Normal[morphismAssociation]]]; monomorphisms = {}; 
     (Module[{morphism = #1, morphismPairs, isMonomorphism}, 
        morphismPairs = Tuples[Select[Normal[morphismAssociation], Length[FindShortestPath[objectEquivalenceGraph, 
                Last[Last[#1]], First[Last[morphism]]]] > 0 & ], 2]; isMonomorphism = True; 
         (If[MemberQ[VertexList[morphismEquivalenceGraph], compositionSymbol[First[morphism], First[First[#1]]]] && 
             MemberQ[VertexList[morphismEquivalenceGraph], compositionSymbol[First[morphism], First[Last[#1]]]], 
            If[Length[FindShortestPath[morphismEquivalenceGraph, compositionSymbol[First[morphism], First[First[#1]]], 
                compositionSymbol[First[morphism], First[Last[#1]]]]] > 0, 
             If[MemberQ[VertexList[morphismEquivalenceGraph], First[First[#1]]] && MemberQ[VertexList[
                 morphismEquivalenceGraph], First[Last[#1]]], If[Length[FindShortestPath[morphismEquivalenceGraph, 
                  First[First[#1]], First[Last[#1]]]] == 0, isMonomorphism = False], isMonomorphism = False]]] & ) /@ 
          morphismPairs; monomorphisms = Append[monomorphisms, First[morphism] -> isMonomorphism]] & ) /@ 
      Normal[morphismAssociation]; Association[monomorphisms]] /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["ReducedMonomorphisms"] := 
  Module[{morphismAssociation, compositions, reducedMorphismAssociation, reducedCompositions, objectEquivalenceGraph, 
     morphismEquivalenceGraph, reducedMonomorphisms}, 
    morphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, Length[objects]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ objects; reducedMorphismAssociation = 
      Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[arrows, arrowEquivalences], 
          quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[reducedCompositions = Select[Tuples[Normal[reducedMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[reducedMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          reducedMorphismAssociation = Association[Append[Normal[reducedMorphismAssociation], 
             compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ reducedCompositions, 
      Length[reduceObjects[objects, quiverObjectEquivalences]]]; reducedMorphismAssociation = 
      Association[Select[Normal[reducedMorphismAssociation], Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[reducedMorphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        reducedMorphismAssociation = Association[Append[Normal[reducedMorphismAssociation], 
           identitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[objects, quiverObjectEquivalences]; 
     objectEquivalenceGraph = Graph[Join[EdgeList[TransitiveClosureGraph[
          Graph[Apply[UndirectedEdge, Join[quiverObjectEquivalences, objectEquivalences], {1}]]]], 
        (UndirectedEdge[#1, #1] & ) /@ objects]]; morphismEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Join[arrowEquivalences, 
             morphismEquivalences], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ First /@ Normal[morphismAssociation]]]; 
     reducedMonomorphisms = {}; (Module[{morphism = #1, morphismPairs, isMonomorphism}, 
        morphismPairs = Tuples[Select[Normal[morphismAssociation], Length[FindShortestPath[objectEquivalenceGraph, 
                Last[Last[#1]], First[Last[morphism]]]] > 0 & ], 2]; isMonomorphism = True; 
         (If[MemberQ[VertexList[morphismEquivalenceGraph], compositionSymbol[First[morphism], First[First[#1]]]] && 
             MemberQ[VertexList[morphismEquivalenceGraph], compositionSymbol[First[morphism], First[Last[#1]]]], 
            If[Length[FindShortestPath[morphismEquivalenceGraph, compositionSymbol[First[morphism], First[First[#1]]], 
                compositionSymbol[First[morphism], First[Last[#1]]]]] > 0, 
             If[MemberQ[VertexList[morphismEquivalenceGraph], First[First[#1]]] && MemberQ[VertexList[
                 morphismEquivalenceGraph], First[Last[#1]]], If[Length[FindShortestPath[morphismEquivalenceGraph, 
                  First[First[#1]], First[Last[#1]]]] == 0, isMonomorphism = False], isMonomorphism = False]]] & ) /@ 
          morphismPairs; reducedMonomorphisms = Append[reducedMonomorphisms, First[morphism] -> isMonomorphism]] & ) /@ 
      Normal[reduceArrowsFinal[reduceArrowsInitial[reducedMorphismAssociation, morphismEquivalences], 
        objectEquivalences]]; Association[reducedMonomorphisms]] /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["Epimorphisms"] := 
  Module[{morphismAssociation, compositions, objectEquivalenceGraph, morphismEquivalenceGraph, epimorphisms}, 
    morphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, Length[objects]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ objects; objectEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Join[quiverObjectEquivalences, 
             objectEquivalences], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ objects]]; 
     morphismEquivalenceGraph = Graph[Join[EdgeList[TransitiveClosureGraph[
          Graph[Apply[UndirectedEdge, Join[arrowEquivalences, morphismEquivalences], {1}]]]], 
        (UndirectedEdge[#1, #1] & ) /@ First /@ Normal[morphismAssociation]]]; epimorphisms = {}; 
     (Module[{morphism = #1, morphismPairs, isEpimorphism}, 
        morphismPairs = Tuples[Select[Normal[morphismAssociation], Length[FindShortestPath[objectEquivalenceGraph, 
                First[Last[#1]], Last[Last[morphism]]]] > 0 & ], 2]; isEpimorphism = True; 
         (If[MemberQ[VertexList[morphismEquivalenceGraph], compositionSymbol[First[First[#1]], First[morphism]]] && 
             MemberQ[VertexList[morphismEquivalenceGraph], compositionSymbol[First[Last[#1]], First[morphism]]], 
            If[Length[FindShortestPath[morphismEquivalenceGraph, compositionSymbol[First[First[#1]], First[morphism]], 
                compositionSymbol[First[Last[#1]], First[morphism]]]] > 0, 
             If[MemberQ[VertexList[morphismEquivalenceGraph], First[First[#1]]] && MemberQ[VertexList[
                 morphismEquivalenceGraph], First[Last[#1]]], If[Length[FindShortestPath[morphismEquivalenceGraph, 
                  First[First[#1]], First[Last[#1]]]] == 0, isEpimorphism = False], isEpimorphism = False]]] & ) /@ 
          morphismPairs; epimorphisms = Append[epimorphisms, First[morphism] -> isEpimorphism]] & ) /@ 
      Normal[morphismAssociation]; Association[epimorphisms]] /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["ReducedEpimorphisms"] := 
  Module[{morphismAssociation, compositions, reducedMorphismAssociation, reducedCompositions, objectEquivalenceGraph, 
     morphismEquivalenceGraph, reducedEpimorphisms}, 
    morphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, Length[objects]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ objects; reducedMorphismAssociation = 
      Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[arrows, arrowEquivalences], 
          quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[reducedCompositions = Select[Tuples[Normal[reducedMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[reducedMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          reducedMorphismAssociation = Association[Append[Normal[reducedMorphismAssociation], 
             compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ reducedCompositions, 
      Length[reduceObjects[objects, quiverObjectEquivalences]]]; reducedMorphismAssociation = 
      Association[Select[Normal[reducedMorphismAssociation], Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[reducedMorphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        reducedMorphismAssociation = Association[Append[Normal[reducedMorphismAssociation], 
           identitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[objects, quiverObjectEquivalences]; 
     objectEquivalenceGraph = Graph[Join[EdgeList[TransitiveClosureGraph[
          Graph[Apply[UndirectedEdge, Join[quiverObjectEquivalences, objectEquivalences], {1}]]]], 
        (UndirectedEdge[#1, #1] & ) /@ objects]]; morphismEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Join[arrowEquivalences, 
             morphismEquivalences], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ First /@ Normal[morphismAssociation]]]; 
     reducedEpimorphisms = {}; (Module[{morphism = #1, morphismPairs, isEpimorphism}, 
        morphismPairs = Tuples[Select[Normal[morphismAssociation], Length[FindShortestPath[objectEquivalenceGraph, 
                First[Last[#1]], Last[Last[morphism]]]] > 0 & ], 2]; isEpimorphism = True; 
         (If[MemberQ[VertexList[morphismEquivalenceGraph], compositionSymbol[First[First[#1]], First[morphism]]] && 
             MemberQ[VertexList[morphismEquivalenceGraph], compositionSymbol[First[Last[#1]], First[morphism]]], 
            If[Length[FindShortestPath[morphismEquivalenceGraph, compositionSymbol[First[First[#1]], First[morphism]], 
                compositionSymbol[First[Last[#1]], First[morphism]]]] > 0, 
             If[MemberQ[VertexList[morphismEquivalenceGraph], First[First[#1]]] && MemberQ[VertexList[
                 morphismEquivalenceGraph], First[Last[#1]]], If[Length[FindShortestPath[morphismEquivalenceGraph, 
                  First[First[#1]], First[Last[#1]]]] == 0, isEpimorphism = False], isEpimorphism = False]]] & ) /@ 
          morphismPairs; reducedEpimorphisms = Append[reducedEpimorphisms, First[morphism] -> isEpimorphism]] & ) /@ 
      Normal[reduceArrowsFinal[reduceArrowsInitial[reducedMorphismAssociation, morphismEquivalences], 
        objectEquivalences]]; Association[reducedEpimorphisms]] /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["Bimorphisms"] := 
  Module[{morphismAssociation, compositions, objectEquivalenceGraph, morphismEquivalenceGraph, bimorphisms}, 
    morphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, Length[objects]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ objects; objectEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Join[quiverObjectEquivalences, 
             objectEquivalences], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ objects]]; 
     morphismEquivalenceGraph = Graph[Join[EdgeList[TransitiveClosureGraph[
          Graph[Apply[UndirectedEdge, Join[arrowEquivalences, morphismEquivalences], {1}]]]], 
        (UndirectedEdge[#1, #1] & ) /@ First /@ Normal[morphismAssociation]]]; bimorphisms = {}; 
     (Module[{morphism = #1, morphismPairs1, morphismPairs2, isMonomorphism, isEpimorphism}, 
        morphismPairs1 = Tuples[Select[Normal[morphismAssociation], Length[FindShortestPath[objectEquivalenceGraph, 
                Last[Last[#1]], First[Last[morphism]]]] > 0 & ], 2]; morphismPairs2 = 
          Tuples[Select[Normal[morphismAssociation], Length[FindShortestPath[objectEquivalenceGraph, First[Last[#1]], 
                Last[Last[morphism]]]] > 0 & ], 2]; isMonomorphism = True; 
         (If[MemberQ[VertexList[morphismEquivalenceGraph], compositionSymbol[First[morphism], First[First[#1]]]] && 
             MemberQ[VertexList[morphismEquivalenceGraph], compositionSymbol[First[morphism], First[Last[#1]]]], 
            If[Length[FindShortestPath[morphismEquivalenceGraph, compositionSymbol[First[morphism], First[First[#1]]], 
                compositionSymbol[First[morphism], First[Last[#1]]]]] > 0, 
             If[MemberQ[VertexList[morphismEquivalenceGraph], First[First[#1]]] && MemberQ[VertexList[
                 morphismEquivalenceGraph], First[Last[#1]]], If[Length[FindShortestPath[morphismEquivalenceGraph, 
                  First[First[#1]], First[Last[#1]]]] == 0, isMonomorphism = False], isMonomorphism = False]]] & ) /@ 
          morphismPairs1; isEpimorphism = True; (If[MemberQ[VertexList[morphismEquivalenceGraph], 
              compositionSymbol[First[First[#1]], First[morphism]]] && MemberQ[VertexList[morphismEquivalenceGraph], 
              compositionSymbol[First[Last[#1]], First[morphism]]], If[Length[FindShortestPath[morphismEquivalenceGraph, 
                compositionSymbol[First[First[#1]], First[morphism]], compositionSymbol[First[Last[#1]], 
                 First[morphism]]]] > 0, If[MemberQ[VertexList[morphismEquivalenceGraph], First[First[#1]]] && MemberQ[
                VertexList[morphismEquivalenceGraph], First[Last[#1]]], If[Length[FindShortestPath[
                  morphismEquivalenceGraph, First[First[#1]], First[Last[#1]]]] == 0, isEpimorphism = False], 
              isEpimorphism = False]]] & ) /@ morphismPairs2; bimorphisms = Append[bimorphisms, 
           First[morphism] -> isMonomorphism && isEpimorphism]] & ) /@ Normal[morphismAssociation]; 
     Association[bimorphisms]] /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["ReducedBimorphisms"] := 
  Module[{morphismAssociation, compositions, reducedMorphismAssociation, reducedCompositions, objectEquivalenceGraph, 
     morphismEquivalenceGraph, reducedBimorphisms}, 
    morphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, Length[objects]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ objects; reducedMorphismAssociation = 
      Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[arrows, arrowEquivalences], 
          quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[reducedCompositions = Select[Tuples[Normal[reducedMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[reducedMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          reducedMorphismAssociation = Association[Append[Normal[reducedMorphismAssociation], 
             compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ reducedCompositions, 
      Length[reduceObjects[objects, quiverObjectEquivalences]]]; reducedMorphismAssociation = 
      Association[Select[Normal[reducedMorphismAssociation], Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[reducedMorphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        reducedMorphismAssociation = Association[Append[Normal[reducedMorphismAssociation], 
           identitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[objects, quiverObjectEquivalences]; 
     objectEquivalenceGraph = Graph[Join[EdgeList[TransitiveClosureGraph[
          Graph[Apply[UndirectedEdge, Join[quiverObjectEquivalences, objectEquivalences], {1}]]]], 
        (UndirectedEdge[#1, #1] & ) /@ objects]]; morphismEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Join[arrowEquivalences, 
             morphismEquivalences], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ First /@ Normal[morphismAssociation]]]; 
     reducedBimorphisms = {}; (Module[{morphism = #1, morphismPairs1, morphismPairs2, isMonomorphism, isEpimorphism}, 
        morphismPairs1 = Tuples[Select[Normal[morphismAssociation], Length[FindShortestPath[objectEquivalenceGraph, 
                Last[Last[#1]], First[Last[morphism]]]] > 0 & ], 2]; morphismPairs2 = 
          Tuples[Select[Normal[morphismAssociation], Length[FindShortestPath[objectEquivalenceGraph, First[Last[#1]], 
                Last[Last[morphism]]]] > 0 & ], 2]; isMonomorphism = True; 
         (If[MemberQ[VertexList[morphismEquivalenceGraph], compositionSymbol[First[morphism], First[First[#1]]]] && 
             MemberQ[VertexList[morphismEquivalenceGraph], compositionSymbol[First[morphism], First[Last[#1]]]], 
            If[Length[FindShortestPath[morphismEquivalenceGraph, compositionSymbol[First[morphism], First[First[#1]]], 
                compositionSymbol[First[morphism], First[Last[#1]]]]] > 0, 
             If[MemberQ[VertexList[morphismEquivalenceGraph], First[First[#1]]] && MemberQ[VertexList[
                 morphismEquivalenceGraph], First[Last[#1]]], If[Length[FindShortestPath[morphismEquivalenceGraph, 
                  First[First[#1]], First[Last[#1]]]] == 0, isMonomorphism = False], isMonomorphism = False]]] & ) /@ 
          morphismPairs1; isEpimorphism = True; (If[MemberQ[VertexList[morphismEquivalenceGraph], 
              compositionSymbol[First[First[#1]], First[morphism]]] && MemberQ[VertexList[morphismEquivalenceGraph], 
              compositionSymbol[First[Last[#1]], First[morphism]]], If[Length[FindShortestPath[morphismEquivalenceGraph, 
                compositionSymbol[First[First[#1]], First[morphism]], compositionSymbol[First[Last[#1]], 
                 First[morphism]]]] > 0, If[MemberQ[VertexList[morphismEquivalenceGraph], First[First[#1]]] && MemberQ[
                VertexList[morphismEquivalenceGraph], First[Last[#1]]], If[Length[FindShortestPath[
                  morphismEquivalenceGraph, First[First[#1]], First[Last[#1]]]] == 0, isEpimorphism = False], 
              isEpimorphism = False]]] & ) /@ morphismPairs2; reducedBimorphisms = Append[reducedBimorphisms, 
           First[morphism] -> isMonomorphism && isEpimorphism]] & ) /@ 
      Normal[reduceArrowsFinal[reduceArrowsInitial[reducedMorphismAssociation, morphismEquivalences], 
        objectEquivalences]]; Association[reducedBimorphisms]] /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["Retractions"] := 
  Module[{morphismAssociation, compositions, objectEquivalenceGraph, morphismEquivalenceGraph, retractions}, 
    morphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, Length[objects]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ objects; objectEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Join[quiverObjectEquivalences, 
             objectEquivalences], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ objects]]; 
     morphismEquivalenceGraph = Graph[Join[EdgeList[TransitiveClosureGraph[
          Graph[Apply[UndirectedEdge, Join[arrowEquivalences, morphismEquivalences], {1}]]]], 
        (UndirectedEdge[#1, #1] & ) /@ First /@ Normal[morphismAssociation]]]; retractions = {}; 
     (Module[{morphism = #1, morphisms, isRetraction}, morphisms = Select[Normal[morphismAssociation], 
           Length[FindShortestPath[objectEquivalenceGraph, Last[Last[#1]], First[Last[morphism]]]] > 0 && 
             Length[FindShortestPath[objectEquivalenceGraph, First[Last[#1]], Last[Last[morphism]]]] > 0 & ]; 
         isRetraction = False; (If[morphism === (identitySymbol[#1] -> DirectedEdge[#1, #1]), isRetraction = True] & ) /@ 
          objects; (Module[{newMorphism = #1, equivalentObjects}, If[MemberQ[VertexList[morphismEquivalenceGraph], 
              compositionSymbol[First[morphism], First[newMorphism]]], equivalentObjects = Union[VertexComponent[
                 objectEquivalenceGraph, Last[Last[morphism]]], VertexComponent[objectEquivalenceGraph, 
                 First[Last[newMorphism]]]]; (If[MemberQ[VertexList[morphismEquivalenceGraph], identitySymbol[#1]], 
                 If[Length[FindShortestPath[morphismEquivalenceGraph, compositionSymbol[First[morphism], 
                      First[newMorphism]], identitySymbol[#1]]] > 0, isRetraction = True]] & ) /@ 
               equivalentObjects]] & ) /@ morphisms; retractions = Append[retractions, First[morphism] -> 
            isRetraction]] & ) /@ Normal[morphismAssociation]; Association[retractions]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["ReducedRetractions"] := 
  Module[{morphismAssociation, compositions, reducedMorphismAssociation, reducedCompositions, objectEquivalenceGraph, 
     morphismEquivalenceGraph, reducedRetractions}, 
    morphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, Length[objects]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ objects; reducedMorphismAssociation = 
      Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[arrows, arrowEquivalences], 
          quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[reducedCompositions = Select[Tuples[Normal[reducedMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[reducedMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          reducedMorphismAssociation = Association[Append[Normal[reducedMorphismAssociation], 
             compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ reducedCompositions, 
      Length[reduceObjects[objects, quiverObjectEquivalences]]]; reducedMorphismAssociation = 
      Association[Select[Normal[reducedMorphismAssociation], Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[reducedMorphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        reducedMorphismAssociation = Association[Append[Normal[reducedMorphismAssociation], 
           identitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[objects, quiverObjectEquivalences]; 
     objectEquivalenceGraph = Graph[Join[EdgeList[TransitiveClosureGraph[
          Graph[Apply[UndirectedEdge, Join[quiverObjectEquivalences, objectEquivalences], {1}]]]], 
        (UndirectedEdge[#1, #1] & ) /@ objects]]; morphismEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Join[arrowEquivalences, 
             morphismEquivalences], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ First /@ Normal[morphismAssociation]]]; 
     reducedRetractions = {}; (Module[{morphism = #1, morphisms, isRetraction}, 
        morphisms = Select[Normal[morphismAssociation], Length[FindShortestPath[objectEquivalenceGraph, Last[Last[#1]], 
                First[Last[morphism]]]] > 0 && Length[FindShortestPath[objectEquivalenceGraph, First[Last[#1]], 
                Last[Last[morphism]]]] > 0 & ]; isRetraction = False; 
         (If[morphism === (identitySymbol[#1] -> DirectedEdge[#1, #1]), isRetraction = True] & ) /@ objects; 
         (Module[{newMorphism = #1, equivalentObjects}, If[MemberQ[VertexList[morphismEquivalenceGraph], 
              compositionSymbol[First[morphism], First[newMorphism]]], equivalentObjects = Union[VertexComponent[
                 objectEquivalenceGraph, Last[Last[morphism]]], VertexComponent[objectEquivalenceGraph, 
                 First[Last[newMorphism]]]]; (If[MemberQ[VertexList[morphismEquivalenceGraph], identitySymbol[#1]], 
                 If[Length[FindShortestPath[morphismEquivalenceGraph, compositionSymbol[First[morphism], 
                      First[newMorphism]], identitySymbol[#1]]] > 0, isRetraction = True]] & ) /@ 
               equivalentObjects]] & ) /@ morphisms; reducedRetractions = Append[reducedRetractions, 
           First[morphism] -> isRetraction]] & ) /@ Normal[reduceArrowsFinal[reduceArrowsInitial[
         reducedMorphismAssociation, morphismEquivalences], objectEquivalences]]; Association[reducedRetractions]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["LeftInverses"] := 
  Module[{morphismAssociation, compositions, objectEquivalenceGraph, morphismEquivalenceGraph, leftInverses}, 
    morphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, Length[objects]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ objects; objectEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Join[quiverObjectEquivalences, 
             objectEquivalences], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ objects]]; 
     morphismEquivalenceGraph = Graph[Join[EdgeList[TransitiveClosureGraph[
          Graph[Apply[UndirectedEdge, Join[arrowEquivalences, morphismEquivalences], {1}]]]], 
        (UndirectedEdge[#1, #1] & ) /@ First /@ Normal[morphismAssociation]]]; leftInverses = {}; 
     (Module[{morphism = #1, morphisms, leftInverseList}, morphisms = Select[Normal[morphismAssociation], 
           Length[FindShortestPath[objectEquivalenceGraph, Last[Last[#1]], First[Last[morphism]]]] > 0 && 
             Length[FindShortestPath[objectEquivalenceGraph, First[Last[#1]], Last[Last[morphism]]]] > 0 & ]; 
         leftInverseList = {}; (If[morphism === (identitySymbol[#1] -> DirectedEdge[#1, #1]), 
            leftInverseList = Append[leftInverseList, First[morphism]]] & ) /@ objects; 
         (Module[{newMorphism = #1, equivalentObjects}, If[MemberQ[VertexList[morphismEquivalenceGraph], 
              compositionSymbol[First[newMorphism], First[morphism]]], equivalentObjects = Union[VertexComponent[
                 objectEquivalenceGraph, First[Last[morphism]]], VertexComponent[objectEquivalenceGraph, 
                 Last[Last[newMorphism]]]]; (If[MemberQ[VertexList[morphismEquivalenceGraph], identitySymbol[#1]], 
                 If[Length[FindShortestPath[morphismEquivalenceGraph, compositionSymbol[First[newMorphism], 
                      First[morphism]], identitySymbol[#1]]] > 0, leftInverseList = Append[leftInverseList, 
                    First[newMorphism]]]] & ) /@ equivalentObjects]] & ) /@ morphisms; 
         leftInverses = Append[leftInverses, First[morphism] -> leftInverseList]] & ) /@ Normal[morphismAssociation]; 
     Association[leftInverses]] /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["ReducedLeftInverses"] := 
  Module[{morphismAssociation, compositions, reducedMorphismAssociation, reducedCompositions, objectEquivalenceGraph, 
     morphismEquivalenceGraph, reducedLeftInverses}, 
    morphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, Length[objects]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ objects; reducedMorphismAssociation = 
      Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[arrows, arrowEquivalences], 
          quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[reducedCompositions = Select[Tuples[Normal[reducedMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[reducedMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          reducedMorphismAssociation = Association[Append[Normal[reducedMorphismAssociation], 
             compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ reducedCompositions, 
      Length[reduceObjects[objects, quiverObjectEquivalences]]]; reducedMorphismAssociation = 
      Association[Select[Normal[reducedMorphismAssociation], Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[reducedMorphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        reducedMorphismAssociation = Association[Append[Normal[reducedMorphismAssociation], 
           identitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[objects, quiverObjectEquivalences]; 
     objectEquivalenceGraph = Graph[Join[EdgeList[TransitiveClosureGraph[
          Graph[Apply[UndirectedEdge, Join[quiverObjectEquivalences, objectEquivalences], {1}]]]], 
        (UndirectedEdge[#1, #1] & ) /@ objects]]; morphismEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Join[arrowEquivalences, 
             morphismEquivalences], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ First /@ Normal[morphismAssociation]]]; 
     reducedLeftInverses = {}; (Module[{morphism = #1, morphisms, leftInverseList}, 
        morphisms = Select[Normal[morphismAssociation], Length[FindShortestPath[objectEquivalenceGraph, Last[Last[#1]], 
                First[Last[morphism]]]] > 0 && Length[FindShortestPath[objectEquivalenceGraph, First[Last[#1]], 
                Last[Last[morphism]]]] > 0 & ]; leftInverseList = {}; 
         (If[morphism === (identitySymbol[#1] -> DirectedEdge[#1, #1]), leftInverseList = Append[leftInverseList, 
              First[morphism]]] & ) /@ objects; (Module[{newMorphism = #1, equivalentObjects}, 
            If[MemberQ[VertexList[morphismEquivalenceGraph], compositionSymbol[First[newMorphism], First[morphism]]], 
             equivalentObjects = Union[VertexComponent[objectEquivalenceGraph, First[Last[morphism]]], 
                VertexComponent[objectEquivalenceGraph, Last[Last[newMorphism]]]]; 
              (If[MemberQ[VertexList[morphismEquivalenceGraph], identitySymbol[#1]], 
                 If[Length[FindShortestPath[morphismEquivalenceGraph, compositionSymbol[First[newMorphism], 
                      First[morphism]], identitySymbol[#1]]] > 0, leftInverseList = Append[leftInverseList, 
                    First[newMorphism]]]] & ) /@ equivalentObjects]] & ) /@ morphisms; 
         reducedLeftInverses = Append[reducedLeftInverses, First[morphism] -> leftInverseList]] & ) /@ 
      Normal[reduceArrowsFinal[reduceArrowsInitial[reducedMorphismAssociation, morphismEquivalences], 
        objectEquivalences]]; Association[reducedLeftInverses]] /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["Sections"] := 
  Module[{morphismAssociation, compositions, objectEquivalenceGraph, morphismEquivalenceGraph, sections}, 
    morphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, Length[objects]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ objects; objectEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Join[quiverObjectEquivalences, 
             objectEquivalences], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ objects]]; 
     morphismEquivalenceGraph = Graph[Join[EdgeList[TransitiveClosureGraph[
          Graph[Apply[UndirectedEdge, Join[arrowEquivalences, morphismEquivalences], {1}]]]], 
        (UndirectedEdge[#1, #1] & ) /@ First /@ Normal[morphismAssociation]]]; sections = {}; 
     (Module[{morphism = #1, morphisms, isSection}, morphisms = Select[Normal[morphismAssociation], 
           Length[FindShortestPath[objectEquivalenceGraph, Last[Last[#1]], First[Last[morphism]]]] > 0 && 
             Length[FindShortestPath[objectEquivalenceGraph, First[Last[#1]], Last[Last[morphism]]]] > 0 & ]; 
         isSection = False; (If[morphism === (identitySymbol[#1] -> DirectedEdge[#1, #1]), isSection = True] & ) /@ 
          objects; (Module[{newMorphism = #1, equivalentObjects}, If[MemberQ[VertexList[morphismEquivalenceGraph], 
              compositionSymbol[First[newMorphism], First[morphism]]], equivalentObjects = Union[VertexComponent[
                 objectEquivalenceGraph, First[Last[morphism]]], VertexComponent[objectEquivalenceGraph, 
                 Last[Last[newMorphism]]]]; (If[MemberQ[VertexList[morphismEquivalenceGraph], identitySymbol[#1]], 
                 If[Length[FindShortestPath[morphismEquivalenceGraph, compositionSymbol[First[newMorphism], 
                      First[morphism]], identitySymbol[#1]]] > 0, isSection = True]] & ) /@ equivalentObjects]] & ) /@ 
          morphisms; sections = Append[sections, First[morphism] -> isSection]] & ) /@ Normal[morphismAssociation]; 
     Association[sections]] /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["ReducedSections"] := 
  Module[{morphismAssociation, compositions, reducedMorphismAssociation, reducedCompositions, objectEquivalenceGraph, 
     morphismEquivalenceGraph, reducedSections}, 
    morphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, Length[objects]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ objects; reducedMorphismAssociation = 
      Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[arrows, arrowEquivalences], 
          quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[reducedCompositions = Select[Tuples[Normal[reducedMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[reducedMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          reducedMorphismAssociation = Association[Append[Normal[reducedMorphismAssociation], 
             compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ reducedCompositions, 
      Length[reduceObjects[objects, quiverObjectEquivalences]]]; reducedMorphismAssociation = 
      Association[Select[Normal[reducedMorphismAssociation], Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[reducedMorphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        reducedMorphismAssociation = Association[Append[Normal[reducedMorphismAssociation], 
           identitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[objects, quiverObjectEquivalences]; 
     objectEquivalenceGraph = Graph[Join[EdgeList[TransitiveClosureGraph[
          Graph[Apply[UndirectedEdge, Join[quiverObjectEquivalences, objectEquivalences], {1}]]]], 
        (UndirectedEdge[#1, #1] & ) /@ objects]]; morphismEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Join[arrowEquivalences, 
             morphismEquivalences], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ First /@ Normal[morphismAssociation]]]; 
     reducedSections = {}; (Module[{morphism = #1, morphisms, isSection}, 
        morphisms = Select[Normal[morphismAssociation], Length[FindShortestPath[objectEquivalenceGraph, Last[Last[#1]], 
                First[Last[morphism]]]] > 0 && Length[FindShortestPath[objectEquivalenceGraph, First[Last[#1]], 
                Last[Last[morphism]]]] > 0 & ]; isSection = False; 
         (If[morphism === (identitySymbol[#1] -> DirectedEdge[#1, #1]), isSection = True] & ) /@ objects; 
         (Module[{newMorphism = #1, equivalentObjects}, If[MemberQ[VertexList[morphismEquivalenceGraph], 
              compositionSymbol[First[newMorphism], First[morphism]]], equivalentObjects = Union[VertexComponent[
                 objectEquivalenceGraph, First[Last[morphism]]], VertexComponent[objectEquivalenceGraph, 
                 Last[Last[newMorphism]]]]; (If[MemberQ[VertexList[morphismEquivalenceGraph], identitySymbol[#1]], 
                 If[Length[FindShortestPath[morphismEquivalenceGraph, compositionSymbol[First[newMorphism], 
                      First[morphism]], identitySymbol[#1]]] > 0, isSection = True]] & ) /@ equivalentObjects]] & ) /@ 
          morphisms; reducedSections = Append[reducedSections, First[morphism] -> isSection]] & ) /@ 
      Normal[reduceArrowsFinal[reduceArrowsInitial[reducedMorphismAssociation, morphismEquivalences], 
        objectEquivalences]]; Association[reducedSections]] /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["RightInverses"] := 
  Module[{morphismAssociation, compositions, objectEquivalenceGraph, morphismEquivalenceGraph, rightInverses}, 
    morphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, Length[objects]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ objects; objectEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Join[quiverObjectEquivalences, 
             objectEquivalences], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ objects]]; 
     morphismEquivalenceGraph = Graph[Join[EdgeList[TransitiveClosureGraph[
          Graph[Apply[UndirectedEdge, Join[arrowEquivalences, morphismEquivalences], {1}]]]], 
        (UndirectedEdge[#1, #1] & ) /@ First /@ Normal[morphismAssociation]]]; rightInverses = {}; 
     (Module[{morphism = #1, morphisms, rightInverseList}, morphisms = Select[Normal[morphismAssociation], 
           Length[FindShortestPath[objectEquivalenceGraph, Last[Last[#1]], First[Last[morphism]]]] > 0 && 
             Length[FindShortestPath[objectEquivalenceGraph, First[Last[#1]], Last[Last[morphism]]]] > 0 & ]; 
         rightInverseList = {}; (If[morphism === (identitySymbol[#1] -> DirectedEdge[#1, #1]), 
            rightInverseList = Append[rightInverseList, First[morphism]]] & ) /@ objects; 
         (Module[{newMorphism = #1, equivalentObjects}, If[MemberQ[VertexList[morphismEquivalenceGraph], 
              compositionSymbol[First[morphism], First[newMorphism]]], equivalentObjects = Union[VertexComponent[
                 objectEquivalenceGraph, Last[Last[morphism]]], VertexComponent[objectEquivalenceGraph, 
                 First[Last[newMorphism]]]]; (If[MemberQ[VertexList[morphismEquivalenceGraph], identitySymbol[#1]], 
                 If[Length[FindShortestPath[morphismEquivalenceGraph, compositionSymbol[First[morphism], 
                      First[newMorphism]], identitySymbol[#1]]] > 0, rightInverseList = Append[rightInverseList, 
                    First[newMorphism]]]] & ) /@ equivalentObjects]] & ) /@ morphisms; 
         rightInverses = Append[rightInverses, First[morphism] -> rightInverseList]] & ) /@ Normal[morphismAssociation]; 
     Association[rightInverses]] /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["ReducedRightInverses"] := 
  Module[{morphismAssociation, compositions, reducedMorphismAssociation, reducedCompositions, objectEquivalenceGraph, 
     morphismEquivalenceGraph, reducedRightInverses}, 
    morphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, Length[objects]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ objects; reducedMorphismAssociation = 
      Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[arrows, arrowEquivalences], 
          quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[reducedCompositions = Select[Tuples[Normal[reducedMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[reducedMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          reducedMorphismAssociation = Association[Append[Normal[reducedMorphismAssociation], 
             compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ reducedCompositions, 
      Length[reduceObjects[objects, quiverObjectEquivalences]]]; reducedMorphismAssociation = 
      Association[Select[Normal[reducedMorphismAssociation], Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[reducedMorphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        reducedMorphismAssociation = Association[Append[Normal[reducedMorphismAssociation], 
           identitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[objects, quiverObjectEquivalences]; 
     objectEquivalenceGraph = Graph[Join[EdgeList[TransitiveClosureGraph[
          Graph[Apply[UndirectedEdge, Join[quiverObjectEquivalences, objectEquivalences], {1}]]]], 
        (UndirectedEdge[#1, #1] & ) /@ objects]]; morphismEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Join[arrowEquivalences, 
             morphismEquivalences], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ First /@ Normal[morphismAssociation]]]; 
     reducedRightInverses = {}; (Module[{morphism = #1, morphisms, rightInverseList}, 
        morphisms = Select[Normal[morphismAssociation], Length[FindShortestPath[objectEquivalenceGraph, Last[Last[#1]], 
                First[Last[morphism]]]] > 0 && Length[FindShortestPath[objectEquivalenceGraph, First[Last[#1]], 
                Last[Last[morphism]]]] > 0 & ]; rightInverseList = {}; 
         (If[morphism === (identitySymbol[#1] -> DirectedEdge[#1, #1]), rightInverseList = Append[rightInverseList, 
              First[morphism]]] & ) /@ objects; (Module[{newMorphism = #1, equivalentObjects}, 
            If[MemberQ[VertexList[morphismEquivalenceGraph], compositionSymbol[First[morphism], First[newMorphism]]], 
             equivalentObjects = Union[VertexComponent[objectEquivalenceGraph, Last[Last[morphism]]], 
                VertexComponent[objectEquivalenceGraph, First[Last[newMorphism]]]]; 
              (If[MemberQ[VertexList[morphismEquivalenceGraph], identitySymbol[#1]], 
                 If[Length[FindShortestPath[morphismEquivalenceGraph, compositionSymbol[First[morphism], 
                      First[newMorphism]], identitySymbol[#1]]] > 0, rightInverseList = Append[rightInverseList, 
                    First[newMorphism]]]] & ) /@ equivalentObjects]] & ) /@ morphisms; 
         reducedRightInverses = Append[reducedRightInverses, First[morphism] -> rightInverseList]] & ) /@ 
      Normal[reduceArrowsFinal[reduceArrowsInitial[reducedMorphismAssociation, morphismEquivalences], 
        objectEquivalences]]; Association[reducedRightInverses]] /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["Isomorphisms"] := 
  Module[{morphismAssociation, compositions, objectEquivalenceGraph, morphismEquivalenceGraph, isomorphisms}, 
    morphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, Length[objects]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ objects; objectEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Join[quiverObjectEquivalences, 
             objectEquivalences], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ objects]]; 
     morphismEquivalenceGraph = Graph[Join[EdgeList[TransitiveClosureGraph[
          Graph[Apply[UndirectedEdge, Join[arrowEquivalences, morphismEquivalences], {1}]]]], 
        (UndirectedEdge[#1, #1] & ) /@ First /@ Normal[morphismAssociation]]]; isomorphisms = {}; 
     (Module[{morphism = #1, morphisms, isRetraction, isSection}, 
        morphisms = Select[Normal[morphismAssociation], Length[FindShortestPath[objectEquivalenceGraph, Last[Last[#1]], 
                First[Last[morphism]]]] > 0 && Length[FindShortestPath[objectEquivalenceGraph, First[Last[#1]], 
                Last[Last[morphism]]]] > 0 & ]; isRetraction = False; isSection = False; 
         (If[morphism === (identitySymbol[#1] -> DirectedEdge[#1, #1]), isRetraction = True] & ) /@ objects; 
         (If[morphism === (identitySymbol[#1] -> DirectedEdge[#1, #1]), isSection = True] & ) /@ objects; 
         (Module[{newMorphism = #1, equivalentObjects}, If[MemberQ[VertexList[morphismEquivalenceGraph], 
               compositionSymbol[First[morphism], First[newMorphism]]], equivalentObjects = Union[VertexComponent[
                  objectEquivalenceGraph, Last[Last[morphism]]], VertexComponent[objectEquivalenceGraph, 
                  First[Last[newMorphism]]]]; (If[MemberQ[VertexList[morphismEquivalenceGraph], identitySymbol[#1]], 
                  If[Length[FindShortestPath[morphismEquivalenceGraph, compositionSymbol[First[morphism], 
                       First[newMorphism]], identitySymbol[#1]]] > 0, isRetraction = True]] & ) /@ equivalentObjects]; 
             If[MemberQ[VertexList[morphismEquivalenceGraph], compositionSymbol[First[newMorphism], First[morphism]]], 
              equivalentObjects = Union[VertexComponent[objectEquivalenceGraph, First[Last[morphism]]], 
                 VertexComponent[objectEquivalenceGraph, Last[Last[newMorphism]]]]; 
               (If[MemberQ[VertexList[morphismEquivalenceGraph], identitySymbol[#1]], If[Length[FindShortestPath[
                      morphismEquivalenceGraph, compositionSymbol[First[newMorphism], First[morphism]], identitySymbol[
                       #1]]] > 0, isSection = True]] & ) /@ equivalentObjects]] & ) /@ morphisms; 
         isomorphisms = Append[isomorphisms, First[morphism] -> isRetraction && isSection]] & ) /@ 
      Normal[morphismAssociation]; Association[isomorphisms]] /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["ReducedIsomorphisms"] := 
  Module[{morphismAssociation, compositions, reducedMorphismAssociation, reducedCompositions, objectEquivalenceGraph, 
     morphismEquivalenceGraph, reducedIsomorphisms}, 
    morphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, Length[objects]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ objects; reducedMorphismAssociation = 
      Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[arrows, arrowEquivalences], 
          quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[reducedCompositions = Select[Tuples[Normal[reducedMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[reducedMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          reducedMorphismAssociation = Association[Append[Normal[reducedMorphismAssociation], 
             compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ reducedCompositions, 
      Length[reduceObjects[objects, quiverObjectEquivalences]]]; reducedMorphismAssociation = 
      Association[Select[Normal[reducedMorphismAssociation], Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[reducedMorphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        reducedMorphismAssociation = Association[Append[Normal[reducedMorphismAssociation], 
           identitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[objects, quiverObjectEquivalences]; 
     objectEquivalenceGraph = Graph[Join[EdgeList[TransitiveClosureGraph[
          Graph[Apply[UndirectedEdge, Join[quiverObjectEquivalences, objectEquivalences], {1}]]]], 
        (UndirectedEdge[#1, #1] & ) /@ objects]]; morphismEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Join[arrowEquivalences, 
             morphismEquivalences], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ First /@ Normal[morphismAssociation]]]; 
     reducedIsomorphisms = {}; (Module[{morphism = #1, morphisms, isRetraction, isSection}, 
        morphisms = Select[Normal[morphismAssociation], Length[FindShortestPath[objectEquivalenceGraph, Last[Last[#1]], 
                First[Last[morphism]]]] > 0 && Length[FindShortestPath[objectEquivalenceGraph, First[Last[#1]], 
                Last[Last[morphism]]]] > 0 & ]; isRetraction = False; isSection = False; 
         (If[morphism === (identitySymbol[#1] -> DirectedEdge[#1, #1]), isRetraction = True] & ) /@ objects; 
         (If[morphism === (identitySymbol[#1] -> DirectedEdge[#1, #1]), isSection = True] & ) /@ objects; 
         (Module[{newMorphism = #1, equivalentObjects}, If[MemberQ[VertexList[morphismEquivalenceGraph], 
               compositionSymbol[First[morphism], First[newMorphism]]], equivalentObjects = Union[VertexComponent[
                  objectEquivalenceGraph, Last[Last[morphism]]], VertexComponent[objectEquivalenceGraph, 
                  First[Last[newMorphism]]]]; (If[MemberQ[VertexList[morphismEquivalenceGraph], identitySymbol[#1]], 
                  If[Length[FindShortestPath[morphismEquivalenceGraph, compositionSymbol[First[morphism], 
                       First[newMorphism]], identitySymbol[#1]]] > 0, isRetraction = True]] & ) /@ equivalentObjects]; 
             If[MemberQ[VertexList[morphismEquivalenceGraph], compositionSymbol[First[newMorphism], First[morphism]]], 
              equivalentObjects = Union[VertexComponent[objectEquivalenceGraph, First[Last[morphism]]], 
                 VertexComponent[objectEquivalenceGraph, Last[Last[newMorphism]]]]; 
               (If[MemberQ[VertexList[morphismEquivalenceGraph], identitySymbol[#1]], If[Length[FindShortestPath[
                      morphismEquivalenceGraph, compositionSymbol[First[newMorphism], First[morphism]], identitySymbol[
                       #1]]] > 0, isSection = True]] & ) /@ equivalentObjects]] & ) /@ morphisms; 
         reducedIsomorphisms = Append[reducedIsomorphisms, First[morphism] -> isRetraction && isSection]] & ) /@ 
      Normal[reduceArrowsFinal[reduceArrowsInitial[reducedMorphismAssociation, morphismEquivalences], 
        objectEquivalences]]; Association[reducedIsomorphisms]] /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["Inverses"] := 
  Module[{morphismAssociation, compositions, objectEquivalenceGraph, morphismEquivalenceGraph, inverses}, 
    morphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, Length[objects]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ objects; objectEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Join[quiverObjectEquivalences, 
             objectEquivalences], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ objects]]; 
     morphismEquivalenceGraph = Graph[Join[EdgeList[TransitiveClosureGraph[
          Graph[Apply[UndirectedEdge, Join[arrowEquivalences, morphismEquivalences], {1}]]]], 
        (UndirectedEdge[#1, #1] & ) /@ First /@ Normal[morphismAssociation]]]; inverses = {}; 
     (Module[{morphism = #1, morphisms, inverseList}, morphisms = Select[Normal[morphismAssociation], 
           Length[FindShortestPath[objectEquivalenceGraph, Last[Last[#1]], First[Last[morphism]]]] > 0 && 
             Length[FindShortestPath[objectEquivalenceGraph, First[Last[#1]], Last[Last[morphism]]]] > 0 & ]; 
         inverseList = {}; (If[morphism === (identitySymbol[#1] -> DirectedEdge[#1, #1]), 
            inverseList = Append[inverseList, First[morphism]]] & ) /@ objects; 
         (Module[{newMorphism = #1, isRetraction, isSection, equivalentObjects}, isRetraction = False; isSection = False; 
             If[MemberQ[VertexList[morphismEquivalenceGraph], compositionSymbol[First[morphism], First[newMorphism]]], 
              equivalentObjects = Union[VertexComponent[objectEquivalenceGraph, Last[Last[morphism]]], 
                 VertexComponent[objectEquivalenceGraph, First[Last[newMorphism]]]]; 
               (If[MemberQ[VertexList[morphismEquivalenceGraph], identitySymbol[#1]], If[Length[FindShortestPath[
                      morphismEquivalenceGraph, compositionSymbol[First[morphism], First[newMorphism]], identitySymbol[
                       #1]]] > 0, isRetraction = True]] & ) /@ equivalentObjects]; 
             If[MemberQ[VertexList[morphismEquivalenceGraph], compositionSymbol[First[newMorphism], First[morphism]]], 
              equivalentObjects = Union[VertexComponent[objectEquivalenceGraph, First[Last[morphism]]], 
                 VertexComponent[objectEquivalenceGraph, Last[Last[newMorphism]]]]; 
               (If[MemberQ[VertexList[morphismEquivalenceGraph], identitySymbol[#1]], If[Length[FindShortestPath[
                      morphismEquivalenceGraph, compositionSymbol[First[newMorphism], First[morphism]], identitySymbol[
                       #1]]] > 0, isSection = True]] & ) /@ equivalentObjects]; If[isRetraction && isSection, 
              inverseList = Append[inverseList, First[newMorphism]]]] & ) /@ morphisms; 
         inverses = Append[inverses, First[morphism] -> inverseList]] & ) /@ Normal[morphismAssociation]; 
     Association[inverses]] /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["ReducedInverses"] := 
  Module[{morphismAssociation, compositions, reducedMorphismAssociation, reducedCompositions, objectEquivalenceGraph, 
     morphismEquivalenceGraph, reducedInverses}, 
    morphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, Length[objects]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ objects; reducedMorphismAssociation = 
      Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[arrows, arrowEquivalences], 
          quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[reducedCompositions = Select[Tuples[Normal[reducedMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[reducedMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          reducedMorphismAssociation = Association[Append[Normal[reducedMorphismAssociation], 
             compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ reducedCompositions, 
      Length[reduceObjects[objects, quiverObjectEquivalences]]]; reducedMorphismAssociation = 
      Association[Select[Normal[reducedMorphismAssociation], Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[reducedMorphismAssociation], identitySymbol[#1, #1] -> DirectedEdge[#1, #1]], 
        reducedMorphismAssociation = Association[Append[Normal[reducedMorphismAssociation], 
           identitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[objects, quiverObjectEquivalences]; 
     objectEquivalenceGraph = Graph[Join[EdgeList[TransitiveClosureGraph[
          Graph[Apply[UndirectedEdge, Join[quiverObjectEquivalences, objectEquivalences], {1}]]]], 
        (UndirectedEdge[#1, #1] & ) /@ objects]]; morphismEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Join[arrowEquivalences, 
             morphismEquivalences], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ First /@ Normal[morphismAssociation]]]; 
     reducedInverses = {}; (Module[{morphism = #1, morphisms, inverseList}, 
        morphisms = Select[Normal[morphismAssociation], Length[FindShortestPath[objectEquivalenceGraph, Last[Last[#1]], 
                First[Last[morphism]]]] > 0 && Length[FindShortestPath[objectEquivalenceGraph, First[Last[#1]], 
                Last[Last[morphism]]]] > 0 & ]; inverseList = {}; 
         (If[morphism === (identitySymbol[#1] -> DirectedEdge[#1, #1]), inverseList = Append[inverseList, 
              First[morphism]]] & ) /@ objects; (Module[{newMorphism = #1, isRetraction, isSection, equivalentObjects}, 
            isRetraction = False; isSection = False; If[MemberQ[VertexList[morphismEquivalenceGraph], compositionSymbol[
                First[morphism], First[newMorphism]]], equivalentObjects = Union[VertexComponent[objectEquivalenceGraph, 
                  Last[Last[morphism]]], VertexComponent[objectEquivalenceGraph, First[Last[newMorphism]]]]; 
               (If[MemberQ[VertexList[morphismEquivalenceGraph], identitySymbol[#1]], If[Length[FindShortestPath[
                      morphismEquivalenceGraph, compositionSymbol[First[morphism], First[newMorphism]], identitySymbol[
                       #1]]] > 0, isRetraction = True]] & ) /@ equivalentObjects]; 
             If[MemberQ[VertexList[morphismEquivalenceGraph], compositionSymbol[First[newMorphism], First[morphism]]], 
              equivalentObjects = Union[VertexComponent[objectEquivalenceGraph, First[Last[morphism]]], 
                 VertexComponent[objectEquivalenceGraph, Last[Last[newMorphism]]]]; 
               (If[MemberQ[VertexList[morphismEquivalenceGraph], identitySymbol[#1]], If[Length[FindShortestPath[
                      morphismEquivalenceGraph, compositionSymbol[First[newMorphism], First[morphism]], identitySymbol[
                       #1]]] > 0, isSection = True]] & ) /@ equivalentObjects]; If[isRetraction && isSection, 
              inverseList = Append[inverseList, First[newMorphism]]]] & ) /@ morphisms; 
         reducedInverses = Append[reducedInverses, First[morphism] -> inverseList]] & ) /@ 
      Normal[reduceArrowsFinal[reduceArrowsInitial[reducedMorphismAssociation, morphismEquivalences], 
        objectEquivalences]]; Association[reducedInverses]] /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["Endomorphisms"] := 
  Module[{morphismAssociation, compositions, objectEquivalenceGraph, endomorphisms}, 
    morphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, Length[objects]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ objects; objectEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Join[quiverObjectEquivalences, 
             objectEquivalences], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ objects]]; endomorphisms = {}; 
     (Module[{morphism = #1, isEndomorphism}, isEndomorphism = False; 
         If[Length[FindShortestPath[objectEquivalenceGraph, First[Last[morphism]], Last[Last[morphism]]]] > 0, 
          isEndomorphism = True]; endomorphisms = Append[endomorphisms, First[morphism] -> isEndomorphism]] & ) /@ 
      Normal[morphismAssociation]; Association[endomorphisms]] /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["ReducedEndomorphisms"] := 
  Module[{morphismAssociation, compositions, objectEquivalenceGraph, reducedEndomorphisms}, 
    morphismAssociation = Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[arrows, arrowEquivalences], 
          quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, 
      Length[reduceObjects[objects, quiverObjectEquivalences]]]; morphismAssociation = 
      Association[Select[Normal[morphismAssociation], Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[objects, quiverObjectEquivalences]; 
     objectEquivalenceGraph = Graph[Join[EdgeList[TransitiveClosureGraph[
          Graph[Apply[UndirectedEdge, Join[quiverObjectEquivalences, objectEquivalences], {1}]]]], 
        (UndirectedEdge[#1, #1] & ) /@ objects]]; reducedEndomorphisms = {}; 
     (Module[{morphism = #1, isEndomorphism}, isEndomorphism = False; 
         If[Length[FindShortestPath[objectEquivalenceGraph, First[Last[morphism]], Last[Last[morphism]]]] > 0, 
          isEndomorphism = True]; reducedEndomorphisms = Append[reducedEndomorphisms, First[morphism] -> 
            isEndomorphism]] & ) /@ Normal[reduceArrowsFinal[reduceArrowsInitial[morphismAssociation, 
         morphismEquivalences], objectEquivalences]]; Association[reducedEndomorphisms]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["Automorphisms"] := 
  Module[{morphismAssociation, compositions, objectEquivalenceGraph, morphismEquivalenceGraph, automorphisms}, 
    morphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, Length[objects]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ objects; objectEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Join[quiverObjectEquivalences, 
             objectEquivalences], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ objects]]; 
     morphismEquivalenceGraph = Graph[Join[EdgeList[TransitiveClosureGraph[
          Graph[Apply[UndirectedEdge, Join[arrowEquivalences, morphismEquivalences], {1}]]]], 
        (UndirectedEdge[#1, #1] & ) /@ First /@ Normal[morphismAssociation]]]; automorphisms = {}; 
     (Module[{morphism = #1, morphisms, isRetraction, isSection, isEndomorphism}, 
        morphisms = Select[Normal[morphismAssociation], Length[FindShortestPath[objectEquivalenceGraph, Last[Last[#1]], 
                First[Last[morphism]]]] > 0 && Length[FindShortestPath[objectEquivalenceGraph, First[Last[#1]], 
                Last[Last[morphism]]]] > 0 & ]; isRetraction = False; isSection = False; 
         (If[morphism === (identitySymbol[#1] -> DirectedEdge[#1, #1]), isRetraction = True] & ) /@ objects; 
         (If[morphism === (identitySymbol[#1] -> DirectedEdge[#1, #1]), isSection = True] & ) /@ objects; 
         (Module[{newMorphism = #1, equivalentObjects}, If[MemberQ[VertexList[morphismEquivalenceGraph], 
               compositionSymbol[First[morphism], First[newMorphism]]], equivalentObjects = Union[VertexComponent[
                  objectEquivalenceGraph, Last[Last[morphism]]], VertexComponent[objectEquivalenceGraph, 
                  First[Last[newMorphism]]]]; (If[MemberQ[VertexList[morphismEquivalenceGraph], identitySymbol[#1]], 
                  If[Length[FindShortestPath[morphismEquivalenceGraph, compositionSymbol[First[morphism], 
                       First[newMorphism]], identitySymbol[#1]]] > 0, isRetraction = True]] & ) /@ equivalentObjects]; 
             If[MemberQ[VertexList[morphismEquivalenceGraph], compositionSymbol[First[newMorphism], First[morphism]]], 
              equivalentObjects = Union[VertexComponent[objectEquivalenceGraph, First[Last[morphism]]], 
                 VertexComponent[objectEquivalenceGraph, Last[Last[newMorphism]]]]; 
               (If[MemberQ[VertexList[morphismEquivalenceGraph], identitySymbol[#1]], If[Length[FindShortestPath[
                      morphismEquivalenceGraph, compositionSymbol[First[newMorphism], First[morphism]], identitySymbol[
                       #1]]] > 0, isSection = True]] & ) /@ equivalentObjects]] & ) /@ morphisms; isEndomorphism = False; 
         If[Length[FindShortestPath[objectEquivalenceGraph, First[Last[morphism]], Last[Last[morphism]]]] > 0, 
          isEndomorphism = True]; automorphisms = Append[automorphisms, First[morphism] -> isRetraction && isSection && 
             isEndomorphism]] & ) /@ Normal[morphismAssociation]; Association[automorphisms]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["ReducedAutomorphisms"] := 
  Module[{morphismAssociation, compositions, reducedMorphismAssociation, reducedCompositions, objectEquivalenceGraph, 
     morphismEquivalenceGraph, reducedAutomorphisms}, 
    morphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, Length[objects]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ objects; reducedMorphismAssociation = 
      Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[arrows, arrowEquivalences], 
          quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[reducedCompositions = Select[Tuples[Normal[reducedMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[reducedMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          reducedMorphismAssociation = Association[Append[Normal[reducedMorphismAssociation], 
             compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ reducedCompositions, 
      Length[reduceObjects[objects, quiverObjectEquivalences]]]; reducedMorphismAssociation = 
      Association[Select[Normal[reducedMorphismAssociation], Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[reducedMorphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        reducedMorphismAssociation = Association[Append[Normal[reducedMorphismAssociation], 
           identitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[objects, quiverObjectEquivalences]; 
     objectEquivalenceGraph = Graph[Join[EdgeList[TransitiveClosureGraph[
          Graph[Apply[UndirectedEdge, Join[quiverObjectEquivalences, objectEquivalences], {1}]]]], 
        (UndirectedEdge[#1, #1] & ) /@ objects]]; morphismEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Join[arrowEquivalences, 
             morphismEquivalences], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ First /@ Normal[morphismAssociation]]]; 
     reducedAutomorphisms = {}; (Module[{morphism = #1, morphisms, isRetraction, isSection, isEndomorphism}, 
        morphisms = Select[Normal[morphismAssociation], Length[FindShortestPath[objectEquivalenceGraph, Last[Last[#1]], 
                First[Last[morphism]]]] > 0 && Length[FindShortestPath[objectEquivalenceGraph, First[Last[#1]], 
                Last[Last[morphism]]]] > 0 & ]; isRetraction = False; isSection = False; 
         (If[morphism === (identitySymbol[#1] -> DirectedEdge[#1, #1]), isRetraction = True] & ) /@ objects; 
         (If[morphism === (identitySymbol[#1] -> DirectedEdge[#1, #1]), isSection = True] & ) /@ objects; 
         (Module[{newMorphism = #1, equivalentObjects}, If[MemberQ[VertexList[morphismEquivalenceGraph], 
               compositionSymbol[First[morphism], First[newMorphism]]], equivalentObjects = Union[VertexComponent[
                  objectEquivalenceGraph, Last[Last[morphism]]], VertexComponent[objectEquivalenceGraph, 
                  First[Last[newMorphism]]]]; (If[MemberQ[VertexList[morphismEquivalenceGraph], identitySymbol[#1]], 
                  If[Length[FindShortestPath[morphismEquivalenceGraph, compositionSymbol[First[morphism], 
                       First[newMorphism]], identitySymbol[#1]]] > 0, isRetraction = True]] & ) /@ equivalentObjects]; 
             If[MemberQ[VertexList[morphismEquivalenceGraph], compositionSymbol[First[newMorphism], First[morphism]]], 
              equivalentObjects = Union[VertexComponent[objectEquivalenceGraph, First[Last[morphism]]], 
                 VertexComponent[objectEquivalenceGraph, Last[Last[newMorphism]]]]; 
               (If[MemberQ[VertexList[morphismEquivalenceGraph], identitySymbol[#1]], If[Length[FindShortestPath[
                      morphismEquivalenceGraph, compositionSymbol[First[newMorphism], First[morphism]], identitySymbol[
                       #1]]] > 0, isSection = True]] & ) /@ equivalentObjects]] & ) /@ morphisms; isEndomorphism = False; 
         If[Length[FindShortestPath[objectEquivalenceGraph, First[Last[morphism]], Last[Last[morphism]]]] > 0, 
          isEndomorphism = True]; reducedAutomorphisms = Append[reducedAutomorphisms, First[morphism] -> 
            isRetraction && isSection && isEndomorphism]] & ) /@ 
      Normal[reduceArrowsFinal[reduceArrowsInitial[reducedMorphismAssociation, morphismEquivalences], 
        objectEquivalences]]; Association[reducedAutomorphisms]] /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["InitialObjects"] := 
  Module[{morphismAssociation, compositions, initialObjects}, 
    morphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, Length[objects]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ objects; initialObjects = {}; 
     (Module[{object = #1, morphisms, isInitialObject}, morphisms = Select[Normal[morphismAssociation], 
           First[Last[#1]] === object & ]; isInitialObject = True; 
         (Module[{newObject = #1}, If[Length[Select[morphisms, Last[Last[#1]] === newObject & ]] != 1, 
             isInitialObject = False]] & ) /@ objects; initialObjects = Append[initialObjects, 
           object -> isInitialObject]] & ) /@ objects; Association[initialObjects]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["ReducedInitialObjects"] := 
  Module[{morphismAssociation, compositions, reducedInitialObjects}, 
    morphismAssociation = Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[arrows, arrowEquivalences], 
          quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, 
      Length[reduceObjects[objects, quiverObjectEquivalences]]]; morphismAssociation = 
      Association[Select[Normal[morphismAssociation], Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[objects, quiverObjectEquivalences]; reducedInitialObjects = {}; 
     (Module[{object = #1, morphisms, isInitialObject}, 
        morphisms = Select[Normal[reduceArrowsFinal[reduceArrowsInitial[morphismAssociation, morphismEquivalences], 
             objectEquivalences]], First[Last[#1]] === object & ]; isInitialObject = True; 
         (Module[{newObject = #1}, If[Length[Select[morphisms, Last[Last[#1]] === newObject & ]] != 1, 
             isInitialObject = False]] & ) /@ reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
           objectEquivalences]; reducedInitialObjects = Append[reducedInitialObjects, object -> isInitialObject]] & ) /@ 
      reduceObjects[reduceObjects[objects, quiverObjectEquivalences], objectEquivalences]; 
     Association[reducedInitialObjects]] /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["StrictInitialObjects"] := 
  Module[{morphismAssociation, compositions, objectEquivalenceGraph, morphismEquivalenceGraph, isomorphisms, 
     strictInitialObjects}, morphismAssociation = Association[Select[Normal[arrows], 
        First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, Length[objects]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ objects; objectEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Join[quiverObjectEquivalences, 
             objectEquivalences], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ objects]]; 
     morphismEquivalenceGraph = Graph[Join[EdgeList[TransitiveClosureGraph[
          Graph[Apply[UndirectedEdge, Join[arrowEquivalences, morphismEquivalences], {1}]]]], 
        (UndirectedEdge[#1, #1] & ) /@ First /@ Normal[morphismAssociation]]]; isomorphisms = {}; 
     (Module[{morphism = #1, morphisms, isRetraction, isSection}, 
        morphisms = Select[Normal[morphismAssociation], Length[FindShortestPath[objectEquivalenceGraph, Last[Last[#1]], 
                First[Last[morphism]]]] > 0 && Length[FindShortestPath[objectEquivalenceGraph, First[Last[#1]], 
                Last[Last[morphism]]]] > 0 & ]; isRetraction = False; isSection = False; 
         (If[morphism === (identitySymbol[#1] -> DirectedEdge[#1, #1]), isRetraction = True] & ) /@ objects; 
         (If[morphism === (identitySymbol[#1] -> DirectedEdge[#1, #1]), isSection = True] & ) /@ objects; 
         (Module[{newMorphism = #1, equivalentObjects}, If[MemberQ[VertexList[morphismEquivalenceGraph], 
               compositionSymbol[First[morphism], First[newMorphism]]], equivalentObjects = Union[VertexComponent[
                  objectEquivalenceGraph, Last[Last[morphism]]], VertexComponent[objectEquivalenceGraph, 
                  First[Last[newMorphism]]]]; (If[MemberQ[VertexList[morphismEquivalenceGraph], identitySymbol[#1]], 
                  If[Length[FindShortestPath[morphismEquivalenceGraph, compositionSymbol[First[morphism], 
                       First[newMorphism]], identitySymbol[#1]]] > 0, isRetraction = True]] & ) /@ equivalentObjects]; 
             If[MemberQ[VertexList[morphismEquivalenceGraph], compositionSymbol[First[newMorphism], First[morphism]]], 
              equivalentObjects = Union[VertexComponent[objectEquivalenceGraph, First[Last[morphism]]], 
                 VertexComponent[objectEquivalenceGraph, Last[Last[newMorphism]]]]; 
               (If[MemberQ[VertexList[morphismEquivalenceGraph], identitySymbol[#1]], If[Length[FindShortestPath[
                      morphismEquivalenceGraph, compositionSymbol[First[newMorphism], First[morphism]], identitySymbol[
                       #1]]] > 0, isSection = True]] & ) /@ equivalentObjects]] & ) /@ morphisms; 
         isomorphisms = Append[isomorphisms, First[morphism] -> isRetraction && isSection]] & ) /@ 
      Normal[morphismAssociation]; strictInitialObjects = {}; 
     (Module[{object = #1, morphisms1, morphisms2, isStrictInitialObject}, 
        morphisms1 = Select[Normal[morphismAssociation], First[Last[#1]] === object & ]; 
         morphisms2 = Select[Normal[Association[isomorphisms]], MemberQ[First /@ Select[Normal[morphismAssociation], 
               Last[Last[#1]] === object & ], #1] & ]; isStrictInitialObject = True; 
         (Module[{newObject = #1}, If[Length[Select[morphisms1, Last[Last[#1]] === newObject & ]] != 1, 
             isStrictInitialObject = False]] & ) /@ objects; 
         (If[Last[#1] === False, isStrictInitialObject = False] & ) /@ morphisms2; strictInitialObjects = 
          Append[strictInitialObjects, object -> isStrictInitialObject]] & ) /@ objects; 
     Association[strictInitialObjects]] /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["ReducedStrictInitialObjects"] := 
  Module[{morphismAssociation, compositions, reducedMorphismAssociation, reducedCompositions, objectEquivalenceGraph, 
     morphismEquivalenceGraph, reducedIsomorphisms, reducedStrictInitialObjects}, 
    morphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, Length[objects]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ objects; reducedMorphismAssociation = 
      Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[arrows, arrowEquivalences], 
          quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[reducedCompositions = Select[Tuples[Normal[reducedMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[reducedMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          reducedMorphismAssociation = Association[Append[Normal[reducedMorphismAssociation], 
             compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ reducedCompositions, 
      Length[reduceObjects[objects, quiverObjectEquivalences]]]; reducedMorphismAssociation = 
      Association[Select[Normal[reducedMorphismAssociation], Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[reducedMorphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        reducedMorphismAssociation = Association[Append[Normal[reducedMorphismAssociation], 
           identitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[objects, quiverObjectEquivalences]; 
     objectEquivalenceGraph = Graph[Join[EdgeList[TransitiveClosureGraph[
          Graph[Apply[UndirectedEdge, Join[quiverObjectEquivalences, objectEquivalences], {1}]]]], 
        (UndirectedEdge[#1, #1] & ) /@ objects]]; morphismEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Join[arrowEquivalences, 
             morphismEquivalences], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ First /@ Normal[morphismAssociation]]]; 
     reducedIsomorphisms = {}; (Module[{morphism = #1, morphisms, isRetraction, isSection}, 
        morphisms = Select[Normal[morphismAssociation], Length[FindShortestPath[objectEquivalenceGraph, Last[Last[#1]], 
                First[Last[morphism]]]] > 0 && Length[FindShortestPath[objectEquivalenceGraph, First[Last[#1]], 
                Last[Last[morphism]]]] > 0 & ]; isRetraction = False; isSection = False; 
         (If[morphism === (identitySymbol[#1] -> DirectedEdge[#1, #1]), isRetraction = True] & ) /@ objects; 
         (If[morphism === (identitySymbol[#1] -> DirectedEdge[#1, #1]), isSection = True] & ) /@ objects; 
         (Module[{newMorphism = #1, equivalentObjects}, If[MemberQ[VertexList[morphismEquivalenceGraph], 
               compositionSymbol[First[morphism], First[newMorphism]]], equivalentObjects = Union[VertexComponent[
                  objectEquivalenceGraph, Last[Last[morphism]]], VertexComponent[objectEquivalenceGraph, 
                  First[Last[newMorphism]]]]; (If[MemberQ[VertexList[morphismEquivalenceGraph], identitySymbol[#1]], 
                  If[Length[FindShortestPath[morphismEquivalenceGraph, compositionSymbol[First[morphism], 
                       First[newMorphism]], identitySymbol[#1]]] > 0, isRetraction = True]] & ) /@ equivalentObjects]; 
             If[MemberQ[VertexList[morphismEquivalenceGraph], compositionSymbol[First[newMorphism], First[morphism]]], 
              equivalentObjects = Union[VertexComponent[objectEquivalenceGraph, First[Last[morphism]]], 
                 VertexComponent[objectEquivalenceGraph, Last[Last[newMorphism]]]]; 
               (If[MemberQ[VertexList[morphismEquivalenceGraph], identitySymbol[#1]], If[Length[FindShortestPath[
                      morphismEquivalenceGraph, compositionSymbol[First[newMorphism], First[morphism]], identitySymbol[
                       #1]]] > 0, isSection = True]] & ) /@ equivalentObjects]] & ) /@ morphisms; 
         reducedIsomorphisms = Append[reducedIsomorphisms, First[morphism] -> isRetraction && isSection]] & ) /@ 
      Normal[reduceArrowsFinal[reduceArrowsInitial[reducedMorphismAssociation, morphismEquivalences], 
        objectEquivalences]]; reducedStrictInitialObjects = {}; 
     (Module[{object = #1, morphisms1, morphisms2, isStrictInitialObject}, 
        morphisms1 = Select[Normal[reduceArrowsFinal[reduceArrowsInitial[reducedMorphismAssociation, 
              morphismEquivalences], objectEquivalences]], First[Last[#1]] === object & ]; 
         morphisms2 = Select[Normal[Association[reducedIsomorphisms]], 
           MemberQ[First /@ Select[Normal[reduceArrowsFinal[reduceArrowsInitial[reducedMorphismAssociation, 
                  morphismEquivalences], objectEquivalences]], Last[Last[#1]] === object & ], #1] & ]; 
         isStrictInitialObject = True; (Module[{newObject = #1}, If[Length[Select[morphisms1, 
                Last[Last[#1]] === newObject & ]] != 1, isStrictInitialObject = False]] & ) /@ 
          reduceObjects[reduceObjects[objects, quiverObjectEquivalences], objectEquivalences]; 
         (If[Last[#1] === False, isStrictInitialObject = False] & ) /@ morphisms2; reducedStrictInitialObjects = 
          Append[reducedStrictInitialObjects, object -> isStrictInitialObject]] & ) /@ 
      reduceObjects[reduceObjects[objects, quiverObjectEquivalences], objectEquivalences]; 
     Association[reducedStrictInitialObjects]] /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["TerminalObjects"] := 
  Module[{morphismAssociation, compositions, terminalObjects}, 
    morphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, Length[objects]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ objects; terminalObjects = {}; 
     (Module[{object = #1, morphisms, isTerminalObject}, morphisms = Select[Normal[morphismAssociation], 
           Last[Last[#1]] === object & ]; isTerminalObject = True; 
         (Module[{newObject = #1}, If[Length[Select[morphisms, First[Last[#1]] === newObject & ]] != 1, 
             isTerminalObject = False]] & ) /@ objects; terminalObjects = Append[terminalObjects, 
           object -> isTerminalObject]] & ) /@ objects; Association[terminalObjects]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["ReducedTerminalObjects"] := 
  Module[{morphismAssociation, compositions, reducedTerminalObjects}, 
    morphismAssociation = Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[arrows, arrowEquivalences], 
          quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, 
      Length[reduceObjects[objects, quiverObjectEquivalences]]]; morphismAssociation = 
      Association[Select[Normal[morphismAssociation], Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[objects, quiverObjectEquivalences]; reducedTerminalObjects = {}; 
     (Module[{object = #1, morphisms, isTerminalObject}, 
        morphisms = Select[Normal[reduceArrowsFinal[reduceArrowsInitial[morphismAssociation, morphismEquivalences], 
             objectEquivalences]], Last[Last[#1]] === object & ]; isTerminalObject = True; 
         (Module[{newObject = #1}, If[Length[Select[morphisms, First[Last[#1]] === newObject & ]] != 1, 
             isTerminalObject = False]] & ) /@ reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
           objectEquivalences]; reducedTerminalObjects = Append[reducedTerminalObjects, 
           object -> isTerminalObject]] & ) /@ reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
       objectEquivalences]; Association[reducedTerminalObjects]] /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["StrictTerminalObjects"] := 
  Module[{morphismAssociation, compositions, objectEquivalenceGraph, morphismEquivalenceGraph, isomorphisms, 
     strictTerminalObjects}, morphismAssociation = Association[Select[Normal[arrows], 
        First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, Length[objects]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ objects; objectEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Join[quiverObjectEquivalences, 
             objectEquivalences], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ objects]]; 
     morphismEquivalenceGraph = Graph[Join[EdgeList[TransitiveClosureGraph[
          Graph[Apply[UndirectedEdge, Join[arrowEquivalences, morphismEquivalences], {1}]]]], 
        (UndirectedEdge[#1, #1] & ) /@ First /@ Normal[morphismAssociation]]]; isomorphisms = {}; 
     (Module[{morphism = #1, morphisms, isRetraction, isSection}, 
        morphisms = Select[Normal[morphismAssociation], Length[FindShortestPath[objectEquivalenceGraph, Last[Last[#1]], 
                First[Last[morphism]]]] > 0 && Length[FindShortestPath[objectEquivalenceGraph, First[Last[#1]], 
                Last[Last[morphism]]]] > 0 & ]; isRetraction = False; isSection = False; 
         (If[morphism === (identitySymbol[#1] -> DirectedEdge[#1, #1]), isRetraction = True] & ) /@ objects; 
         (If[morphism === (identitySymbol[#1] -> DirectedEdge[#1, #1]), isSection = True] & ) /@ objects; 
         (Module[{newMorphism = #1, equivalentObjects}, If[MemberQ[VertexList[morphismEquivalenceGraph], 
               compositionSymbol[First[morphism], First[newMorphism]]], equivalentObjects = Union[VertexComponent[
                  objectEquivalenceGraph, Last[Last[morphism]]], VertexComponent[objectEquivalenceGraph, 
                  First[Last[newMorphism]]]]; (If[MemberQ[VertexList[morphismEquivalenceGraph], identitySymbol[#1]], 
                  If[Length[FindShortestPath[morphismEquivalenceGraph, compositionSymbol[First[morphism], 
                       First[newMorphism]], identitySymbol[#1]]] > 0, isRetraction = True]] & ) /@ equivalentObjects]; 
             If[MemberQ[VertexList[morphismEquivalenceGraph], compositionSymbol[First[newMorphism], First[morphism]]], 
              equivalentObjects = Union[VertexComponent[objectEquivalenceGraph, First[Last[morphism]]], 
                 VertexComponent[objectEquivalenceGraph, Last[Last[newMorphism]]]]; 
               (If[MemberQ[VertexList[morphismEquivalenceGraph], identitySymbol[#1]], If[Length[FindShortestPath[
                      morphismEquivalenceGraph, compositionSymbol[First[newMorphism], First[morphism]], identitySymbol[
                       #1]]] > 0, isSection = True]] & ) /@ equivalentObjects]] & ) /@ morphisms; 
         isomorphisms = Append[isomorphisms = First[morphism] -> isRetraction && isSection]] & ) /@ 
      Normal[morphismAssociation]; strictTerminalObjects = {}; 
     (Module[{object = #1, morphisms1, morphisms2, isStrictTerminalObject}, 
        morphisms1 = Select[Normal[morphismAssociation], Last[Last[#1]] === object & ]; 
         morphisms2 = Select[Normal[Association[isomorphisms]], MemberQ[First /@ Select[Normal[morphismAssociation], 
               First[Last[#1]] === object & ], #1] & ]; isStrictTerminalObject = True; 
         (Module[{newObject = #1}, If[Length[Select[morphisms1, First[Last[#1]] === newObject & ]] != 1, 
             isStrictTerminalObject = False]] & ) /@ objects; 
         (If[Last[#1] === False, isStrictTerminalObject = False] & ) /@ morphisms2; strictTerminalObjects = 
          Append[strictTerminalObjects, object -> isStrictTerminalObject]] & ) /@ objects; 
     Association[strictTerminalObjects]] /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["ReducedStrictTerminalObjects"] := 
  Module[{morphismAssociation, compositions, reducedMorphismAssociation, reducedCompositions, objectEquivalenceGraph, 
     morphismEquivalenceGraph, reducedIsomorphisms, reducedStrictTerminalObjects}, 
    morphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, Length[objects]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ objects; reducedMorphismAssociation = 
      Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[arrows, arrowEquivalences], 
          quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[reducedCompositions = Select[Tuples[Normal[reducedMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[reducedMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          reducedMorphismAssociation = Association[Append[Normal[reducedMorphismAssociation], 
             compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ reducedCompositions, 
      Length[reduceObjects[objects, quiverObjectEquivalences]]]; reducedMorphismAssociation = 
      Association[Select[Normal[reducedMorphismAssociation], Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[reducedMorphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        reducedMorphismAssociation = Association[Append[Normal[reducedMorphismAssociation], 
           identitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[objects, quiverObjectEquivalences]; 
     objectEquivalenceGraph = Graph[Join[EdgeList[TransitiveClosureGraph[
          Graph[Apply[UndirectedEdge, Join[quiverObjectEquivalences, objectEquivalences], {1}]]]], 
        (UndirectedEdge[#1, #1] & ) /@ objects]]; morphismEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Join[arrowEquivalences, 
             morphismEquivalences], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ First /@ Normal[morphismAssociation]]]; 
     reducedIsomorphisms = {}; (Module[{morphism = #1, morphisms, isRetraction, isSection}, 
        morphisms = Select[Normal[morphismAssociation], Length[FindShortestPath[objectEquivalenceGraph, Last[Last[#1]], 
                First[Last[morphism]]]] > 0 && Length[FindShortestPath[objectEquivalenceGraph, First[Last[#1]], 
                Last[Last[morphism]]]] > 0 & ]; isRetraction = False; isSection = False; 
         (If[morphism === (identitySymbol[#1] -> DirectedEdge[#1, #1]), isRetraction = True] & ) /@ objects; 
         (If[morphism === (identitySymbol[#1] -> DirectedEdge[#1, #1]), isSection = True] & ) /@ objects; 
         (Module[{newMorphism = #1, equivalentObjects}, If[MemberQ[VertexList[morphismEquivalenceGraph], 
               compositionSymbol[First[morphism], First[newMorphism]]], equivalentObjects = Union[VertexComponent[
                  objectEquivalenceGraph, Last[Last[morphism]]], VertexComponent[objectEquivalenceGraph, 
                  First[Last[newMorphism]]]]; (If[MemberQ[VertexList[morphismEquivalenceGraph], identitySymbol[#1]], 
                  If[Length[FindShortestPath[morphismEquivalenceGraph, compositionSymbol[First[morphism], 
                       First[newMorphism]], identitySymbol[#1]]] > 0, isRetraction = True]] & ) /@ equivalentObjects]; 
             If[MemberQ[VertexList[morphismEquivalenceGraph], compositionSymbol[First[newMorphism], First[morphism]]], 
              equivalentObjects = Union[VertexComponent[objectEquivalenceGraph, First[Last[morphism]]], 
                 VertexComponent[objectEquivalenceGraph, Last[Last[newMorphism]]]]; 
               (If[MemberQ[VertexList[morphismEquivalenceGraph], identitySymbol[#1]], If[Length[FindShortestPath[
                      morphismEquivalenceGraph, compositionSymbol[First[newMorphism], First[morphism]], identitySymbol[
                       #1]]] > 0, isSection = True]] & ) /@ equivalentObjects]] & ) /@ morphisms; 
         reducedIsomorphisms = Append[reducedIsomorphisms, First[morphism] -> isRetraction && isSection]] & ) /@ 
      Normal[reduceArrowsFinal[reduceArrowsInitial[reducedMorphismAssociation, morphismEquivalences], 
        objectEquivalences]]; reducedStrictTerminalObjects = {}; 
     (Module[{object = #1, morphisms1, morphisms2, isStrictTerminalObject}, 
        morphisms1 = Select[Normal[reduceArrowsFinal[reduceArrowsInitial[reducedMorphismAssociation, 
              morphismEquivalences], objectEquivalences]], Last[Last[#1]] === object & ]; 
         morphisms2 = Select[Normal[Association[reducedIsomorphisms]], 
           MemberQ[First /@ Select[Normal[reduceArrowsFinal[reduceArrowsInitial[reducedMorphismAssociation, 
                  morphismEquivalences], objectEquivalences]], First[Last[#1]] === object & ], #1] & ]; 
         isStrictTerminalObject = True; (Module[{newObject = #1}, If[Length[Select[morphisms1, 
                First[Last[#1]] === newObject & ]] != 1, isStrictTerminalObject = False]] & ) /@ 
          reduceObjects[reduceObjects[objects, quiverObjectEquivalences], objectEquivalences]; 
         (If[Last[#1] === False, isStrictTerminalObject = False] & ) /@ morphisms2; reducedStrictTerminalObjects = 
          Append[reducedStrictTerminalObjects, object -> isStrictTerminalObject]] & ) /@ 
      reduceObjects[reduceObjects[objects, quiverObjectEquivalences], objectEquivalences]; 
     Association[reducedStrictTerminalObjects]] /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["ZeroObjects"] := Module[{morphismAssociation, compositions, zeroObjects}, 
    morphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, Length[objects]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ objects; zeroObjects = {}; 
     (Module[{object = #1, morphisms1, morphisms2, isInitialObject, isTerminalObject}, 
        morphisms1 = Select[Normal[morphismAssociation], First[Last[#1]] === object & ]; 
         morphisms2 = Select[Normal[morphismAssociation], Last[Last[#1]] === object & ]; isInitialObject = True; 
         (Module[{newObject = #1}, If[Length[Select[morphisms1, Last[Last[#1]] === newObject & ]] != 1, 
             isInitialObject = False]] & ) /@ objects; isTerminalObject = True; 
         (Module[{newObject = #1}, If[Length[Select[morphisms2, First[Last[#1]] === newObject & ]] != 1, 
             isTerminalObject = False]] & ) /@ objects; zeroObjects = Append[zeroObjects, 
           object -> isInitialObject && isTerminalObject]] & ) /@ objects; Association[zeroObjects]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["ReducedZeroObjects"] := 
  Module[{morphismAssociation, compositions, reducedZeroObjects}, 
    morphismAssociation = Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[arrows, arrowEquivalences], 
          quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, 
      Length[reduceObjects[objects, quiverObjectEquivalences]]]; morphismAssociation = 
      Association[Select[Normal[morphismAssociation], Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[objects, quiverObjectEquivalences]; reducedZeroObjects = {}; 
     (Module[{object = #1, morphisms1, morphisms2, isInitialObject, isTerminalObject}, 
        morphisms1 = Select[Normal[reduceArrowsFinal[reduceArrowsInitial[morphismAssociation, morphismEquivalences], 
             objectEquivalences]], First[Last[#1]] === object & ]; morphisms2 = 
          Select[Normal[reduceArrowsFinal[reduceArrowsInitial[morphismAssociation, morphismEquivalences], 
             objectEquivalences]], Last[Last[#1]] === object & ]; isInitialObject = True; 
         (Module[{newObject = #1}, If[Length[Select[morphisms1, Last[Last[#1]] === newObject & ]] != 1, 
             isInitialObject = False]] & ) /@ reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
           objectEquivalences]; isTerminalObject = True; 
         (Module[{newObject = #1}, If[Length[Select[morphisms2, First[Last[#1]] === newObject & ]] != 1, 
             isTerminalObject = False]] & ) /@ reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
           objectEquivalences]; reducedZeroObjects = Append[reducedZeroObjects, 
           object -> isInitialObject && isTerminalObject]] & ) /@ 
      reduceObjects[reduceObjects[objects, quiverObjectEquivalences], objectEquivalences]; 
     Association[reducedZeroObjects]] /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["StrictZeroObjects"] := 
  Module[{morphismAssociation, compositions, objectEquivalenceGraph, morphismEquivalenceGraph, isomorphisms, 
     strictZeroObjects}, morphismAssociation = Association[Select[Normal[arrows], 
        First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, Length[objects]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ objects; objectEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Join[quiverObjectEquivalences, 
             objectEquivalences], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ objects]]; 
     morphismEquivalenceGraph = Graph[Join[EdgeList[TransitiveClosureGraph[
          Graph[Apply[UndirectedEdge, Join[arrowEquivalences, morphismEquivalences], {1}]]]], 
        (UndirectedEdge[#1, #1] & ) /@ First /@ Normal[morphismAssociation]]]; isomorphisms = {}; 
     (Module[{morphism = #1, morphisms, isRetraction, isSection}, 
        morphisms = Select[Normal[morphismAssociation], Length[FindShortestPath[objectEquivalenceGraph, Last[Last[#1]], 
                First[Last[morphism]]]] > 0 && Length[FindShortestPath[objectEquivalenceGraph, First[Last[#1]], 
                Last[Last[morphism]]]] > 0 & ]; isRetraction = False; isSection = False; 
         (If[morphism === (identitySymbol[#1] -> DirectedEdge[#1, #1]), isRetraction = True] & ) /@ objects; 
         (If[morphism === (identitySymbol[#1] -> DirectedEdge[#1, #1]), isSection = True] & ) /@ objects; 
         (Module[{newMorphism = #1, equivalentObjects}, If[MemberQ[VertexList[morphismEquivalenceGraph], 
               compositionSymbol[First[morphism], First[newMorphism]]], equivalentObjects = Union[VertexComponent[
                  objectEquivalenceGraph, Last[Last[morphism]]], VertexComponent[objectEquivalenceGraph, 
                  First[Last[newMorphism]]]]; (If[MemberQ[VertexList[morphismEquivalenceGraph], identitySymbol[#1]], 
                  If[Length[FindShortestPath[morphismEquivalenceGraph, compositionSymbol[First[morphism], 
                       First[newMorphism]], identitySymbol[#1]]] > 0, isRetraction = True]] & ) /@ equivalentObjects]; 
             If[MemberQ[VertexList[morphismEquivalenceGraph], compositionSymbol[First[newMorphism], First[morphism]]], 
              equivalentObjects = Union[VertexComponent[objectEquivalenceGraph, First[Last[morphism]]], 
                 VertexComponent[objectEquivalenceGraph, Last[Last[newMorphism]]]]; 
               (If[MemberQ[VertexList[morphismEquivalenceGraph], identitySymbol[#1]], If[Length[FindShortestPath[
                      morphismEquivalenceGraph, compositionSymbol[First[newMorphism], First[morphism]], identitySymbol[
                       #1]]] > 0, isSection = True]] & ) /@ equivalentObjects]] & ) /@ morphisms; 
         isomorphisms = Append[isomorphisms, First[morphism] -> isRetraction && isSection]] & ) /@ 
      Normal[morphismAssociation]; strictZeroObjects = {}; 
     (Module[{object = #1, morphisms1, morphisms2, morphisms3, morphisms4, isStrictInitialObject, 
         isStrictTerminalObject}, morphisms1 = Select[Normal[morphismAssociation], First[Last[#1]] === object & ]; 
         morphisms2 = Select[Normal[Association[isomorphisms]], MemberQ[First /@ Select[Normal[morphismAssociation], 
               Last[Last[#1]] === object & ], #1] & ]; isStrictInitialObject = True; 
         (Module[{newObject = #1}, If[Length[Select[morphisms1, Last[Last[#1]] === newObject & ]] != 1, 
             isStrictInitialObject = False]] & ) /@ objects; 
         (If[Last[#1] === False, isStrictInitialObject = False] & ) /@ morphisms2; 
         morphisms3 = Select[Normal[morphismAssociation], Last[Last[#1]] === object & ]; 
         morphisms4 = Select[Normal[Association[isomorphisms]], MemberQ[First /@ Select[Normal[morphismAssociation], 
               First[Last[#1]] === object & ], #1] & ]; isStrictTerminalObject = True; 
         (Module[{newObject = #1}, If[Length[Select[morphisms3, First[Last[#1]] === newObject & ]] != 1, 
             isStrictTerminalObject = False]] & ) /@ objects; 
         (If[Last[#1] === False, isStrictTerminalObject = False] & ) /@ morphisms4; 
         strictZeroObjects = Append[strictZeroObjects, object -> isStrictInitialObject && isStrictTerminalObject]] & ) /@ 
      objects; Association[strictZeroObjects]] /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["ReducedStrictZeroObjects"] := 
  Module[{morphismAssociation, compositions, reducedMorphismAssociation, reducedCompositions, objectEquivalenceGraph, 
     morphismEquivalenceGraph, reducedIsomorphisms, reducedStrictZeroObjects}, 
    morphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, Length[objects]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ objects; reducedMorphismAssociation = 
      Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[arrows, arrowEquivalences], 
          quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[reducedCompositions = Select[Tuples[Normal[reducedMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[reducedMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          reducedMorphismAssociation = Association[Append[Normal[reducedMorphismAssociation], 
             compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ reducedCompositions, 
      Length[reduceObjects[objects, quiverObjectEquivalences]]]; reducedMorphismAssociation = 
      Association[Select[Normal[reducedMorphismAssociation], Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[reducedMorphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        reducedMorphismAssociation = Association[Append[Normal[reducedMorphismAssociation], 
           identitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[objects, quiverObjectEquivalences]; 
     objectEquivalenceGraph = Graph[Join[EdgeList[TransitiveClosureGraph[
          Graph[Apply[UndirectedEdge, Join[quiverObjectEquivalences, objectEquivalences], {1}]]]], 
        (UndirectedEdge[#1, #1] & ) /@ objects]]; morphismEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Join[arrowEquivalences, 
             morphismEquivalences], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ First /@ Normal[morphismAssociation]]]; 
     reducedIsomorphisms = {}; (Module[{morphism = #1, morphisms, isRetraction, isSection}, 
        morphisms = Select[Normal[morphismAssociation], Length[FindShortestPath[objectEquivalenceGraph, Last[Last[#1]], 
                First[Last[morphism]]]] > 0 && Length[FindShortestPath[objectEquivalenceGraph, First[Last[#1]], 
                Last[Last[morphism]]]] > 0 & ]; isRetraction = False; isSection = False; 
         (If[morphism === (identitySymbol[#1] -> DirectedEdge[#1, #1]), isRetraction = True] & ) /@ objects; 
         (If[morphism === (identitySymbol[#1] -> DirectedEdge[#1, #1]), isSection = True] & ) /@ objects; 
         (Module[{newMorphism = #1, equivalentObjects}, If[MemberQ[VertexList[morphismEquivalenceGraph], 
               compositionSymbol[First[morphism], First[newMorphism]]], equivalentObjects = Union[VertexComponent[
                  objectEquivalenceGraph, Last[Last[morphism]]], VertexComponent[objectEquivalenceGraph, 
                  First[Last[newMorphism]]]]; (If[MemberQ[VertexList[morphismEquivalenceGraph], identitySymbol[#1]], 
                  If[Length[FindShortestPath[morphismEquivalenceGraph, compositionSymbol[First[morphism], 
                       First[newMorphism]], identitySymbol[#1]]] > 0, isRetraction = True]] & ) /@ equivalentObjects]; 
             If[MemberQ[VertexList[morphismEquivalenceGraph], compositionSymbol[First[newMorphism], First[morphism]]], 
              equivalentObjects = Union[VertexComponent[objectEquivalenceGraph, First[Last[morphism]]], 
                 VertexComponent[objectEquivalenceGraph, Last[Last[newMorphism]]]]; 
               (If[MemberQ[VertexList[morphismEquivalenceGraph], identitySymbol[#1]], If[Length[FindShortestPath[
                      morphismEquivalenceGraph, compositionSymbol[First[newMorphism], First[morphism]], identitySymbol[
                       #1]]] > 0, isSection = True]] & ) /@ equivalentObjects]] & ) /@ morphisms; 
         reducedIsomorphisms = Append[reducedIsomorphisms, First[morphism] -> isRetraction && isSection]] & ) /@ 
      Normal[reduceArrowsFinal[reduceArrowsInitial[reducedMorphismAssociation, morphismEquivalences], 
        objectEquivalences]]; reducedStrictZeroObjects = {}; 
     (Module[{object = #1, morphisms1, morphisms2, morphisms3, morphisms4, isStrictInitialObject, 
         isStrictTerminalObject}, morphisms1 = Select[Normal[reduceArrowsFinal[reduceArrowsInitial[
              reducedMorphismAssociation, morphismEquivalences], objectEquivalences]], First[Last[#1]] === object & ]; 
         morphisms2 = Select[Normal[Association[reducedIsomorphisms]], 
           MemberQ[First /@ Select[Normal[reduceArrowsFinal[reduceArrowsInitial[reducedMorphismAssociation, 
                  morphismEquivalences], objectEquivalences]], Last[Last[#1]] === object & ], #1] & ]; 
         isStrictInitialObject = True; (Module[{newObject = #1}, If[Length[Select[morphisms1, 
                Last[Last[#1]] === newObject & ]] != 1, isStrictInitialObject = False]] & ) /@ 
          reduceObjects[reduceObjects[objects, quiverObjectEquivalences], objectEquivalences]; 
         (If[Last[#1] === False, isStrictInitialObject = False] & ) /@ morphisms2; 
         morphisms3 = Select[Normal[reduceArrowsFinal[reduceArrowsInitial[reducedMorphismAssociation, 
              morphismEquivalences], objectEquivalences]], Last[Last[#1]] === object & ]; 
         morphisms4 = Select[Normal[Association[reducedIsomorphisms]], 
           MemberQ[First /@ Select[Normal[reduceArrowsFinal[reduceArrowsInitial[reducedMorphismAssociation, 
                  morphismEquivalences], objectEquivalences]], First[Last[#1]] === object & ], #1] & ]; 
         isStrictTerminalObject = True; (Module[{newObject = #1}, If[Length[Select[morphisms3, 
                First[Last[#1]] === newObject & ]] != 1, isStrictTerminalObject = False]] & ) /@ 
          reduceObjects[reduceObjects[objects, quiverObjectEquivalences], objectEquivalences]; 
         (If[Last[#1] === False, isStrictTerminalObject = False] & ) /@ morphisms4; reducedStrictZeroObjects = 
          Append[reducedStrictZeroObjects, object -> isStrictInitialObject && isStrictTerminalObject]] & ) /@ 
      reduceObjects[reduceObjects[objects, quiverObjectEquivalences], objectEquivalences]; 
     Association[reducedStrictZeroObjects]] /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["PointedCategoryQ"] := 
  Module[{morphismAssociation, compositions, reducedZeroObjects}, 
    morphismAssociation = Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[arrows, arrowEquivalences], 
          quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, 
      Length[reduceObjects[objects, quiverObjectEquivalences]]]; morphismAssociation = 
      Association[Select[Normal[morphismAssociation], Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[objects, quiverObjectEquivalences]; reducedZeroObjects = {}; 
     (Module[{object = #1, morphisms1, morphisms2, isInitialObject, isTerminalObject}, 
        morphisms1 = Select[Normal[reduceArrowsFinal[reduceArrowsInitial[morphismAssociation, morphismEquivalences], 
             objectEquivalences]], First[Last[#1]] === object & ]; morphisms2 = 
          Select[Normal[reduceArrowsFinal[reduceArrowsInitial[morphismAssociation, morphismEquivalences], 
             objectEquivalences]], Last[Last[#1]] === object & ]; isInitialObject = True; 
         (Module[{newObject = #1}, If[Length[Select[morphisms1, Last[Last[#1]] === newObject & ]] != 1, 
             isInitialObject = False]] & ) /@ reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
           objectEquivalences]; isTerminalObject = True; 
         (Module[{newObject = #1}, If[Length[Select[morphisms2, First[Last[#1]] === newObject & ]] != 1, 
             isTerminalObject = False]] & ) /@ reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
           objectEquivalences]; reducedZeroObjects = Append[reducedZeroObjects, 
           object -> isInitialObject && isTerminalObject]] & ) /@ 
      reduceObjects[reduceObjects[objects, quiverObjectEquivalences], objectEquivalences]; 
     Or @@ Last /@ Normal[Association[reducedZeroObjects]]] /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["ConstantMorphisms"] := 
  Module[{morphismAssociation, compositions, objectEquivalenceGraph, morphismEquivalenceGraph, constantMorphisms}, 
    morphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, Length[objects]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ objects; objectEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Join[quiverObjectEquivalences, 
             objectEquivalences], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ objects]]; 
     morphismEquivalenceGraph = Graph[Join[EdgeList[TransitiveClosureGraph[
          Graph[Apply[UndirectedEdge, Join[arrowEquivalences, morphismEquivalences], {1}]]]], 
        (UndirectedEdge[#1, #1] & ) /@ First /@ Normal[morphismAssociation]]]; constantMorphisms = {}; 
     (Module[{morphism = #1, morphismPairs, isConstantMorphism}, 
        morphismPairs = Tuples[Select[Normal[morphismAssociation], Length[FindShortestPath[objectEquivalenceGraph, 
                Last[Last[#1]], First[Last[morphism]]]] > 0 & ], 2]; isConstantMorphism = True; 
         (If[Length[FindShortestPath[objectEquivalenceGraph, First[Last[First[#1]]], First[Last[Last[#1]]]]] > 0, 
            If[MemberQ[VertexList[morphismEquivalenceGraph], First[First[#1]]] && MemberQ[VertexList[
                morphismEquivalenceGraph], First[Last[#1]]], If[Length[FindShortestPath[morphismEquivalenceGraph, 
                 First[First[#1]], First[Last[#1]]]] == 0, If[MemberQ[VertexList[morphismEquivalenceGraph], 
                 compositionSymbol[First[morphism], First[First[#1]]]] && MemberQ[VertexList[morphismEquivalenceGraph], 
                 compositionSymbol[First[morphism], First[Last[#1]]]], If[Length[FindShortestPath[
                   morphismEquivalenceGraph, compositionSymbol[First[morphism], First[First[#1]]], compositionSymbol[
                    First[morphism], First[Last[#1]]]]] == 0, isConstantMorphism = False], isConstantMorphism = 
                False]]]] & ) /@ morphismPairs; constantMorphisms = Append[constantMorphisms, 
           First[morphism] -> isConstantMorphism]] & ) /@ Normal[morphismAssociation]; Association[constantMorphisms]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["ReducedConstantMorphisms"] := 
  Module[{morphismAssociation, compositions, reducedMorphismAssociation, reducedCompositions, objectEquivalenceGraph, 
     morphismEquivalenceGraph, reducedConstantMorphisms}, 
    morphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, Length[objects]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ objects; reducedMorphismAssociation = 
      Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[arrows, arrowEquivalences], 
          quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[reducedCompositions = Select[Tuples[Normal[reducedMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[reducedMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          reducedMorphismAssociation = Association[Append[Normal[reducedMorphismAssociation], 
             compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ reducedCompositions, 
      Length[reduceObjects[objects, quiverObjectEquivalences]]]; reducedMorphismAssociation = 
      Association[Select[Normal[reducedMorphismAssociation], Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[reducedMorphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        reducedMorphismAssociation = Association[Append[Normal[reducedMorphismAssociation], 
           identitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[objects, quiverObjectEquivalences]; 
     objectEquivalenceGraph = Graph[Join[EdgeList[TransitiveClosureGraph[
          Graph[Apply[UndirectedEdge, Join[quiverObjectEquivalences, objectEquivalences], {1}]]]], 
        (UndirectedEdge[#1, #1] & ) /@ objects]]; morphismEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Join[arrowEquivalences, 
             morphismEquivalences], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ First /@ Normal[morphismAssociation]]]; 
     reducedConstantMorphisms = {}; (Module[{morphism = #1, morphismPairs, isConstantMorphism}, 
        morphismPairs = Tuples[Select[Normal[morphismAssociation], Length[FindShortestPath[objectEquivalenceGraph, 
                Last[Last[#1]], First[Last[morphism]]]] > 0 & ], 2]; isConstantMorphism = True; 
         (If[Length[FindShortestPath[objectEquivalenceGraph, First[Last[First[#1]]], First[Last[Last[#1]]]]] > 0, 
            If[MemberQ[VertexList[morphismEquivalenceGraph], First[First[#1]]] && MemberQ[VertexList[
                morphismEquivalenceGraph], First[Last[#1]]], If[Length[FindShortestPath[morphismEquivalenceGraph, 
                 First[First[#1]], First[Last[#1]]]] == 0, If[MemberQ[VertexList[morphismEquivalenceGraph], 
                 compositionSymbol[First[morphism], First[First[#1]]]] && MemberQ[VertexList[morphismEquivalenceGraph], 
                 compositionSymbol[First[morphism], First[Last[#1]]]], If[Length[FindShortestPath[
                   morphismEquivalenceGraph, compositionSymbol[First[morphism], First[First[#1]]], compositionSymbol[
                    First[morphism], First[Last[#1]]]]] == 0, isConstantMorphism = False], isConstantMorphism = 
                False]]]] & ) /@ morphismPairs; reducedConstantMorphisms = Append[reducedConstantMorphisms, 
           First[morphism] -> isConstantMorphism]] & ) /@ 
      Normal[reduceArrowsFinal[reduceArrowsInitial[reducedMorphismAssociation, morphismEquivalences], 
        objectEquivalences]]; Association[reducedConstantMorphisms]] /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["CoconstantMorphisms"] := 
  Module[{morphismAssociation, compositions, objectEquivalenceGraph, morphismEquivalenceGraph, coconstantMorphisms}, 
    morphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, Length[objects]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ objects; objectEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Join[quiverObjectEquivalences, 
             objectEquivalences], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ objects]]; 
     morphismEquivalenceGraph = Graph[Join[EdgeList[TransitiveClosureGraph[
          Graph[Apply[UndirectedEdge, Join[arrowEquivalences, morphismEquivalences], {1}]]]], 
        (UndirectedEdge[#1, #1] & ) /@ First /@ Normal[morphismAssociation]]]; coconstantMorphisms = {}; 
     (Module[{morphism = #1, morphismPairs, isCoconstantMorphism}, 
        morphismPairs = Tuples[Select[Normal[morphismAssociation], Length[FindShortestPath[objectEquivalenceGraph, 
                First[Last[#1]], Last[Last[morphism]]]] > 0 & ], 2]; isCoconstantMorphism = True; 
         (If[Length[FindShortestPath[objectEquivalenceGraph, Last[Last[First[#1]]], Last[Last[Last[#1]]]]] > 0, 
            If[MemberQ[VertexList[morphismEquivalenceGraph], First[First[#1]]] && MemberQ[VertexList[
                morphismEquivalenceGraph], First[Last[#1]]], If[Length[FindShortestPath[morphismEquivalenceGraph, 
                 First[First[#1]], First[Last[#1]]]] == 0, If[MemberQ[VertexList[morphismEquivalenceGraph], 
                 compositionSymbol[First[First[#1]], First[morphism]]] && MemberQ[VertexList[morphismEquivalenceGraph], 
                 compositionSymbol[First[Last[#1]], First[morphism]]], If[Length[FindShortestPath[
                   morphismEquivalenceGraph, compositionSymbol[First[First[#1]], First[morphism]], compositionSymbol[
                    First[Last[#1]], First[morphism]]]] == 0, isCoconstantMorphism = False], isCoconstantMorphism = 
                False]]]] & ) /@ morphismPairs; coconstantMorphisms = Append[coconstantMorphisms, 
           First[morphism] -> isCoconstantMorphism]] & ) /@ Normal[morphismAssociation]; 
     Association[coconstantMorphisms]] /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["ReducedCoconstantMorphisms"] := 
  Module[{morphismAssociation, compositions, reducedMorphismAssociation, reducedCompositions, objectEquivalenceGraph, 
     morphismEquivalenceGraph, reducedCoconstantMorphisms}, 
    morphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, Length[objects]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ objects; reducedMorphismAssociation = 
      Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[arrows, arrowEquivalences], 
          quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[reducedCompositions = Select[Tuples[Normal[reducedMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[reducedMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          reducedMorphismAssociation = Association[Append[Normal[reducedMorphismAssociation], 
             compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ reducedCompositions, 
      Length[reduceObjects[objects, quiverObjectEquivalences]]]; reducedMorphismAssociation = 
      Association[Select[Normal[reducedMorphismAssociation], Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[reducedMorphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        reducedMorphismAssociation = Association[Append[Normal[reducedMorphismAssociation], 
           identitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[objects, quiverObjectEquivalences]; 
     objectEquivalenceGraph = Graph[Join[EdgeList[TransitiveClosureGraph[
          Graph[Apply[UndirectedEdge, Join[quiverObjectEquivalences, objectEquivalences], {1}]]]], 
        (UndirectedEdge[#1, #1] & ) /@ objects]]; morphismEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Join[arrowEquivalences, 
             morphismEquivalences], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ First /@ Normal[morphismAssociation]]]; 
     reducedCoconstantMorphisms = {}; (Module[{morphism = #1, morphismPairs, isCoconstantMorphism}, 
        morphismPairs = Tuples[Select[Normal[morphismAssociation], Length[FindShortestPath[objectEquivalenceGraph, 
                First[Last[#1]], Last[Last[morphism]]]] > 0 & ], 2]; isCoconstantMorphism = True; 
         (If[Length[FindShortestPath[objectEquivalenceGraph, Last[Last[First[#1]]], Last[Last[Last[#1]]]]] > 0, 
            If[MemberQ[VertexList[morphismEquivalenceGraph], First[First[#1]]] && MemberQ[VertexList[
                morphismEquivalenceGraph], First[Last[#1]]], If[Length[FindShortestPath[morphismEquivalenceGraph, 
                 First[First[#1]], First[Last[#1]]]] == 0, If[MemberQ[VertexList[morphismEquivalenceGraph], 
                 compositionSymbol[First[First[#1]], First[morphism]]] && MemberQ[VertexList[morphismEquivalenceGraph], 
                 compositionSymbol[First[Last[#1]], First[morphism]]], If[Length[FindShortestPath[
                   morphismEquivalenceGraph, compositionSymbol[First[First[#1]], First[morphism]], compositionSymbol[
                    First[Last[#1]], First[morphism]]]] == 0, isCoconstantMorphism = False], isCoconstantMorphism = 
                False]]]] & ) /@ morphismPairs; reducedCoconstantMorphisms = Append[reducedCoconstantMorphisms, 
           First[morphism] -> isCoconstantMorphism]] & ) /@ 
      Normal[reduceArrowsFinal[reduceArrowsInitial[reducedMorphismAssociation, morphismEquivalences], 
        objectEquivalences]]; Association[reducedCoconstantMorphisms]] /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["ZeroMorphisms"] := 
  Module[{morphismAssociation, compositions, objectEquivalenceGraph, morphismEquivalenceGraph, zeroMorphisms}, 
    morphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, Length[objects]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ objects; objectEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Join[quiverObjectEquivalences, 
             objectEquivalences], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ objects]]; 
     morphismEquivalenceGraph = Graph[Join[EdgeList[TransitiveClosureGraph[
          Graph[Apply[UndirectedEdge, Join[arrowEquivalences, morphismEquivalences], {1}]]]], 
        (UndirectedEdge[#1, #1] & ) /@ First /@ Normal[morphismAssociation]]]; zeroMorphisms = {}; 
     (Module[{morphism = #1, morphismPairs1, morphismPairs2, isConstantMorphism, isCoconstantMorphism}, 
        morphismPairs1 = Tuples[Select[Normal[morphismAssociation], Length[FindShortestPath[objectEquivalenceGraph, 
                Last[Last[#1]], First[Last[morphism]]]] > 0 & ], 2]; morphismPairs2 = 
          Tuples[Select[Normal[morphismAssociation], Length[FindShortestPath[objectEquivalenceGraph, First[Last[#1]], 
                Last[Last[morphism]]]] > 0 & ], 2]; isConstantMorphism = True; 
         (If[Length[FindShortestPath[objectEquivalenceGraph, First[Last[First[#1]]], First[Last[Last[#1]]]]] > 0, 
            If[MemberQ[VertexList[morphismEquivalenceGraph], First[First[#1]]] && MemberQ[VertexList[
                morphismEquivalenceGraph], First[Last[#1]]], If[Length[FindShortestPath[morphismEquivalenceGraph, 
                 First[First[#1]], First[Last[#1]]]] == 0, If[MemberQ[VertexList[morphismEquivalenceGraph], 
                 compositionSymbol[First[morphism], First[First[#1]]]] && MemberQ[VertexList[morphismEquivalenceGraph], 
                 compositionSymbol[First[morphism], First[Last[#1]]]], If[Length[FindShortestPath[
                   morphismEquivalenceGraph, compositionSymbol[First[morphism], First[First[#1]]], compositionSymbol[
                    First[morphism], First[Last[#1]]]]] == 0, isConstantMorphism = False], isConstantMorphism = 
                False]]]] & ) /@ morphismPairs1; isCoconstantMorphism = True; 
         (If[Length[FindShortestPath[objectEquivalenceGraph, Last[Last[First[#1]]], Last[Last[Last[#1]]]]] > 0, 
            If[MemberQ[VertexList[morphismEquivalenceGraph], First[First[#1]]] && MemberQ[VertexList[
                morphismEquivalenceGraph], First[Last[#1]]], If[Length[FindShortestPath[morphismEquivalenceGraph, 
                 First[First[#1]], First[Last[#1]]]] == 0, If[MemberQ[VertexList[morphismEquivalenceGraph], 
                 compositionSymbol[First[First[#1]], First[morphism]]] && MemberQ[VertexList[morphismEquivalenceGraph], 
                 compositionSymbol[First[Last[#1]], First[morphism]]], If[Length[FindShortestPath[
                   morphismEquivalenceGraph, compositionSymbol[First[First[#1]], First[morphism]], compositionSymbol[
                    First[Last[#1]], First[morphism]]]] == 0, isCoconstantMorphism = False], isCoconstantMorphism = 
                False]]]] & ) /@ morphismPairs2; zeroMorphisms = Append[zeroMorphisms, First[morphism] -> 
            isConstantMorphism && isCoconstantMorphism]] & ) /@ Normal[morphismAssociation]; 
     Association[zeroMorphisms]] /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["ReducedZeroMorphisms"] := 
  Module[{morphismAssociation, compositions, reducedMorphismAssociation, reducedCompositions, objectEquivalenceGraph, 
     morphismEquivalenceGraph, reducedZeroMorphisms}, 
    morphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, Length[objects]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ objects; reducedMorphismAssociation = 
      Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[arrows, arrowEquivalences], 
          quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[reducedCompositions = Select[Tuples[Normal[reducedMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[reducedMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          reducedMorphismAssociation = Association[Append[Normal[reducedMorphismAssociation], 
             compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ reducedCompositions, 
      Length[reduceObjects[objects, quiverObjectEquivalences]]]; reducedMorphismAssociation = 
      Association[Select[Normal[reducedMorphismAssociation], Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[reducedMorphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        reducedMorphismAssociation = Association[Append[Normal[reducedMorphismAssociation], 
           identitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[objects, quiverObjectEquivalences]; 
     objectEquivalenceGraph = Graph[Join[EdgeList[TransitiveClosureGraph[
          Graph[Apply[UndirectedEdge, Join[quiverObjectEquivalences, objectEquivalences], {1}]]]], 
        (UndirectedEdge[#1, #1] & ) /@ objects]]; morphismEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Join[arrowEquivalences, 
             morphismEquivalences], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ First /@ Normal[morphismAssociation]]]; 
     reducedZeroMorphisms = {}; (Module[{morphism = #1, morphismPairs1, morphismPairs2, isConstantMorphism, 
         isCoconstantMorphism}, morphismPairs1 = Tuples[Select[Normal[morphismAssociation], 
            Length[FindShortestPath[objectEquivalenceGraph, Last[Last[#1]], First[Last[morphism]]]] > 0 & ], 2]; 
         morphismPairs2 = Tuples[Select[Normal[morphismAssociation], Length[FindShortestPath[objectEquivalenceGraph, 
                First[Last[#1]], Last[Last[morphism]]]] > 0 & ], 2]; isConstantMorphism = True; 
         (If[Length[FindShortestPath[objectEquivalenceGraph, First[Last[First[#1]]], First[Last[Last[#1]]]]] > 0, 
            If[MemberQ[VertexList[morphismEquivalenceGraph], First[First[#1]]] && MemberQ[VertexList[
                morphismEquivalenceGraph], First[Last[#1]]], If[Length[FindShortestPath[morphismEquivalenceGraph, 
                 First[First[#1]], First[Last[#1]]]] == 0, If[MemberQ[VertexList[morphismEquivalenceGraph], 
                 compositionSymbol[First[morphism], First[First[#1]]]] && MemberQ[VertexList[morphismEquivalenceGraph], 
                 compositionSymbol[First[morphism], First[Last[#1]]]], If[Length[FindShortestPath[
                   morphismEquivalenceGraph, compositionSymbol[First[morphism], First[First[#1]]], compositionSymbol[
                    First[morphism], First[Last[#1]]]]] == 0, isConstantMorphism = False], isConstantMorphism = 
                False]]]] & ) /@ morphismPairs1; isCoconstantMorphism = True; 
         (If[Length[FindShortestPath[objectEquivalenceGraph, Last[Last[First[#1]]], Last[Last[Last[#1]]]]] > 0, 
            If[MemberQ[VertexList[morphismEquivalenceGraph], First[First[#1]]] && MemberQ[VertexList[
                morphismEquivalenceGraph], First[Last[#1]]], If[Length[FindShortestPath[morphismEquivalenceGraph, 
                 First[First[#1]], First[Last[#1]]]] == 0, If[MemberQ[VertexList[morphismEquivalenceGraph], 
                 compositionSymbol[First[First[#1]], First[morphism]]] && MemberQ[VertexList[morphismEquivalenceGraph], 
                 compositionSymbol[First[Last[#1]], First[morphism]]], If[Length[FindShortestPath[
                   morphismEquivalenceGraph, compositionSymbol[First[First[#1]], First[morphism]], compositionSymbol[
                    First[Last[#1]], First[morphism]]]] == 0, isCoconstantMorphism = False], isCoconstantMorphism = 
                False]]]] & ) /@ morphismPairs2; reducedZeroMorphisms = Append[reducedZeroMorphisms, 
           First[morphism] -> isConstantMorphism && isCoconstantMorphism]] & ) /@ 
      Normal[reduceArrowsFinal[reduceArrowsInitial[reducedMorphismAssociation, morphismEquivalences], 
        objectEquivalences]]; Association[reducedZeroMorphisms]] /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["DiscreteCategoryQ"] := 
  Module[{morphismAssociation, compositions}, 
    morphismAssociation = Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[arrows, arrowEquivalences], 
          quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, 
      Length[reduceObjects[objects, quiverObjectEquivalences]]]; morphismAssociation = 
      Association[Select[Normal[morphismAssociation], Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[objects, quiverObjectEquivalences]; 
     Length[reduceObjects[reduceObjects[objects, quiverObjectEquivalences], objectEquivalences]] == 
      Length[Normal[reduceArrowsFinal[reduceArrowsInitial[morphismAssociation, morphismEquivalences], 
         objectEquivalences]]]] /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["IndiscreteCategoryQ"] := 
  Module[{morphismAssociation, compositions, objectPairs, isIndiscreteCategory}, 
    morphismAssociation = Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[arrows, arrowEquivalences], 
          quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, 
      Length[reduceObjects[objects, quiverObjectEquivalences]]]; morphismAssociation = 
      Association[Select[Normal[morphismAssociation], Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[objects, quiverObjectEquivalences]; 
     objectPairs = Tuples[reduceObjects[reduceObjects[objects, quiverObjectEquivalences], objectEquivalences], 2]; 
     isIndiscreteCategory = True; 
     (Module[{objectPair = #1}, If[Length[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[morphismAssociation, 
               morphismEquivalences], objectEquivalences]], First[Last[#1]] === First[objectPair] && 
              Last[Last[#1]] === Last[objectPair] & ]] != 1, isIndiscreteCategory = False]] & ) /@ objectPairs; 
     isIndiscreteCategory] /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["BalancedCategoryQ"] := 
  Module[{morphismAssociation, compositions, reducedMorphismAssociation, reducedCompositions, objectEquivalenceGraph, 
     morphismEquivalenceGraph, reducedBimorphisms, reducedIsomorphisms, isBalancedCategory}, 
    morphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, Length[objects]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ objects; reducedMorphismAssociation = 
      Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[arrows, arrowEquivalences], 
          quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[reducedCompositions = Select[Tuples[Normal[reducedMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[reducedMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          reducedMorphismAssociation = Association[Append[Normal[reducedMorphismAssociation], 
             compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ reducedCompositions, 
      Length[reduceObjects[objects, quiverObjectEquivalences]]]; reducedMorphismAssociation = 
      Association[Select[Normal[reducedMorphismAssociation], Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[reducedMorphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        reducedMorphismAssociation = Association[Append[Normal[reducedMorphismAssociation], 
           identitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[objects, quiverObjectEquivalences]; 
     objectEquivalenceGraph = Graph[Join[EdgeList[TransitiveClosureGraph[
          Graph[Apply[UndirectedEdge, Join[quiverObjectEquivalences, objectEquivalences], {1}]]]], 
        (UndirectedEdge[#1, #1] & ) /@ objects]]; morphismEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Join[arrowEquivalences, 
             morphismEquivalences], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ First /@ Normal[morphismAssociation]]]; 
     reducedBimorphisms = {}; (Module[{morphism = #1, morphismPairs1, morphismPairs2, isMonomorphism, isEpimorphism}, 
        morphismPairs1 = Tuples[Select[Normal[morphismAssociation], Length[FindShortestPath[objectEquivalenceGraph, 
                Last[Last[#1]], First[Last[morphism]]]] > 0 & ], 2]; morphismPairs2 = 
          Tuples[Select[Normal[morphismAssociation], Length[FindShortestPath[objectEquivalenceGraph, First[Last[#1]], 
                Last[Last[morphism]]]] > 0 & ], 2]; isMonomorphism = True; 
         (If[MemberQ[VertexList[morphismEquivalenceGraph], compositionSymbol[First[morphism], First[First[#1]]]] && 
             MemberQ[VertexList[morphismEquivalenceGraph], compositionSymbol[First[morphism], First[Last[#1]]]], 
            If[Length[FindShortestPath[morphismEquivalenceGraph, compositionSymbol[First[morphism], First[First[#1]]], 
                compositionSymbol[First[morphism], First[Last[#1]]]]] > 0, 
             If[MemberQ[VertexList[morphismEquivalenceGraph], First[First[#1]]] && MemberQ[VertexList[
                 morphismEquivalenceGraph], First[Last[#1]]], If[Length[FindShortestPath[morphismEquivalenceGraph, 
                  First[First[#1]], First[Last[#1]]]] == 0, isMonomorphism = False], isMonomorphism = False]]] & ) /@ 
          morphismPairs1; isEpimorphism = True; (If[MemberQ[VertexList[morphismEquivalenceGraph], 
              compositionSymbol[First[First[#1]], First[morphism]]] && MemberQ[VertexList[morphismEquivalenceGraph], 
              compositionSymbol[First[Last[#1]], First[morphism]]], If[Length[FindShortestPath[morphismEquivalenceGraph, 
                compositionSymbol[First[First[#1]], First[morphism]], compositionSymbol[First[Last[#1]], 
                 First[morphism]]]] > 0, If[MemberQ[VertexList[morphismEquivalenceGraph], First[First[#1]]] && MemberQ[
                VertexList[morphismEquivalenceGraph], First[Last[#1]]], If[Length[FindShortestPath[
                  morphismEquivalenceGraph, First[First[#1]], First[Last[#1]]]] == 0, isEpimorphism = False], 
              isEpimorphism = False]]] & ) /@ morphismPairs2; reducedBimorphisms = Append[reducedBimorphisms, 
           First[morphism] -> isMonomorphism && isEpimorphism]] & ) /@ 
      Normal[reduceArrowsFinal[reduceArrowsInitial[reducedMorphismAssociation, morphismEquivalences], 
        objectEquivalences]]; reducedIsomorphisms = {}; 
     (Module[{morphism = #1, morphisms, isRetraction, isSection}, 
        morphisms = Select[Normal[morphismAssociation], Length[FindShortestPath[objectEquivalenceGraph, Last[Last[#1]], 
                First[Last[morphism]]]] > 0 && Length[FindShortestPath[objectEquivalenceGraph, First[Last[#1]], 
                Last[Last[morphism]]]] > 0 & ]; isRetraction = False; isSection = False; 
         (If[morphism === (identitySymbol[#1] -> DirectedEdge[#1, #1]), isRetraction = True] & ) /@ objects; 
         (If[morphism === (identitySymbol[#1] -> DirectedEdge[#1, #1]), isSection = True] & ) /@ objects; 
         (Module[{newMorphism = #1, equivalentObjects}, If[MemberQ[VertexList[morphismEquivalenceGraph], 
               compositionSymbol[First[morphism], First[newMorphism]]], equivalentObjects = Union[VertexComponent[
                  objectEquivalenceGraph, Last[Last[morphism]]], VertexComponent[objectEquivalenceGraph, 
                  First[Last[newMorphism]]]]; (If[MemberQ[VertexList[morphismEquivalenceGraph], identitySymbol[#1]], 
                  If[Length[FindShortestPath[morphismEquivalenceGraph, compositionSymbol[First[morphism], 
                       First[newMorphism]], identitySymbol[#1]]] > 0, isRetraction = True]] & ) /@ equivalentObjects]; 
             If[MemberQ[VertexList[morphismEquivalenceGraph], compositionSymbol[First[newMorphism], First[morphism]]], 
              equivalentObjects = Union[VertexComponent[objectEquivalenceGraph, First[Last[morphism]]], 
                 VertexComponent[objectEquivalenceGraph, Last[Last[newMorphism]]]]; 
               (If[MemberQ[VertexList[morphismEquivalenceGraph], identitySymbol[#1]], If[Length[FindShortestPath[
                      morphismEquivalenceGraph, compositionSymbol[First[newMorphism], First[morphism]], identitySymbol[
                       #1]]] > 0, isSection = True]] & ) /@ equivalentObjects]] & ) /@ morphisms; 
         reducedIsomorphisms = Append[reducedIsomorphisms, First[morphism] -> isRetraction && isSection]] & ) /@ 
      Normal[reduceArrowsFinal[reduceArrowsInitial[morphismAssociation, morphismEquivalences], objectEquivalences]]; 
     isBalancedCategory = True; (Module[{reducedBimorphism = #1}, If[Last[reducedBimorphism] === True, 
         If[Last[First[Select[reducedIsomorphisms, First[#1] === First[reducedBimorphism] & ]]] === False, 
          isBalancedCategory = False]]] & ) /@ reducedBimorphisms; isBalancedCategory] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["GroupoidQ"] := 
  Module[{morphismAssociation, compositions, objectEquivalenceGraph, morphismEquivalenceGraph, isomorphisms, 
     reducedMorphismAssociation, reducedCompositions}, 
    morphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, Length[objects]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ objects; objectEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Join[quiverObjectEquivalences, 
             objectEquivalences], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ objects]]; 
     morphismEquivalenceGraph = Graph[Join[EdgeList[TransitiveClosureGraph[
          Graph[Apply[UndirectedEdge, Join[arrowEquivalences, morphismEquivalences], {1}]]]], 
        (UndirectedEdge[#1, #1] & ) /@ First /@ Normal[morphismAssociation]]]; isomorphisms = {}; 
     (Module[{morphism = #1, morphisms, isRetraction, isSection}, 
        morphisms = Select[Normal[morphismAssociation], Length[FindShortestPath[objectEquivalenceGraph, Last[Last[#1]], 
                First[Last[morphism]]]] > 0 && Length[FindShortestPath[objectEquivalenceGraph, First[Last[#1]], 
                Last[Last[morphism]]]] > 0 & ]; isRetraction = False; isSection = False; 
         (If[morphism === (identitySymbol[#1] -> DirectedEdge[#1, #1]), isRetraction = True] & ) /@ objects; 
         (If[morphism === (identitySymbol[#1] -> DirectedEdge[#1, #1]), isSection = True] & ) /@ objects; 
         (Module[{newMorphism = #1, equivalentObjects}, If[MemberQ[VertexList[morphismEquivalenceGraph], 
               compositionSymbol[First[morphism], First[newMorphism]]], equivalentObjects = Union[VertexComponent[
                  objectEquivalenceGraph, Last[Last[morphism]]], VertexComponent[objectEquivalenceGraph, 
                  First[Last[newMorphism]]]]; (If[MemberQ[VertexList[morphismEquivalenceGraph], identitySymbol[#1]], 
                  If[Length[FindShortestPath[morphismEquivalenceGraph, compositionSymbol[First[morphism], 
                       First[newMorphism]], identitySymbol[#1]]] > 0, isRetraction = True]] & ) /@ equivalentObjects]; 
             If[MemberQ[VertexList[morphismEquivalenceGraph], compositionSymbol[First[newMorphism], First[morphism]]], 
              equivalentObjects = Union[VertexComponent[objectEquivalenceGraph, First[Last[morphism]]], 
                 VertexComponent[objectEquivalenceGraph, Last[Last[newMorphism]]]]; 
               (If[MemberQ[VertexList[morphismEquivalenceGraph], identitySymbol[#1]], If[Length[FindShortestPath[
                      morphismEquivalenceGraph, compositionSymbol[First[newMorphism], First[morphism]], identitySymbol[
                       #1]]] > 0, isSection = True]] & ) /@ equivalentObjects]] & ) /@ morphisms; 
         isomorphisms = Append[isomorphisms, First[morphism] -> isRetraction && isSection]] & ) /@ 
      Normal[morphismAssociation]; reducedMorphismAssociation = 
      Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[arrows, arrowEquivalences], 
          quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[reducedCompositions = Select[Tuples[Normal[reducedMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[reducedMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          reducedMorphismAssociation = Association[Append[Normal[reducedMorphismAssociation], 
             compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ reducedCompositions, 
      Length[reduceObjects[objects, quiverObjectEquivalences]]]; reducedMorphismAssociation = 
      Association[Select[Normal[reducedMorphismAssociation], Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[reducedMorphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        reducedMorphismAssociation = Association[Append[Normal[reducedMorphismAssociation], 
           identitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[objects, quiverObjectEquivalences]; 
     And @@ (Module[{reducedMorphism = #1}, If[Length[Select[isomorphisms, First[#1] === First[reducedMorphism] & ]] > 0, 
          Last[First[Select[isomorphisms, First[#1] === First[reducedMorphism] & ]]], False]] & ) /@ 
       Normal[reduceArrowsFinal[reduceArrowsInitial[reducedMorphismAssociation, morphismEquivalences], 
         objectEquivalences]]] /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["GroupoidEquations"] := 
  Module[{morphismAssociation, compositions, commutativityEquations}, 
    If[And @@ (Module[{arrow = #1}, Length[Select[Normal[arrows], DirectedEdge @@ Last[#1] === Reverse[DirectedEdge @@ 
                Last[arrow]] & ]] > 0] & ) /@ Normal[arrows], 
     morphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
      Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
          Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
        (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
             StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
            Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
               DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, Length[objects]]; 
      morphismAssociation = Association[Select[Normal[morphismAssociation], 
         Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == Length[DeleteDuplicates[
             Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
      (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
         morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
             DirectedEdge[#1, #1]]]] & ) /@ objects; commutativityEquations = 
       Flatten[(EdgeList[TransitiveReductionGraph[Graph[Apply[UndirectedEdge, Tuples[First /@ #1, 2], {1}]]]] /. 
           UndirectedEdge -> Equal & ) /@ Select[GatherBy[(First[#1] -> DirectedEdge @@ Last[#1] & ) /@ 
            Normal[morphismAssociation], Last], Length[#1] > 1 & ]]; 
      (If[MatchQ[First[#1], identitySymbol[x_]] || MatchQ[Last[#1], identitySymbol[x_]], #1, Reverse[#1]] & ) /@ 
       commutativityEquations, Indeterminate]] /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["ReducedGroupoidEquations"] := 
  Module[{morphismAssociation, compositions, commutativityEquations}, 
    If[And @@ (Module[{arrow = #1}, Length[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[reduceArrowsFinal[
                reduceArrowsInitial[arrows, arrowEquivalences], quiverObjectEquivalences], morphismEquivalences], 
              objectEquivalences]], DirectedEdge @@ Last[#1] === Reverse[DirectedEdge @@ Last[arrow]] & ]] > 0] & ) /@ 
       Normal[reduceArrowsFinal[reduceArrowsInitial[reduceArrowsFinal[reduceArrowsInitial[arrows, arrowEquivalences], 
           quiverObjectEquivalences], morphismEquivalences], objectEquivalences]], 
     morphismAssociation = Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[arrows, arrowEquivalences], 
           quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
      Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
          Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
        (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
             StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
            Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
               DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, 
       Length[reduceObjects[objects, quiverObjectEquivalences]]]; morphismAssociation = 
       Association[Select[Normal[morphismAssociation], Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
           Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
      (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
         morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
             DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[objects, quiverObjectEquivalences]; 
      commutativityEquations = Flatten[(EdgeList[TransitiveReductionGraph[Graph[Apply[UndirectedEdge, Tuples[First /@ #1, 
                2], {1}]]]] /. UndirectedEdge -> Equal & ) /@ 
         Select[GatherBy[(First[#1] -> DirectedEdge @@ Last[#1] & ) /@ Normal[reduceArrowsFinal[
              reduceArrowsInitial[morphismAssociation, morphismEquivalences], objectEquivalences]], Last], 
          Length[#1] > 1 & ]]; (If[MatchQ[First[#1], identitySymbol[x_]] || MatchQ[Last[#1], identitySymbol[x_]], #1, 
         Reverse[#1]] & ) /@ commutativityEquations, Indeterminate]] /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["FullLabeledGraph"] := 
  Module[{morphismAssociation, compositions}, 
    morphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, Length[objects]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ objects; EdgeTaggedGraph[objects, 
      (Labeled[DirectedEdge @@ Last[#1], Placed[First[#1], 0.5]] & ) /@ Normal[morphismAssociation], VertexSize -> 0.3, 
      VertexStyle -> Directive[Transparent, EdgeForm[None]], VertexLabels -> Placed["Name", Center], 
      VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
      EdgeStyle -> Directive[Black, Thick], GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["FullUnlabeledGraph"] := 
  Module[{morphismAssociation, compositions}, 
    morphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, Length[objects]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ objects; EdgeTaggedGraph[objects, (DirectedEdge @@ Last[#1] & ) /@ 
       Normal[morphismAssociation], VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], 
      VertexLabels -> Placed["Name", Center], VertexLabelStyle -> Directive[Bold, 20], 
      EdgeLabelStyle -> Directive[Bold, 20], EdgeStyle -> Directive[Black, Thick], 
      GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["ReducedLabeledGraph"] := 
  Module[{morphismAssociation, compositions}, 
    morphismAssociation = Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[arrows, arrowEquivalences], 
          quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, 
      Length[reduceObjects[objects, quiverObjectEquivalences]]]; morphismAssociation = 
      Association[Select[Normal[morphismAssociation], Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[objects, quiverObjectEquivalences]; 
     EdgeTaggedGraph[reduceObjects[reduceObjects[objects, quiverObjectEquivalences], objectEquivalences], 
      (Labeled[DirectedEdge @@ Last[#1], Placed[First[#1], 0.5]] & ) /@ 
       Normal[reduceArrowsFinal[reduceArrowsInitial[morphismAssociation, morphismEquivalences], objectEquivalences]], 
      VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], VertexLabels -> Placed["Name", Center], 
      VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
      EdgeStyle -> Directive[Black, Thick], GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["ReducedUnlabeledGraph"] := 
  Module[{morphismAssociation, compositions}, 
    morphismAssociation = Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[arrows, arrowEquivalences], 
          quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, 
      Length[reduceObjects[objects, quiverObjectEquivalences]]]; morphismAssociation = 
      Association[Select[Normal[morphismAssociation], Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[objects, quiverObjectEquivalences]; 
     EdgeTaggedGraph[reduceObjects[reduceObjects[objects, quiverObjectEquivalences], objectEquivalences], 
      (DirectedEdge @@ Last[#1] & ) /@ Normal[reduceArrowsFinal[reduceArrowsInitial[morphismAssociation, 
          morphismEquivalences], objectEquivalences]], VertexSize -> 0.3, 
      VertexStyle -> Directive[Transparent, EdgeForm[None]], VertexLabels -> Placed["Name", Center], 
      VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
      EdgeStyle -> Directive[Black, Thick], GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["SimpleLabeledGraph"] := 
  Module[{morphismAssociation, compositions}, 
    morphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, Length[objects]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     EdgeTaggedGraph[objects, (Labeled[DirectedEdge @@ Last[#1], Placed[First[#1], 0.5]] & ) /@ 
       Select[DeleteDuplicatesBy[Normal[morphismAssociation], DirectedEdge @@ Last[#1] & ], 
        First[Last[#1]] =!= Last[Last[#1]] & ], VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], 
      VertexLabels -> Placed["Name", Center], VertexLabelStyle -> Directive[Bold, 20], 
      EdgeLabelStyle -> Directive[Bold, 20], EdgeStyle -> Directive[Black, Thick], 
      GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["SimpleUnlabeledGraph"] := 
  Module[{morphismAssociation, compositions}, 
    morphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, Length[objects]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     EdgeTaggedGraph[objects, (DirectedEdge @@ Last[#1] & ) /@ Select[DeleteDuplicatesBy[Normal[morphismAssociation], 
         DirectedEdge @@ Last[#1] & ], First[Last[#1]] =!= Last[Last[#1]] & ], VertexSize -> 0.3, 
      VertexStyle -> Directive[Transparent, EdgeForm[None]], VertexLabels -> Placed["Name", Center], 
      VertexLabelStyle -> Directive[Bold, 20], EdgeStyle -> Directive[Black, Thick], 
      GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["ReducedSimpleLabeledGraph"] := 
  Module[{morphismAssociation, compositions}, 
    morphismAssociation = Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[arrows, arrowEquivalences], 
          quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, 
      Length[reduceObjects[objects, quiverObjectEquivalences]]]; morphismAssociation = 
      Association[Select[Normal[morphismAssociation], Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     EdgeTaggedGraph[reduceObjects[reduceObjects[objects, quiverObjectEquivalences], objectEquivalences], 
      (Labeled[DirectedEdge @@ Last[#1], Placed[First[#1], 0.5]] & ) /@ 
       Normal[reduceArrowsFinal[reduceArrowsInitial[Association[Select[DeleteDuplicatesBy[Normal[morphismAssociation], 
             DirectedEdge @@ Last[#1] & ], First[Last[#1]] =!= Last[Last[#1]] & ]], morphismEquivalences], 
         objectEquivalences]], VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], 
      VertexLabels -> Placed["Name", Center], VertexLabelStyle -> Directive[Bold, 20], 
      EdgeLabelStyle -> Directive[Bold, 20], EdgeStyle -> Directive[Black, Thick], 
      GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["ReducedSimpleUnlabeledGraph"] := 
  Module[{morphismAssociation, compositions}, 
    morphismAssociation = Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[arrows, arrowEquivalences], 
          quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, 
      Length[reduceObjects[objects, quiverObjectEquivalences]]]; morphismAssociation = 
      Association[Select[Normal[morphismAssociation], Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     EdgeTaggedGraph[reduceObjects[reduceObjects[objects, quiverObjectEquivalences], objectEquivalences], 
      (DirectedEdge @@ Last[#1] & ) /@ Normal[reduceArrowsFinal[reduceArrowsInitial[
          Association[Select[DeleteDuplicatesBy[Normal[morphismAssociation], DirectedEdge @@ Last[#1] & ], 
            First[Last[#1]] =!= Last[Last[#1]] & ]], morphismEquivalences], objectEquivalences]], VertexSize -> 0.3, 
      VertexStyle -> Directive[Transparent, EdgeForm[None]], VertexLabels -> Placed["Name", Center], 
      VertexLabelStyle -> Directive[Bold, 20], EdgeStyle -> Directive[Black, Thick], 
      GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["AssociationForm"] := 
  Association["Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> arrowEquivalences, 
       "Arrows" -> arrows, "ObjectEquivalences" -> quiverObjectEquivalences, "Objects" -> objects]], 
    "CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
    "ObjectEquivalences" -> objectEquivalences, "MorphismEquivalences" -> morphismEquivalences] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]["Properties"] := {"Objects", "ObjectCount", "MorphismAssociation", "MorphismNames", 
    "MorphismEdges", "MorphismCount", "ObjectEquivalences", "ObjectEquivalenceCount", "MorphismEquivalences", 
    "MorphismEquivalenceCount", "ReducedObjects", "ReducedObjectCount", "ReducedMorphismAssociation", 
    "ReducedMorphismNames", "ReducedMorphismEdges", "ReducedMorphismCount", "SimpleMorphismAssociation", 
    "SimpleMorphismNames", "SimpleMorphismEdges", "SimpleMorphismCount", "ReducedSimpleMorphismAssociation", 
    "ReducedSimpleMorphismNames", "ReducedSimpleMorphismEdges", "ReducedSimpleMorphismCount", "CompositionSymbol", 
    "IdentitySymbol", "DualCategory", "Quiver", "AssociativityEquations", "ReducedAssociativityEquations", 
    "IdentityEquations", "ReducedIdentityEquations", "CommutativeDiagramQ", "CommutativityEquations", 
    "ReducedCommutativityEquations", "Monomorphisms", "ReducedMonomorphisms", "Epimorphisms", "ReducedEpimorphisms", 
    "Bimorphisms", "ReducedBimorphisms", "Retractions", "ReducedRetractions", "LeftInverses", "ReducedLeftInverses", 
    "Sections", "ReducedSections", "RightInverses", "ReducedRightInverses", "Isomorphisms", "ReducedIsomorphisms", 
    "Inverses", "ReducedInverses", "Endomorphisms", "ReducedEndomorphisms", "Automorphisms", "ReducedAutomorphisms", 
    "InitialObjects", "ReducedInitialObjects", "StrictInitialObjects", "ReducedStrictInitialObjects", "TerminalObjects", 
    "ReducedTerminalObjects", "StrictTerminalObjects", "ReducedStrictTerminalObjects", "ZeroObjects", 
    "ReducedZeroObjects", "StrictZeroObjects", "ReducedStrictZeroObjects", "PointedCategoryQ", "ConstantMorphisms", 
    "ReducedConstantMorphisms", "CoconstantMorphisms", "ReducedCoconstantMorphisms", "ZeroMorphisms", 
    "ReducedZeroMorphisms", "DiscreteCategoryQ", "IndiscreteCategoryQ", "BalancedCategoryQ", "GroupoidQ", 
    "GroupoidEquations", "ReducedGroupoidEquations", "FullLabeledGraph", "FullUnlabeledGraph", "ReducedLabeledGraph", 
    "ReducedUnlabeledGraph", "SimpleLabeledGraph", "SimpleUnlabeledGraph", "ReducedSimpleLabeledGraph", 
    "ReducedSimpleUnlabeledGraph", "AssociationForm", "Properties"} /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory /: MakeBoxes[abstractCategory:AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, 
       "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> morphismEquivalences_List, 
       "ObjectEquivalences" -> objectEquivalences_List, "Quiver" -> (abstractQuiver_)[
         Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
          "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], format_] := 
   Module[{morphismAssociation, compositions, reducedMorphismAssociation, reducedCompositions, icon, commutativeDiagram, 
      objectCount, morphismCount, reducedObjectCount, reducedMorphismCount}, 
     morphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
      Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
          Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
        (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
             StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
            Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
               DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, Length[objects]]; 
      morphismAssociation = Association[Select[Normal[morphismAssociation], 
         Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == Length[DeleteDuplicates[
             Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
      (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
         morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
             DirectedEdge[#1, #1]]]] & ) /@ objects; reducedMorphismAssociation = 
       Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[arrows, arrowEquivalences], 
           quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
      Do[reducedCompositions = Select[Tuples[Normal[reducedMorphismAssociation], 2], 
          Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
        (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
              Normal[reducedMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                 First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
           reducedMorphismAssociation = Association[Append[Normal[reducedMorphismAssociation], 
              compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], 
                Last[Last[Last[#1]]]]]]] & ) /@ reducedCompositions, 
       Length[reduceObjects[objects, quiverObjectEquivalences]]]; reducedMorphismAssociation = 
       Association[Select[Normal[reducedMorphismAssociation], 
         Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == Length[DeleteDuplicates[
             Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
      (If[ !MemberQ[Normal[reducedMorphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
         reducedMorphismAssociation = Association[Append[Normal[reducedMorphismAssociation], 
            identitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[objects, quiverObjectEquivalences]; 
      icon = GraphPlot[EdgeTaggedGraph[objects, (DirectedEdge @@ Last[#1] & ) /@ Normal[morphismAssociation], 
         VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], EdgeShapeFunction -> 
          GraphElementData["ShortFilledArrow", "ArrowSize" -> 0.05], EdgeStyle -> Black, 
         GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]]; 
      commutativeDiagram = AllTrue[Normal[CountsBy[Normal[reduceArrowsFinal[reduceArrowsInitial[
             reducedMorphismAssociation, morphismEquivalences], objectEquivalences]], DirectedEdge @@ Last[#1] & ]], 
        Last[#1] == 1 & ]; objectCount = Length[objects]; morphismCount = Length[Normal[morphismAssociation]]; 
      reducedObjectCount = Length[reduceObjects[reduceObjects[objects, quiverObjectEquivalences], objectEquivalences]]; 
      reducedMorphismCount = Length[Normal[reduceArrowsFinal[reduceArrowsInitial[reducedMorphismAssociation, 
           morphismEquivalences], objectEquivalences]]]; BoxForm`ArrangeSummaryBox["AbstractCategory", abstractCategory, 
       icon, {{BoxForm`SummaryItem[{"Commutative Diagram: ", commutativeDiagram}]}, 
        {BoxForm`SummaryItem[{"Objects: ", objectCount}], BoxForm`SummaryItem[{"Morphisms: ", morphismCount}]}}, 
       {{BoxForm`SummaryItem[{"Reduced Objects: ", reducedObjectCount}], BoxForm`SummaryItem[
          {"Reduced Morphisms: ", reducedMorphismCount}]}}, format, "Interpretable" -> Automatic]] /; 
    SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[arrows_List] := AbstractCategory[Association["CompositionSymbol" -> CircleDot, 
    "IdentitySymbol" -> OverTilde, "MorphismEquivalences" -> {}, "ObjectEquivalences" -> {}, 
    "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> {}, 
       "Arrows" -> Association[(Subscript["\[FormalF]", ToString[#1]] -> arrows[[#1]] & ) /@ Range[Length[arrows]]], 
       "ObjectEquivalences" -> {}, "Objects" -> DeleteDuplicates[Flatten[Apply[List, arrows, {1}]]]]]]]
AbstractCategory[arrows_Association] := AbstractCategory[Association["CompositionSymbol" -> CircleDot, 
     "IdentitySymbol" -> OverTilde, "MorphismEquivalences" -> {}, "ObjectEquivalences" -> {}, 
     "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> {}, "Arrows" -> arrows, 
        "ObjectEquivalences" -> {}, "Objects" -> DeleteDuplicates[Flatten[Apply[List, Last /@ Normal[arrows], 
            {1}]]]]]]] /;  !KeyExistsQ[arrows, "CompositionSymbol"] &&  !KeyExistsQ[arrows, "IdentitySymbol"] && 
     !KeyExistsQ[arrows, "MorphismEquivalences"] &&  !KeyExistsQ[arrows, "ObjectEquivalences"] && 
     !KeyExistsQ[arrows, "Quiver"]
AbstractCategory[objects_List, arrows_List] := AbstractCategory[Association["CompositionSymbol" -> CircleDot, 
    "IdentitySymbol" -> OverTilde, "MorphismEquivalences" -> {}, "ObjectEquivalences" -> {}, 
    "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> {}, 
       "Arrows" -> Association[(Subscript["\[FormalF]", ToString[#1]] -> arrows[[#1]] & ) /@ Range[Length[arrows]]], 
       "ObjectEquivalences" -> {}, "Objects" -> objects]]]]
AbstractCategory[objects_List, arrows_Association] := 
  AbstractCategory[Association["CompositionSymbol" -> CircleDot, "IdentitySymbol" -> OverTilde, 
     "MorphismEquivalences" -> {}, "ObjectEquivalences" -> {}, "Quiver" -> ResourceFunction["AbstractQuiver"][
       Association["ArrowEquivalences" -> {}, "Arrows" -> arrows, "ObjectEquivalences" -> {}, "Objects" -> objects]]]] /; 
    !KeyExistsQ[arrows, "CompositionSymbol"] &&  !KeyExistsQ[arrows, "IdentitySymbol"] && 
     !KeyExistsQ[arrows, "MorphismEquivalences"] &&  !KeyExistsQ[arrows, "ObjectEquivalences"] && 
     !KeyExistsQ[arrows, "Quiver"]
AbstractCategory[objects_List, arrows_List, compositionSymbol_] := 
  AbstractCategory[Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> OverTilde, 
     "MorphismEquivalences" -> {}, "ObjectEquivalences" -> {}, "Quiver" -> ResourceFunction["AbstractQuiver"][
       Association["ArrowEquivalences" -> {}, "Arrows" -> Association[
          (Subscript["\[FormalF]", ToString[#1]] -> arrows[[#1]] & ) /@ Range[Length[arrows]]], "ObjectEquivalences" -> {}, 
        "Objects" -> objects]]]] /;  !ListQ[compositionSymbol]
AbstractCategory[objects_List, arrows_Association, compositionSymbol_] := 
  AbstractCategory[Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> OverTilde, 
     "MorphismEquivalences" -> {}, "ObjectEquivalences" -> {}, "Quiver" -> ResourceFunction["AbstractQuiver"][
       Association["ArrowEquivalences" -> {}, "Arrows" -> arrows, "ObjectEquivalences" -> {}, "Objects" -> objects]]]] /; 
    !KeyExistsQ[arrows, "CompositionSymbol"] &&  !KeyExistsQ[arrows, "IdentitySymbol"] && 
     !KeyExistsQ[arrows, "MorphismEquivalences"] &&  !KeyExistsQ[arrows, "ObjectEquivalences"] && 
     !KeyExistsQ[arrows, "Quiver"] &&  !ListQ[compositionSymbol]
AbstractCategory[objects_List, arrows_List, compositionSymbol_, identitySymbol_] := 
  AbstractCategory[Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
     "MorphismEquivalences" -> {}, "ObjectEquivalences" -> {}, "Quiver" -> ResourceFunction["AbstractQuiver"][
       Association["ArrowEquivalences" -> {}, "Arrows" -> Association[
          (Subscript["\[FormalF]", ToString[#1]] -> arrows[[#1]] & ) /@ Range[Length[arrows]]], "ObjectEquivalences" -> {}, 
        "Objects" -> objects]]]] /;  !ListQ[compositionSymbol] &&  !ListQ[identitySymbol]
AbstractCategory[objects_List, arrows_Association, compositionSymbol_, identitySymbol_] := 
  AbstractCategory[Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
     "MorphismEquivalences" -> {}, "ObjectEquivalences" -> {}, "Quiver" -> ResourceFunction["AbstractQuiver"][
       Association["ArrowEquivalences" -> {}, "Arrows" -> arrows, "ObjectEquivalences" -> {}, "Objects" -> objects]]]] /; 
    !KeyExistsQ[arrows, "CompositionSymbol"] &&  !KeyExistsQ[arrows, "IdentitySymbol"] && 
     !KeyExistsQ[arrows, "MorphismEquivalences"] &&  !KeyExistsQ[arrows, "ObjectEquivalences"] && 
     !KeyExistsQ[arrows, "Quiver"] &&  !ListQ[compositionSymbol] &&  !ListQ[identitySymbol]
AbstractCategory[objects_List, arrows_List, objectEquivalences_List] := 
  AbstractCategory[Association["CompositionSymbol" -> CircleDot, "IdentitySymbol" -> OverTilde, 
    "MorphismEquivalences" -> {}, "ObjectEquivalences" -> objectEquivalences, 
    "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> {}, 
       "Arrows" -> Association[(Subscript["\[FormalF]", ToString[#1]] -> arrows[[#1]] & ) /@ Range[Length[arrows]]], 
       "ObjectEquivalences" -> {}, "Objects" -> objects]]]]
AbstractCategory[objects_List, arrows_Association, objectEquivalences_List] := 
  AbstractCategory[Association["CompositionSymbol" -> CircleDot, "IdentitySymbol" -> OverTilde, 
     "MorphismEquivalences" -> {}, "ObjectEquivalences" -> objectEquivalences, 
     "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> {}, "Arrows" -> arrows, 
        "ObjectEquivalences" -> {}, "Objects" -> objects]]]] /;  !KeyExistsQ[arrows, "CompositionSymbol"] && 
     !KeyExistsQ[arrows, "IdentitySymbol"] &&  !KeyExistsQ[arrows, "MorphismEquivalences"] && 
     !KeyExistsQ[arrows, "ObjectEquivalences"] &&  !KeyExistsQ[arrows, "Quiver"]
AbstractCategory[objects_List, arrows_List, objectEquivalences_List, morphismEquivalences_List] := 
  AbstractCategory[Association["CompositionSymbol" -> CircleDot, "IdentitySymbol" -> OverTilde, 
    "MorphismEquivalences" -> morphismEquivalences, "ObjectEquivalences" -> objectEquivalences, 
    "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> {}, 
       "Arrows" -> Association[(Subscript["\[FormalF]", ToString[#1]] -> arrows[[#1]] & ) /@ Range[Length[arrows]]], 
       "ObjectEquivalences" -> {}, "Objects" -> objects]]]]
AbstractCategory[objects_List, arrows_Association, objectEquivalences_List, morphismEquivalences_List] := 
  AbstractCategory[Association["CompositionSymbol" -> CircleDot, "IdentitySymbol" -> OverTilde, 
     "MorphismEquivalences" -> morphismEquivalences, "ObjectEquivalences" -> objectEquivalences, 
     "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> {}, "Arrows" -> arrows, 
        "ObjectEquivalences" -> {}, "Objects" -> objects]]]] /;  !KeyExistsQ[arrows, "CompositionSymbol"] && 
     !KeyExistsQ[arrows, "IdentitySymbol"] &&  !KeyExistsQ[arrows, "MorphismEquivalences"] && 
     !KeyExistsQ[arrows, "ObjectEquivalences"] &&  !KeyExistsQ[arrows, "Quiver"]
AbstractCategory[objects_List, arrows_List, compositionSymbol_, objectEquivalences_List] := 
  AbstractCategory[Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> OverTilde, 
     "MorphismEquivalences" -> {}, "ObjectEquivalences" -> objectEquivalences, 
     "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> {}, 
        "Arrows" -> Association[(Subscript["\[FormalF]", ToString[#1]] -> arrows[[#1]] & ) /@ Range[Length[arrows]]], 
        "ObjectEquivalences" -> {}, "Objects" -> objects]]]] /;  !ListQ[compositionSymbol]
AbstractCategory[objects_List, arrows_Association, compositionSymbol_, objectEquivalences_List] := 
  AbstractCategory[Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> OverTilde, 
     "MorphismEquivalences" -> {}, "ObjectEquivalences" -> objectEquivalences, 
     "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> {}, "Arrows" -> arrows, 
        "ObjectEquivalences" -> {}, "Objects" -> objects]]]] /;  !KeyExistsQ[arrows, "CompositionSymbol"] && 
     !KeyExistsQ[arrows, "IdentitySymbol"] &&  !KeyExistsQ[arrows, "MorphismEquivalences"] && 
     !KeyExistsQ[arrows, "ObjectEquivalences"] &&  !KeyExistsQ[arrows, "Quiver"] &&  !ListQ[compositionSymbol]
AbstractCategory[objects_List, arrows_List, compositionSymbol_, objectEquivalences_List, morphismEquivalences_List] := 
  AbstractCategory[Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> OverTilde, 
     "MorphismEquivalences" -> morphismEquivalences, "ObjectEquivalences" -> objectEquivalences, 
     "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> {}, 
        "Arrows" -> Association[(Subscript["\[FormalF]", ToString[#1]] -> arrows[[#1]] & ) /@ Range[Length[arrows]]], 
        "ObjectEquivalences" -> {}, "Objects" -> objects]]]] /;  !ListQ[compositionSymbol]
AbstractCategory[objects_List, arrows_Association, compositionSymbol_, objectEquivalences_List, 
   morphismEquivalences_List] := AbstractCategory[Association["CompositionSymbol" -> compositionSymbol, 
     "IdentitySymbol" -> OverTilde, "MorphismEquivalences" -> morphismEquivalences, 
     "ObjectEquivalences" -> objectEquivalences, "Quiver" -> ResourceFunction["AbstractQuiver"][
       Association["ArrowEquivalences" -> {}, "Arrows" -> arrows, "ObjectEquivalences" -> {}, "Objects" -> objects]]]] /; 
    !KeyExistsQ[arrows, "CompositionSymbol"] &&  !KeyExistsQ[arrows, "IdentitySymbol"] && 
     !KeyExistsQ[arrows, "MorphismEquivalences"] &&  !KeyExistsQ[arrows, "ObjectEquivalences"] && 
     !KeyExistsQ[arrows, "Quiver"] &&  !ListQ[compositionSymbol]
AbstractCategory[objects_List, arrows_List, compositionSymbol_, identitySymbol_, objectEquivalences_List] := 
  AbstractCategory[Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
     "MorphismEquivalences" -> {}, "ObjectEquivalences" -> objectEquivalences, 
     "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> {}, 
        "Arrows" -> Association[(Subscript["\[FormalF]", ToString[#1]] -> arrows[[#1]] & ) /@ Range[Length[arrows]]], 
        "ObjectEquivalences" -> {}, "Objects" -> objects]]]] /;  !ListQ[compositionSymbol] &&  !ListQ[identitySymbol]
AbstractCategory[objects_List, arrows_Association, compositionSymbol_, identitySymbol_, objectEquivalences_List] := 
  AbstractCategory[Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
     "MorphismEquivalences" -> {}, "ObjectEquivalences" -> objectEquivalences, 
     "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> {}, "Arrows" -> arrows, 
        "ObjectEquivalences" -> {}, "Objects" -> objects]]]] /;  !KeyExistsQ[arrows, "CompositionSymbol"] && 
     !KeyExistsQ[arrows, "IdentitySymbol"] &&  !KeyExistsQ[arrows, "MorphismEquivalences"] && 
     !KeyExistsQ[arrows, "ObjectEquivalences"] &&  !KeyExistsQ[arrows, "Quiver"] &&  !ListQ[compositionSymbol] && 
     !ListQ[identitySymbol]
AbstractCategory[objects_List, arrows_List, compositionSymbol_, identitySymbol_, objectEquivalences_List, 
   morphismEquivalences_List] := AbstractCategory[Association["CompositionSymbol" -> compositionSymbol, 
     "IdentitySymbol" -> identitySymbol, "MorphismEquivalences" -> morphismEquivalences, 
     "ObjectEquivalences" -> objectEquivalences, "Quiver" -> ResourceFunction["AbstractQuiver"][
       Association["ArrowEquivalences" -> {}, "Arrows" -> Association[
          (Subscript["\[FormalF]", ToString[#1]] -> arrows[[#1]] & ) /@ Range[Length[arrows]]], "ObjectEquivalences" -> {}, 
        "Objects" -> objects]]]] /;  !ListQ[compositionSymbol] &&  !ListQ[identitySymbol]
AbstractCategory[objects_List, arrows_Association, compositionSymbol_, identitySymbol_, objectEquivalences_List, 
   morphismEquivalences_List] := AbstractCategory[Association["CompositionSymbol" -> compositionSymbol, 
     "IdentitySymbol" -> identitySymbol, "MorphismEquivalences" -> morphismEquivalences, 
     "ObjectEquivalences" -> objectEquivalences, "Quiver" -> ResourceFunction["AbstractQuiver"][
       Association["ArrowEquivalences" -> {}, "Arrows" -> arrows, "ObjectEquivalences" -> {}, "Objects" -> objects]]]] /; 
    !KeyExistsQ[arrows, "CompositionSymbol"] &&  !KeyExistsQ[arrows, "IdentitySymbol"] && 
     !KeyExistsQ[arrows, "MorphismEquivalences"] &&  !KeyExistsQ[arrows, "ObjectEquivalences"] && 
     !KeyExistsQ[arrows, "Quiver"] &&  !ListQ[compositionSymbol] &&  !ListQ[identitySymbol]
AbstractCategory[arrows_Association, objectEquivalences_List] := 
  AbstractCategory[Association["CompositionSymbol" -> CircleDot, "IdentitySymbol" -> OverTilde, 
     "MorphismEquivalences" -> {}, "ObjectEquivalences" -> objectEquivalences, 
     "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> {}, "Arrows" -> arrows, 
        "ObjectEquivalences" -> {}, "Objects" -> DeleteDuplicates[Flatten[Apply[List, Last /@ Normal[arrows], 
            {1}]]]]]]] /;  !KeyExistsQ[arrows, "CompositionSymbol"] &&  !KeyExistsQ[arrows, "IdentitySymbol"] && 
     !KeyExistsQ[arrows, "MorphismEquivalences"] &&  !KeyExistsQ[arrows, "ObjectEquivalences"] && 
     !KeyExistsQ[arrows, "Quiver"]
AbstractCategory[arrows_Association, objectEquivalences_List, morphismEquivalences_List] := 
  AbstractCategory[Association["CompositionSymbol" -> CircleDot, "IdentitySymbol" -> OverTilde, 
     "MorphismEquivalences" -> morphismEquivalences, "ObjectEquivalences" -> objectEquivalences, 
     "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> {}, "Arrows" -> arrows, 
        "ObjectEquivalences" -> {}, "Objects" -> DeleteDuplicates[Flatten[Apply[List, Last /@ Normal[arrows], 
            {1}]]]]]]] /;  !KeyExistsQ[arrows, "CompositionSymbol"] &&  !KeyExistsQ[arrows, "IdentitySymbol"] && 
     !KeyExistsQ[arrows, "MorphismEquivalences"] &&  !KeyExistsQ[arrows, "ObjectEquivalences"] && 
     !KeyExistsQ[arrows, "Quiver"]
AbstractCategory[arrows_Association, compositionSymbol_] := 
  AbstractCategory[Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> OverTilde, 
     "MorphismEquivalences" -> {}, "ObjectEquivalences" -> {}, "Quiver" -> ResourceFunction["AbstractQuiver"][
       Association["ArrowEquivalences" -> {}, "Arrows" -> arrows, "ObjectEquivalences" -> {}, 
        "Objects" -> DeleteDuplicates[Flatten[Apply[List, Last /@ Normal[arrows], {1}]]]]]]] /; 
    !KeyExistsQ[arrows, "CompositionSymbol"] &&  !KeyExistsQ[arrows, "IdentitySymbol"] && 
     !KeyExistsQ[arrows, "MorphismEquivalences"] &&  !KeyExistsQ[arrows, "ObjectEquivalences"] && 
     !KeyExistsQ[arrows, "Quiver"] &&  !ListQ[compositionSymbol]
AbstractCategory[arrows_Association, compositionSymbol_, objectEquivalences_List] := 
  AbstractCategory[Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> OverTilde, 
     "MorphismEquivalences" -> {}, "ObjectEquivalences" -> objectEquivalences, 
     "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> {}, "Arrows" -> arrows, 
        "ObjectEquivalences" -> {}, "Objects" -> DeleteDuplicates[Flatten[Apply[List, Last /@ Normal[arrows], 
            {1}]]]]]]] /;  !KeyExistsQ[arrows, "CompositionSymbol"] &&  !KeyExistsQ[arrows, "IdentitySymbol"] && 
     !KeyExistsQ[arrows, "MorphismEquivalences"] &&  !KeyExistsQ[arrows, "ObjectEquivalences"] && 
     !KeyExistsQ[arrows, "Quiver"] &&  !ListQ[compositionSymbol]
AbstractCategory[arrows_Association, compositionSymbol_, objectEquivalences_List, morphismEquivalences_List] := 
  AbstractCategory[Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> OverTilde, 
     "MorphismEquivalences" -> morphismEquivalences, "ObjectEquivalences" -> objectEquivalences, 
     "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> {}, "Arrows" -> arrows, 
        "ObjectEquivalences" -> {}, "Objects" -> DeleteDuplicates[Flatten[Apply[List, Last /@ Normal[arrows], 
            {1}]]]]]]] /;  !KeyExistsQ[arrows, "CompositionSymbol"] &&  !KeyExistsQ[arrows, "IdentitySymbol"] && 
     !KeyExistsQ[arrows, "MorphismEquivalences"] &&  !KeyExistsQ[arrows, "ObjectEquivalences"] && 
     !KeyExistsQ[arrows, "Quiver"] &&  !ListQ[compositionSymbol]
AbstractCategory[arrows_Association, compositionSymbol_, identitySymbol_] := 
  AbstractCategory[Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
     "MorphismEquivalences" -> {}, "ObjectEquivalences" -> {}, "Quiver" -> ResourceFunction["AbstractQuiver"][
       Association["ArrowEquivalences" -> {}, "Arrows" -> arrows, "ObjectEquivalences" -> {}, 
        "Objects" -> DeleteDuplicates[Flatten[Apply[List, Last /@ Normal[arrows], {1}]]]]]]] /; 
    !KeyExistsQ[arrows, "CompositionSymbol"] &&  !KeyExistsQ[arrows, "IdentitySymbol"] && 
     !KeyExistsQ[arrows, "MorphismEquivalences"] &&  !KeyExistsQ[arrows, "ObjectEquivalences"] && 
     !KeyExistsQ[arrows, "Quiver"] &&  !ListQ[compositionSymbol] &&  !ListQ[identitySymbol]
AbstractCategory[arrows_Association, compositionSymbol_, identitySymbol_, objectEquivalences_List] := 
  AbstractCategory[Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
     "MorphismEquivalences" -> {}, "ObjectEquivalences" -> objectEquivalences, 
     "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> {}, "Arrows" -> arrows, 
        "ObjectEquivalences" -> {}, "Objects" -> DeleteDuplicates[Flatten[Apply[List, Last /@ Normal[arrows], 
            {1}]]]]]]] /;  !KeyExistsQ[arrows, "CompositionSymbol"] &&  !KeyExistsQ[arrows, "IdentitySymbol"] && 
     !KeyExistsQ[arrows, "MorphismEquivalences"] &&  !KeyExistsQ[arrows, "ObjectEquivalences"] && 
     !KeyExistsQ[arrows, "Quiver"] &&  !ListQ[compositionSymbol] &&  !ListQ[identitySymbol]
AbstractCategory[arrows_Association, compositionSymbol_, identitySymbol_, objectEquivalences_List, 
   morphismEquivalences_List] := AbstractCategory[Association["CompositionSymbol" -> compositionSymbol, 
     "IdentitySymbol" -> identitySymbol, "MorphismEquivalences" -> morphismEquivalences, 
     "ObjectEquivalences" -> objectEquivalences, "Quiver" -> ResourceFunction["AbstractQuiver"][
       Association["ArrowEquivalences" -> {}, "Arrows" -> arrows, "ObjectEquivalences" -> {}, 
        "Objects" -> DeleteDuplicates[Flatten[Apply[List, Last /@ Normal[arrows], {1}]]]]]]] /; 
    !KeyExistsQ[arrows, "CompositionSymbol"] &&  !KeyExistsQ[arrows, "IdentitySymbol"] && 
     !KeyExistsQ[arrows, "MorphismEquivalences"] &&  !KeyExistsQ[arrows, "ObjectEquivalences"] && 
     !KeyExistsQ[arrows, "Quiver"] &&  !ListQ[compositionSymbol] &&  !ListQ[identitySymbol]
AbstractCategory[(abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
     "Arrows" -> arrows_Association, "ObjectEquivalences" -> objectEquivalences_List, "Objects" -> objects_List]]] := 
  AbstractCategory[Association["CompositionSymbol" -> CircleDot, "IdentitySymbol" -> OverTilde, 
     "MorphismEquivalences" -> {}, "ObjectEquivalences" -> {}, "Quiver" -> ResourceFunction["AbstractQuiver"][
       Association["ArrowEquivalences" -> arrowEquivalences, "Arrows" -> arrows, "ObjectEquivalences" -> 
         objectEquivalences, "Objects" -> objects]]]] /; SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[(abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
     "Arrows" -> arrows_Association, "ObjectEquivalences" -> objectEquivalences_List, "Objects" -> objects_List]], 
   compositionSymbol_] := AbstractCategory[Association["CompositionSymbol" -> compositionSymbol, 
     "IdentitySymbol" -> OverTilde, "MorphismEquivalences" -> {}, "ObjectEquivalences" -> {}, 
     "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> arrowEquivalences, 
        "Arrows" -> arrows, "ObjectEquivalences" -> objectEquivalences, "Objects" -> objects]]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" &&  !ListQ[compositionSymbol]
AbstractCategory[(abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
     "Arrows" -> arrows_Association, "ObjectEquivalences" -> objectEquivalences_List, "Objects" -> objects_List]], 
   compositionSymbol_, identitySymbol_] := AbstractCategory[Association["CompositionSymbol" -> compositionSymbol, 
     "IdentitySymbol" -> identitySymbol, "MorphismEquivalences" -> {}, "ObjectEquivalences" -> {}, 
     "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> arrowEquivalences, 
        "Arrows" -> arrows, "ObjectEquivalences" -> objectEquivalences, "Objects" -> objects]]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" &&  !ListQ[compositionSymbol] &&  !ListQ[identitySymbol]
AbstractCategory[(abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
     "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]], 
   objectEquivalences_List] := AbstractCategory[Association["CompositionSymbol" -> CircleDot, 
     "IdentitySymbol" -> OverTilde, "MorphismEquivalences" -> {}, "ObjectEquivalences" -> objectEquivalences, 
     "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> arrowEquivalences, 
        "Arrows" -> arrows, "ObjectEquivalences" -> quiverObjectEquivalences, "Objects" -> objects]]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[(abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
     "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]], 
   objectEquivalences_List, morphismEquivalences_List] := 
  AbstractCategory[Association["CompositionSymbol" -> CircleDot, "IdentitySymbol" -> OverTilde, 
     "MorphismEquivalences" -> morphismEquivalences, "ObjectEquivalences" -> objectEquivalences, 
     "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> arrowEquivalences, 
        "Arrows" -> arrows, "ObjectEquivalences" -> quiverObjectEquivalences, "Objects" -> objects]]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[(abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
     "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]], 
   compositionSymbol_, objectEquivalences_List] := 
  AbstractCategory[Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> OverTilde, 
     "MorphismEquivalences" -> {}, "ObjectEquivalences" -> objectEquivalences, 
     "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> arrowEquivalences, 
        "Arrows" -> arrows, "ObjectEquivalences" -> quiverObjectEquivalences, "Objects" -> objects]]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" &&  !ListQ[compositionSymbol]
AbstractCategory[(abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
     "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]], 
   compositionSymbol_, objectEquivalences_List, morphismEquivalences_List] := 
  AbstractCategory[Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> OverTilde, 
     "MorphismEquivalences" -> morphismEquivalences, "ObjectEquivalences" -> objectEquivalences, 
     "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> arrowEquivalences, 
        "Arrows" -> arrows, "ObjectEquivalences" -> quiverObjectEquivalences, "Objects" -> objects]]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" &&  !ListQ[compositionSymbol]
AbstractCategory[(abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
     "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]], 
   compositionSymbol_, identitySymbol_, objectEquivalences_List] := 
  AbstractCategory[Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
     "MorphismEquivalences" -> {}, "ObjectEquivalences" -> objectEquivalences, 
     "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> arrowEquivalences, 
        "Arrows" -> arrows, "ObjectEquivalences" -> quiverObjectEquivalences, "Objects" -> objects]]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" &&  !ListQ[compositionSymbol] &&  !ListQ[identitySymbol]
AbstractCategory[(abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
     "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]], 
   compositionSymbol_, identitySymbol_, objectEquivalences_List, morphismEquivalences_List] := 
  AbstractCategory[Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
     "MorphismEquivalences" -> morphismEquivalences, "ObjectEquivalences" -> objectEquivalences, 
     "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> arrowEquivalences, 
        "Arrows" -> arrows, "ObjectEquivalences" -> quiverObjectEquivalences, "Objects" -> objects]]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" &&  !ListQ[compositionSymbol] &&  !ListQ[identitySymbol]
AbstractCategory[quiverGraph_Graph] := AbstractCategory[Association["CompositionSymbol" -> CircleDot, 
    "IdentitySymbol" -> OverTilde, "MorphismEquivalences" -> {}, "ObjectEquivalences" -> {}, 
    "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> {}, 
       "Arrows" -> Association[(Subscript["\[FormalF]", ToString[#1]] -> EdgeList[quiverGraph][[#1]] & ) /@ 
          Range[Length[EdgeList[quiverGraph]]]], "ObjectEquivalences" -> {}, "Objects" -> VertexList[quiverGraph]]]]]
AbstractCategory[quiverGraph_Graph, compositionSymbol_] := 
  AbstractCategory[Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> OverTilde, 
     "MorphismEquivalences" -> {}, "ObjectEquivalences" -> {}, "Quiver" -> ResourceFunction["AbstractQuiver"][
       Association["ArrowEquivalences" -> {}, "Arrows" -> Association[
          (Subscript["\[FormalF]", ToString[#1]] -> EdgeList[quiverGraph][[#1]] & ) /@ Range[Length[EdgeList[quiverGraph]]]], 
        "ObjectEquivalences" -> {}, "Objects" -> VertexList[quiverGraph]]]]] /;  !ListQ[compositionSymbol]
AbstractCategory[quiverGraph_Graph, compositionSymbol_, identitySymbol_] := 
  AbstractCategory[Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
     "MorphismEquivalences" -> {}, "ObjectEquivalences" -> {}, "Quiver" -> ResourceFunction["AbstractQuiver"][
       Association["ArrowEquivalences" -> {}, "Arrows" -> Association[
          (Subscript["\[FormalF]", ToString[#1]] -> EdgeList[quiverGraph][[#1]] & ) /@ Range[Length[EdgeList[quiverGraph]]]], 
        "ObjectEquivalences" -> {}, "Objects" -> VertexList[quiverGraph]]]]] /; 
    !ListQ[compositionSymbol] &&  !ListQ[identitySymbol]
AbstractCategory[quiverGraph_Graph, objectEquivalences_List] := 
  AbstractCategory[Association["CompositionSymbol" -> CircleDot, "IdentitySymbol" -> OverTilde, 
    "MorphismEquivalences" -> {}, "ObjectEquivalences" -> objectEquivalences, 
    "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> {}, 
       "Arrows" -> Association[(Subscript["\[FormalF]", ToString[#1]] -> EdgeList[quiverGraph][[#1]] & ) /@ 
          Range[Length[EdgeList[quiverGraph]]]], "ObjectEquivalences" -> {}, "Objects" -> VertexList[quiverGraph]]]]]
AbstractCategory[quiverGraph_Graph, objectEquivalences_List, morphismEquivalences_List] := 
  AbstractCategory[Association["CompositionSymbol" -> CircleDot, "IdentitySymbol" -> OverTilde, 
    "MorphismEquivalences" -> morphismEquivalences, "ObjectEquivalences" -> objectEquivalences, 
    "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> {}, 
       "Arrows" -> Association[(Subscript["\[FormalF]", ToString[#1]] -> EdgeList[quiverGraph][[#1]] & ) /@ 
          Range[Length[EdgeList[quiverGraph]]]], "ObjectEquivalences" -> {}, "Objects" -> VertexList[quiverGraph]]]]]
AbstractCategory[quiverGraph_Graph, compositionSymbol_, objectEquivalences_List] := 
  AbstractCategory[Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> OverTilde, 
     "MorphismEquivalences" -> {}, "ObjectEquivalences" -> objectEquivalences, 
     "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> {}, 
        "Arrows" -> Association[(Subscript["\[FormalF]", ToString[#1]] -> EdgeList[quiverGraph][[#1]] & ) /@ 
           Range[Length[EdgeList[quiverGraph]]]], "ObjectEquivalences" -> {}, "Objects" -> VertexList[quiverGraph]]]]] /; 
    !ListQ[compositionSymbol]
AbstractCategory[quiverGraph_Graph, compositionSymbol_, objectEquivalences_List, morphismEquivalences_List] := 
  AbstractCategory[Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> OverTilde, 
     "MorphismEquivalences" -> morphismEquivalences, "ObjectEquivalences" -> objectEquivalences, 
     "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> {}, 
        "Arrows" -> Association[(Subscript["\[FormalF]", ToString[#1]] -> EdgeList[quiverGraph][[#1]] & ) /@ 
           Range[Length[EdgeList[quiverGraph]]]], "ObjectEquivalences" -> {}, "Objects" -> VertexList[quiverGraph]]]]] /; 
    !ListQ[compositionSymbol]
AbstractCategory[quiverGraph_Graph, compositionSymbol_, identitySymbol_, objectEquivalences_List] := 
  AbstractCategory[Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
     "MorphismEquivalences" -> {}, "ObjectEquivalences" -> objectEquivalences, 
     "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> {}, 
        "Arrows" -> Association[(Subscript["\[FormalF]", ToString[#1]] -> EdgeList[quiverGraph][[#1]] & ) /@ 
           Range[Length[EdgeList[quiverGraph]]]], "ObjectEquivalences" -> {}, "Objects" -> VertexList[quiverGraph]]]]] /; 
    !ListQ[compositionSymbol] &&  !ListQ[identitySymbol]
AbstractCategory[quiverGraph_Graph, compositionSymbol_, identitySymbol_, objectEquivalences_List, 
   morphismEquivalences_List] := AbstractCategory[Association["CompositionSymbol" -> compositionSymbol, 
     "IdentitySymbol" -> identitySymbol, "MorphismEquivalences" -> morphismEquivalences, 
     "ObjectEquivalences" -> objectEquivalences, "Quiver" -> ResourceFunction["AbstractQuiver"][
       Association["ArrowEquivalences" -> {}, "Arrows" -> Association[
          (Subscript["\[FormalF]", ToString[#1]] -> EdgeList[quiverGraph][[#1]] & ) /@ Range[Length[EdgeList[quiverGraph]]]], 
        "ObjectEquivalences" -> {}, "Objects" -> VertexList[quiverGraph]]]]] /; 
    !ListQ[compositionSymbol] &&  !ListQ[identitySymbol]
AbstractCategory[category_Association] := AbstractCategory[KeySort[category]] /; 
   KeyExistsQ[category, "CompositionSymbol"] && KeyExistsQ[category, "IdentitySymbol"] && 
    KeyExistsQ[category, "MorphismEquivalences"] && KeyExistsQ[category, "ObjectEquivalences"] && 
    KeyExistsQ[category, "Quiver"] && Keys[KeySort[category]] =!= Keys[category]
AbstractCategory[AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]], newCompositionSymbol_] := 
  AbstractCategory[Association["CompositionSymbol" -> newCompositionSymbol, "IdentitySymbol" -> identitySymbol, 
     "MorphismEquivalences" -> morphismEquivalences, "ObjectEquivalences" -> objectEquivalences, 
     "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> arrowEquivalences, 
        "Arrows" -> arrows, "ObjectEquivalences" -> quiverObjectEquivalences, "Objects" -> objects]]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" &&  !ListQ[newCompositionSymbol]
AbstractCategory[AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]], newCompositionSymbol_, newIdentitySymbol_] := 
  AbstractCategory[Association["CompositionSymbol" -> newCompositionSymbol, "IdentitySymbol" -> newIdentitySymbol, 
     "MorphismEquivalences" -> morphismEquivalences, "ObjectEquivalences" -> objectEquivalences, 
     "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> arrowEquivalences, 
        "Arrows" -> arrows, "ObjectEquivalences" -> quiverObjectEquivalences, "Objects" -> objects]]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" &&  !ListQ[newCompositionSymbol] &&  !ListQ[newIdentitySymbol]
AbstractCategory[AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]], newCompositionSymbol_, newIdentitySymbol_, newObjectEquivalences_List] := 
  AbstractCategory[Association["CompositionSymbol" -> newCompositionSymbol, "IdentitySymbol" -> newIdentitySymbol, 
     "MorphismEquivalences" -> morphismEquivalences, "ObjectEquivalences" -> newObjectEquivalences, 
     "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> arrowEquivalences, 
        "Arrows" -> arrows, "ObjectEquivalences" -> quiverObjectEquivalences, "Objects" -> objects]]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" &&  !ListQ[newCompositionSymbol] &&  !ListQ[newIdentitySymbol]
AbstractCategory[AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]], newCompositionSymbol_, newIdentitySymbol_, newObjectEquivalences_List, 
   newMorphismEquivalences_List] := AbstractCategory[Association["CompositionSymbol" -> newCompositionSymbol, 
     "IdentitySymbol" -> newIdentitySymbol, "MorphismEquivalences" -> newMorphismEquivalences, 
     "ObjectEquivalences" -> newObjectEquivalences, "Quiver" -> ResourceFunction["AbstractQuiver"][
       Association["ArrowEquivalences" -> arrowEquivalences, "Arrows" -> arrows, "ObjectEquivalences" -> 
         quiverObjectEquivalences, "Objects" -> objects]]]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
     !ListQ[newCompositionSymbol] &&  !ListQ[newIdentitySymbol]
AbstractCategory[AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]], newObjectEquivalences_List] := 
  AbstractCategory[Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
     "MorphismEquivalences" -> morphismEquivalences, "ObjectEquivalences" -> newObjectEquivalences, 
     "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> arrowEquivalences, 
        "Arrows" -> arrows, "ObjectEquivalences" -> quiverObjectEquivalences, "Objects" -> objects]]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]], newObjectEquivalences_List, newMorphismEquivalences_List] := 
  AbstractCategory[Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
     "MorphismEquivalences" -> newMorphismEquivalences, "ObjectEquivalences" -> newObjectEquivalences, 
     "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> arrowEquivalences, 
        "Arrows" -> arrows, "ObjectEquivalences" -> quiverObjectEquivalences, "Objects" -> objects]]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver"
AbstractCategory[AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]], newCompositionSymbol_, newObjectEquivalences_List] := 
  AbstractCategory[Association["CompositionSymbol" -> newCompositionSymbol, "IdentitySymbol" -> identitySymbol, 
     "MorphismEquivalences" -> morphismEquivalences, "ObjectEquivalences" -> newObjectEquivalences, 
     "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> arrowEquivalences, 
        "Arrows" -> arrows, "ObjectEquivalences" -> quiverObjectEquivalences, "Objects" -> objects]]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" &&  !ListQ[newCompositionSymbol]
AbstractCategory[AbstractCategory[Association["CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]], newCompositionSymbol_, newObjectEquivalences_List, 
   newMorphismEquivalences_List] := AbstractCategory[Association["CompositionSymbol" -> newCompositionSymbol, 
     "IdentitySymbol" -> identitySymbol, "MorphismEquivalences" -> newMorphismEquivalences, 
     "ObjectEquivalences" -> newObjectEquivalences, "Quiver" -> ResourceFunction["AbstractQuiver"][
       Association["ArrowEquivalences" -> arrowEquivalences, "Arrows" -> arrows, "ObjectEquivalences" -> 
         quiverObjectEquivalences, "Objects" -> objects]]]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
     !ListQ[newCompositionSymbol]

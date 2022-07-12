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
reduceObjectsWithDuplicates[objects_List, {}] := objects
reduceObjectsWithDuplicates[objects_List, objectEquivalences_List] := 
  reduceObjectsWithDuplicates[objects /. First[First[objectEquivalences]] -> Last[First[objectEquivalences]], 
    Drop[objectEquivalences /. First[First[objectEquivalences]] -> Last[First[objectEquivalences]], 1]] /; 
   Length[objectEquivalences] > 0
reduceArrowsInitialWithDuplicates[arrows_List, {}] := arrows
reduceArrowsInitialWithDuplicates[arrows_List, arrowEquivalences_List] := 
  reduceArrowsInitialWithDuplicates[arrows /. First[First[arrowEquivalences]] -> Last[First[arrowEquivalences]], 
    Drop[arrowEquivalences /. First[First[arrowEquivalences]] -> Last[First[arrowEquivalences]], 1]] /; 
   Length[arrowEquivalences] > 0
reduceArrowsFinalWithDuplicates[arrows_List, {}] := arrows
reduceArrowsFinalWithDuplicates[arrows_List, objectEquivalences_List] := 
  reduceArrowsFinalWithDuplicates[arrows /. First[First[objectEquivalences]] -> Last[First[objectEquivalences]], 
    Drop[objectEquivalences /. First[First[objectEquivalences]] -> Last[First[objectEquivalences]], 1]] /; 
   Length[objectEquivalences] > 0
reduceComponentNames[componentNames_Association, {}] := componentNames
reduceComponentNames[componentNames_Association, objectEquivalences_List] := 
  reduceComponentNames[Association[DeleteDuplicatesBy[Normal[componentNames] /. First[First[objectEquivalences]] -> 
        Last[First[objectEquivalences]], First]], 
    Drop[DeleteDuplicates[objectEquivalences /. First[First[objectEquivalences]] -> Last[First[objectEquivalences]]], 
     1]] /; Length[objectEquivalences] > 0
AbstractNaturalTransformation[Association["Category" -> (abstractCategory_)[
       Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
        "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
        "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
           "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
           "Objects" -> objects_List]]]], "ComponentEquivalences" -> componentEquivalences_List, 
     "ComponentNames" -> componentNames_Association, "Covariant" -> covariant_, 
     "LeftArrowMappings" -> leftArrowMappings_Association, "LeftMorphismEquivalences" -> leftMorphismEquivalences_List, 
     "LeftNewArrows" -> leftNewArrows_Association, "LeftNewObjects" -> leftNewObjects_List, 
     "LeftObjectEquivalences" -> leftObjectEquivalences_List, "LeftObjectMappings" -> leftObjectMappings_Association, 
     "NewCompositionSymbol" -> newCompositionSymbol_, "NewIdentitySymbol" -> newIdentitySymbol_, 
     "RightArrowMappings" -> rightArrowMappings_Association, "RightMorphismEquivalences" -> 
      rightMorphismEquivalences_List, "RightNewArrows" -> rightNewArrows_Association, 
     "RightNewObjects" -> rightNewObjects_List, "RightObjectEquivalences" -> rightObjectEquivalences_List, 
     "RightObjectMappings" -> rightObjectMappings_Association]]["ComponentAssociation"] := 
  Module[{leftObjectFunction, rightObjectFunction, componentAssociation}, 
    leftObjectFunction = Join[Association[(#1 -> #1 & ) /@ objects], leftObjectMappings]; 
     rightObjectFunction = Join[Association[(#1 -> #1 & ) /@ objects], rightObjectMappings]; componentAssociation = {}; 
     (Module[{object = #1}, componentAssociation = Append[componentAssociation, componentNames[object] -> 
           DirectedEdge[leftObjectFunction[object], rightObjectFunction[object]]]] & ) /@ objects; 
     Association[DeleteDuplicates[componentAssociation]]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"
AbstractNaturalTransformation[Association["Category" -> (abstractCategory_)[
       Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
        "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
        "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
           "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
           "Objects" -> objects_List]]]], "ComponentEquivalences" -> componentEquivalences_List, 
     "ComponentNames" -> componentNames_Association, "Covariant" -> covariant_, 
     "LeftArrowMappings" -> leftArrowMappings_Association, "LeftMorphismEquivalences" -> leftMorphismEquivalences_List, 
     "LeftNewArrows" -> leftNewArrows_Association, "LeftNewObjects" -> leftNewObjects_List, 
     "LeftObjectEquivalences" -> leftObjectEquivalences_List, "LeftObjectMappings" -> leftObjectMappings_Association, 
     "NewCompositionSymbol" -> newCompositionSymbol_, "NewIdentitySymbol" -> newIdentitySymbol_, 
     "RightArrowMappings" -> rightArrowMappings_Association, "RightMorphismEquivalences" -> 
      rightMorphismEquivalences_List, "RightNewArrows" -> rightNewArrows_Association, 
     "RightNewObjects" -> rightNewObjects_List, "RightObjectEquivalences" -> rightObjectEquivalences_List, 
     "RightObjectMappings" -> rightObjectMappings_Association]]["ComponentNames"] := 
  Module[{leftObjectFunction, rightObjectFunction, componentAssociation}, 
    leftObjectFunction = Join[Association[(#1 -> #1 & ) /@ objects], leftObjectMappings]; 
     rightObjectFunction = Join[Association[(#1 -> #1 & ) /@ objects], rightObjectMappings]; componentAssociation = {}; 
     (Module[{object = #1}, componentAssociation = Append[componentAssociation, componentNames[object] -> 
           DirectedEdge[leftObjectFunction[object], rightObjectFunction[object]]]] & ) /@ objects; 
     First /@ Normal[Association[DeleteDuplicates[componentAssociation]]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractNaturalTransformation[Association["Category" -> (abstractCategory_)[
       Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
        "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
        "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
           "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
           "Objects" -> objects_List]]]], "ComponentEquivalences" -> componentEquivalences_List, 
     "ComponentNames" -> componentNames_Association, "Covariant" -> covariant_, 
     "LeftArrowMappings" -> leftArrowMappings_Association, "LeftMorphismEquivalences" -> leftMorphismEquivalences_List, 
     "LeftNewArrows" -> leftNewArrows_Association, "LeftNewObjects" -> leftNewObjects_List, 
     "LeftObjectEquivalences" -> leftObjectEquivalences_List, "LeftObjectMappings" -> leftObjectMappings_Association, 
     "NewCompositionSymbol" -> newCompositionSymbol_, "NewIdentitySymbol" -> newIdentitySymbol_, 
     "RightArrowMappings" -> rightArrowMappings_Association, "RightMorphismEquivalences" -> 
      rightMorphismEquivalences_List, "RightNewArrows" -> rightNewArrows_Association, 
     "RightNewObjects" -> rightNewObjects_List, "RightObjectEquivalences" -> rightObjectEquivalences_List, 
     "RightObjectMappings" -> rightObjectMappings_Association]]["ComponentEdges"] := 
  Module[{leftObjectFunction, rightObjectFunction, componentAssociation}, 
    leftObjectFunction = Join[Association[(#1 -> #1 & ) /@ objects], leftObjectMappings]; 
     rightObjectFunction = Join[Association[(#1 -> #1 & ) /@ objects], rightObjectMappings]; componentAssociation = {}; 
     (Module[{object = #1}, componentAssociation = Append[componentAssociation, componentNames[object] -> 
           DirectedEdge[leftObjectFunction[object], rightObjectFunction[object]]]] & ) /@ objects; 
     (DirectedEdge @@ Last[#1] & ) /@ Normal[Association[DeleteDuplicates[componentAssociation]]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractNaturalTransformation[Association["Category" -> (abstractCategory_)[
       Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
        "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
        "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
           "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
           "Objects" -> objects_List]]]], "ComponentEquivalences" -> componentEquivalences_List, 
     "ComponentNames" -> componentNames_Association, "Covariant" -> covariant_, 
     "LeftArrowMappings" -> leftArrowMappings_Association, "LeftMorphismEquivalences" -> leftMorphismEquivalences_List, 
     "LeftNewArrows" -> leftNewArrows_Association, "LeftNewObjects" -> leftNewObjects_List, 
     "LeftObjectEquivalences" -> leftObjectEquivalences_List, "LeftObjectMappings" -> leftObjectMappings_Association, 
     "NewCompositionSymbol" -> newCompositionSymbol_, "NewIdentitySymbol" -> newIdentitySymbol_, 
     "RightArrowMappings" -> rightArrowMappings_Association, "RightMorphismEquivalences" -> 
      rightMorphismEquivalences_List, "RightNewArrows" -> rightNewArrows_Association, 
     "RightNewObjects" -> rightNewObjects_List, "RightObjectEquivalences" -> rightObjectEquivalences_List, 
     "RightObjectMappings" -> rightObjectMappings_Association]]["ComponentCount"] := 
  Module[{leftObjectFunction, rightObjectFunction, componentAssociation}, 
    leftObjectFunction = Join[Association[(#1 -> #1 & ) /@ objects], leftObjectMappings]; 
     rightObjectFunction = Join[Association[(#1 -> #1 & ) /@ objects], rightObjectMappings]; componentAssociation = {}; 
     (Module[{object = #1}, componentAssociation = Append[componentAssociation, componentNames[object] -> 
           DirectedEdge[leftObjectFunction[object], rightObjectFunction[object]]]] & ) /@ objects; 
     Length[Normal[Association[DeleteDuplicates[componentAssociation]]]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractNaturalTransformation[Association["Category" -> (abstractCategory_)[
       Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
        "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
        "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
           "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
           "Objects" -> objects_List]]]], "ComponentEquivalences" -> componentEquivalences_List, 
     "ComponentNames" -> componentNames_Association, "Covariant" -> covariant_, 
     "LeftArrowMappings" -> leftArrowMappings_Association, "LeftMorphismEquivalences" -> leftMorphismEquivalences_List, 
     "LeftNewArrows" -> leftNewArrows_Association, "LeftNewObjects" -> leftNewObjects_List, 
     "LeftObjectEquivalences" -> leftObjectEquivalences_List, "LeftObjectMappings" -> leftObjectMappings_Association, 
     "NewCompositionSymbol" -> newCompositionSymbol_, "NewIdentitySymbol" -> newIdentitySymbol_, 
     "RightArrowMappings" -> rightArrowMappings_Association, "RightMorphismEquivalences" -> 
      rightMorphismEquivalences_List, "RightNewArrows" -> rightNewArrows_Association, 
     "RightNewObjects" -> rightNewObjects_List, "RightObjectEquivalences" -> rightObjectEquivalences_List, 
     "RightObjectMappings" -> rightObjectMappings_Association]]["ReducedComponentAssociation"] := 
  Module[{leftObjectFunction, rightObjectFunction, componentAssociation}, 
    leftObjectFunction = Join[Association[
        Thread[Keys[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
              objectEquivalences]]] -> reduceObjectsWithDuplicates[Values[Association[(#1 -> #1 & ) /@ 
              reduceObjects[reduceObjects[objects, quiverObjectEquivalences], objectEquivalences]]], 
           leftObjectEquivalences]]], Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[
            Keys[leftObjectMappings], quiverObjectEquivalences], objectEquivalences] -> reduceObjectsWithDuplicates[
           Values[leftObjectMappings], leftObjectEquivalences]]]]; rightObjectFunction = 
      Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, 
               quiverObjectEquivalences], objectEquivalences]]] -> reduceObjectsWithDuplicates[
           Values[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
               objectEquivalences]]], rightObjectEquivalences]]], 
       Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[rightObjectMappings], 
            quiverObjectEquivalences], objectEquivalences] -> reduceObjectsWithDuplicates[Values[rightObjectMappings], 
           rightObjectEquivalences]]]]; componentAssociation = {}; 
     (Module[{object = #1}, componentAssociation = Append[componentAssociation, 
          reduceComponentNames[reduceComponentNames[componentNames, quiverObjectEquivalences], objectEquivalences][
            object] -> DirectedEdge[leftObjectFunction[object], rightObjectFunction[object]]]] & ) /@ 
      reduceObjects[reduceObjects[objects, quiverObjectEquivalences], objectEquivalences]; 
     reduceArrowsInitial[Association[DeleteDuplicates[componentAssociation]], componentEquivalences]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractNaturalTransformation[Association["Category" -> (abstractCategory_)[
       Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
        "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
        "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
           "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
           "Objects" -> objects_List]]]], "ComponentEquivalences" -> componentEquivalences_List, 
     "ComponentNames" -> componentNames_Association, "Covariant" -> covariant_, 
     "LeftArrowMappings" -> leftArrowMappings_Association, "LeftMorphismEquivalences" -> leftMorphismEquivalences_List, 
     "LeftNewArrows" -> leftNewArrows_Association, "LeftNewObjects" -> leftNewObjects_List, 
     "LeftObjectEquivalences" -> leftObjectEquivalences_List, "LeftObjectMappings" -> leftObjectMappings_Association, 
     "NewCompositionSymbol" -> newCompositionSymbol_, "NewIdentitySymbol" -> newIdentitySymbol_, 
     "RightArrowMappings" -> rightArrowMappings_Association, "RightMorphismEquivalences" -> 
      rightMorphismEquivalences_List, "RightNewArrows" -> rightNewArrows_Association, 
     "RightNewObjects" -> rightNewObjects_List, "RightObjectEquivalences" -> rightObjectEquivalences_List, 
     "RightObjectMappings" -> rightObjectMappings_Association]]["ReducedComponentNames"] := 
  Module[{leftObjectFunction, rightObjectFunction, componentAssociation}, 
    leftObjectFunction = Join[Association[
        Thread[Keys[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
              objectEquivalences]]] -> reduceObjectsWithDuplicates[Values[Association[(#1 -> #1 & ) /@ 
              reduceObjects[reduceObjects[objects, quiverObjectEquivalences], objectEquivalences]]], 
           leftObjectEquivalences]]], Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[
            Keys[leftObjectMappings], quiverObjectEquivalences], objectEquivalences] -> reduceObjectsWithDuplicates[
           Values[leftObjectMappings], leftObjectEquivalences]]]]; rightObjectFunction = 
      Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, 
               quiverObjectEquivalences], objectEquivalences]]] -> reduceObjectsWithDuplicates[
           Values[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
               objectEquivalences]]], rightObjectEquivalences]]], 
       Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[rightObjectMappings], 
            quiverObjectEquivalences], objectEquivalences] -> reduceObjectsWithDuplicates[Values[rightObjectMappings], 
           rightObjectEquivalences]]]]; componentAssociation = {}; 
     (Module[{object = #1}, componentAssociation = Append[componentAssociation, 
          reduceComponentNames[reduceComponentNames[componentNames, quiverObjectEquivalences], objectEquivalences][
            object] -> DirectedEdge[leftObjectFunction[object], rightObjectFunction[object]]]] & ) /@ 
      reduceObjects[reduceObjects[objects, quiverObjectEquivalences], objectEquivalences]; 
     First /@ Normal[reduceArrowsInitial[Association[DeleteDuplicates[componentAssociation]], componentEquivalences]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractNaturalTransformation[Association["Category" -> (abstractCategory_)[
       Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
        "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
        "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
           "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
           "Objects" -> objects_List]]]], "ComponentEquivalences" -> componentEquivalences_List, 
     "ComponentNames" -> componentNames_Association, "Covariant" -> covariant_, 
     "LeftArrowMappings" -> leftArrowMappings_Association, "LeftMorphismEquivalences" -> leftMorphismEquivalences_List, 
     "LeftNewArrows" -> leftNewArrows_Association, "LeftNewObjects" -> leftNewObjects_List, 
     "LeftObjectEquivalences" -> leftObjectEquivalences_List, "LeftObjectMappings" -> leftObjectMappings_Association, 
     "NewCompositionSymbol" -> newCompositionSymbol_, "NewIdentitySymbol" -> newIdentitySymbol_, 
     "RightArrowMappings" -> rightArrowMappings_Association, "RightMorphismEquivalences" -> 
      rightMorphismEquivalences_List, "RightNewArrows" -> rightNewArrows_Association, 
     "RightNewObjects" -> rightNewObjects_List, "RightObjectEquivalences" -> rightObjectEquivalences_List, 
     "RightObjectMappings" -> rightObjectMappings_Association]]["ReducedComponentEdges"] := 
  Module[{leftObjectFunction, rightObjectFunction, componentAssociation}, 
    leftObjectFunction = Join[Association[
        Thread[Keys[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
              objectEquivalences]]] -> reduceObjectsWithDuplicates[Values[Association[(#1 -> #1 & ) /@ 
              reduceObjects[reduceObjects[objects, quiverObjectEquivalences], objectEquivalences]]], 
           leftObjectEquivalences]]], Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[
            Keys[leftObjectMappings], quiverObjectEquivalences], objectEquivalences] -> reduceObjectsWithDuplicates[
           Values[leftObjectMappings], leftObjectEquivalences]]]]; rightObjectFunction = 
      Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, 
               quiverObjectEquivalences], objectEquivalences]]] -> reduceObjectsWithDuplicates[
           Values[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
               objectEquivalences]]], rightObjectEquivalences]]], 
       Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[rightObjectMappings], 
            quiverObjectEquivalences], objectEquivalences] -> reduceObjectsWithDuplicates[Values[rightObjectMappings], 
           rightObjectEquivalences]]]]; componentAssociation = {}; 
     (Module[{object = #1}, componentAssociation = Append[componentAssociation, 
          reduceComponentNames[reduceComponentNames[componentNames, quiverObjectEquivalences], objectEquivalences][
            object] -> DirectedEdge[leftObjectFunction[object], rightObjectFunction[object]]]] & ) /@ 
      reduceObjects[reduceObjects[objects, quiverObjectEquivalences], objectEquivalences]; 
     (DirectedEdge @@ Last[#1] & ) /@ Normal[reduceArrowsInitial[Association[DeleteDuplicates[componentAssociation]], 
        componentEquivalences]]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"
AbstractNaturalTransformation[Association["Category" -> (abstractCategory_)[
       Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
        "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
        "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
           "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
           "Objects" -> objects_List]]]], "ComponentEquivalences" -> componentEquivalences_List, 
     "ComponentNames" -> componentNames_Association, "Covariant" -> covariant_, 
     "LeftArrowMappings" -> leftArrowMappings_Association, "LeftMorphismEquivalences" -> leftMorphismEquivalences_List, 
     "LeftNewArrows" -> leftNewArrows_Association, "LeftNewObjects" -> leftNewObjects_List, 
     "LeftObjectEquivalences" -> leftObjectEquivalences_List, "LeftObjectMappings" -> leftObjectMappings_Association, 
     "NewCompositionSymbol" -> newCompositionSymbol_, "NewIdentitySymbol" -> newIdentitySymbol_, 
     "RightArrowMappings" -> rightArrowMappings_Association, "RightMorphismEquivalences" -> 
      rightMorphismEquivalences_List, "RightNewArrows" -> rightNewArrows_Association, 
     "RightNewObjects" -> rightNewObjects_List, "RightObjectEquivalences" -> rightObjectEquivalences_List, 
     "RightObjectMappings" -> rightObjectMappings_Association]]["ReducedComponentCount"] := 
  Module[{leftObjectFunction, rightObjectFunction, componentAssociation}, 
    leftObjectFunction = Join[Association[
        Thread[Keys[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
              objectEquivalences]]] -> reduceObjectsWithDuplicates[Values[Association[(#1 -> #1 & ) /@ 
              reduceObjects[reduceObjects[objects, quiverObjectEquivalences], objectEquivalences]]], 
           leftObjectEquivalences]]], Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[
            Keys[leftObjectMappings], quiverObjectEquivalences], objectEquivalences] -> reduceObjectsWithDuplicates[
           Values[leftObjectMappings], leftObjectEquivalences]]]]; rightObjectFunction = 
      Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, 
               quiverObjectEquivalences], objectEquivalences]]] -> reduceObjectsWithDuplicates[
           Values[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
               objectEquivalences]]], rightObjectEquivalences]]], 
       Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[rightObjectMappings], 
            quiverObjectEquivalences], objectEquivalences] -> reduceObjectsWithDuplicates[Values[rightObjectMappings], 
           rightObjectEquivalences]]]]; componentAssociation = {}; 
     (Module[{object = #1}, componentAssociation = Append[componentAssociation, 
          reduceComponentNames[reduceComponentNames[componentNames, quiverObjectEquivalences], objectEquivalences][
            object] -> DirectedEdge[leftObjectFunction[object], rightObjectFunction[object]]]] & ) /@ 
      reduceObjects[reduceObjects[objects, quiverObjectEquivalences], objectEquivalences]; 
     Length[Normal[reduceArrowsInitial[Association[DeleteDuplicates[componentAssociation]], componentEquivalences]]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractNaturalTransformation[Association["Category" -> (abstractCategory_)[
       Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
        "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
        "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
           "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
           "Objects" -> objects_List]]]], "ComponentEquivalences" -> componentEquivalences_List, 
     "ComponentNames" -> componentNames_Association, "Covariant" -> covariant_, 
     "LeftArrowMappings" -> leftArrowMappings_Association, "LeftMorphismEquivalences" -> leftMorphismEquivalences_List, 
     "LeftNewArrows" -> leftNewArrows_Association, "LeftNewObjects" -> leftNewObjects_List, 
     "LeftObjectEquivalences" -> leftObjectEquivalences_List, "LeftObjectMappings" -> leftObjectMappings_Association, 
     "NewCompositionSymbol" -> newCompositionSymbol_, "NewIdentitySymbol" -> newIdentitySymbol_, 
     "RightArrowMappings" -> rightArrowMappings_Association, "RightMorphismEquivalences" -> 
      rightMorphismEquivalences_List, "RightNewArrows" -> rightNewArrows_Association, 
     "RightNewObjects" -> rightNewObjects_List, "RightObjectEquivalences" -> rightObjectEquivalences_List, 
     "RightObjectMappings" -> rightObjectMappings_Association]]["LeftFunctor"] := 
  ResourceFunction["AbstractFunctor"][Association["ArrowMappings" -> leftArrowMappings, 
     "Category" -> ResourceFunction["AbstractCategory"][Association["CompositionSymbol" -> compositionSymbol, 
        "IdentitySymbol" -> identitySymbol, "MorphismEquivalences" -> morphismEquivalences, 
        "ObjectEquivalences" -> objectEquivalences, "Quiver" -> ResourceFunction["AbstractQuiver"][
          Association["ArrowEquivalences" -> arrowEquivalences, "Arrows" -> arrows, "ObjectEquivalences" -> 
            quiverObjectEquivalences, "Objects" -> objects]]]], "Covariant" -> covariant, 
     "MorphismEquivalences" -> leftMorphismEquivalences, "NewArrows" -> leftNewArrows, 
     "NewCompositionSymbol" -> newCompositionSymbol, "NewIdentitySymbol" -> newIdentitySymbol, 
     "NewObjects" -> leftNewObjects, "ObjectEquivalences" -> leftObjectEquivalences, 
     "ObjectMappings" -> leftObjectMappings]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"
AbstractNaturalTransformation[Association["Category" -> (abstractCategory_)[
       Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
        "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
        "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
           "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
           "Objects" -> objects_List]]]], "ComponentEquivalences" -> componentEquivalences_List, 
     "ComponentNames" -> componentNames_Association, "Covariant" -> covariant_, 
     "LeftArrowMappings" -> leftArrowMappings_Association, "LeftMorphismEquivalences" -> leftMorphismEquivalences_List, 
     "LeftNewArrows" -> leftNewArrows_Association, "LeftNewObjects" -> leftNewObjects_List, 
     "LeftObjectEquivalences" -> leftObjectEquivalences_List, "LeftObjectMappings" -> leftObjectMappings_Association, 
     "NewCompositionSymbol" -> newCompositionSymbol_, "NewIdentitySymbol" -> newIdentitySymbol_, 
     "RightArrowMappings" -> rightArrowMappings_Association, "RightMorphismEquivalences" -> 
      rightMorphismEquivalences_List, "RightNewArrows" -> rightNewArrows_Association, 
     "RightNewObjects" -> rightNewObjects_List, "RightObjectEquivalences" -> rightObjectEquivalences_List, 
     "RightObjectMappings" -> rightObjectMappings_Association]]["RightFunctor"] := 
  ResourceFunction["AbstractFunctor"][Association["ArrowMappings" -> rightArrowMappings, 
     "Category" -> ResourceFunction["AbstractCategory"][Association["CompositionSymbol" -> compositionSymbol, 
        "IdentitySymbol" -> identitySymbol, "MorphismEquivalences" -> morphismEquivalences, 
        "ObjectEquivalences" -> objectEquivalences, "Quiver" -> ResourceFunction["AbstractQuiver"][
          Association["ArrowEquivalences" -> arrowEquivalences, "Arrows" -> arrows, "ObjectEquivalences" -> 
            quiverObjectEquivalences, "Objects" -> objects]]]], "Covariant" -> covariant, 
     "MorphismEquivalences" -> rightMorphismEquivalences, "NewArrows" -> rightNewArrows, 
     "NewCompositionSymbol" -> newCompositionSymbol, "NewIdentitySymbol" -> newIdentitySymbol, 
     "NewObjects" -> rightNewObjects, "ObjectEquivalences" -> rightObjectEquivalences, 
     "ObjectMappings" -> rightObjectMappings]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"
AbstractNaturalTransformation[Association["Category" -> (abstractCategory_)[
       Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
        "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
        "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
           "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
           "Objects" -> objects_List]]]], "ComponentEquivalences" -> componentEquivalences_List, 
     "ComponentNames" -> componentNames_Association, "Covariant" -> covariant_, 
     "LeftArrowMappings" -> leftArrowMappings_Association, "LeftMorphismEquivalences" -> leftMorphismEquivalences_List, 
     "LeftNewArrows" -> leftNewArrows_Association, "LeftNewObjects" -> leftNewObjects_List, 
     "LeftObjectEquivalences" -> leftObjectEquivalences_List, "LeftObjectMappings" -> leftObjectMappings_Association, 
     "NewCompositionSymbol" -> newCompositionSymbol_, "NewIdentitySymbol" -> newIdentitySymbol_, 
     "RightArrowMappings" -> rightArrowMappings_Association, "RightMorphismEquivalences" -> 
      rightMorphismEquivalences_List, "RightNewArrows" -> rightNewArrows_Association, 
     "RightNewObjects" -> rightNewObjects_List, "RightObjectEquivalences" -> rightObjectEquivalences_List, 
     "RightObjectMappings" -> rightObjectMappings_Association]]["MatchingCodomainsQ"] := 
  Module[{leftImageObjects, leftImageArrows, leftImageQuiverObjectEquivalences, leftImageObjectEquivalences, 
     leftImageArrowEquivalences, leftImageMorphismEquivalences, leftImageMorphismAssociation, leftImageCompositions, 
     rightImageObjects, rightImageArrows, rightImageQuiverObjectEquivalences, rightImageObjectEquivalences, 
     rightImageArrowEquivalences, rightImageMorphismEquivalences, rightImageMorphismAssociation, rightImageCompositions}, 
    leftImageObjects = DeleteDuplicates[Join[objects /. Normal[leftObjectMappings], leftNewObjects]]; 
     leftImageArrows = Association[DeleteDuplicates[Join[Normal[arrows] /. Normal[leftArrowMappings] /. 
          Normal[leftObjectMappings], Normal[leftNewArrows]]]]; leftImageQuiverObjectEquivalences = 
      quiverObjectEquivalences /. Normal[leftObjectMappings]; leftImageObjectEquivalences = 
      DeleteDuplicates[Join[objectEquivalences /. Normal[leftObjectMappings], leftObjectEquivalences]]; 
     leftImageArrowEquivalences = arrowEquivalences /. Normal[leftArrowMappings]; 
     leftImageMorphismEquivalences = If[covariant === True, DeleteDuplicates[
        Join[morphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[leftArrowMappings] /. 
          Normal[leftObjectMappings], leftMorphismEquivalences]], DeleteDuplicates[
        Join[morphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[leftArrowMappings] /. 
           Normal[leftObjectMappings] /. {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
            newCompositionSymbol[z, newCompositionSymbol[y, x]], newCompositionSymbol[newCompositionSymbol[x_, y_], 
             z_] :> newCompositionSymbol[newCompositionSymbol[z, y], x], newCompositionSymbol[x_, y_] :> 
            newCompositionSymbol[y, x]}, leftMorphismEquivalences]]]; leftImageMorphismAssociation = 
      Association[Select[Normal[Association[DeleteDuplicates[Join[If[covariant === True, 
             Normal[reduceArrowsFinal[reduceArrowsInitial[leftImageArrows, leftImageArrowEquivalences], 
               leftImageQuiverObjectEquivalences]], (First[#1] -> Reverse[Last[#1]] & ) /@ Normal[reduceArrowsFinal[
                reduceArrowsInitial[leftImageArrows, leftImageArrowEquivalences], leftImageQuiverObjectEquivalences]]], 
            Normal[leftNewArrows]]]]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[leftImageCompositions = Select[Tuples[Normal[leftImageMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[leftImageMorphismAssociation], StringDelete[ToString[newCompositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          leftImageMorphismAssociation = Association[Append[Normal[leftImageMorphismAssociation], 
             newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ leftImageCompositions, 
      Length[reduceObjects[leftImageObjects, leftImageQuiverObjectEquivalences]]]; 
     leftImageMorphismAssociation = Association[Select[Normal[leftImageMorphismAssociation], 
        Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[leftImageMorphismAssociation], newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        leftImageMorphismAssociation = Association[Append[Normal[leftImageMorphismAssociation], 
           newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[leftImageObjects, 
       leftImageQuiverObjectEquivalences]; rightImageObjects = DeleteDuplicates[
       Join[objects /. Normal[rightObjectMappings], rightNewObjects]]; 
     rightImageArrows = Association[DeleteDuplicates[Join[Normal[arrows] /. Normal[rightArrowMappings] /. 
          Normal[rightObjectMappings], Normal[rightNewArrows]]]]; rightImageQuiverObjectEquivalences = 
      quiverObjectEquivalences /. Normal[rightObjectMappings]; rightImageObjectEquivalences = 
      DeleteDuplicates[Join[objectEquivalences /. Normal[rightObjectMappings], rightObjectEquivalences]]; 
     rightImageArrowEquivalences = arrowEquivalences /. Normal[rightArrowMappings]; 
     rightImageMorphismEquivalences = If[covariant === True, DeleteDuplicates[
        Join[morphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[rightArrowMappings] /. 
          Normal[rightObjectMappings], rightMorphismEquivalences]], DeleteDuplicates[
        Join[morphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[rightArrowMappings] /. 
           Normal[rightObjectMappings] /. {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
            newCompositionSymbol[z, newCompositionSymbol[y, x]], newCompositionSymbol[newCompositionSymbol[x_, y_], 
             z_] :> newCompositionSymbol[newCompositionSymbol[z, y], x], newCompositionSymbol[x_, y_] :> 
            newCompositionSymbol[y, x]}, rightMorphismEquivalences]]]; rightImageMorphismAssociation = 
      Association[Select[Normal[Association[DeleteDuplicates[Join[If[covariant === True, 
             Normal[reduceArrowsFinal[reduceArrowsInitial[rightImageArrows, rightImageArrowEquivalences], 
               rightImageQuiverObjectEquivalences]], (First[#1] -> Reverse[Last[#1]] & ) /@ Normal[reduceArrowsFinal[
                reduceArrowsInitial[rightImageArrows, rightImageArrowEquivalences], 
                rightImageQuiverObjectEquivalences]]], Normal[rightNewArrows]]]]], 
        First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[rightImageCompositions = Select[Tuples[Normal[rightImageMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[rightImageMorphismAssociation], StringDelete[ToString[newCompositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          rightImageMorphismAssociation = Association[Append[Normal[rightImageMorphismAssociation], 
             newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ rightImageCompositions, 
      Length[reduceObjects[rightImageObjects, rightImageQuiverObjectEquivalences]]]; 
     rightImageMorphismAssociation = Association[Select[Normal[rightImageMorphismAssociation], 
        Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[rightImageMorphismAssociation], newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        rightImageMorphismAssociation = Association[Append[Normal[rightImageMorphismAssociation], 
           newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[rightImageObjects, 
       rightImageQuiverObjectEquivalences]; 
     Sort[reduceObjects[reduceObjects[leftImageObjects, leftImageQuiverObjectEquivalences], 
         leftImageObjectEquivalences]] === Sort[reduceObjects[reduceObjects[rightImageObjects, 
          rightImageQuiverObjectEquivalences], rightImageObjectEquivalences]] && 
      Sort[(First[#1] -> DirectedEdge @@ Last[#1] & ) /@ Normal[reduceArrowsFinal[reduceArrowsInitial[
            leftImageMorphismAssociation, leftImageMorphismEquivalences], leftImageObjectEquivalences]]] === 
       Sort[(First[#1] -> DirectedEdge @@ Last[#1] & ) /@ Normal[reduceArrowsFinal[reduceArrowsInitial[
            rightImageMorphismAssociation, rightImageMorphismEquivalences], rightImageObjectEquivalences]]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractNaturalTransformation[Association["Category" -> (abstractCategory_)[
       Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
        "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
        "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
           "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
           "Objects" -> objects_List]]]], "ComponentEquivalences" -> componentEquivalences_List, 
     "ComponentNames" -> componentNames_Association, "Covariant" -> covariant_, 
     "LeftArrowMappings" -> leftArrowMappings_Association, "LeftMorphismEquivalences" -> leftMorphismEquivalences_List, 
     "LeftNewArrows" -> leftNewArrows_Association, "LeftNewObjects" -> leftNewObjects_List, 
     "LeftObjectEquivalences" -> leftObjectEquivalences_List, "LeftObjectMappings" -> leftObjectMappings_Association, 
     "NewCompositionSymbol" -> newCompositionSymbol_, "NewIdentitySymbol" -> newIdentitySymbol_, 
     "RightArrowMappings" -> rightArrowMappings_Association, "RightMorphismEquivalences" -> 
      rightMorphismEquivalences_List, "RightNewArrows" -> rightNewArrows_Association, 
     "RightNewObjects" -> rightNewObjects_List, "RightObjectEquivalences" -> rightObjectEquivalences_List, 
     "RightObjectMappings" -> rightObjectMappings_Association]]["ValidNaturalTransformationQ"] := 
  Module[{leftImageObjects, leftImageArrows, leftImageQuiverObjectEquivalences, leftImageObjectEquivalences, 
     leftImageArrowEquivalences, leftImageMorphismEquivalences, leftImageMorphismAssociation, leftImageCompositions, 
     rightImageObjects, rightImageArrows, rightImageQuiverObjectEquivalences, rightImageObjectEquivalences, 
     rightImageArrowEquivalences, rightImageMorphismEquivalences, rightImageMorphismAssociation, rightImageCompositions, 
     domainMorphismAssociation, domainCompositions, leftObjectFunction, rightObjectFunction, 
     leftObjectListWithDuplicates, leftArrowListWithDuplicates, rightObjectListWithDuplicates, 
     rightArrowListWithDuplicates, domainMorphismList, domainCompositionsList, leftImageMorphismList, 
     leftImageCompositionsList, leftMorphismFunction, rightImageMorphismList, rightImageCompositionsList, 
     rightMorphismFunction, naturalArrows, naturalMorphismEquivalences, naturalMorphismAssociation, naturalCompositions}, 
    leftImageObjects = DeleteDuplicates[Join[objects /. Normal[leftObjectMappings], leftNewObjects]]; 
     leftImageArrows = Association[DeleteDuplicates[Join[Normal[arrows] /. Normal[leftArrowMappings] /. 
          Normal[leftObjectMappings], Normal[leftNewArrows]]]]; leftImageQuiverObjectEquivalences = 
      quiverObjectEquivalences /. Normal[leftObjectMappings]; leftImageObjectEquivalences = 
      DeleteDuplicates[Join[objectEquivalences /. Normal[leftObjectMappings], leftObjectEquivalences]]; 
     leftImageArrowEquivalences = arrowEquivalences /. Normal[leftArrowMappings]; 
     leftImageMorphismEquivalences = If[covariant === True, DeleteDuplicates[
        Join[morphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[leftArrowMappings] /. 
          Normal[leftObjectMappings], leftMorphismEquivalences]], DeleteDuplicates[
        Join[morphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[leftArrowMappings] /. 
           Normal[leftObjectMappings] /. {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
            newCompositionSymbol[z, newCompositionSymbol[y, x]], newCompositionSymbol[newCompositionSymbol[x_, y_], 
             z_] :> newCompositionSymbol[newCompositionSymbol[z, y], x], newCompositionSymbol[x_, y_] :> 
            newCompositionSymbol[y, x]}, leftMorphismEquivalences]]]; leftImageMorphismAssociation = 
      Association[Select[Normal[Association[DeleteDuplicates[Join[If[covariant === True, 
             Normal[reduceArrowsFinal[reduceArrowsInitial[leftImageArrows, leftImageArrowEquivalences], 
               leftImageQuiverObjectEquivalences]], (First[#1] -> Reverse[Last[#1]] & ) /@ Normal[reduceArrowsFinal[
                reduceArrowsInitial[leftImageArrows, leftImageArrowEquivalences], leftImageQuiverObjectEquivalences]]], 
            Normal[leftNewArrows]]]]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[leftImageCompositions = Select[Tuples[Normal[leftImageMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[leftImageMorphismAssociation], StringDelete[ToString[newCompositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          leftImageMorphismAssociation = Association[Append[Normal[leftImageMorphismAssociation], 
             newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ leftImageCompositions, 
      Length[reduceObjects[leftImageObjects, leftImageQuiverObjectEquivalences]]]; 
     leftImageMorphismAssociation = Association[Select[Normal[leftImageMorphismAssociation], 
        Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[leftImageMorphismAssociation], newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        leftImageMorphismAssociation = Association[Append[Normal[leftImageMorphismAssociation], 
           newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[leftImageObjects, 
       leftImageQuiverObjectEquivalences]; rightImageObjects = DeleteDuplicates[
       Join[objects /. Normal[rightObjectMappings], rightNewObjects]]; 
     rightImageArrows = Association[DeleteDuplicates[Join[Normal[arrows] /. Normal[rightArrowMappings] /. 
          Normal[rightObjectMappings], Normal[rightNewArrows]]]]; rightImageQuiverObjectEquivalences = 
      quiverObjectEquivalences /. Normal[rightObjectMappings]; rightImageObjectEquivalences = 
      DeleteDuplicates[Join[objectEquivalences /. Normal[rightObjectMappings], rightObjectEquivalences]]; 
     rightImageArrowEquivalences = arrowEquivalences /. Normal[rightArrowMappings]; 
     rightImageMorphismEquivalences = If[covariant === True, DeleteDuplicates[
        Join[morphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[rightArrowMappings] /. 
          Normal[rightObjectMappings], rightMorphismEquivalences]], DeleteDuplicates[
        Join[morphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[rightArrowMappings] /. 
           Normal[rightObjectMappings] /. {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
            newCompositionSymbol[z, newCompositionSymbol[y, x]], newCompositionSymbol[newCompositionSymbol[x_, y_], 
             z_] :> newCompositionSymbol[newCompositionSymbol[z, y], x], newCompositionSymbol[x_, y_] :> 
            newCompositionSymbol[y, x]}, rightMorphismEquivalences]]]; rightImageMorphismAssociation = 
      Association[Select[Normal[Association[DeleteDuplicates[Join[If[covariant === True, 
             Normal[reduceArrowsFinal[reduceArrowsInitial[rightImageArrows, rightImageArrowEquivalences], 
               rightImageQuiverObjectEquivalences]], (First[#1] -> Reverse[Last[#1]] & ) /@ Normal[reduceArrowsFinal[
                reduceArrowsInitial[rightImageArrows, rightImageArrowEquivalences], 
                rightImageQuiverObjectEquivalences]]], Normal[rightNewArrows]]]]], 
        First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[rightImageCompositions = Select[Tuples[Normal[rightImageMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[rightImageMorphismAssociation], StringDelete[ToString[newCompositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          rightImageMorphismAssociation = Association[Append[Normal[rightImageMorphismAssociation], 
             newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ rightImageCompositions, 
      Length[reduceObjects[rightImageObjects, rightImageQuiverObjectEquivalences]]]; 
     rightImageMorphismAssociation = Association[Select[Normal[rightImageMorphismAssociation], 
        Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[rightImageMorphismAssociation], newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        rightImageMorphismAssociation = Association[Append[Normal[rightImageMorphismAssociation], 
           newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[rightImageObjects, 
       rightImageQuiverObjectEquivalences]; domainMorphismAssociation = 
      Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[arrows, arrowEquivalences], 
          quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[domainCompositions = Select[Tuples[Normal[domainMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[domainMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          domainMorphismAssociation = Association[Append[Normal[domainMorphismAssociation], 
             compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ domainCompositions, Length[reduceObjects[objects, quiverObjectEquivalences]]]; 
     domainMorphismAssociation = Association[Select[Normal[domainMorphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[domainMorphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        domainMorphismAssociation = Association[Append[Normal[domainMorphismAssociation], 
           identitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[objects, quiverObjectEquivalences]; 
     leftObjectFunction = Join[Association[
        Thread[Keys[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
              objectEquivalences]]] -> reduceObjectsWithDuplicates[Values[Association[(#1 -> #1 & ) /@ 
              reduceObjects[reduceObjects[objects, quiverObjectEquivalences], objectEquivalences]]], 
           leftObjectEquivalences]]], Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[
            Keys[leftObjectMappings], quiverObjectEquivalences], objectEquivalences] -> reduceObjectsWithDuplicates[
           Values[leftObjectMappings], leftObjectEquivalences]]]]; rightObjectFunction = 
      Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, 
               quiverObjectEquivalences], objectEquivalences]]] -> reduceObjectsWithDuplicates[
           Values[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
               objectEquivalences]]], rightObjectEquivalences]]], 
       Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[rightObjectMappings], 
            quiverObjectEquivalences], objectEquivalences] -> reduceObjectsWithDuplicates[Values[rightObjectMappings], 
           rightObjectEquivalences]]]]; leftObjectListWithDuplicates = objects /. Normal[leftObjectMappings]; 
     leftArrowListWithDuplicates = If[covariant === True, Normal[arrows] /. Normal[leftArrowMappings] /. 
        Normal[leftObjectMappings], (First[#1] -> Reverse[Last[#1]] & ) /@ 
        (Normal[arrows] /. Normal[leftArrowMappings] /. Normal[leftObjectMappings])]; 
     rightObjectListWithDuplicates = objects /. Normal[rightObjectMappings]; rightArrowListWithDuplicates = 
      If[covariant === True, Normal[arrows] /. Normal[rightArrowMappings] /. Normal[rightObjectMappings], 
       (First[#1] -> Reverse[Last[#1]] & ) /@ (Normal[arrows] /. Normal[rightArrowMappings] /. 
         Normal[rightObjectMappings])]; domainMorphismList = Select[reduceArrowsFinalWithDuplicates[
        reduceArrowsInitialWithDuplicates[Normal[arrows], arrowEquivalences], quiverObjectEquivalences], 
       First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[domainCompositionsList = Select[Tuples[domainMorphismList, 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ domainMorphismList, 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], domainMorphismList = 
           Append[domainMorphismList, compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ domainCompositionsList, 
      Length[reduceObjectsWithDuplicates[objects, quiverObjectEquivalences]]]; 
     domainMorphismList = Select[domainMorphismList, Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        domainMorphismList = Append[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      reduceObjectsWithDuplicates[objects, quiverObjectEquivalences]; domainMorphismList = 
      reduceArrowsFinalWithDuplicates[reduceArrowsInitialWithDuplicates[domainMorphismList, morphismEquivalences], 
       objectEquivalences]; leftImageMorphismList = Select[reduceArrowsFinalWithDuplicates[
        reduceArrowsInitialWithDuplicates[leftArrowListWithDuplicates, arrowEquivalences /. Normal[leftArrowMappings]], 
        quiverObjectEquivalences /. Normal[leftObjectMappings]], First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[leftImageCompositions = Select[Tuples[leftImageMorphismList, 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ leftImageMorphismList, 
            StringDelete[ToString[newCompositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], leftImageMorphismList = 
           Append[leftImageMorphismList, newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ leftImageCompositions, 
      Length[reduceObjectsWithDuplicates[leftObjectListWithDuplicates, quiverObjectEquivalences /. 
         Normal[leftObjectMappings]]]]; leftImageMorphismList = Select[leftImageMorphismList, 
       Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[leftImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        leftImageMorphismList = Append[leftImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      reduceObjectsWithDuplicates[leftObjectListWithDuplicates, quiverObjectEquivalences /. Normal[leftObjectMappings]]; 
     leftImageMorphismList = reduceArrowsFinalWithDuplicates[reduceArrowsInitialWithDuplicates[leftImageMorphismList, 
        If[covariant === True, DeleteDuplicates[Join[morphismEquivalences /. compositionSymbol -> newCompositionSymbol /. 
            Normal[leftArrowMappings], leftMorphismEquivalences]], DeleteDuplicates[
          Join[morphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[leftArrowMappings] /. 
            {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> newCompositionSymbol[z, newCompositionSymbol[y, 
                x]], newCompositionSymbol[newCompositionSymbol[x_, y_], z_] :> newCompositionSymbol[newCompositionSymbol[
                z, y], x], newCompositionSymbol[x_, y_] :> newCompositionSymbol[y, x]}, leftMorphismEquivalences]]]], 
       DeleteDuplicates[Join[objectEquivalences /. Normal[leftObjectMappings], leftObjectEquivalences]]]; 
     leftMorphismFunction = Association[Normal[Association[Thread[First /@ domainMorphismList -> 
            First /@ leftImageMorphismList]]] //. {compositionSymbol[x_, compositionSymbol[y_, z_]] :> 
          compositionSymbol[compositionSymbol[x, y], z], newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
          newCompositionSymbol[newCompositionSymbol[x, y], z]}]; rightImageMorphismList = 
      Select[reduceArrowsFinalWithDuplicates[reduceArrowsInitialWithDuplicates[rightArrowListWithDuplicates, 
         arrowEquivalences /. Normal[rightArrowMappings]], quiverObjectEquivalences /. Normal[rightObjectMappings]], 
       First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[rightImageCompositions = Select[Tuples[rightImageMorphismList, 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ rightImageMorphismList, 
            StringDelete[ToString[newCompositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], rightImageMorphismList = 
           Append[rightImageMorphismList, newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ rightImageCompositions, 
      Length[reduceObjectsWithDuplicates[rightObjectListWithDuplicates, quiverObjectEquivalences /. 
         Normal[rightObjectMappings]]]]; rightImageMorphismList = Select[rightImageMorphismList, 
       Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[rightImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        rightImageMorphismList = Append[rightImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      reduceObjectsWithDuplicates[rightObjectListWithDuplicates, quiverObjectEquivalences /. 
        Normal[rightObjectMappings]]; rightImageMorphismList = reduceArrowsFinalWithDuplicates[
       reduceArrowsInitialWithDuplicates[rightImageMorphismList, If[covariant === True, 
         DeleteDuplicates[Join[morphismEquivalences /. compositionSymbol -> newCompositionSymbol /. 
            Normal[rightArrowMappings], rightMorphismEquivalences]], DeleteDuplicates[
          Join[morphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[rightArrowMappings] /. 
            {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> newCompositionSymbol[z, newCompositionSymbol[y, 
                x]], newCompositionSymbol[newCompositionSymbol[x_, y_], z_] :> newCompositionSymbol[newCompositionSymbol[
                z, y], x], newCompositionSymbol[x_, y_] :> newCompositionSymbol[y, x]}, rightMorphismEquivalences]]]], 
       DeleteDuplicates[Join[objectEquivalences /. Normal[rightObjectMappings], rightObjectEquivalences]]]; 
     rightMorphismFunction = Association[Normal[Association[Thread[First /@ domainMorphismList -> 
            First /@ rightImageMorphismList]]] //. {compositionSymbol[x_, compositionSymbol[y_, z_]] :> 
          compositionSymbol[compositionSymbol[x, y], z], newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
          newCompositionSymbol[newCompositionSymbol[x, y], z]}]; naturalArrows = {}; naturalMorphismEquivalences = {}; 
     (Module[{morphism = #1 //. {compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[
              compositionSymbol[x, y], z], newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
             newCompositionSymbol[newCompositionSymbol[x, y], z]}}, 
        naturalArrows = Join[naturalArrows, {reduceComponentNames[reduceComponentNames[componentNames, 
                quiverObjectEquivalences], objectEquivalences][First[Last[morphism]]] -> 
             DirectedEdge[leftObjectFunction[First[Last[morphism]]], rightObjectFunction[First[Last[morphism]]]], 
            reduceComponentNames[reduceComponentNames[componentNames, quiverObjectEquivalences], objectEquivalences][
              Last[Last[morphism]]] -> DirectedEdge[leftObjectFunction[Last[Last[morphism]]], rightObjectFunction[Last[
                Last[morphism]]]]}]; naturalArrows = Join[naturalArrows, {leftMorphismFunction[First[morphism]] -> 
             DirectedEdge[leftObjectFunction[First[Last[morphism]]], leftObjectFunction[Last[Last[morphism]]]], 
            rightMorphismFunction[First[morphism]] -> DirectedEdge[rightObjectFunction[First[Last[morphism]]], 
              rightObjectFunction[Last[Last[morphism]]]]}]; naturalMorphismEquivalences = 
          Append[naturalMorphismEquivalences, newCompositionSymbol[reduceComponentNames[reduceComponentNames[
                componentNames, quiverObjectEquivalences], objectEquivalences][Last[Last[morphism]]], 
             leftMorphismFunction[First[morphism]]] == newCompositionSymbol[rightMorphismFunction[First[morphism]], 
             reduceComponentNames[reduceComponentNames[componentNames, quiverObjectEquivalences], objectEquivalences][
              First[Last[morphism]]]]]] & ) /@ Normal[reduceArrowsFinal[reduceArrowsInitial[domainMorphismAssociation, 
         morphismEquivalences], objectEquivalences]]; naturalArrows = Association[DeleteDuplicates[naturalArrows]]; 
     naturalMorphismAssociation = Association[Select[Normal[naturalArrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[naturalCompositions = Select[Tuples[Normal[naturalMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[naturalMorphismAssociation], StringDelete[ToString[newCompositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          naturalMorphismAssociation = Association[Append[Normal[naturalMorphismAssociation], 
             newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ naturalCompositions, Length[objects]]; 
     naturalMorphismAssociation = Association[Normal[Association[Select[Normal[naturalMorphismAssociation], 
           Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == Length[DeleteDuplicates[Flatten[
                {First[#1] /. newCompositionSymbol -> List}]]] & ]]] //. 
        {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> newCompositionSymbol[newCompositionSymbol[x, y], z]}]; 
     (If[ !MemberQ[Normal[naturalMorphismAssociation], newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        naturalMorphismAssociation = Association[Append[Normal[naturalMorphismAssociation], 
           newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ DeleteDuplicates[
       Catenate[({First[Last[#1]], Last[Last[#1]]} & ) /@ Normal[naturalMorphismAssociation]]]; 
     Sort[reduceObjects[reduceObjects[leftImageObjects, leftImageQuiverObjectEquivalences], 
         leftImageObjectEquivalences]] === Sort[reduceObjects[reduceObjects[rightImageObjects, 
          rightImageQuiverObjectEquivalences], rightImageObjectEquivalences]] && 
      Sort[(First[#1] -> DirectedEdge @@ Last[#1] & ) /@ Normal[reduceArrowsFinal[reduceArrowsInitial[
            leftImageMorphismAssociation, leftImageMorphismEquivalences], leftImageObjectEquivalences]]] === 
       Sort[(First[#1] -> DirectedEdge @@ Last[#1] & ) /@ Normal[reduceArrowsFinal[reduceArrowsInitial[
            rightImageMorphismAssociation, rightImageMorphismEquivalences], rightImageObjectEquivalences]]] && 
      SubsetQ[reduceObjects[reduceObjects[leftImageObjects, leftImageQuiverObjectEquivalences], 
        leftImageObjectEquivalences], DeleteDuplicates[Catenate[({First[Last[#1]], Last[Last[#1]]} & ) /@ 
          Normal[naturalMorphismAssociation]]]] && SubsetQ[reduceObjects[reduceObjects[rightImageObjects, 
         rightImageQuiverObjectEquivalences], rightImageObjectEquivalences], 
       DeleteDuplicates[Catenate[({First[Last[#1]], Last[Last[#1]]} & ) /@ Normal[naturalMorphismAssociation]]]] && 
      SubsetQ[(First[#1] -> DirectedEdge @@ Last[#1] & ) /@ Normal[reduceArrowsFinal[reduceArrowsInitial[
           leftImageMorphismAssociation, leftImageMorphismEquivalences], leftImageObjectEquivalences]], 
       Normal[reduceArrowsInitial[reduceArrowsInitial[reduceArrowsInitial[naturalMorphismAssociation, 
           naturalMorphismEquivalences //. {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
              newCompositionSymbol[newCompositionSymbol[x, y], z]}], Join[morphismEquivalences /. 
            Normal[leftMorphismFunction], morphismEquivalences /. Normal[rightMorphismFunction]]], 
         componentEquivalences]]] && SubsetQ[(First[#1] -> DirectedEdge @@ Last[#1] & ) /@ 
        Normal[reduceArrowsFinal[reduceArrowsInitial[rightImageMorphismAssociation, rightImageMorphismEquivalences], 
          rightImageObjectEquivalences]], Normal[reduceArrowsInitial[reduceArrowsInitial[
          reduceArrowsInitial[naturalMorphismAssociation, naturalMorphismEquivalences //. 
            {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> newCompositionSymbol[newCompositionSymbol[x, 
                y], z]}], Join[morphismEquivalences /. Normal[leftMorphismFunction], morphismEquivalences /. 
            Normal[rightMorphismFunction]]], componentEquivalences]]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractNaturalTransformation[Association["Category" -> (abstractCategory_)[
       Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
        "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
        "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
           "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
           "Objects" -> objects_List]]]], "ComponentEquivalences" -> componentEquivalences_List, 
     "ComponentNames" -> componentNames_Association, "Covariant" -> covariant_, 
     "LeftArrowMappings" -> leftArrowMappings_Association, "LeftMorphismEquivalences" -> leftMorphismEquivalences_List, 
     "LeftNewArrows" -> leftNewArrows_Association, "LeftNewObjects" -> leftNewObjects_List, 
     "LeftObjectEquivalences" -> leftObjectEquivalences_List, "LeftObjectMappings" -> leftObjectMappings_Association, 
     "NewCompositionSymbol" -> newCompositionSymbol_, "NewIdentitySymbol" -> newIdentitySymbol_, 
     "RightArrowMappings" -> rightArrowMappings_Association, "RightMorphismEquivalences" -> 
      rightMorphismEquivalences_List, "RightNewArrows" -> rightNewArrows_Association, 
     "RightNewObjects" -> rightNewObjects_List, "RightObjectEquivalences" -> rightObjectEquivalences_List, 
     "RightObjectMappings" -> rightObjectMappings_Association]]["NaturalTransformationEquations"] := 
  Module[{domainMorphismAssociation, domainCompositions, leftObjectFunction, rightObjectFunction, 
     leftObjectListWithDuplicates, leftArrowListWithDuplicates, rightObjectListWithDuplicates, 
     rightArrowListWithDuplicates, domainMorphismList, domainCompositionsList, leftImageMorphismList, 
     leftImageCompositions, leftMorphismFunction, rightImageMorphismList, rightImageCompositions, rightMorphismFunction, 
     naturalMorphismEquivalences}, domainMorphismAssociation = 
      Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[domainCompositions = Select[Tuples[Normal[domainMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & )[
             Normal[domainMorphismAssociation]], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          domainMorphismAssociation = Association[Append[Normal[domainMorphismAssociation], 
             compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ domainCompositions, Length[objects]]; 
     domainMorphismAssociation = Association[Select[Normal[domainMorphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[domainMorphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        domainMorphismAssociation = Association[Append[Normal[domainMorphismAssociation], 
           identitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ objects; 
     leftObjectFunction = Join[Association[(#1 -> #1 & ) /@ objects], leftObjectMappings]; 
     rightObjectFunction = Join[Association[(#1 -> #1 & ) /@ objects], rightObjectMappings]; 
     leftObjectListWithDuplicates = objects /. Normal[leftObjectMappings]; leftArrowListWithDuplicates = 
      If[covariant === True, Normal[arrows] /. Normal[leftArrowMappings] /. Normal[leftObjectMappings], 
       (First[#1] -> Reverse[Last[#1]] & ) /@ (Normal[arrows] /. Normal[leftArrowMappings] /. 
         Normal[leftObjectMappings])]; rightObjectListWithDuplicates = objects /. Normal[rightObjectMappings]; 
     rightArrowListWithDuplicates = If[covariant === True, Normal[arrows] /. Normal[rightArrowMappings] /. 
        Normal[rightObjectMappings], (First[#1] -> Reverse[Last[#1]] & ) /@ 
        (Normal[arrows] /. Normal[rightArrowMappings] /. Normal[rightObjectMappings])]; 
     domainMorphismList = Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[domainCompositionsList = Select[Tuples[domainMorphismList, 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ domainMorphismList, 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], domainMorphismList = 
           Append[domainMorphismList, compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ domainCompositionsList, 
      Length[objects]]; domainMorphismList = Select[domainMorphismList, 
       Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        domainMorphismList = Append[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ objects; 
     leftImageMorphismList = Select[leftArrowListWithDuplicates, First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[leftImageCompositions = Select[Tuples[leftImageMorphismList, 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ leftImageMorphismList, 
            StringDelete[ToString[newCompositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], leftImageMorphismList = 
           Append[leftImageMorphismList, newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ leftImageCompositions, 
      Length[leftObjectListWithDuplicates]]; leftImageMorphismList = Select[leftImageMorphismList, 
       Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[leftImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        leftImageMorphismList = Append[leftImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      leftObjectListWithDuplicates; leftMorphismFunction = 
      Association[Normal[Association[Thread[First /@ domainMorphismList -> First /@ leftImageMorphismList]]] //. 
        {compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[compositionSymbol[x, y], z], 
         newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> newCompositionSymbol[newCompositionSymbol[x, y], z]}]; 
     rightImageMorphismList = Select[rightArrowListWithDuplicates, First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[rightImageCompositions = Select[Tuples[rightImageMorphismList, 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ rightImageMorphismList, 
            StringDelete[ToString[newCompositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], rightImageMorphismList = 
           Append[rightImageMorphismList, newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ rightImageCompositions, 
      Length[rightObjectListWithDuplicates]]; rightImageMorphismList = Select[rightImageMorphismList, 
       Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[rightImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        rightImageMorphismList = Append[rightImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      rightObjectListWithDuplicates; rightMorphismFunction = 
      Association[Normal[Association[Thread[First /@ domainMorphismList -> First /@ rightImageMorphismList]]] //. 
        {compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[compositionSymbol[x, y], z], 
         newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> newCompositionSymbol[newCompositionSymbol[x, y], z]}]; 
     naturalMorphismEquivalences = {}; 
     (Module[{morphism = #1 //. {compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[
              compositionSymbol[x, y], z], newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
             newCompositionSymbol[newCompositionSymbol[x, y], z]}}, naturalMorphismEquivalences = 
         Append[naturalMorphismEquivalences, newCompositionSymbol[componentNames[Last[Last[morphism]]], 
            leftMorphismFunction[First[morphism]]] == newCompositionSymbol[rightMorphismFunction[First[morphism]], 
            componentNames[First[Last[morphism]]]]]] & ) /@ Normal[domainMorphismAssociation]; 
     DeleteDuplicates[naturalMorphismEquivalences]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"
AbstractNaturalTransformation[Association["Category" -> (abstractCategory_)[
       Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
        "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
        "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
           "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
           "Objects" -> objects_List]]]], "ComponentEquivalences" -> componentEquivalences_List, 
     "ComponentNames" -> componentNames_Association, "Covariant" -> covariant_, 
     "LeftArrowMappings" -> leftArrowMappings_, "LeftMorphismEquivalences" -> leftMorphismEquivalences_List, 
     "LeftNewArrows" -> leftNewArrows_Association, "LeftNewObjects" -> leftNewObjects_List, 
     "LeftObjectEquivalences" -> leftObjectEquivalences_List, "LeftObjectMappings" -> leftObjectMappings_Association, 
     "NewCompositionSymbol" -> newCompositionSymbol_, "NewIdentitySymbol" -> newIdentitySymbol_, 
     "RightArrowMappings" -> rightArrowMappings_Association, "RightMorphismEquivalences" -> 
      rightMorphismEquivalences_List, "RightNewArrows" -> rightNewArrows_Association, 
     "RightNewObjects" -> rightNewObjects_List, "RightObjectEquivalences" -> rightObjectEquivalences_List, 
     "RightObjectMappings" -> rightObjectMappings_Association]]["ReducedNaturalTransformationEquations"] := 
  Module[{domainMorphismAssociation, domainCompositions, leftObjectFunction, rightObjectFunction, 
     leftObjectListWithDuplicates, leftArrowListWithDuplicates, rightObjectListWithDuplicates, 
     rightArrowListWithDuplicates, domainMorphismList, domainCompositionsList, leftImageMorphismList, 
     leftImageCompositions, leftMorphismFunction, rightImageMorphismList, rightImageCompositions, rightMorphismFunction, 
     naturalMorphismEquivalences}, domainMorphismAssociation = 
      Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[arrows, arrowEquivalences], 
          quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[domainCompositions = Select[Tuples[Normal[domainMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[domainMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          domainMorphismAssociation = Association[Append[Normal[domainMorphismAssociation], 
             compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ domainCompositions, Length[reduceObjects[objects, quiverObjectEquivalences]]]; 
     domainMorphismAssociation = Association[Select[Normal[domainMorphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[domainMorphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        domainMorphismAssociation = Association[Append[Normal[domainMorphismAssociation], 
           identitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[objects, quiverObjectEquivalences]; 
     leftObjectFunction = Join[Association[
        Thread[Keys[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
              objectEquivalences]]] -> reduceObjectsWithDuplicates[Values[Association[(#1 -> #1 & ) /@ 
              reduceObjects[reduceObjects[objects, quiverObjectEquivalences], objectEquivalences]]], 
           leftObjectEquivalences]]], Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[
            Keys[leftObjectMappings], quiverObjectEquivalences], objectEquivalences] -> reduceObjectsWithDuplicates[
           Values[leftObjectMappings], leftObjectEquivalences]]]]; rightObjectFunction = 
      Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, 
               quiverObjectEquivalences], objectEquivalences]]] -> reduceObjectsWithDuplicates[
           Values[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
               objectEquivalences]]], rightObjectEquivalences]]], 
       Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[rightObjectMappings], 
            quiverObjectEquivalences], objectEquivalences] -> reduceObjectsWithDuplicates[Values[rightObjectMappings], 
           rightObjectEquivalences]]]]; leftObjectListWithDuplicates = objects /. Normal[leftObjectMappings]; 
     leftArrowListWithDuplicates = If[covariant === True, Normal[arrows] /. Normal[leftArrowMappings] /. 
        Normal[leftObjectMappings], (First[#1] -> Reverse[Last[#1]] & ) /@ 
        (Normal[arrows] /. Normal[leftArrowMappings] /. Normal[leftObjectMappings])]; 
     rightObjectListWithDuplicates = objects /. Normal[rightObjectMappings]; rightArrowListWithDuplicates = 
      If[covariant === True, Normal[arrows] /. Normal[rightArrowMappings] /. Normal[rightObjectMappings], 
       (First[#1] -> Reverse[Last[#1]] & ) /@ (Normal[arrows] /. Normal[rightArrowMappings] /. 
         Normal[rightObjectMappings])]; domainMorphismList = Select[reduceArrowsFinalWithDuplicates[
        reduceArrowsInitialWithDuplicates[Normal[arrows], arrowEquivalences], quiverObjectEquivalences], 
       First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[domainCompositionsList = Select[Tuples[domainMorphismList, 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ domainMorphismList, 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], domainMorphismList = 
           Append[domainMorphismList, compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ domainCompositionsList, 
      Length[reduceObjectsWithDuplicates[objects, quiverObjectEquivalences]]]; 
     domainMorphismList = Select[domainMorphismList, Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        domainMorphismList = Append[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      reduceObjectsWithDuplicates[objects, quiverObjectEquivalences]; domainMorphismList = 
      reduceArrowsFinalWithDuplicates[reduceArrowsInitialWithDuplicates[domainMorphismList, morphismEquivalences], 
       objectEquivalences]; leftImageMorphismList = Select[reduceArrowsFinalWithDuplicates[
        reduceArrowsInitialWithDuplicates[leftArrowListWithDuplicates, arrowEquivalences /. Normal[leftArrowMappings]], 
        quiverObjectEquivalences /. Normal[leftObjectMappings]], First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[leftImageCompositions = Select[Tuples[leftImageMorphismList, 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ leftImageMorphismList, 
            StringDelete[ToString[newCompositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], leftImageMorphismList = 
           Append[leftImageMorphismList, newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ leftImageCompositions, 
      Length[reduceObjectsWithDuplicates[leftObjectListWithDuplicates, quiverObjectEquivalences /. 
         Normal[leftObjectMappings]]]]; leftImageMorphismList = Select[leftImageMorphismList, 
       Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[leftImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        leftImageMorphismList = Append[leftImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      reduceObjectsWithDuplicates[leftObjectListWithDuplicates, quiverObjectEquivalences /. Normal[leftObjectMappings]]; 
     leftImageMorphismList = reduceArrowsFinalWithDuplicates[reduceArrowsInitialWithDuplicates[leftImageMorphismList, 
        If[covariant === True, DeleteDuplicates[Join[morphismEquivalences /. compositionSymbol -> newCompositionSymbol /. 
            Normal[leftArrowMappings], leftMorphismEquivalences]], DeleteDuplicates[
          Join[morphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[leftArrowMappings] /. 
            {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> newCompositionSymbol[z, newCompositionSymbol[y, 
                x]], newCompositionSymbol[newCompositionSymbol[x_, y_], z_] :> newCompositionSymbol[newCompositionSymbol[
                z, y], x], newCompositionSymbol[x_, y_] :> newCompositionSymbol[y, x]}, leftMorphismEquivalences]]]], 
       DeleteDuplicates[Join[objectEquivalences /. Normal[leftObjectMappings], leftObjectEquivalences]]]; 
     leftMorphismFunction = Association[Normal[Association[Thread[First /@ domainMorphismList -> 
            First /@ leftImageMorphismList]]] //. {compositionSymbol[x_, compositionSymbol[y_, z_]] :> 
          compositionSymbol[compositionSymbol[x, y], z], newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
          newCompositionSymbol[newCompositionSymbol[x, y], z]}]; rightImageMorphismList = 
      Select[reduceArrowsFinalWithDuplicates[reduceArrowsInitialWithDuplicates[rightArrowListWithDuplicates, 
         arrowEquivalences /. Normal[rightArrowMappings]], quiverObjectEquivalences /. Normal[rightObjectMappings]], 
       First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[rightImageCompositions = Select[Tuples[rightImageMorphismList, 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ rightImageMorphismList, 
            StringDelete[ToString[newCompositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], rightImageMorphismList = 
           Append[rightImageMorphismList, newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ rightImageCompositions, 
      Length[reduceObjectsWithDuplicates[rightObjectListWithDuplicates, quiverObjectEquivalences /. 
         Normal[rightObjectMappings]]]]; rightImageMorphismList = Select[rightImageMorphismList, 
       Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[rightImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        rightImageMorphismList = Append[rightImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      reduceObjectsWithDuplicates[rightObjectListWithDuplicates, quiverObjectEquivalences /. 
        Normal[rightObjectMappings]]; rightImageMorphismList = reduceArrowsFinalWithDuplicates[
       reduceArrowsInitialWithDuplicates[rightImageMorphismList, If[covariant === True, 
         DeleteDuplicates[Join[morphismEquivalences /. compositionSymbol -> newCompositionSymbol /. 
            Normal[rightArrowMappings], rightMorphismEquivalences]], DeleteDuplicates[
          Join[morphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[rightArrowMappings] /. 
            {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> newCompositionSymbol[z, newCompositionSymbol[y, 
                x]], newCompositionSymbol[newCompositionSymbol[x_, y_], z_] :> newCompositionSymbol[newCompositionSymbol[
                z, y], x], newCompositionSymbol[x_, y_] :> newCompositionSymbol[y, x]}, rightMorphismEquivalences]]]], 
       DeleteDuplicates[Join[objectEquivalences /. Normal[rightObjectMappings], rightObjectEquivalences]]]; 
     rightMorphismFunction = Association[Normal[Association[Thread[First /@ domainMorphismList -> 
            First /@ rightImageMorphismList]]] //. {compositionSymbol[x_, compositionSymbol[y_, z_]] :> 
          compositionSymbol[compositionSymbol[x, y], z], newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
          newCompositionSymbol[newCompositionSymbol[x, y], z]}]; naturalMorphismEquivalences = {}; 
     (Module[{morphism = #1 //. {compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[
              compositionSymbol[x, y], z], newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
             newCompositionSymbol[newCompositionSymbol[x, y], z]}}, naturalMorphismEquivalences = 
         Append[naturalMorphismEquivalences, newCompositionSymbol[reduceComponentNames[reduceComponentNames[
               reduceComponentNames[componentNames, quiverObjectEquivalences], objectEquivalences], 
              componentEquivalences][Last[Last[morphism]]], leftMorphismFunction[First[morphism]]] == 
           newCompositionSymbol[rightMorphismFunction[First[morphism]], reduceComponentNames[reduceComponentNames[
               reduceComponentNames[componentNames, quiverObjectEquivalences], objectEquivalences], 
              componentEquivalences][First[Last[morphism]]]]]] & ) /@ 
      Normal[reduceArrowsFinal[reduceArrowsInitial[domainMorphismAssociation, morphismEquivalences], 
        objectEquivalences]]; DeleteDuplicates[naturalMorphismEquivalences]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractNaturalTransformation[Association["Category" -> (abstractCategory_)[
       Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
        "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
        "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
           "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
           "Objects" -> objects_List]]]], "ComponentEquivalences" -> componentEquivalences_List, 
     "ComponentNames" -> componentNames_Association, "Covariant" -> covariant_, 
     "LeftArrowMappings" -> leftArrowMappings_Association, "LeftMorphismEquivalences" -> leftMorphismEquivalences_List, 
     "LeftNewArrows" -> leftNewArrows_Association, "LeftNewObjects" -> leftNewObjects_List, 
     "LeftObjectEquivalences" -> leftObjectEquivalences_List, "LeftObjectMappings" -> leftObjectMappings_Association, 
     "NewCompositionSymbol" -> newCompositionSymbol_, "NewIdentitySymbol" -> newIdentitySymbol_, 
     "RightArrowMappings" -> rightArrowMappings_Association, "RightMorphismEquivalences" -> 
      rightMorphismEquivalences_List, "RightNewArrows" -> rightNewArrows_Association, 
     "RightNewObjects" -> rightNewObjects_List, "RightObjectEquivalences" -> rightObjectEquivalences_List, 
     "RightObjectMappings" -> rightObjectMappings_Association]]["NaturalIsomorphisms"] := 
  Module[{domainMorphismAssociation, domainCompositions, leftObjectFunction, rightObjectFunction, 
     leftObjectListWithDuplicates, leftArrowListWithDuplicates, rightObjectListWithDuplicates, 
     rightArrowListWithDuplicates, domainMorphismList, domainCompositionsList, leftImageMorphismList, 
     leftImageCompositions, leftMorphismFunction, rightImageMorphismList, rightImageCompositions, rightMorphismFunction, 
     naturalArrows, naturalMorphismEquivalences, naturalMorphismAssociation, naturalCompositions, 
     leftImageQuiverObjectEquivalences, leftImageObjectEquivalences, leftImageArrowEquivalences, 
     leftImageMorphismEquivalences, rightImageQuiverObjectEquivalences, rightImageObjectEquivalences, 
     rightImageArrowEquivalences, rightImageMorphismEquivalences, objectEquivalenceGraph, morphismEquivalenceGraph, 
     componentAssociation, naturalIsomorphisms}, 
    domainMorphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[domainCompositions = Select[Tuples[Normal[domainMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[domainMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          domainMorphismAssociation = Association[Append[Normal[domainMorphismAssociation], 
             compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ domainCompositions, Length[objects]]; 
     domainMorphismAssociation = Association[Select[Normal[domainMorphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[domainMorphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        domainMorphismAssociation = Association[Append[Normal[domainMorphismAssociation], 
           identitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ objects; 
     leftObjectFunction = Join[Association[(#1 -> #1 & ) /@ objects], leftObjectMappings]; 
     rightObjectFunction = Join[Association[(#1 -> #1 & ) /@ objects], rightObjectMappings]; 
     leftObjectListWithDuplicates = objects /. Normal[leftObjectMappings]; leftArrowListWithDuplicates = 
      If[covariant === True, Normal[arrows] /. Normal[leftArrowMappings] /. Normal[leftObjectMappings], 
       (First[#1] -> Reverse[Last[#1]] & ) /@ (Normal[arrows] /. Normal[leftArrowMappings] /. 
         Normal[leftObjectMappings])]; rightObjectListWithDuplicates = objects /. Normal[rightObjectMappings]; 
     rightArrowListWithDuplicates = If[covariant === True, Normal[arrows] /. Normal[rightArrowMappings] /. 
        Normal[rightObjectMappings], (First[#1] -> Reverse[Last[#1]] & ) /@ 
        (Normal[arrows] /. Normal[rightArrowMappings] /. Normal[rightObjectMappings])]; 
     domainMorphismList = Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[domainCompositionsList = Select[Tuples[domainMorphismList, 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ domainMorphismList, 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], domainMorphismList = 
           Append[domainMorphismList, compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ domainCompositionsList, 
      Length[objects]]; domainMorphismList = Select[domainMorphismList, 
       Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        domainMorphismList = Append[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ objects; 
     leftImageMorphismList = Select[leftArrowListWithDuplicates, First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[leftImageCompositions = Select[Tuples[leftImageMorphismList, 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ leftImageMorphismList, 
            StringDelete[ToString[newCompositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], leftImageMorphismList = 
           Append[leftImageMorphismList, newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ leftImageCompositions, 
      Length[leftObjectListWithDuplicates]]; leftImageMorphismList = Select[leftImageMorphismList, 
       Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[leftImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        leftImageMorphismList = Append[leftImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      leftObjectListWithDuplicates; leftMorphismFunction = 
      Association[Normal[Association[Thread[First /@ domainMorphismList -> First /@ leftImageMorphismList]]] //. 
        {compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[compositionSymbol[x, y], z], 
         newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> newCompositionSymbol[newCompositionSymbol[x, y], z]}]; 
     rightImageMorphismList = Select[rightArrowListWithDuplicates, First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[rightImageCompositions = Select[Tuples[rightImageMorphismList, 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ rightImageMorphismList, 
            StringDelete[ToString[newCompositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], rightImageMorphismList = 
           Append[rightImageMorphismList, newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ rightImageCompositions, 
      Length[rightObjectListWithDuplicates]]; rightImageMorphismList = Select[rightImageMorphismList, 
       Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[rightImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        rightImageMorphismList = Append[rightImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      rightObjectListWithDuplicates; rightMorphismFunction = 
      Association[Normal[Association[Thread[First /@ domainMorphismList -> First /@ rightImageMorphismList]]] //. 
        {compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[compositionSymbol[x, y], z], 
         newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> newCompositionSymbol[newCompositionSymbol[x, y], z]}]; 
     naturalArrows = {}; naturalMorphismEquivalences = {}; 
     (Module[{morphism = #1 //. {compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[
              compositionSymbol[x, y], z], newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
             newCompositionSymbol[newCompositionSymbol[x, y], z]}}, 
        naturalArrows = Join[naturalArrows, {componentNames[First[Last[morphism]]] -> 
             DirectedEdge[leftObjectFunction[First[Last[morphism]]], rightObjectFunction[First[Last[morphism]]]], 
            componentNames[Last[Last[morphism]]] -> DirectedEdge[leftObjectFunction[Last[Last[morphism]]], 
              rightObjectFunction[Last[Last[morphism]]]]}]; naturalArrows = Join[naturalArrows, 
           {leftMorphismFunction[First[morphism]] -> DirectedEdge[leftObjectFunction[First[Last[morphism]]], 
              leftObjectFunction[Last[Last[morphism]]]], rightMorphismFunction[First[morphism]] -> 
             DirectedEdge[rightObjectFunction[First[Last[morphism]]], rightObjectFunction[Last[Last[morphism]]]]}]; 
         naturalMorphismEquivalences = Append[naturalMorphismEquivalences, 
           newCompositionSymbol[componentNames[Last[Last[morphism]]], leftMorphismFunction[First[morphism]]] == 
            newCompositionSymbol[rightMorphismFunction[First[morphism]], componentNames[First[Last[morphism]]]]]] & ) /@ 
      Normal[domainMorphismAssociation]; naturalArrows = Association[DeleteDuplicates[naturalArrows]]; 
     naturalMorphismEquivalences = DeleteDuplicates[naturalMorphismEquivalences]; 
     naturalMorphismAssociation = Association[Select[Normal[naturalArrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[naturalCompositions = Select[Tuples[Normal[naturalMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[naturalMorphismAssociation], StringDelete[ToString[newCompositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          naturalMorphismAssociation = Association[Append[Normal[naturalMorphismAssociation], 
             newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ naturalCompositions, Length[objects]]; 
     naturalMorphismAssociation = Association[Select[Normal[naturalMorphismAssociation], 
        Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[naturalMorphismAssociation], newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        naturalMorphismAssociation = Association[Append[Normal[naturalMorphismAssociation], 
           newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ DeleteDuplicates[
       Union[objects /. Normal[leftObjectMappings], objects /. Normal[rightObjectMappings]]]; 
     leftImageQuiverObjectEquivalences = quiverObjectEquivalences /. Normal[leftObjectMappings]; 
     leftImageObjectEquivalences = DeleteDuplicates[Join[objectEquivalences /. Normal[leftObjectMappings], 
        leftObjectEquivalences]]; leftImageArrowEquivalences = arrowEquivalences /. Normal[leftArrowMappings]; 
     leftImageMorphismEquivalences = If[covariant === True, DeleteDuplicates[
        Join[morphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[leftArrowMappings] /. 
          Normal[leftObjectMappings], leftMorphismEquivalences]], DeleteDuplicates[
        Join[morphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[leftArrowMappings] /. 
           Normal[leftObjectMappings] /. {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
            newCompositionSymbol[z, newCompositionSymbol[y, x]], newCompositionSymbol[newCompositionSymbol[x_, y_], 
             z_] :> newCompositionSymbol[newCompositionSymbol[z, y], x], newCompositionSymbol[x_, y_] :> 
            newCompositionSymbol[y, x]}, leftMorphismEquivalences]]]; rightImageQuiverObjectEquivalences = 
      quiverObjectEquivalences /. Normal[rightObjectMappings]; rightImageObjectEquivalences = 
      DeleteDuplicates[Join[objectEquivalences /. Normal[rightObjectMappings], rightObjectEquivalences]]; 
     rightImageArrowEquivalences = arrowEquivalences /. Normal[rightArrowMappings]; 
     rightImageMorphismEquivalences = If[covariant === True, DeleteDuplicates[
        Join[morphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[rightArrowMappings] /. 
          Normal[rightObjectMappings], rightMorphismEquivalences]], DeleteDuplicates[
        Join[morphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[rightArrowMappings] /. 
           Normal[rightObjectMappings] /. {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
            newCompositionSymbol[z, newCompositionSymbol[y, x]], newCompositionSymbol[newCompositionSymbol[x_, y_], 
             z_] :> newCompositionSymbol[newCompositionSymbol[z, y], x], newCompositionSymbol[x_, y_] :> 
            newCompositionSymbol[y, x]}, rightMorphismEquivalences]]]; objectEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Union[leftImageQuiverObjectEquivalences, 
             leftObjectEquivalences, rightImageQuiverObjectEquivalences, rightObjectEquivalences], {1}]]]], 
        (UndirectedEdge[#1, #1] & ) /@ DeleteDuplicates[Union[objects /. Normal[leftObjectMappings], 
           objects /. Normal[rightObjectMappings]]]]]; morphismEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Union[leftImageArrowEquivalences, 
             leftImageMorphismEquivalences, rightImageArrowEquivalences, rightImageMorphismEquivalences, 
             naturalMorphismEquivalences, componentEquivalences], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ 
         First /@ Normal[naturalMorphismAssociation]]]; componentAssociation = {}; 
     (Module[{object = #1}, componentAssociation = Append[componentAssociation, componentNames[object] -> 
           DirectedEdge[leftObjectFunction[object], rightObjectFunction[object]]]] & ) /@ objects; 
     naturalIsomorphisms = {}; (Module[{morphism = #1, morphisms, isRetraction, isSection}, 
        morphisms = Select[Normal[naturalMorphismAssociation], Length[FindShortestPath[objectEquivalenceGraph, 
                Last[Last[#1]], First[Last[morphism]]]] > 0 && Length[FindShortestPath[objectEquivalenceGraph, 
                First[Last[#1]], Last[Last[morphism]]]] > 0 & ]; isRetraction = False; isSection = False; 
         (If[morphism === (newIdentitySymbol[#1] -> DirectedEdge[#1, #1]), isRetraction = True] & ) /@ objects; 
         (If[morphism === (newIdentitySymbol[#1] -> DirectedEdge[#1, #1]), isSection = True] & ) /@ objects; 
         (Module[{newMorphism = #1, equivalentObjects}, If[MemberQ[VertexList[morphismEquivalenceGraph], 
               newCompositionSymbol[First[morphism], First[newMorphism]]], equivalentObjects = 
                Union[VertexComponent[objectEquivalenceGraph, Last[Last[morphism]]], VertexComponent[
                  objectEquivalenceGraph, First[Last[newMorphism]]]]; (If[MemberQ[VertexList[morphismEquivalenceGraph], 
                   newIdentitySymbol[#1]], If[Length[FindShortestPath[morphismEquivalenceGraph, newCompositionSymbol[
                       First[morphism], First[newMorphism]], newIdentitySymbol[#1]]] > 0, isRetraction = True]] & ) /@ 
                equivalentObjects]; If[MemberQ[VertexList[morphismEquivalenceGraph], newCompositionSymbol[
                First[newMorphism], First[morphism]]], equivalentObjects = Union[VertexComponent[objectEquivalenceGraph, 
                  First[Last[morphism]]], VertexComponent[objectEquivalenceGraph, Last[Last[newMorphism]]]]; 
               (If[MemberQ[VertexList[morphismEquivalenceGraph], newIdentitySymbol[#1]], 
                  If[Length[FindShortestPath[morphismEquivalenceGraph, newCompositionSymbol[First[newMorphism], 
                       First[morphism]], newIdentitySymbol[#1]]] > 0, isSection = True]] & ) /@ 
                equivalentObjects]] & ) /@ morphisms; naturalIsomorphisms = Append[naturalIsomorphisms, 
           First[morphism] -> isRetraction && isSection]] & ) /@ Normal[componentAssociation]; 
     Association[naturalIsomorphisms]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"
AbstractNaturalTransformation[Association["Category" -> (abstractCategory_)[
       Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
        "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
        "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
           "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
           "Objects" -> objects_List]]]], "ComponentEquivalences" -> componentEquivalences_List, 
     "ComponentNames" -> componentNames_Association, "Covariant" -> covariant_, 
     "LeftArrowMappings" -> leftArrowMappings_Association, "LeftMorphismEquivalences" -> leftMorphismEquivalences_List, 
     "LeftNewArrows" -> leftNewArrows_Association, "LeftNewObjects" -> leftNewObjects_List, 
     "LeftObjectEquivalences" -> leftObjectEquivalences_List, "LeftObjectMappings" -> leftObjectMappings_Association, 
     "NewCompositionSymbol" -> newCompositionSymbol_, "NewIdentitySymbol" -> newIdentitySymbol_, 
     "RightArrowMappings" -> rightArrowMappings_Association, "RightMorphismEquivalences" -> 
      rightMorphismEquivalences_List, "RightNewArrows" -> rightNewArrows_Association, 
     "RightNewObjects" -> rightNewObjects_List, "RightObjectEquivalences" -> rightObjectEquivalences_List, 
     "RightObjectMappings" -> rightObjectMappings_Association]]["ReducedNaturalIsomorphisms"] := 
  Module[{domainMorphismAssociation, domainCompositions, leftObjectFunction, rightObjectFunction, 
     leftObjectListWithDuplicates, leftArrowListWithDuplicates, rightObjectListWithDuplicates, 
     rightArrowListWithDuplicates, domainMorphismList, domainCompositionsList, leftImageMorphismList, 
     leftImageCompositions, leftMorphismFunction, rightImageMorphismList, rightImageCompositions, rightMorphismFunction, 
     naturalArrows, naturalMorphismEquivalences, naturalMorphismAssociation, naturalCompositions, 
     leftImageQuiverObjectEquivalences, leftImageObjectEquivalences, leftImageArrowEquivalences, 
     leftImageMorphismEquivalences, rightImageQuiverObjectEquivalences, rightImageObjectEquivalences, 
     rightImageArrowEquivalences, rightImageMorphismEquivalences, objectEquivalenceGraph, morphismEquivalenceGraph, 
     reducedLeftObjectFunction, reducedRightObjectFunction, reducedComponentAssociation, reducedNaturalIsomorphisms}, 
    domainMorphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[domainCompositions = Select[Tuples[Normal[domainMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[domainMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          domainMorphismAssociation = Association[Append[Normal[domainMorphismAssociation], 
             compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ domainCompositions, Length[objects]]; 
     domainMorphismAssociation = Association[Select[Normal[domainMorphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[domainMorphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        domainMorphismAssociation = Association[Append[Normal[domainMorphismAssociation], 
           identitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ objects; 
     leftObjectFunction = Join[Association[(#1 -> #1 & ) /@ objects], leftObjectMappings]; 
     rightObjectFunction = Join[Association[(#1 -> #1 & ) /@ objects], rightObjectMappings]; 
     leftObjectListWithDuplicates = objects /. Normal[leftObjectMappings]; leftArrowListWithDuplicates = 
      If[covariant === True, Normal[arrows] /. Normal[leftArrowMappings] /. Normal[leftObjectMappings], 
       (First[#1] -> Reverse[Last[#1]] & ) /@ (Normal[arrows] /. Normal[leftArrowMappings] /. 
         Normal[leftObjectMappings])]; rightObjectListWithDuplicates = objects /. Normal[rightObjectMappings]; 
     rightArrowListWithDuplicates = If[covariant === True, Normal[arrows] /. Normal[rightArrowMappings] /. 
        Normal[rightObjectMappings], (First[#1] -> Reverse[Last[#1]] & ) /@ 
        (Normal[arrows] /. Normal[rightArrowMappings] /. Normal[rightObjectMappings])]; 
     domainMorphismList = Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[domainCompositionsList = Select[Tuples[domainMorphismList, 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ domainMorphismList, 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], domainMorphismList = 
           Append[domainMorphismList, compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ domainCompositionsList, 
      Length[objects]]; domainMorphismList = Select[domainMorphismList, 
       Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        domainMorphismList = Append[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ objects; 
     leftImageMorphismList = Select[leftArrowListWithDuplicates, First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[leftImageCompositions = Select[Tuples[leftImageMorphismList, 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ leftImageMorphismList, 
            StringDelete[ToString[newCompositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], leftImageMorphismList = 
           Append[leftImageMorphismList, newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ leftImageCompositions, 
      Length[leftObjectListWithDuplicates]]; leftImageMorphismList = Select[leftImageMorphismList, 
       Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[leftImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        leftImageMorphismList = Append[leftImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      leftObjectListWithDuplicates; leftMorphismFunction = 
      Association[Normal[Association[Thread[First /@ domainMorphismList -> First /@ leftImageMorphismList]]] //. 
        {compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[compositionSymbol[x, y], z], 
         newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> newCompositionSymbol[newCompositionSymbol[x, y], z]}]; 
     rightImageMorphismList = Select[rightArrowListWithDuplicates, First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[rightImageCompositions = Select[Tuples[rightImageMorphismList, 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ rightImageMorphismList, 
            StringDelete[ToString[newCompositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], rightImageMorphismList = 
           Append[rightImageMorphismList, newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ rightImageCompositions, 
      Length[rightObjectListWithDuplicates]]; rightImageMorphismList = Select[rightImageMorphismList, 
       Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[rightImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        rightImageMorphismList = Append[rightImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      rightObjectListWithDuplicates; rightMorphismFunction = 
      Association[Normal[Association[Thread[First /@ domainMorphismList -> First /@ rightImageMorphismList]]] //. 
        {compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[compositionSymbol[x, y], z], 
         newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> newCompositionSymbol[newCompositionSymbol[x, y], z]}]; 
     naturalArrows = {}; naturalMorphismEquivalences = {}; 
     (Module[{morphism = #1 //. {compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[
              compositionSymbol[x, y], z], newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
             newCompositionSymbol[newCompositionSymbol[x, y], z]}}, 
        naturalArrows = Join[naturalArrows, {componentNames[First[Last[morphism]]] -> 
             DirectedEdge[leftObjectFunction[First[Last[morphism]]], rightObjectFunction[First[Last[morphism]]]], 
            componentNames[Last[Last[morphism]]] -> DirectedEdge[leftObjectFunction[Last[Last[morphism]]], 
              rightObjectFunction[Last[Last[morphism]]]]}]; naturalArrows = Join[naturalArrows, 
           {leftMorphismFunction[First[morphism]] -> DirectedEdge[leftObjectFunction[First[Last[morphism]]], 
              leftObjectFunction[Last[Last[morphism]]]], rightMorphismFunction[First[morphism]] -> 
             DirectedEdge[rightObjectFunction[First[Last[morphism]]], rightObjectFunction[Last[Last[morphism]]]]}]; 
         naturalMorphismEquivalences = Append[naturalMorphismEquivalences, 
           newCompositionSymbol[componentNames[Last[Last[morphism]]], leftMorphismFunction[First[morphism]]] == 
            newCompositionSymbol[rightMorphismFunction[First[morphism]], componentNames[First[Last[morphism]]]]]] & ) /@ 
      Normal[domainMorphismAssociation]; naturalArrows = Association[DeleteDuplicates[naturalArrows]]; 
     naturalMorphismEquivalences = DeleteDuplicates[naturalMorphismEquivalences]; 
     naturalMorphismAssociation = Association[Select[Normal[naturalArrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[naturalCompositions = Select[Tuples[Normal[naturalMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[naturalMorphismAssociation], StringDelete[ToString[newCompositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          naturalMorphismAssociation = Association[Append[Normal[naturalMorphismAssociation], 
             newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ naturalCompositions, Length[objects]]; 
     naturalMorphismAssociation = Association[Select[Normal[naturalMorphismAssociation], 
        Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[naturalMorphismAssociation], newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        naturalMorphismAssociation = Association[Append[Normal[naturalMorphismAssociation], 
           newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ DeleteDuplicates[
       Union[objects /. Normal[leftObjectMappings], objects /. Normal[rightObjectMappings]]]; 
     leftImageQuiverObjectEquivalences = quiverObjectEquivalences /. Normal[leftObjectMappings]; 
     leftImageObjectEquivalences = DeleteDuplicates[Join[objectEquivalences /. Normal[leftObjectMappings], 
        leftObjectEquivalences]]; leftImageArrowEquivalences = arrowEquivalences /. Normal[leftArrowMappings]; 
     leftImageMorphismEquivalences = If[covariant === True, DeleteDuplicates[
        Join[morphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[leftArrowMappings] /. 
          Normal[leftObjectMappings], leftMorphismEquivalences]], DeleteDuplicates[
        Join[morphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[leftArrowMappings] /. 
           Normal[leftObjectMappings] /. {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
            newCompositionSymbol[z, newCompositionSymbol[y, x]], newCompositionSymbol[newCompositionSymbol[x_, y_], 
             z_] :> newCompositionSymbol[newCompositionSymbol[z, y], x], newCompositionSymbol[x_, y_] :> 
            newCompositionSymbol[y, x]}, leftMorphismEquivalences]]]; rightImageQuiverObjectEquivalences = 
      quiverObjectEquivalences /. Normal[rightObjectMappings]; rightImageObjectEquivalences = 
      DeleteDuplicates[Join[objectEquivalences /. Normal[rightObjectMappings], rightObjectEquivalences]]; 
     rightImageArrowEquivalences = arrowEquivalences /. Normal[rightArrowMappings]; 
     rightImageMorphismEquivalences = If[covariant === True, DeleteDuplicates[
        Join[morphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[rightArrowMappings] /. 
          Normal[rightObjectMappings], rightMorphismEquivalences]], DeleteDuplicates[
        Join[morphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[rightArrowMappings] /. 
           Normal[rightObjectMappings] /. {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
            newCompositionSymbol[z, newCompositionSymbol[y, x]], newCompositionSymbol[newCompositionSymbol[x_, y_], 
             z_] :> newCompositionSymbol[newCompositionSymbol[z, y], x], newCompositionSymbol[x_, y_] :> 
            newCompositionSymbol[y, x]}, rightMorphismEquivalences]]]; objectEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Union[leftImageQuiverObjectEquivalences, 
             leftObjectEquivalences, rightImageQuiverObjectEquivalences, rightObjectEquivalences], {1}]]]], 
        (UndirectedEdge[#1, #1] & ) /@ DeleteDuplicates[Union[objects /. Normal[leftObjectMappings], 
           objects /. Normal[rightObjectMappings]]]]]; morphismEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Union[leftImageArrowEquivalences, 
             leftImageMorphismEquivalences, rightImageArrowEquivalences, rightImageMorphismEquivalences, 
             naturalMorphismEquivalences, componentEquivalences], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ 
         First /@ Normal[naturalMorphismAssociation]]]; reducedLeftObjectFunction = 
      Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, 
               quiverObjectEquivalences], objectEquivalences]]] -> reduceObjectsWithDuplicates[
           Values[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
               objectEquivalences]]], leftObjectEquivalences]]], 
       Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[leftObjectMappings], 
            quiverObjectEquivalences], objectEquivalences] -> reduceObjectsWithDuplicates[Values[leftObjectMappings], 
           leftObjectEquivalences]]]]; reducedRightObjectFunction = 
      Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, 
               quiverObjectEquivalences], objectEquivalences]]] -> reduceObjectsWithDuplicates[
           Values[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
               objectEquivalences]]], rightObjectEquivalences]]], 
       Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[rightObjectMappings], 
            quiverObjectEquivalences], objectEquivalences] -> reduceObjectsWithDuplicates[Values[rightObjectMappings], 
           rightObjectEquivalences]]]]; reducedComponentAssociation = {}; 
     (Module[{object = #1}, reducedComponentAssociation = Append[reducedComponentAssociation, 
          reduceComponentNames[reduceComponentNames[componentNames, quiverObjectEquivalences], objectEquivalences][
            object] -> DirectedEdge[reducedLeftObjectFunction[object], reducedRightObjectFunction[object]]]] & ) /@ 
      reduceObjects[reduceObjects[objects, quiverObjectEquivalences], objectEquivalences]; 
     reducedComponentAssociation = reduceArrowsInitial[Association[DeleteDuplicates[reducedComponentAssociation]], 
       componentEquivalences]; reducedNaturalIsomorphisms = {}; 
     (Module[{morphism = #1, morphisms, isRetraction, isSection}, 
        morphisms = Select[Normal[naturalMorphismAssociation], Length[FindShortestPath[objectEquivalenceGraph, 
                Last[Last[#1]], First[Last[morphism]]]] > 0 && Length[FindShortestPath[objectEquivalenceGraph, 
                First[Last[#1]], Last[Last[morphism]]]] > 0 & ]; isRetraction = False; isSection = False; 
         (If[morphism === (newIdentitySymbol[#1] -> DirectedEdge[#1, #1]), isRetraction = True] & ) /@ objects; 
         (If[morphism === (newIdentitySymbol[#1] -> DirectedEdge[#1, #1]), isSection = True] & ) /@ objects; 
         (Module[{newMorphism = #1, equivalentObjects}, If[MemberQ[VertexList[morphismEquivalenceGraph], 
               newCompositionSymbol[First[morphism], First[newMorphism]]], equivalentObjects = 
                Union[VertexComponent[objectEquivalenceGraph, Last[Last[morphism]]], VertexComponent[
                  objectEquivalenceGraph, First[Last[newMorphism]]]]; (If[MemberQ[VertexList[morphismEquivalenceGraph], 
                   newIdentitySymbol[#1]], If[Length[FindShortestPath[morphismEquivalenceGraph, newCompositionSymbol[
                       First[morphism], First[newMorphism]], newIdentitySymbol[#1]]] > 0, isRetraction = True]] & ) /@ 
                equivalentObjects]; If[MemberQ[VertexList[morphismEquivalenceGraph], newCompositionSymbol[
                First[newMorphism], First[morphism]]], equivalentObjects = Union[VertexComponent[objectEquivalenceGraph, 
                  First[Last[morphism]]], VertexComponent[objectEquivalenceGraph, Last[Last[newMorphism]]]]; 
               (If[MemberQ[VertexList[morphismEquivalenceGraph], newIdentitySymbol[#1]], 
                  If[Length[FindShortestPath[morphismEquivalenceGraph, newCompositionSymbol[First[newMorphism], 
                       First[morphism]], newIdentitySymbol[#1]]] > 0, isSection = True]] & ) /@ 
                equivalentObjects]] & ) /@ morphisms; reducedNaturalIsomorphisms = Append[reducedNaturalIsomorphisms, 
           First[morphism] -> isRetraction && isSection]] & ) /@ Normal[reducedComponentAssociation]; 
     Association[reducedNaturalIsomorphisms]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"
AbstractNaturalTransformation[Association["Category" -> (abstractCategory_)[
       Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
        "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
        "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
           "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
           "Objects" -> objects_List]]]], "ComponentEquivalences" -> componentEquivalences_List, 
     "ComponentNames" -> componentNames_Association, "Covariant" -> covariant_, 
     "LeftArrowMappings" -> leftArrowMappings_Association, "LeftMorphismEquivalences" -> leftMorphismEquivalences_List, 
     "LeftNewArrows" -> leftNewArrows_Association, "LeftNewObjects" -> leftNewObjects_List, 
     "LeftObjectEquivalences" -> leftObjectEquivalences_List, "LeftObjectMappings" -> leftObjectMappings_Association, 
     "NewCompositionSymbol" -> newCompositionSymbol_, "NewIdentitySymbol" -> newIdentitySymbol_, 
     "RightArrowMappings" -> rightArrowMappings_Association, "RightMorphismEquivalences" -> 
      rightMorphismEquivalences_List, "RightNewArrows" -> rightNewArrows_Association, 
     "RightNewObjects" -> rightNewObjects_List, "RightObjectEquivalences" -> rightObjectEquivalences_List, 
     "RightObjectMappings" -> rightObjectMappings_Association]]["NaturalIsomorphismQ"] := 
  Module[{domainMorphismAssociation, domainCompositions, leftObjectFunction, rightObjectFunction, 
     leftObjectListWithDuplicates, leftArrowListWithDuplicates, rightObjectListWithDuplicates, 
     rightArrowListWithDuplicates, domainMorphismList, domainCompositionsList, leftImageMorphismList, 
     leftImageCompositions, leftMorphismFunction, rightImageMorphismList, rightImageCompositions, rightMorphismFunction, 
     naturalArrows, naturalMorphismEquivalences, naturalMorphismAssociation, naturalCompositions, 
     leftImageQuiverObjectEquivalences, leftImageObjectEquivalences, leftImageArrowEquivalences, 
     leftImageMorphismEquivalences, rightImageQuiverObjectEquivalences, rightImageObjectEquivalences, 
     rightImageArrowEquivalences, rightImageMorphismEquivalences, objectEquivalenceGraph, morphismEquivalenceGraph, 
     reducedLeftObjectFunction, reducedRightObjectFunction, reducedComponentAssociation, reducedNaturalIsomorphisms}, 
    domainMorphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[domainCompositions = Select[Tuples[Normal[domainMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[domainMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          domainMorphismAssociation = Association[Append[Normal[domainMorphismAssociation], 
             compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ domainCompositions, Length[objects]]; 
     domainMorphismAssociation = Association[Select[Normal[domainMorphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[domainMorphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        domainMorphismAssociation = Association[Append[Normal[domainMorphismAssociation], 
           identitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ objects; 
     leftObjectFunction = Join[Association[(#1 -> #1 & ) /@ objects], leftObjectMappings]; 
     rightObjectFunction = Join[Association[(#1 -> #1 & ) /@ objects], rightObjectMappings]; 
     leftObjectListWithDuplicates = objects /. Normal[leftObjectMappings]; leftArrowListWithDuplicates = 
      If[covariant === True, Normal[arrows] /. Normal[leftArrowMappings] /. Normal[leftObjectMappings], 
       (First[#1] -> Reverse[Last[#1]] & ) /@ (Normal[arrows] /. Normal[leftArrowMappings] /. 
         Normal[leftObjectMappings])]; rightObjectListWithDuplicates = objects /. Normal[rightObjectMappings]; 
     rightArrowListWithDuplicates = If[covariant === True, Normal[arrows] /. Normal[rightArrowMappings] /. 
        Normal[rightObjectMappings], (First[#1] -> Reverse[Last[#1]] & ) /@ 
        (Normal[arrows] /. Normal[rightArrowMappings] /. Normal[rightObjectMappings])]; 
     domainMorphismList = Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[domainCompositionsList = Select[Tuples[domainMorphismList, 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ domainMorphismList, 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], domainMorphismList = 
           Append[domainMorphismList, compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ domainCompositionsList, 
      Length[objects]]; domainMorphismList = Select[domainMorphismList, 
       Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        domainMorphismList = Append[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ objects; 
     leftImageMorphismList = Select[leftArrowListWithDuplicates, First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[leftImageCompositions = Select[Tuples[leftImageMorphismList, 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ leftImageMorphismList, 
            StringDelete[ToString[newCompositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], leftImageMorphismList = 
           Append[leftImageMorphismList, newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ leftImageCompositions, 
      Length[leftObjectListWithDuplicates]]; leftImageMorphismList = Select[leftImageMorphismList, 
       Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[leftImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        leftImageMorphismList = Append[leftImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      leftObjectListWithDuplicates; leftMorphismFunction = 
      Association[Normal[Association[Thread[First /@ domainMorphismList -> First /@ leftImageMorphismList]]] //. 
        {compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[compositionSymbol[x, y], z], 
         newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> newCompositionSymbol[newCompositionSymbol[x, y], z]}]; 
     rightImageMorphismList = Select[rightArrowListWithDuplicates, First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[rightImageCompositions = Select[Tuples[rightImageMorphismList, 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ rightImageMorphismList, 
            StringDelete[ToString[newCompositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], rightImageMorphismList = 
           Append[rightImageMorphismList, newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ rightImageCompositions, 
      Length[rightObjectListWithDuplicates]]; rightImageMorphismList = Select[rightImageMorphismList, 
       Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[rightImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        rightImageMorphismList = Append[rightImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      rightObjectListWithDuplicates; rightMorphismFunction = 
      Association[Normal[Association[Thread[First /@ domainMorphismList -> First /@ rightImageMorphismList]]] //. 
        {compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[compositionSymbol[x, y], z], 
         newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> newCompositionSymbol[newCompositionSymbol[x, y], z]}]; 
     naturalArrows = {}; naturalMorphismEquivalences = {}; 
     (Module[{morphism = #1 //. {compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[
              compositionSymbol[x, y], z], newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
             newCompositionSymbol[newCompositionSymbol[x, y], z]}}, 
        naturalArrows = Join[naturalArrows, {componentNames[First[Last[morphism]]] -> 
             DirectedEdge[leftObjectFunction[First[Last[morphism]]], rightObjectFunction[First[Last[morphism]]]], 
            componentNames[Last[Last[morphism]]] -> DirectedEdge[leftObjectFunction[Last[Last[morphism]]], 
              rightObjectFunction[Last[Last[morphism]]]]}]; naturalArrows = Join[naturalArrows, 
           {leftMorphismFunction[First[morphism]] -> DirectedEdge[leftObjectFunction[First[Last[morphism]]], 
              leftObjectFunction[Last[Last[morphism]]]], rightMorphismFunction[First[morphism]] -> 
             DirectedEdge[rightObjectFunction[First[Last[morphism]]], rightObjectFunction[Last[Last[morphism]]]]}]; 
         naturalMorphismEquivalences = Append[naturalMorphismEquivalences, 
           newCompositionSymbol[componentNames[Last[Last[morphism]]], leftMorphismFunction[First[morphism]]] == 
            newCompositionSymbol[rightMorphismFunction[First[morphism]], componentNames[First[Last[morphism]]]]]] & ) /@ 
      Normal[domainMorphismAssociation]; naturalArrows = Association[DeleteDuplicates[naturalArrows]]; 
     naturalMorphismEquivalences = DeleteDuplicates[naturalMorphismEquivalences]; 
     naturalMorphismAssociation = Association[Select[Normal[naturalArrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[naturalCompositions = Select[Tuples[Normal[naturalMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[naturalMorphismAssociation], StringDelete[ToString[newCompositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          naturalMorphismAssociation = Association[Append[Normal[naturalMorphismAssociation], 
             newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ naturalCompositions, Length[objects]]; 
     naturalMorphismAssociation = Association[Select[Normal[naturalMorphismAssociation], 
        Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[naturalMorphismAssociation], newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        naturalMorphismAssociation = Association[Append[Normal[naturalMorphismAssociation], 
           newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ DeleteDuplicates[
       Union[objects /. Normal[leftObjectMappings], objects /. Normal[rightObjectMappings]]]; 
     leftImageQuiverObjectEquivalences = quiverObjectEquivalences /. Normal[leftObjectMappings]; 
     leftImageObjectEquivalences = DeleteDuplicates[Join[objectEquivalences /. Normal[leftObjectMappings], 
        leftObjectEquivalences]]; leftImageArrowEquivalences = arrowEquivalences /. Normal[leftArrowMappings]; 
     leftImageMorphismEquivalences = If[covariant === True, DeleteDuplicates[
        Join[morphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[leftArrowMappings] /. 
          Normal[leftObjectMappings], leftMorphismEquivalences]], DeleteDuplicates[
        Join[morphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[leftArrowMappings] /. 
           Normal[leftObjectMappings] /. {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
            newCompositionSymbol[z, newCompositionSymbol[y, x]], newCompositionSymbol[newCompositionSymbol[x_, y_], 
             z_] :> newCompositionSymbol[newCompositionSymbol[z, y], x], newCompositionSymbol[x_, y_] :> 
            newCompositionSymbol[y, x]}, leftMorphismEquivalences]]]; rightImageQuiverObjectEquivalences = 
      quiverObjectEquivalences /. Normal[rightObjectMappings]; rightImageObjectEquivalences = 
      DeleteDuplicates[Join[objectEquivalences /. Normal[rightObjectMappings], rightObjectEquivalences]]; 
     rightImageArrowEquivalences = arrowEquivalences /. Normal[rightArrowMappings]; 
     rightImageMorphismEquivalences = If[covariant === True, DeleteDuplicates[
        Join[morphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[rightArrowMappings] /. 
          Normal[rightObjectMappings], rightMorphismEquivalences]], DeleteDuplicates[
        Join[morphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[rightArrowMappings] /. 
           Normal[rightObjectMappings] /. {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
            newCompositionSymbol[z, newCompositionSymbol[y, x]], newCompositionSymbol[newCompositionSymbol[x_, y_], 
             z_] :> newCompositionSymbol[newCompositionSymbol[z, y], x], newCompositionSymbol[x_, y_] :> 
            newCompositionSymbol[y, x]}, rightMorphismEquivalences]]]; objectEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Union[leftImageQuiverObjectEquivalences, 
             leftObjectEquivalences, rightImageQuiverObjectEquivalences, rightObjectEquivalences], {1}]]]], 
        (UndirectedEdge[#1, #1] & ) /@ DeleteDuplicates[Union[objects /. Normal[leftObjectMappings], 
           objects /. Normal[rightObjectMappings]]]]]; morphismEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Union[leftImageArrowEquivalences, 
             leftImageMorphismEquivalences, rightImageArrowEquivalences, rightImageMorphismEquivalences, 
             naturalMorphismEquivalences, componentEquivalences], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ 
         First /@ Normal[naturalMorphismAssociation]]]; reducedLeftObjectFunction = 
      Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, 
               quiverObjectEquivalences], objectEquivalences]]] -> reduceObjectsWithDuplicates[
           Values[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
               objectEquivalences]]], leftObjectEquivalences]]], 
       Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[leftObjectMappings], 
            quiverObjectEquivalences], objectEquivalences] -> reduceObjectsWithDuplicates[Values[leftObjectMappings], 
           leftObjectEquivalences]]]]; reducedRightObjectFunction = 
      Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, 
               quiverObjectEquivalences], objectEquivalences]]] -> reduceObjectsWithDuplicates[
           Values[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
               objectEquivalences]]], rightObjectEquivalences]]], 
       Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[rightObjectMappings], 
            quiverObjectEquivalences], objectEquivalences] -> reduceObjectsWithDuplicates[Values[rightObjectMappings], 
           rightObjectEquivalences]]]]; reducedComponentAssociation = {}; 
     (Module[{object = #1}, reducedComponentAssociation = Append[reducedComponentAssociation, 
          reduceComponentNames[reduceComponentNames[componentNames, quiverObjectEquivalences], objectEquivalences][
            object] -> DirectedEdge[reducedLeftObjectFunction[object], reducedRightObjectFunction[object]]]] & ) /@ 
      reduceObjects[reduceObjects[objects, quiverObjectEquivalences], objectEquivalences]; 
     reducedComponentAssociation = reduceArrowsInitial[Association[DeleteDuplicates[reducedComponentAssociation]], 
       componentEquivalences]; reducedNaturalIsomorphisms = {}; 
     (Module[{morphism = #1, morphisms, isRetraction, isSection}, 
        morphisms = Select[Normal[naturalMorphismAssociation], Length[FindShortestPath[objectEquivalenceGraph, 
                Last[Last[#1]], First[Last[morphism]]]] > 0 && Length[FindShortestPath[objectEquivalenceGraph, 
                First[Last[#1]], Last[Last[morphism]]]] > 0 & ]; isRetraction = False; isSection = False; 
         (If[morphism === (newIdentitySymbol[#1] -> DirectedEdge[#1, #1]), isRetraction = True] & ) /@ objects; 
         (If[morphism === (newIdentitySymbol[#1] -> DirectedEdge[#1, #1]), isSection = True] & ) /@ objects; 
         (Module[{newMorphism = #1, equivalentObjects}, If[MemberQ[VertexList[morphismEquivalenceGraph], 
               newCompositionSymbol[First[morphism], First[newMorphism]]], equivalentObjects = 
                Union[VertexComponent[objectEquivalenceGraph, Last[Last[morphism]]], VertexComponent[
                  objectEquivalenceGraph, First[Last[newMorphism]]]]; (If[MemberQ[VertexList[morphismEquivalenceGraph], 
                   newIdentitySymbol[#1]], If[Length[FindShortestPath[morphismEquivalenceGraph, newCompositionSymbol[
                       First[morphism], First[newMorphism]], newIdentitySymbol[#1]]] > 0, isRetraction = True]] & ) /@ 
                equivalentObjects]; If[MemberQ[VertexList[morphismEquivalenceGraph], newCompositionSymbol[
                First[newMorphism], First[morphism]]], equivalentObjects = Union[VertexComponent[objectEquivalenceGraph, 
                  First[Last[morphism]]], VertexComponent[objectEquivalenceGraph, Last[Last[newMorphism]]]]; 
               (If[MemberQ[VertexList[morphismEquivalenceGraph], newIdentitySymbol[#1]], 
                  If[Length[FindShortestPath[morphismEquivalenceGraph, newCompositionSymbol[First[newMorphism], 
                       First[morphism]], newIdentitySymbol[#1]]] > 0, isSection = True]] & ) /@ 
                equivalentObjects]] & ) /@ morphisms; reducedNaturalIsomorphisms = Append[reducedNaturalIsomorphisms, 
           First[morphism] -> isRetraction && isSection]] & ) /@ Normal[reducedComponentAssociation]; 
     And @@ Last /@ Normal[Association[reducedNaturalIsomorphisms]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractNaturalTransformation[Association["Category" -> (abstractCategory_)[
       Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
        "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
        "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
           "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
           "Objects" -> objects_List]]]], "ComponentEquivalences" -> componentEquivalences_List, 
     "ComponentNames" -> componentNames_Association, "Covariant" -> covariant_, 
     "LeftArrowMappings" -> leftArrowMappings_Association, "LeftMorphismEquivalences" -> leftMorphismEquivalences_List, 
     "LeftNewArrows" -> leftNewArrows_Association, "LeftNewObjects" -> leftNewObjects_List, 
     "LeftObjectEquivalences" -> leftObjectEquivalences_List, "LeftObjectMappings" -> leftObjectMappings_Association, 
     "NewCompositionSymbol" -> newCompositionSymbol_, "NewIdentitySymbol" -> newIdentitySymbol_, 
     "RightArrowMappings" -> rightArrowMappings_Association, "RightMorphismEquivalences" -> 
      rightMorphismEquivalences_List, "RightNewArrows" -> rightNewArrows_Association, 
     "RightNewObjects" -> rightNewObjects_List, "RightObjectEquivalences" -> rightObjectEquivalences_List, 
     "RightObjectMappings" -> rightObjectMappings_Association]]["FullLabeledGraph"] := 
  Module[{domainMorphismAssociation, domainCompositions, leftObjectFunction, rightObjectFunction, 
     leftObjectListWithDuplicates, leftArrowListWithDuplicates, rightObjectListWithDuplicates, 
     rightArrowListWithDuplicates, domainMorphismList, domainCompositionsList, leftImageMorphismList, 
     leftImageCompositions, leftMorphismFunction, rightImageMorphismList, rightImageCompositions, rightMorphismFunction, 
     naturalArrows, naturalMorphismAssociation, naturalCompositions}, 
    domainMorphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[domainCompositions = Select[Tuples[Normal[domainMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[domainMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          domainMorphismAssociation = Association[Append[Normal[domainMorphismAssociation], 
             compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ domainCompositions, Length[objects]]; 
     domainMorphismAssociation = Association[Select[Normal[domainMorphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[domainMorphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        domainMorphismAssociation = Association[Append[Normal[domainMorphismAssociation], 
           identitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ objects; 
     leftObjectFunction = Join[Association[(#1 -> #1 & ) /@ objects], leftObjectMappings]; 
     rightObjectFunction = Join[Association[(#1 -> #1 & ) /@ objects], rightObjectMappings]; 
     leftObjectListWithDuplicates = objects /. Normal[leftObjectMappings]; leftArrowListWithDuplicates = 
      If[covariant === True, Normal[arrows] /. Normal[leftArrowMappings] /. Normal[leftObjectMappings], 
       (First[#1] -> Reverse[Last[#1]] & ) /@ (Normal[arrows] /. Normal[leftArrowMappings] /. 
         Normal[leftObjectMappings])]; rightObjectListWithDuplicates = objects /. Normal[rightObjectMappings]; 
     rightArrowListWithDuplicates = If[covariant === True, Normal[arrows] /. Normal[rightArrowMappings] /. 
        Normal[rightObjectMappings], (First[#1] -> Reverse[Last[#1]] & ) /@ 
        (Normal[arrows] /. Normal[rightArrowMappings] /. Normal[rightObjectMappings])]; 
     domainMorphismList = Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[domainCompositionsList = Select[Tuples[domainMorphismList, 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ domainMorphismList, 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], domainMorphismList = 
           Append[domainMorphismList, compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ domainCompositionsList, 
      Length[objects]]; domainMorphismList = Select[domainMorphismList, 
       Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        domainMorphismList = Append[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ objects; 
     leftImageMorphismList = Select[leftArrowListWithDuplicates, First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[leftImageCompositions = Select[Tuples[leftImageMorphismList, 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ leftImageMorphismList, 
            StringDelete[ToString[newCompositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], leftImageMorphismList = 
           Append[leftImageMorphismList, newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ leftImageCompositions, 
      Length[leftObjectListWithDuplicates]]; leftImageMorphismList = Select[leftImageMorphismList, 
       Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[leftImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        leftImageMorphismList = Append[leftImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      leftObjectListWithDuplicates; leftMorphismFunction = 
      Association[Normal[Association[Thread[First /@ domainMorphismList -> First /@ leftImageMorphismList]]] //. 
        {compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[compositionSymbol[x, y], z], 
         newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> newCompositionSymbol[newCompositionSymbol[x, y], z]}]; 
     rightImageMorphismList = Select[rightArrowListWithDuplicates, First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[rightImageCompositions = Select[Tuples[rightImageMorphismList, 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ rightImageMorphismList, 
            StringDelete[ToString[newCompositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], rightImageMorphismList = 
           Append[rightImageMorphismList, newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ rightImageCompositions, 
      Length[rightObjectListWithDuplicates]]; rightImageMorphismList = Select[rightImageMorphismList, 
       Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[rightImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        rightImageMorphismList = Append[rightImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      rightObjectListWithDuplicates; rightMorphismFunction = 
      Association[Normal[Association[Thread[First /@ domainMorphismList -> First /@ rightImageMorphismList]]] //. 
        {compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[compositionSymbol[x, y], z], 
         newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> newCompositionSymbol[newCompositionSymbol[x, y], z]}]; 
     naturalArrows = {}; 
     (Module[{morphism = #1 //. {compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[
              compositionSymbol[x, y], z], newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
             newCompositionSymbol[newCompositionSymbol[x, y], z]}}, 
        naturalArrows = Join[naturalArrows, {componentNames[First[Last[morphism]]] -> 
             DirectedEdge[leftObjectFunction[First[Last[morphism]]], rightObjectFunction[First[Last[morphism]]]], 
            componentNames[Last[Last[morphism]]] -> DirectedEdge[leftObjectFunction[Last[Last[morphism]]], 
              rightObjectFunction[Last[Last[morphism]]]]}]; naturalArrows = Join[naturalArrows, 
           {leftMorphismFunction[First[morphism]] -> DirectedEdge[leftObjectFunction[First[Last[morphism]]], 
              leftObjectFunction[Last[Last[morphism]]]], rightMorphismFunction[First[morphism]] -> 
             DirectedEdge[rightObjectFunction[First[Last[morphism]]], rightObjectFunction[Last[
                Last[morphism]]]]}]] & ) /@ Normal[domainMorphismAssociation]; 
     naturalArrows = Association[DeleteDuplicates[naturalArrows]]; naturalMorphismAssociation = 
      Association[Select[Normal[naturalArrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[naturalCompositions = Select[Tuples[Normal[naturalMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[naturalMorphismAssociation], StringDelete[ToString[newCompositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          naturalMorphismAssociation = Association[Append[Normal[naturalMorphismAssociation], 
             newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ naturalCompositions, Length[objects]]; 
     naturalMorphismAssociation = Association[Select[Normal[naturalMorphismAssociation], 
        Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[naturalMorphismAssociation], newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        naturalMorphismAssociation = Association[Append[Normal[naturalMorphismAssociation], 
           newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ DeleteDuplicates[
       Union[objects /. Normal[leftObjectMappings], objects /. Normal[rightObjectMappings]]]; 
     EdgeTaggedGraph[DeleteDuplicates[Union[objects /. Normal[leftObjectMappings], 
        objects /. Normal[rightObjectMappings]]], (Labeled[DirectedEdge @@ Last[#1], Placed[First[#1], 0.5]] & ) /@ 
       Normal[naturalMorphismAssociation], VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], 
      VertexLabels -> Placed["Name", Center], VertexLabelStyle -> Directive[Bold, 20], 
      EdgeLabelStyle -> Directive[Bold, 20], EdgeStyle -> Directive[Black, Thick], 
      GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractNaturalTransformation[Association["Category" -> (abstractCategory_)[
       Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
        "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
        "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
           "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
           "Objects" -> objects_List]]]], "ComponentEquivalences" -> componentEquivalences_List, 
     "ComponentNames" -> componentNames_Association, "Covariant" -> covariant_, 
     "LeftArrowMappings" -> leftArrowMappings_Association, "LeftMorphismEquivalences" -> leftMorphismEquivalences_List, 
     "LeftNewArrows" -> leftNewArrows_Association, "LeftNewObjects" -> leftNewObjects_List, 
     "LeftObjectEquivalences" -> leftObjectEquivalences_List, "LeftObjectMappings" -> leftObjectMappings_Association, 
     "NewCompositionSymbol" -> newCompositionSymbol_, "NewIdentitySymbol" -> newIdentitySymbol_, 
     "RightArrowMappings" -> rightArrowMappings_Association, "RightMorphismEquivalences" -> 
      rightMorphismEquivalences_List, "RightNewArrows" -> rightNewArrows_Association, 
     "RightNewObjects" -> rightNewObjects_List, "RightObjectEquivalences" -> rightObjectEquivalences_List, 
     "RightObjectMappings" -> rightObjectMappings_Association]]["FullUnlabeledGraph"] := 
  Module[{domainMorphismAssociation, domainCompositions, leftObjectFunction, rightObjectFunction, 
     leftObjectListWithDuplicates, leftArrowListWithDuplicates, rightObjectListWithDuplicates, 
     rightArrowListWithDuplicates, domainMorphismList, domainCompositionsList, leftImageMorphismList, 
     leftImageCompositions, leftMorphismFunction, rightImageMorphismList, rightImageCompositions, rightMorphismFunction, 
     naturalArrows, naturalMorphismAssociation, naturalCompositions}, 
    domainMorphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[domainCompositions = Select[Tuples[Normal[domainMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[domainMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          domainMorphismAssociation = Association[Append[Normal[domainMorphismAssociation], 
             compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ domainCompositions, Length[objects]]; 
     domainMorphismAssociation = Association[Select[Normal[domainMorphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[domainMorphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        domainMorphismAssociation = Association[Append[Normal[domainMorphismAssociation], 
           identitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ objects; 
     leftObjectFunction = Join[Association[(#1 -> #1 & ) /@ objects], leftObjectMappings]; 
     rightObjectFunction = Join[Association[(#1 -> #1 & ) /@ objects], rightObjectMappings]; 
     leftObjectListWithDuplicates = objects /. Normal[leftObjectMappings]; leftArrowListWithDuplicates = 
      If[covariant === True, Normal[arrows] /. Normal[leftArrowMappings] /. Normal[leftObjectMappings], 
       (First[#1] -> Reverse[Last[#1]] & ) /@ (Normal[arrows] /. Normal[leftArrowMappings] /. 
         Normal[leftObjectMappings])]; rightObjectListWithDuplicates = objects /. Normal[rightObjectMappings]; 
     rightArrowListWithDuplicates = If[covariant === True, Normal[arrows] /. Normal[rightArrowMappings] /. 
        Normal[rightObjectMappings], (First[#1] -> Reverse[Last[#1]] & ) /@ 
        (Normal[arrows] /. Normal[rightArrowMappings] /. Normal[rightObjectMappings])]; 
     domainMorphismList = Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[domainCompositionsList = Select[Tuples[domainMorphismList, 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ domainMorphismList, 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], domainMorphismList = 
           Append[domainMorphismList, compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ domainCompositionsList, 
      Length[objects]]; domainMorphismList = Select[domainMorphismList, 
       Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        domainMorphismList = Append[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ objects; 
     leftImageMorphismList = Select[leftArrowListWithDuplicates, First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[leftImageCompositions = Select[Tuples[leftImageMorphismList, 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ leftImageMorphismList, 
            StringDelete[ToString[newCompositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], leftImageMorphismList = 
           Append[leftImageMorphismList, newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ leftImageCompositions, 
      Length[leftObjectListWithDuplicates]]; leftImageMorphismList = Select[leftImageMorphismList, 
       Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[leftImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        leftImageMorphismList = Append[leftImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      leftObjectListWithDuplicates; leftMorphismFunction = 
      Association[Normal[Association[Thread[First /@ domainMorphismList -> First /@ leftImageMorphismList]]] //. 
        {compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[compositionSymbol[x, y], z], 
         newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> newCompositionSymbol[newCompositionSymbol[x, y], z]}]; 
     rightImageMorphismList = Select[rightArrowListWithDuplicates, First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[rightImageCompositions = Select[Tuples[rightImageMorphismList, 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ rightImageMorphismList, 
            StringDelete[ToString[newCompositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], rightImageMorphismList = 
           Append[rightImageMorphismList, newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ rightImageCompositions, 
      Length[rightObjectListWithDuplicates]]; rightImageMorphismList = Select[rightImageMorphismList, 
       Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[rightImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        rightImageMorphismList = Append[rightImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      rightObjectListWithDuplicates; rightMorphismFunction = 
      Association[Normal[Association[Thread[First /@ domainMorphismList -> First /@ rightImageMorphismList]]] //. 
        {compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[compositionSymbol[x, y], z], 
         newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> newCompositionSymbol[newCompositionSymbol[x, y], z]}]; 
     naturalArrows = {}; 
     (Module[{morphism = #1 //. {compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[
              compositionSymbol[x, y], z], newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
             newCompositionSymbol[newCompositionSymbol[x, y], z]}}, 
        naturalArrows = Join[naturalArrows, {componentNames[First[Last[morphism]]] -> 
             DirectedEdge[leftObjectFunction[First[Last[morphism]]], rightObjectFunction[First[Last[morphism]]]], 
            componentNames[Last[Last[morphism]]] -> DirectedEdge[leftObjectFunction[Last[Last[morphism]]], 
              rightObjectFunction[Last[Last[morphism]]]]}]; naturalArrows = Join[naturalArrows, 
           {leftMorphismFunction[First[morphism]] -> DirectedEdge[leftObjectFunction[First[Last[morphism]]], 
              leftObjectFunction[Last[Last[morphism]]]], rightMorphismFunction[First[morphism]] -> 
             DirectedEdge[rightObjectFunction[First[Last[morphism]]], rightObjectFunction[Last[
                Last[morphism]]]]}]] & ) /@ Normal[domainMorphismAssociation]; 
     naturalArrows = Association[DeleteDuplicates[naturalArrows]]; naturalMorphismAssociation = 
      Association[Select[Normal[naturalArrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[naturalCompositions = Select[Tuples[Normal[naturalMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[naturalMorphismAssociation], StringDelete[ToString[newCompositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          naturalMorphismAssociation = Association[Append[Normal[naturalMorphismAssociation], 
             newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ naturalCompositions, Length[objects]]; 
     naturalMorphismAssociation = Association[Select[Normal[naturalMorphismAssociation], 
        Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[naturalMorphismAssociation], newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        naturalMorphismAssociation = Association[Append[Normal[naturalMorphismAssociation], 
           newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ DeleteDuplicates[
       Union[objects /. Normal[leftObjectMappings], objects /. Normal[rightObjectMappings]]]; 
     EdgeTaggedGraph[DeleteDuplicates[Union[objects /. Normal[leftObjectMappings], 
        objects /. Normal[rightObjectMappings]]], (DirectedEdge @@ Last[#1] & ) /@ Normal[naturalMorphismAssociation], 
      VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], VertexLabels -> Placed["Name", Center], 
      VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
      EdgeStyle -> Directive[Black, Thick], GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractNaturalTransformation[Association["Category" -> (abstractCategory_)[
       Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
        "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
        "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
           "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
           "Objects" -> objects_List]]]], "ComponentEquivalences" -> componentEquivalences_List, 
     "ComponentNames" -> componentNames_Association, "Covariant" -> covariant_, 
     "LeftArrowMappings" -> leftArrowMappings_Association, "LeftMorphismEquivalences" -> leftMorphismEquivalences_List, 
     "LeftNewArrows" -> leftNewArrows_Association, "LeftNewObjects" -> leftNewObjects_List, 
     "LeftObjectEquivalences" -> leftObjectEquivalences_List, "LeftObjectMappings" -> leftObjectMappings_Association, 
     "NewCompositionSymbol" -> newCompositionSymbol_, "NewIdentitySymbol" -> newIdentitySymbol_, 
     "RightArrowMappings" -> rightArrowMappings_Association, "RightMorphismEquivalences" -> 
      rightMorphismEquivalences_List, "RightNewArrows" -> rightNewArrows_Association, 
     "RightNewObjects" -> rightNewObjects_List, "RightObjectEquivalences" -> rightObjectEquivalences_List, 
     "RightObjectMappings" -> rightObjectMappings_Association]]["ReducedLabeledGraph"] := 
  Module[{domainMorphismAssociation, domainCompositions, leftObjectFunction, rightObjectFunction, 
     leftObjectListWithDuplicates, leftArrowListWithDuplicates, rightObjectListWithDuplicates, 
     rightArrowListWithDuplicates, domainMorphismList, domainCompositionsList, leftImageMorphismList, 
     leftImageCompositions, leftMorphismFunction, rightImageMorphismList, rightImageCompositions, rightMorphismFunction, 
     naturalArrows, naturalMorphismEquivalences, naturalMorphismAssociation, naturalCompositions}, 
    domainMorphismAssociation = Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[arrows, 
           arrowEquivalences], quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[domainCompositions = Select[Tuples[Normal[domainMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[domainMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          domainMorphismAssociation = Association[Append[Normal[domainMorphismAssociation], 
             compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ domainCompositions, Length[reduceObjects[objects, quiverObjectEquivalences]]]; 
     domainMorphismAssociation = Association[Select[Normal[domainMorphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[domainMorphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        domainMorphismAssociation = Association[Append[Normal[domainMorphismAssociation], 
           identitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[objects, quiverObjectEquivalences]; 
     leftObjectFunction = Join[Association[
        Thread[Keys[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
              objectEquivalences]]] -> reduceObjectsWithDuplicates[Values[Association[(#1 -> #1 & ) /@ 
              reduceObjects[reduceObjects[objects, quiverObjectEquivalences], objectEquivalences]]], 
           leftObjectEquivalences]]], Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[
            Keys[leftObjectMappings], quiverObjectEquivalences], objectEquivalences] -> reduceObjectsWithDuplicates[
           Values[leftObjectMappings], leftObjectEquivalences]]]]; rightObjectFunction = 
      Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, 
               quiverObjectEquivalences], objectEquivalences]]] -> reduceObjectsWithDuplicates[
           Values[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
               objectEquivalences]]], rightObjectEquivalences]]], 
       Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[rightObjectMappings], 
            quiverObjectEquivalences], objectEquivalences] -> reduceObjectsWithDuplicates[Values[rightObjectMappings], 
           rightObjectEquivalences]]]]; leftObjectListWithDuplicates = objects /. Normal[leftObjectMappings]; 
     leftArrowListWithDuplicates = If[covariant === True, Normal[arrows] /. Normal[leftArrowMappings] /. 
        Normal[leftObjectMappings], (First[#1] -> Reverse[Last[#1]] & ) /@ 
        (Normal[arrows] /. Normal[leftArrowMappings] /. Normal[leftObjectMappings])]; 
     rightObjectListWithDuplicates = objects /. Normal[rightObjectMappings]; rightArrowListWithDuplicates = 
      If[covariant === True, Normal[arrows] /. Normal[rightArrowMappings] /. Normal[rightObjectMappings], 
       (First[#1] -> Reverse[Last[#1]] & ) /@ (Normal[arrows] /. Normal[rightArrowMappings] /. 
         Normal[rightObjectMappings])]; domainMorphismList = Select[reduceArrowsFinalWithDuplicates[
        reduceArrowsInitialWithDuplicates[Normal[arrows], arrowEquivalences], quiverObjectEquivalences], 
       First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[domainCompositionsList = Select[Tuples[domainMorphismList, 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ domainMorphismList, 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], domainMorphismList = 
           Append[domainMorphismList, compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ domainCompositionsList, 
      Length[reduceObjectsWithDuplicates[objects, quiverObjectEquivalences]]]; 
     domainMorphismList = Select[domainMorphismList, Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        domainMorphismList = Append[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      reduceObjectsWithDuplicates[objects, quiverObjectEquivalences]; domainMorphismList = 
      reduceArrowsFinalWithDuplicates[reduceArrowsInitialWithDuplicates[domainMorphismList, morphismEquivalences], 
       objectEquivalences]; leftImageMorphismList = Select[reduceArrowsFinalWithDuplicates[
        reduceArrowsInitialWithDuplicates[leftArrowListWithDuplicates, arrowEquivalences /. Normal[leftArrowMappings]], 
        quiverObjectEquivalences /. Normal[leftObjectMappings]], First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[leftImageCompositions = Select[Tuples[leftImageMorphismList, 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ leftImageMorphismList, 
            StringDelete[ToString[newCompositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], leftImageMorphismList = 
           Append[leftImageMorphismList, newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ leftImageCompositions, 
      Length[reduceObjectsWithDuplicates[leftObjectListWithDuplicates, quiverObjectEquivalences /. 
         Normal[leftObjectMappings]]]]; leftImageMorphismList = Select[leftImageMorphismList, 
       Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[leftImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        leftImageMorphismList = Append[leftImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      reduceObjectsWithDuplicates[leftObjectListWithDuplicates, quiverObjectEquivalences /. Normal[leftObjectMappings]]; 
     leftImageMorphismList = reduceArrowsFinalWithDuplicates[reduceArrowsInitialWithDuplicates[leftImageMorphismList, 
        If[covariant === True, DeleteDuplicates[Join[morphismEquivalences /. compositionSymbol -> newCompositionSymbol /. 
            Normal[leftArrowMappings], leftMorphismEquivalences]], DeleteDuplicates[
          Join[morphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[leftArrowMappings] /. 
            {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> newCompositionSymbol[z, newCompositionSymbol[y, 
                x]], newCompositionSymbol[newCompositionSymbol[x_, y_], z_] :> newCompositionSymbol[newCompositionSymbol[
                z, y], x], newCompositionSymbol[x_, y_] :> newCompositionSymbol[y, x]}, leftMorphismEquivalences]]]], 
       DeleteDuplicates[Join[objectEquivalences /. Normal[leftObjectMappings], leftObjectEquivalences]]]; 
     leftMorphismFunction = Association[Normal[Association[Thread[First /@ domainMorphismList -> 
            First /@ leftImageMorphismList]]] //. {compositionSymbol[x_, compositionSymbol[y_, z_]] :> 
          compositionSymbol[compositionSymbol[x, y], z], newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
          newCompositionSymbol[newCompositionSymbol[x, y], z]}]; rightImageMorphismList = 
      Select[reduceArrowsFinalWithDuplicates[reduceArrowsInitialWithDuplicates[rightArrowListWithDuplicates, 
         arrowEquivalences /. Normal[rightArrowMappings]], quiverObjectEquivalences /. Normal[rightObjectMappings]], 
       First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[rightImageCompositions = Select[Tuples[rightImageMorphismList, 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ rightImageMorphismList, 
            StringDelete[ToString[newCompositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], rightImageMorphismList = 
           Append[rightImageMorphismList, newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ rightImageCompositions, 
      Length[reduceObjectsWithDuplicates[rightObjectListWithDuplicates, quiverObjectEquivalences /. 
         Normal[rightObjectMappings]]]]; rightImageMorphismList = Select[rightImageMorphismList, 
       Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[rightImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        rightImageMorphismList = Append[rightImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      reduceObjectsWithDuplicates[rightObjectListWithDuplicates, quiverObjectEquivalences /. 
        Normal[rightObjectMappings]]; rightImageMorphismList = reduceArrowsFinalWithDuplicates[
       reduceArrowsInitialWithDuplicates[rightImageMorphismList, If[covariant === True, 
         DeleteDuplicates[Join[morphismEquivalences /. compositionSymbol -> newCompositionSymbol /. 
            Normal[rightArrowMappings], rightMorphismEquivalences]], DeleteDuplicates[
          Join[morphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[rightArrowMappings] /. 
            {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> newCompositionSymbol[z, newCompositionSymbol[y, 
                x]], newCompositionSymbol[newCompositionSymbol[x_, y_], z_] :> newCompositionSymbol[newCompositionSymbol[
                z, y], x], newCompositionSymbol[x_, y_] :> newCompositionSymbol[y, x]}, rightMorphismEquivalences]]]], 
       DeleteDuplicates[Join[objectEquivalences /. Normal[rightObjectMappings], rightObjectEquivalences]]]; 
     rightMorphismFunction = Association[Normal[Association[Thread[First /@ domainMorphismList -> 
            First /@ rightImageMorphismList]]] //. {compositionSymbol[x_, compositionSymbol[y_, z_]] :> 
          compositionSymbol[compositionSymbol[x, y], z], newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
          newCompositionSymbol[newCompositionSymbol[x, y], z]}]; naturalArrows = {}; naturalMorphismEquivalences = {}; 
     (Module[{morphism = #1 //. {compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[
              compositionSymbol[x, y], z], newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
             newCompositionSymbol[newCompositionSymbol[x, y], z]}}, 
        naturalArrows = Join[naturalArrows, {reduceComponentNames[reduceComponentNames[componentNames, 
                quiverObjectEquivalences], objectEquivalences][First[Last[morphism]]] -> 
             DirectedEdge[leftObjectFunction[First[Last[morphism]]], rightObjectFunction[First[Last[morphism]]]], 
            reduceComponentNames[reduceComponentNames[componentNames, quiverObjectEquivalences], objectEquivalences][
              Last[Last[morphism]]] -> DirectedEdge[leftObjectFunction[Last[Last[morphism]]], rightObjectFunction[Last[
                Last[morphism]]]]}]; naturalArrows = Join[naturalArrows, {leftMorphismFunction[First[morphism]] -> 
             DirectedEdge[leftObjectFunction[First[Last[morphism]]], leftObjectFunction[Last[Last[morphism]]]], 
            rightMorphismFunction[First[morphism]] -> DirectedEdge[rightObjectFunction[First[Last[morphism]]], 
              rightObjectFunction[Last[Last[morphism]]]]}]; naturalMorphismEquivalences = 
          Append[naturalMorphismEquivalences, newCompositionSymbol[reduceComponentNames[reduceComponentNames[
                componentNames, quiverObjectEquivalences], objectEquivalences][Last[Last[morphism]]], 
             leftMorphismFunction[First[morphism]]] == newCompositionSymbol[rightMorphismFunction[First[morphism]], 
             reduceComponentNames[reduceComponentNames[componentNames, quiverObjectEquivalences], objectEquivalences][
              First[Last[morphism]]]]]] & ) /@ Normal[reduceArrowsFinal[reduceArrowsInitial[domainMorphismAssociation, 
         morphismEquivalences], objectEquivalences]]; naturalArrows = Association[DeleteDuplicates[naturalArrows]]; 
     naturalMorphismAssociation = Association[Select[Normal[naturalArrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[naturalCompositions = Select[Tuples[Normal[naturalMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[naturalMorphismAssociation], StringDelete[ToString[newCompositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          naturalMorphismAssociation = Association[Append[Normal[naturalMorphismAssociation], 
             newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ naturalCompositions, Length[objects]]; 
     naturalMorphismAssociation = Association[Normal[Association[Select[Normal[naturalMorphismAssociation], 
           Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == Length[DeleteDuplicates[Flatten[
                {First[#1] /. newCompositionSymbol -> List}]]] & ]]] //. 
        {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> newCompositionSymbol[newCompositionSymbol[x, y], z]}]; 
     (If[ !MemberQ[Normal[naturalMorphismAssociation], newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        naturalMorphismAssociation = Association[Append[Normal[naturalMorphismAssociation], 
           newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ DeleteDuplicates[
       Catenate[({First[Last[#1]], Last[Last[#1]]} & ) /@ Normal[naturalMorphismAssociation]]]; 
     EdgeTaggedGraph[DeleteDuplicates[Catenate[({First[Last[#1]], Last[Last[#1]]} & ) /@ 
         Normal[naturalMorphismAssociation]]], (Labeled[DirectedEdge @@ Last[#1], Placed[First[#1], 0.5]] & ) /@ 
       Normal[reduceArrowsInitial[reduceArrowsInitial[reduceArrowsInitial[naturalMorphismAssociation, 
           naturalMorphismEquivalences //. {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
              newCompositionSymbol[newCompositionSymbol[x, y], z]}], Join[morphismEquivalences /. 
            Normal[leftMorphismFunction], morphismEquivalences /. Normal[rightMorphismFunction]]], 
         componentEquivalences]], VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], 
      VertexLabels -> Placed["Name", Center], VertexLabelStyle -> Directive[Bold, 20], 
      EdgeLabelStyle -> Directive[Bold, 20], EdgeStyle -> Directive[Black, Thick], 
      GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractNaturalTransformation[Association["Category" -> (abstractCategory_)[
       Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
        "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
        "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
           "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
           "Objects" -> objects_List]]]], "ComponentEquivalences" -> componentEquivalences_List, 
     "ComponentNames" -> componentNames_Association, "Covariant" -> covariant_, 
     "LeftArrowMappings" -> leftArrowMappings_Association, "LeftMorphismEquivalences" -> leftMorphismEquivalences_List, 
     "LeftNewArrows" -> leftNewArrows_Association, "LeftNewObjects" -> leftNewObjects_List, 
     "LeftObjectEquivalences" -> leftObjectEquivalences_List, "LeftObjectMappings" -> leftObjectMappings_Association, 
     "NewCompositionSymbol" -> newCompositionSymbol_, "NewIdentitySymbol" -> newIdentitySymbol_, 
     "RightArrowMappings" -> rightArrowMappings_Association, "RightMorphismEquivalences" -> 
      rightMorphismEquivalences_List, "RightNewArrows" -> rightNewArrows_Association, 
     "RightNewObjects" -> rightNewObjects_List, "RightObjectEquivalences" -> rightObjectEquivalences_List, 
     "RightObjectMappings" -> rightObjectMappings_Association]]["ReducedUnlabeledGraph"] := 
  Module[{domainMorphismAssociation, domainCompositions, leftObjectFunction, rightObjectFunction, 
     leftObjectListWithDuplicates, leftArrowListWithDuplicates, rightObjectListWithDuplicates, 
     rightArrowListWithDuplicates, domainMorphismList, domainCompositionsList, leftImageMorphismList, 
     leftImageCompositions, leftMorphismFunction, rightImageMorphismList, rightImageCompositions, rightMorphismFunction, 
     naturalArrows, naturalMorphismEquivalences, naturalMorphismAssociation, naturalCompositions}, 
    domainMorphismAssociation = Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[arrows, 
           arrowEquivalences], quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[domainCompositions = Select[Tuples[Normal[domainMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[domainMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          domainMorphismAssociation = Association[Append[Normal[domainMorphismAssociation], 
             compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ domainCompositions, Length[reduceObjects[objects, quiverObjectEquivalences]]]; 
     domainMorphismAssociation = Association[Select[Normal[domainMorphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[domainMorphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        domainMorphismAssociation = Association[Append[Normal[domainMorphismAssociation], 
           identitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[objects, quiverObjectEquivalences]; 
     leftObjectFunction = Join[Association[
        Thread[Keys[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
              objectEquivalences]]] -> reduceObjectsWithDuplicates[Values[Association[(#1 -> #1 & ) /@ 
              reduceObjects[reduceObjects[objects, quiverObjectEquivalences], objectEquivalences]]], 
           leftObjectEquivalences]]], Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[
            Keys[leftObjectMappings], quiverObjectEquivalences], objectEquivalences] -> reduceObjectsWithDuplicates[
           Values[leftObjectMappings], leftObjectEquivalences]]]]; rightObjectFunction = 
      Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, 
               quiverObjectEquivalences], objectEquivalences]]] -> reduceObjectsWithDuplicates[
           Values[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
               objectEquivalences]]], rightObjectEquivalences]]], 
       Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[rightObjectMappings], 
            quiverObjectEquivalences], objectEquivalences] -> reduceObjectsWithDuplicates[Values[rightObjectMappings], 
           rightObjectEquivalences]]]]; leftObjectListWithDuplicates = objects /. Normal[leftObjectMappings]; 
     leftArrowListWithDuplicates = If[covariant === True, Normal[arrows] /. Normal[leftArrowMappings] /. 
        Normal[leftObjectMappings], (First[#1] -> Reverse[Last[#1]] & ) /@ 
        (Normal[arrows] /. Normal[leftArrowMappings] /. Normal[leftObjectMappings])]; 
     rightObjectListWithDuplicates = objects /. Normal[rightObjectMappings]; rightArrowListWithDuplicates = 
      If[covariant === True, Normal[arrows] /. Normal[rightArrowMappings] /. Normal[rightObjectMappings], 
       (First[#1] -> Reverse[Last[#1]] & ) /@ (Normal[arrows] /. Normal[rightArrowMappings] /. 
         Normal[rightObjectMappings])]; domainMorphismList = Select[reduceArrowsFinalWithDuplicates[
        reduceArrowsInitialWithDuplicates[Normal[arrows], arrowEquivalences], quiverObjectEquivalences], 
       First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[domainCompositionsList = Select[Tuples[domainMorphismList, 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ domainMorphismList, 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], domainMorphismList = 
           Append[domainMorphismList, compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ domainCompositionsList, 
      Length[reduceObjectsWithDuplicates[objects, quiverObjectEquivalences]]]; 
     domainMorphismList = Select[domainMorphismList, Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        domainMorphismList = Append[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      reduceObjectsWithDuplicates[objects, quiverObjectEquivalences]; domainMorphismList = 
      reduceArrowsFinalWithDuplicates[reduceArrowsInitialWithDuplicates[domainMorphismList, morphismEquivalences], 
       objectEquivalences]; leftImageMorphismList = Select[reduceArrowsFinalWithDuplicates[
        reduceArrowsInitialWithDuplicates[leftArrowListWithDuplicates, arrowEquivalences /. Normal[leftArrowMappings]], 
        quiverObjectEquivalences /. Normal[leftObjectMappings]], First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[leftImageCompositions = Select[Tuples[leftImageMorphismList, 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ leftImageMorphismList, 
            StringDelete[ToString[newCompositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], leftImageMorphismList = 
           Append[leftImageMorphismList, newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ leftImageCompositions, 
      Length[reduceObjectsWithDuplicates[leftObjectListWithDuplicates, quiverObjectEquivalences /. 
         Normal[leftObjectMappings]]]]; leftImageMorphismList = Select[leftImageMorphismList, 
       Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[leftImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        leftImageMorphismList = Append[leftImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      reduceObjectsWithDuplicates[leftObjectListWithDuplicates, quiverObjectEquivalences /. Normal[leftObjectMappings]]; 
     leftImageMorphismList = reduceArrowsFinalWithDuplicates[reduceArrowsInitialWithDuplicates[leftImageMorphismList, 
        If[covariant === True, DeleteDuplicates[Join[morphismEquivalences /. compositionSymbol -> newCompositionSymbol /. 
            Normal[leftArrowMappings], leftMorphismEquivalences]], DeleteDuplicates[
          Join[morphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[leftArrowMappings] /. 
            {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> newCompositionSymbol[z, newCompositionSymbol[y, 
                x]], newCompositionSymbol[newCompositionSymbol[x_, y_], z_] :> newCompositionSymbol[newCompositionSymbol[
                z, y], x], newCompositionSymbol[x_, y_] :> newCompositionSymbol[y, x]}, leftMorphismEquivalences]]]], 
       DeleteDuplicates[Join[objectEquivalences /. Normal[leftObjectMappings], leftObjectEquivalences]]]; 
     leftMorphismFunction = Association[Normal[Association[Thread[First /@ domainMorphismList -> 
            First /@ leftImageMorphismList]]] //. {compositionSymbol[x_, compositionSymbol[y_, z_]] :> 
          newCompositionSymbol[compositionSymbol[x, y], z], newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
          newCompositionSymbol[newCompositionSymbol[x, y], z]}]; rightImageMorphismList = 
      Select[reduceArrowsFinalWithDuplicates[reduceArrowsInitialWithDuplicates[rightArrowListWithDuplicates, 
         arrowEquivalences /. Normal[rightArrowMappings]], quiverObjectEquivalences /. Normal[rightObjectMappings]], 
       First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[rightImageCompositions = Select[Tuples[rightImageMorphismList, 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ rightImageMorphismList, 
            StringDelete[ToString[newCompositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], rightImageMorphismList = 
           Append[rightImageMorphismList, newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ rightImageCompositions, 
      Length[reduceObjectsWithDuplicates[rightObjectListWithDuplicates, quiverObjectEquivalences /. 
         Normal[rightObjectMappings]]]]; rightImageMorphismList = Select[rightImageMorphismList, 
       Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[rightImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        rightImageMorphismList = Append[rightImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      reduceObjectsWithDuplicates[rightObjectListWithDuplicates, quiverObjectEquivalences /. 
        Normal[rightObjectMappings]]; rightImageMorphismList = reduceArrowsFinalWithDuplicates[
       reduceArrowsInitialWithDuplicates[rightImageMorphismList, If[covariant === True, 
         DeleteDuplicates[Join[morphismEquivalences /. compositionSymbol -> newCompositionSymbol /. 
            Normal[rightArrowMappings], rightMorphismEquivalences]], DeleteDuplicates[
          Join[morphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[rightArrowMappings] /. 
            {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> newCompositionSymbol[z, newCompositionSymbol[y, 
                x]], newCompositionSymbol[newCompositionSymbol[x_, y_], z_] :> newCompositionSymbol[newCompositionSymbol[
                z, y], x], newCompositionSymbol[x_, y_] :> newCompositionSymbol[y, x]}, rightMorphismEquivalences]]]], 
       DeleteDuplicates[Join[objectEquivalences /. Normal[rightObjectMappings], rightObjectEquivalences]]]; 
     rightMorphismFunction = Association[Normal[Association[Thread[First /@ domainMorphismList -> 
            First /@ rightImageMorphismList]]] //. {compositionSymbol[x_, compositionSymbol[y_, z_]] :> 
          compositionSymbol[compositionSymbol[x, y], z], newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
          newCompositionSymbol[newCompositionSymbol[x, y], z]}]; naturalArrows = {}; naturalMorphismEquivalences = {}; 
     (Module[{morphism = #1 //. {compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[
              compositionSymbol[x, y], z], newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
             newCompositionSymbol[newCompositionSymbol[x, y], z]}}, 
        naturalArrows = Join[naturalArrows, {reduceComponentNames[reduceComponentNames[componentNames, 
                quiverObjectEquivalences], objectEquivalences][First[Last[morphism]]] -> 
             DirectedEdge[leftObjectFunction[First[Last[morphism]]], rightObjectFunction[First[Last[morphism]]]], 
            reduceComponentNames[reduceComponentNames[componentNames, quiverObjectEquivalences], objectEquivalences][
              Last[Last[morphism]]] -> DirectedEdge[leftObjectFunction[Last[Last[morphism]]], rightObjectFunction[Last[
                Last[morphism]]]]}]; naturalArrows = Join[naturalArrows, {leftMorphismFunction[First[morphism]] -> 
             DirectedEdge[leftObjectFunction[First[Last[morphism]]], leftObjectFunction[Last[Last[morphism]]]], 
            rightMorphismFunction[First[morphism]] -> DirectedEdge[rightObjectFunction[First[Last[morphism]]], 
              rightObjectFunction[Last[Last[morphism]]]]}]; naturalMorphismEquivalences = 
          Append[naturalMorphismEquivalences, newCompositionSymbol[reduceComponentNames[reduceComponentNames[
                componentNames, quiverObjectEquivalences], objectEquivalences][Last[Last[morphism]]], 
             leftMorphismFunction[First[morphism]]] == newCompositionSymbol[rightMorphismFunction[First[morphism]], 
             reduceComponentNames[reduceComponentNames[componentNames, quiverObjectEquivalences], objectEquivalences][
              First[Last[morphism]]]]]] & ) /@ Normal[reduceArrowsFinal[reduceArrowsInitial[domainMorphismAssociation, 
         morphismEquivalences], objectEquivalences]]; naturalArrows = Association[DeleteDuplicates[naturalArrows]]; 
     naturalMorphismAssociation = Association[Select[Normal[naturalArrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[naturalCompositions = Select[Tuples[Normal[naturalMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[naturalMorphismAssociation], StringDelete[ToString[newCompositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          naturalMorphismAssociation = Association[Append[Normal[naturalMorphismAssociation], 
             newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ naturalCompositions, Length[objects]]; 
     naturalMorphismAssociation = Association[Normal[Association[Select[Normal[naturalMorphismAssociation], 
           Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == Length[DeleteDuplicates[Flatten[
                {First[#1] /. newCompositionSymbol -> List}]]] & ]]] //. 
        {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> newCompositionSymbol[newCompositionSymbol[x, y], z]}]; 
     (If[ !MemberQ[Normal[naturalMorphismAssociation], newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        naturalMorphismAssociation = Association[Append[Normal[naturalMorphismAssociation], 
           newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ DeleteDuplicates[
       Catenate[({First[Last[#1]], Last[Last[#1]]} & ) /@ Normal[naturalMorphismAssociation]]]; 
     EdgeTaggedGraph[DeleteDuplicates[Catenate[({First[Last[#1]], Last[Last[#1]]} & ) /@ 
         Normal[naturalMorphismAssociation]]], (DirectedEdge @@ Last[#1] & ) /@ 
       Normal[reduceArrowsInitial[reduceArrowsInitial[reduceArrowsInitial[naturalMorphismAssociation, 
           naturalMorphismEquivalences //. {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
              newCompositionSymbol[newCompositionSymbol[x, y], z]}], Join[morphismEquivalences /. 
            Normal[leftMorphismFunction], morphismEquivalences /. Normal[rightMorphismFunction]]], 
         componentEquivalences]], VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], 
      VertexLabels -> Placed["Name", Center], VertexLabelStyle -> Directive[Bold, 20], 
      EdgeLabelStyle -> Directive[Bold, 20], EdgeStyle -> Directive[Black, Thick], 
      GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractNaturalTransformation[Association["Category" -> (abstractCategory_)[
       Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
        "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
        "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
           "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
           "Objects" -> objects_List]]]], "ComponentEquivalences" -> componentEquivalences_List, 
     "ComponentNames" -> componentNames_Association, "Covariant" -> covariant_, 
     "LeftArrowMappings" -> leftArrowMappings_Association, "LeftMorphismEquivalences" -> leftMorphismEquivalences_List, 
     "LeftNewArrows" -> leftNewArrows_Association, "LeftNewObjects" -> leftNewObjects_List, 
     "LeftObjectEquivalences" -> leftObjectEquivalences_List, "LeftObjectMappings" -> leftObjectMappings_Association, 
     "NewCompositionSymbol" -> newCompositionSymbol_, "NewIdentitySymbol" -> newIdentitySymbol_, 
     "RightArrowMappings" -> rightArrowMappings_Association, "RightMorphismEquivalences" -> 
      rightMorphismEquivalences_List, "RightNewArrows" -> rightNewArrows_Association, 
     "RightNewObjects" -> rightNewObjects_List, "RightObjectEquivalences" -> rightObjectEquivalences_List, 
     "RightObjectMappings" -> rightObjectMappings_Association]]["SimpleLabeledGraph"] := 
  Module[{domainMorphismAssociation, domainCompositions, leftObjectFunction, rightObjectFunction, 
     leftObjectListWithDuplicates, leftArrowListWithDuplicates, rightObjectListWithDuplicates, 
     rightArrowListWithDuplicates, domainMorphismList, domainCompositionsList, leftImageMorphismList, 
     leftImageCompositions, leftMorphismFunction, rightImageMorphismList, rightImageCompositions, rightMorphismFunction, 
     naturalArrows, naturalMorphismAssociation, naturalCompositions}, 
    domainMorphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[domainCompositions = Select[Tuples[Normal[domainMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[domainMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          domainMorphismAssociation = Association[Append[Normal[domainMorphismAssociation], 
             compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ domainCompositions, Length[objects]]; 
     domainMorphismAssociation = Association[Select[Normal[domainMorphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[domainMorphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        domainMorphismAssociation = Association[Append[Normal[domainMorphismAssociation], 
           identitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ objects; 
     leftObjectFunction = Join[Association[(#1 -> #1 & ) /@ objects], leftObjectMappings]; 
     rightObjectFunction = Join[Association[(#1 -> #1 & ) /@ objects], rightObjectMappings]; 
     leftObjectListWithDuplicates = objects /. Normal[leftObjectMappings]; leftArrowListWithDuplicates = 
      If[covariant === True, Normal[arrows] /. Normal[leftArrowMappings] /. Normal[leftObjectMappings], 
       (First[#1] -> Reverse[Last[#1]] & ) /@ (Normal[arrows] /. Normal[leftArrowMappings] /. 
         Normal[leftObjectMappings])]; rightObjectListWithDuplicates = objects /. Normal[rightObjectMappings]; 
     rightArrowListWithDuplicates = If[covariant === True, Normal[arrows] /. Normal[rightArrowMappings] /. 
        Normal[rightObjectMappings], (First[#1] -> Reverse[Last[#1]] & ) /@ 
        (Normal[arrows] /. Normal[rightArrowMappings] /. Normal[rightObjectMappings])]; 
     domainMorphismList = Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[domainCompositionsList = Select[Tuples[domainMorphismList, 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ domainMorphismList, 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], domainMorphismList = 
           Append[domainMorphismList, compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ domainCompositionsList, 
      Length[objects]]; domainMorphismList = Select[domainMorphismList, 
       Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        domainMorphismList = Append[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ objects; 
     leftImageMorphismList = Select[leftArrowListWithDuplicates, First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[leftImageCompositions = Select[Tuples[leftImageMorphismList, 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ leftImageMorphismList, 
            StringDelete[ToString[newCompositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], leftImageMorphismList = 
           Append[leftImageMorphismList, newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ leftImageCompositions, 
      Length[leftObjectListWithDuplicates]]; leftImageMorphismList = Select[leftImageMorphismList, 
       Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[leftImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        leftImageMorphismList = Append[leftImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      leftObjectListWithDuplicates; leftMorphismFunction = 
      Association[Normal[Association[Thread[First /@ domainMorphismList -> First /@ leftImageMorphismList]]] //. 
        {compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[compositionSymbol[x, y], z], 
         newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> newCompositionSymbol[newCompositionSymbol[x, y], z]}]; 
     rightImageMorphismList = Select[rightArrowListWithDuplicates, First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[rightImageCompositions = Select[Tuples[rightImageMorphismList, 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ rightImageMorphismList, 
            StringDelete[ToString[newCompositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], rightImageMorphismList = 
           Append[rightImageMorphismList, newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ rightImageCompositions, 
      Length[rightObjectListWithDuplicates]]; rightImageMorphismList = Select[rightImageMorphismList, 
       Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[rightImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        rightImageMorphismList = Append[rightImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      rightObjectListWithDuplicates; rightMorphismFunction = 
      Association[Normal[Association[Thread[First /@ domainMorphismList -> First /@ rightImageMorphismList]]] //. 
        {compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[compositionSymbol[x, y], z], 
         newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> newCompositionSymbol[newCompositionSymbol[x, y], z]}]; 
     naturalArrows = {}; 
     (Module[{morphism = #1 //. {compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[
              compositionSymbol[x, y], z], newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
             newCompositionSymbol[newCompositionSymbol[x, y], z]}}, 
        naturalArrows = Join[naturalArrows, {componentNames[First[Last[morphism]]] -> 
             DirectedEdge[leftObjectFunction[First[Last[morphism]]], rightObjectFunction[First[Last[morphism]]]], 
            componentNames[Last[Last[morphism]]] -> DirectedEdge[leftObjectFunction[Last[Last[morphism]]], 
              rightObjectFunction[Last[Last[morphism]]]]}]; naturalArrows = Join[naturalArrows, 
           {leftMorphismFunction[First[morphism]] -> DirectedEdge[leftObjectFunction[First[Last[morphism]]], 
              leftObjectFunction[Last[Last[morphism]]]], rightMorphismFunction[First[morphism]] -> 
             DirectedEdge[rightObjectFunction[First[Last[morphism]]], rightObjectFunction[Last[
                Last[morphism]]]]}]] & ) /@ Normal[domainMorphismAssociation]; 
     naturalArrows = Association[DeleteDuplicates[naturalArrows]]; naturalMorphismAssociation = 
      Association[Select[Normal[naturalArrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[naturalCompositions = Select[Tuples[Normal[naturalMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[naturalMorphismAssociation], StringDelete[ToString[newCompositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          naturalMorphismAssociation = Association[Append[Normal[naturalMorphismAssociation], 
             newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ naturalCompositions, Length[objects]]; 
     naturalMorphismAssociation = Association[Select[Normal[naturalMorphismAssociation], 
        Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[naturalMorphismAssociation], newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        naturalMorphismAssociation = Association[Append[Normal[naturalMorphismAssociation], 
           newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ DeleteDuplicates[
       Union[objects /. Normal[leftObjectMappings], objects /. Normal[rightObjectMappings]]]; 
     EdgeTaggedGraph[DeleteDuplicates[Union[objects /. Normal[leftObjectMappings], 
        objects /. Normal[rightObjectMappings]]], (Labeled[DirectedEdge @@ Last[#1], Placed[First[#1], 0.5]] & ) /@ 
       Select[DeleteDuplicatesBy[Normal[naturalMorphismAssociation], DirectedEdge @@ Last[#1] & ], 
        First[Last[#1]] =!= Last[Last[#1]] & ], VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], 
      VertexLabels -> Placed["Name", Center], VertexLabelStyle -> Directive[Bold, 20], 
      EdgeLabelStyle -> Directive[Bold, 20], EdgeStyle -> Directive[Black, Thick], 
      GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractNaturalTransformation[Association["Category" -> (abstractCategory_)[
       Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
        "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
        "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
           "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
           "Objects" -> objects_List]]]], "ComponentEquivalences" -> componentEquivalences_List, 
     "ComponentNames" -> componentNames_Association, "Covariant" -> covariant_, 
     "LeftArrowMappings" -> leftArrowMappings_Association, "LeftMorphismEquivalences" -> leftMorphismEquivalences_List, 
     "LeftNewArrows" -> leftNewArrows_Association, "LeftNewObjects" -> leftNewObjects_List, 
     "LeftObjectEquivalences" -> leftObjectEquivalences_List, "LeftObjectMappings" -> leftObjectMappings_Association, 
     "NewCompositionSymbol" -> newCompositionSymbol_, "NewIdentitySymbol" -> newIdentitySymbol_, 
     "RightArrowMappings" -> rightArrowMappings_Association, "RightMorphismEquivalences" -> 
      rightMorphismEquivalences_List, "RightNewArrows" -> rightNewArrows_Association, 
     "RightNewObjects" -> rightNewObjects_List, "RightObjectEquivalences" -> rightObjectEquivalences_List, 
     "RightObjectMappings" -> rightObjectMappings_Association]]["SimpleUnlabeledGraph"] := 
  Module[{domainMorphismAssociation, domainCompositions, leftObjectFunction, rightObjectFunction, 
     leftObjectListWithDuplicates, leftArrowListWithDuplicates, rightObjectListWithDuplicates, 
     rightArrowListWithDuplicates, domainMorphismList, domainCompositionsList, leftImageMorphismList, 
     leftImageCompositions, leftMorphismFunction, rightImageMorphismList, rightImageCompositions, rightMorphismFunction, 
     naturalArrows, naturalMorphismAssociation, naturalCompositions}, 
    domainMorphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[domainCompositions = Select[Tuples[Normal[domainMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[domainMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          domainMorphismAssociation = Association[Append[Normal[domainMorphismAssociation], 
             compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ domainCompositions, Length[objects]]; 
     domainMorphismAssociation = Association[Select[Normal[domainMorphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[domainMorphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        domainMorphismAssociation = Association[Append[Normal[domainMorphismAssociation], 
           identitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ objects; 
     leftObjectFunction = Join[Association[(#1 -> #1 & ) /@ objects], leftObjectMappings]; 
     rightObjectFunction = Join[Association[(#1 -> #1 & ) /@ objects], rightObjectMappings]; 
     leftObjectListWithDuplicates = objects /. Normal[leftObjectMappings]; leftArrowListWithDuplicates = 
      If[covariant === True, Normal[arrows] /. Normal[leftArrowMappings] /. Normal[leftObjectMappings], 
       (First[#1] -> Reverse[Last[#1]] & ) /@ (Normal[arrows] /. Normal[leftArrowMappings] /. 
         Normal[leftObjectMappings])]; rightObjectListWithDuplicates = objects /. Normal[rightObjectMappings]; 
     rightArrowListWithDuplicates = If[covariant === True, Normal[arrows] /. Normal[rightArrowMappings] /. 
        Normal[rightObjectMappings], (First[#1] -> Reverse[Last[#1]] & ) /@ 
        (Normal[arrows] /. Normal[rightArrowMappings] /. Normal[rightObjectMappings])]; 
     domainMorphismList = Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[domainCompositionsList = Select[Tuples[domainMorphismList, 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ domainMorphismList, 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], domainMorphismList = 
           Append[domainMorphismList, compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ domainCompositionsList, 
      Length[objects]]; domainMorphismList = Select[domainMorphismList, 
       Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        domainMorphismList = Append[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ objects; 
     leftImageMorphismList = Select[leftArrowListWithDuplicates, First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[leftImageCompositions = Select[Tuples[leftImageMorphismList, 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ leftImageMorphismList, 
            StringDelete[ToString[newCompositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], leftImageMorphismList = 
           Append[leftImageMorphismList, newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ leftImageCompositions, 
      Length[leftObjectListWithDuplicates]]; leftImageMorphismList = Select[leftImageMorphismList, 
       Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[leftImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        leftImageMorphismList = Append[leftImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      leftObjectListWithDuplicates; leftMorphismFunction = 
      Association[Normal[Association[Thread[First /@ domainMorphismList -> First /@ leftImageMorphismList]]] //. 
        {compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[compositionSymbol[x, y], z], 
         newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> newCompositionSymbol[newCompositionSymbol[x, y], z]}]; 
     rightImageMorphismList = Select[rightArrowListWithDuplicates, First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[rightImageCompositions = Select[Tuples[rightImageMorphismList, 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ rightImageMorphismList, 
            StringDelete[ToString[newCompositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], rightImageMorphismList = 
           Append[rightImageMorphismList, newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ rightImageCompositions, 
      Length[rightObjectListWithDuplicates]]; rightImageMorphismList = Select[rightImageMorphismList, 
       Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[rightImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        rightImageMorphismList = Append[rightImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      rightObjectListWithDuplicates; rightMorphismFunction = 
      Association[Normal[Association[Thread[First /@ domainMorphismList -> First /@ rightImageMorphismList]]] //. 
        {compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[compositionSymbol[x, y], z], 
         newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> newCompositionSymbol[newCompositionSymbol[x, y], z]}]; 
     naturalArrows = {}; 
     (Module[{morphism = #1 //. {compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[
              compositionSymbol[x, y], z], newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
             newCompositionSymbol[newCompositionSymbol[x, y], z]}}, 
        naturalArrows = Join[naturalArrows, {componentNames[First[Last[morphism]]] -> 
             DirectedEdge[leftObjectFunction[First[Last[morphism]]], rightObjectFunction[First[Last[morphism]]]], 
            componentNames[Last[Last[morphism]]] -> DirectedEdge[leftObjectFunction[Last[Last[morphism]]], 
              rightObjectFunction[Last[Last[morphism]]]]}]; naturalArrows = Join[naturalArrows, 
           {leftMorphismFunction[First[morphism]] -> DirectedEdge[leftObjectFunction[First[Last[morphism]]], 
              leftObjectFunction[Last[Last[morphism]]]], rightMorphismFunction[First[morphism]] -> 
             DirectedEdge[rightObjectFunction[First[Last[morphism]]], rightObjectFunction[Last[
                Last[morphism]]]]}]] & ) /@ Normal[domainMorphismAssociation]; 
     naturalArrows = Association[DeleteDuplicates[naturalArrows]]; naturalMorphismAssociation = 
      Association[Select[Normal[naturalArrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[naturalCompositions = Select[Tuples[Normal[naturalMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[naturalMorphismAssociation], StringDelete[ToString[newCompositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          naturalMorphismAssociation = Association[Append[Normal[naturalMorphismAssociation], 
             newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ naturalCompositions, Length[objects]]; 
     naturalMorphismAssociation = Association[Select[Normal[naturalMorphismAssociation], 
        Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[naturalMorphismAssociation], newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        naturalMorphismAssociation = Association[Append[Normal[naturalMorphismAssociation], 
           newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ DeleteDuplicates[
       Union[objects /. Normal[leftObjectMappings], objects /. Normal[rightObjectMappings]]]; 
     EdgeTaggedGraph[DeleteDuplicates[Union[objects /. Normal[leftObjectMappings], 
        objects /. Normal[rightObjectMappings]]], (DirectedEdge @@ Last[#1] & ) /@ 
       Select[DeleteDuplicatesBy[Normal[naturalMorphismAssociation], DirectedEdge @@ Last[#1] & ], 
        First[Last[#1]] =!= Last[Last[#1]] & ], VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], 
      VertexLabels -> Placed["Name", Center], VertexLabelStyle -> Directive[Bold, 20], 
      EdgeLabelStyle -> Directive[Bold, 20], EdgeStyle -> Directive[Black, Thick], 
      GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractNaturalTransformation[Association["Category" -> (abstractCategory_)[
       Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
        "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
        "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
           "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
           "Objects" -> objects_List]]]], "ComponentEquivalences" -> componentEquivalences_List, 
     "ComponentNames" -> componentNames_Association, "Covariant" -> covariant_, 
     "LeftArrowMappings" -> leftArrowMappings_Association, "LeftMorphismEquivalences" -> leftMorphismEquivalences_List, 
     "LeftNewArrows" -> leftNewArrows_Association, "LeftNewObjects" -> leftNewObjects_List, 
     "LeftObjectEquivalences" -> leftObjectEquivalences_List, "LeftObjectMappings" -> leftObjectMappings_Association, 
     "NewCompositionSymbol" -> newCompositionSymbol_, "NewIdentitySymbol" -> newIdentitySymbol_, 
     "RightArrowMappings" -> rightArrowMappings_Association, "RightMorphismEquivalences" -> 
      rightMorphismEquivalences_List, "RightNewArrows" -> rightNewArrows_Association, 
     "RightNewObjects" -> rightNewObjects_List, "RightObjectEquivalences" -> rightObjectEquivalences_List, 
     "RightObjectMappings" -> rightObjectMappings_Association]]["ReducedSimpleLabeledGraph"] := 
  Module[{domainMorphismAssociation, domainCompositions, leftObjectFunction, rightObjectFunction, 
     leftObjectListWithDuplicates, leftArrowListWithDuplicates, rightObjectListWithDuplicates, 
     rightArrowListWithDuplicates, domainMorphismList, domainCompositionsList, leftImageMorphismList, 
     leftImageCompositions, leftMorphismFunction, rightImageMorphismList, rightImageCompositions, rightMorphismFunction, 
     naturalArrows, naturalMorphismEquivalences, naturalMorphismAssociation, naturalCompositions}, 
    domainMorphismAssociation = Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[arrows, 
           arrowEquivalences], quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[domainCompositions = Select[Tuples[Normal[domainMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[domainMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          domainMorphismAssociation = Association[Append[Normal[domainMorphismAssociation], 
             compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ domainCompositions, Length[reduceObjects[objects, quiverObjectEquivalences]]]; 
     domainMorphismAssociation = Association[Select[Normal[domainMorphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[domainMorphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        domainMorphismAssociation = Association[Append[Normal[domainMorphismAssociation], 
           identitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[objects, quiverObjectEquivalences]; 
     leftObjectFunction = Join[Association[
        Thread[Keys[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
              objectEquivalences]]] -> reduceObjectsWithDuplicates[Values[Association[(#1 -> #1 & ) /@ 
              reduceObjects[reduceObjects[objects, quiverObjectEquivalences], objectEquivalences]]], 
           leftObjectEquivalences]]], Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[
            Keys[leftObjectMappings], quiverObjectEquivalences], objectEquivalences] -> reduceObjectsWithDuplicates[
           Values[leftObjectMappings], leftObjectEquivalences]]]]; rightObjectFunction = 
      Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, 
               quiverObjectEquivalences], objectEquivalences]]] -> reduceObjectsWithDuplicates[
           Values[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
               objectEquivalences]]], rightObjectEquivalences]]], 
       Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[rightObjectMappings], 
            quiverObjectEquivalences], objectEquivalences] -> reduceObjectsWithDuplicates[Values[rightObjectMappings], 
           rightObjectEquivalences]]]]; leftObjectListWithDuplicates = objects /. Normal[leftObjectMappings]; 
     leftArrowListWithDuplicates = If[covariant === True, Normal[arrows] /. Normal[leftArrowMappings] /. 
        Normal[leftObjectMappings], (First[#1] -> Reverse[Last[#1]] & ) /@ 
        (Normal[arrows] /. Normal[leftArrowMappings] /. Normal[leftObjectMappings])]; 
     rightObjectListWithDuplicates = objects /. Normal[rightObjectMappings]; rightArrowListWithDuplicates = 
      If[covariant === True, Normal[arrows] /. Normal[rightArrowMappings] /. Normal[rightObjectMappings], 
       (First[#1] -> Reverse[Last[#1]] & ) /@ (Normal[arrows] /. Normal[rightArrowMappings] /. 
         Normal[rightObjectMappings])]; domainMorphismList = Select[reduceArrowsFinalWithDuplicates[
        reduceArrowsInitialWithDuplicates[Normal[arrows], arrowEquivalences], quiverObjectEquivalences], 
       First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[domainCompositionsList = Select[Tuples[domainMorphismList, 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ domainMorphismList, 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], domainMorphismList = 
           Append[domainMorphismList, compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ domainCompositionsList, 
      Length[reduceObjectsWithDuplicates[objects, quiverObjectEquivalences]]]; 
     domainMorphismList = Select[domainMorphismList, Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        domainMorphismList = Append[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      reduceObjectsWithDuplicates[objects, quiverObjectEquivalences]; domainMorphismList = 
      reduceArrowsFinalWithDuplicates[reduceArrowsInitialWithDuplicates[domainMorphismList, morphismEquivalences], 
       objectEquivalences]; leftImageMorphismList = Select[reduceArrowsFinalWithDuplicates[
        reduceArrowsInitialWithDuplicates[leftArrowListWithDuplicates, arrowEquivalences /. Normal[leftArrowMappings]], 
        quiverObjectEquivalences /. Normal[leftObjectMappings]], First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[leftImageCompositions = Select[Tuples[leftImageMorphismList, 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ leftImageMorphismList, 
            StringDelete[ToString[newCompositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], leftImageMorphismList = 
           Append[leftImageMorphismList, newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ leftImageCompositions, 
      Length[reduceObjectsWithDuplicates[leftObjectListWithDuplicates, quiverObjectEquivalences /. 
         Normal[leftObjectMappings]]]]; leftImageMorphismList = Select[leftImageMorphismList, 
       Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[leftImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        leftImageMorphismList = Append[leftImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      reduceObjectsWithDuplicates[leftObjectListWithDuplicates, quiverObjectEquivalences /. Normal[leftObjectMappings]]; 
     leftImageMorphismList = reduceArrowsFinalWithDuplicates[reduceArrowsInitialWithDuplicates[leftImageMorphismList, 
        If[covariant === True, DeleteDuplicates[Join[morphismEquivalences /. compositionSymbol -> newCompositionSymbol /. 
            Normal[leftArrowMappings], leftMorphismEquivalences]], DeleteDuplicates[
          Join[morphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[leftArrowMappings] /. 
            {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> newCompositionSymbol[z, newCompositionSymbol[y, 
                x]], newCompositionSymbol[newCompositionSymbol[x_, y_], z_] :> newCompositionSymbol[newCompositionSymbol[
                z, y], x], newCompositionSymbol[x_, y_] :> newCompositionSymbol[y, x]}, leftMorphismEquivalences]]]], 
       DeleteDuplicates[Join[objectEquivalences /. Normal[leftObjectMappings], leftObjectEquivalences]]]; 
     leftMorphismFunction = Association[Normal[Association[Thread[First /@ domainMorphismList -> 
            First /@ leftImageMorphismList]]] //. {compositionSymbol[x_, compositionSymbol[y_, z_]] :> 
          compositionSymbol[compositionSymbol[x, y], z], newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
          newCompositionSymbol[newCompositionSymbol[x, y], z]}]; rightImageMorphismList = 
      Select[reduceArrowsFinalWithDuplicates[reduceArrowsInitialWithDuplicates[rightArrowListWithDuplicates, 
         arrowEquivalences /. Normal[rightArrowMappings]], quiverObjectEquivalences /. Normal[rightObjectMappings]], 
       First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[rightImageCompositions = Select[Tuples[rightImageMorphismList, 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ rightImageMorphismList, 
            StringDelete[ToString[newCompositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], rightImageMorphismList = 
           Append[rightImageMorphismList, newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ rightImageCompositions, 
      Length[reduceObjectsWithDuplicates[rightObjectListWithDuplicates, quiverObjectEquivalences /. 
         Normal[rightObjectMappings]]]]; rightImageMorphismList = Select[rightImageMorphismList, 
       Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[rightImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        rightImageMorphismList = Append[rightImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      reduceObjectsWithDuplicates[rightObjectListWithDuplicates, quiverObjectEquivalences /. 
        Normal[rightObjectMappings]]; rightImageMorphismList = reduceArrowsFinalWithDuplicates[
       reduceArrowsInitialWithDuplicates[rightImageMorphismList, If[covariant === True, 
         DeleteDuplicates[Join[morphismEquivalences /. compositionSymbol -> newCompositionSymbol /. 
            Normal[rightArrowMappings], rightMorphismEquivalences]], DeleteDuplicates[
          Join[morphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[rightArrowMappings] /. 
            {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> newCompositionSymbol[z, newCompositionSymbol[y, 
                x]], newCompositionSymbol[newCompositionSymbol[x_, y_], z_] :> newCompositionSymbol[newCompositionSymbol[
                z, y], x], newCompositionSymbol[x_, y_] :> newCompositionSymbol[y, x]}, rightMorphismEquivalences]]]], 
       DeleteDuplicates[Join[objectEquivalences /. Normal[rightObjectMappings], rightObjectEquivalences]]]; 
     rightMorphismFunction = Association[Normal[Association[Thread[First /@ domainMorphismList -> 
            First /@ rightImageMorphismList]]] //. {compositionSymbol[x_, compositionSymbol[y_, z_]] :> 
          compositionSymbol[compositionSymbol[x, y], z], newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
          newCompositionSymbol[newCompositionSymbol[x, y], z]}]; naturalArrows = {}; naturalMorphismEquivalences = {}; 
     (Module[{morphism = #1 //. {compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[
              compositionSymbol[x, y], z], newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
             newCompositionSymbol[newCompositionSymbol[x, y], z]}}, 
        naturalArrows = Join[naturalArrows, {reduceComponentNames[reduceComponentNames[componentNames, 
                quiverObjectEquivalences], objectEquivalences][First[Last[morphism]]] -> 
             DirectedEdge[leftObjectFunction[First[Last[morphism]]], rightObjectFunction[First[Last[morphism]]]], 
            reduceComponentNames[reduceComponentNames[componentNames, quiverObjectEquivalences], objectEquivalences][
              Last[Last[morphism]]] -> DirectedEdge[leftObjectFunction[Last[Last[morphism]]], rightObjectFunction[Last[
                Last[morphism]]]]}]; naturalArrows = Join[naturalArrows, {leftMorphismFunction[First[morphism]] -> 
             DirectedEdge[leftObjectFunction[First[Last[morphism]]], leftObjectFunction[Last[Last[morphism]]]], 
            rightMorphismFunction[First[morphism]] -> DirectedEdge[rightObjectFunction[First[Last[morphism]]], 
              rightObjectFunction[Last[Last[morphism]]]]}]; naturalMorphismEquivalences = 
          Append[naturalMorphismEquivalences, newCompositionSymbol[reduceComponentNames[reduceComponentNames[
                componentNames, quiverObjectEquivalences], objectEquivalences][Last[Last[morphism]]], 
             leftMorphismFunction[First[morphism]]] == newCompositionSymbol[rightMorphismFunction[First[morphism]], 
             reduceComponentNames[reduceComponentNames[componentNames, quiverObjectEquivalences], objectEquivalences][
              First[Last[morphism]]]]]] & ) /@ Normal[reduceArrowsFinal[reduceArrowsInitial[domainMorphismAssociation, 
         morphismEquivalences], objectEquivalences]]; naturalArrows = Association[DeleteDuplicates[naturalArrows]]; 
     naturalMorphismAssociation = Association[Select[Normal[naturalArrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[naturalCompositions = Select[Tuples[Normal[naturalMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[naturalMorphismAssociation], StringDelete[ToString[newCompositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          naturalMorphismAssociation = Association[Append[Normal[naturalMorphismAssociation], 
             newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ naturalCompositions, Length[objects]]; 
     naturalMorphismAssociation = Association[Normal[Association[Select[Normal[naturalMorphismAssociation], 
           Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == Length[DeleteDuplicates[Flatten[
                {First[#1] /. newCompositionSymbol -> List}]]] & ]]] //. 
        {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> newCompositionSymbol[newCompositionSymbol[x, y], z]}]; 
     (If[ !MemberQ[Normal[naturalMorphismAssociation], newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        naturalMorphismAssociation = Association[Append[Normal[naturalMorphismAssociation], 
           newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ DeleteDuplicates[
       Catenate[({First[Last[#1]], Last[Last[#1]]} & ) /@ Normal[naturalMorphismAssociation]]]; 
     EdgeTaggedGraph[DeleteDuplicates[Catenate[({First[Last[#1]], Last[Last[#1]]} & ) /@ 
         Normal[naturalMorphismAssociation]]], (Labeled[DirectedEdge @@ Last[#1], Placed[First[#1], 0.5]] & ) /@ 
       Normal[reduceArrowsInitial[reduceArrowsInitial[reduceArrowsInitial[Association[
            Select[DeleteDuplicatesBy[Normal[naturalMorphismAssociation], DirectedEdge @@ Last[#1] & ], 
             First[Last[#1]] =!= Last[Last[#1]] & ]], naturalMorphismEquivalences //. 
            {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> newCompositionSymbol[newCompositionSymbol[x, 
                y], z]}], Join[morphismEquivalences /. Normal[leftMorphismFunction], morphismEquivalences /. 
            Normal[rightMorphismFunction]]], componentEquivalences]], VertexSize -> 0.3, 
      VertexStyle -> Directive[Transparent, EdgeForm[None]], VertexLabels -> Placed["Name", Center], 
      VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
      EdgeStyle -> Directive[Black, Thick], GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractNaturalTransformation[Association["Category" -> (abstractCategory_)[
       Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
        "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
        "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
           "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
           "Objects" -> objects_List]]]], "ComponentEquivalences" -> componentEquivalences_List, 
     "ComponentNames" -> componentNames_Association, "Covariant" -> covariant_, 
     "LeftArrowMappings" -> leftArrowMappings_Association, "LeftMorphismEquivalences" -> leftMorphismEquivalences_List, 
     "LeftNewArrows" -> leftNewArrows_Association, "LeftNewObjects" -> leftNewObjects_List, 
     "LeftObjectEquivalences" -> leftObjectEquivalences_List, "LeftObjectMappings" -> leftObjectMappings_Association, 
     "NewCompositionSymbol" -> newCompositionSymbol_, "NewIdentitySymbol" -> newIdentitySymbol_, 
     "RightArrowMappings" -> rightArrowMappings_Association, "RightMorphismEquivalences" -> 
      rightMorphismEquivalences_List, "RightNewArrows" -> rightNewArrows_Association, 
     "RightNewObjects" -> rightNewObjects_List, "RightObjectEquivalences" -> rightObjectEquivalences_List, 
     "RightObjectMappings" -> rightObjectMappings_Association]]["ReducedSimpleUnlabeledGraph"] := 
  Module[{domainMorphismAssociation, domainCompositions, leftObjectFunction, rightObjectFunction, 
     leftObjectListWithDuplicates, leftArrowListWithDuplicates, rightObjectListWithDuplicates, 
     rightArrowListWithDuplicates, domainMorphismList, domainCompositionsList, leftImageMorphismList, 
     leftImageCompositions, leftMorphismFunction, rightImageMorphismList, rightImageCompositions, rightMorphismFunction, 
     naturalArrows, naturalMorphismEquivalences, naturalMorphismAssociation, naturalCompositions}, 
    domainMorphismAssociation = Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[arrows, 
           arrowEquivalences], quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[domainCompositions = Select[Tuples[Normal[domainMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[domainMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          domainMorphismAssociation = Association[Append[Normal[domainMorphismAssociation], 
             compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ domainCompositions, Length[reduceObjects[objects, quiverObjectEquivalences]]]; 
     domainMorphismAssociation = Association[Select[Normal[domainMorphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[domainMorphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        domainMorphismAssociation = Association[Append[Normal[domainMorphismAssociation], 
           identitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[objects, quiverObjectEquivalences]; 
     leftObjectFunction = Join[Association[
        Thread[Keys[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
              objectEquivalences]]] -> reduceObjectsWithDuplicates[Values[Association[(#1 -> #1 & ) /@ 
              reduceObjects[reduceObjects[objects, quiverObjectEquivalences], objectEquivalences]]], 
           leftObjectEquivalences]]], Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[
            Keys[leftObjectMappings], quiverObjectEquivalences], objectEquivalences] -> reduceObjectsWithDuplicates[
           Values[leftObjectMappings], leftObjectEquivalences]]]]; rightObjectFunction = 
      Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, 
               quiverObjectEquivalences], objectEquivalences]]] -> reduceObjectsWithDuplicates[
           Values[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
               objectEquivalences]]], rightObjectEquivalences]]], 
       Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[rightObjectMappings], 
            quiverObjectEquivalences], objectEquivalences] -> reduceObjectsWithDuplicates[Values[rightObjectMappings], 
           rightObjectEquivalences]]]]; leftObjectListWithDuplicates = objects /. Normal[leftObjectMappings]; 
     leftArrowListWithDuplicates = If[covariant === True, Normal[arrows] /. Normal[leftArrowMappings] /. 
        Normal[leftObjectMappings], (First[#1] -> Reverse[Last[#1]] & ) /@ 
        (Normal[arrows] /. Normal[leftArrowMappings] /. Normal[leftObjectMappings])]; 
     rightObjectListWithDuplicates = objects /. Normal[rightObjectMappings]; rightArrowListWithDuplicates = 
      If[covariant === True, Normal[arrows] /. Normal[rightArrowMappings] /. Normal[rightObjectMappings], 
       (First[#1] -> Reverse[Last[#1]] & ) /@ (Normal[arrows] /. Normal[rightArrowMappings] /. 
         Normal[rightObjectMappings])]; domainMorphismList = Select[reduceArrowsFinalWithDuplicates[
        reduceArrowsInitialWithDuplicates[Normal[arrows], arrowEquivalences], quiverObjectEquivalences], 
       First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[domainCompositionsList = Select[Tuples[domainMorphismList, 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ domainMorphismList, 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], domainMorphismList = 
           Append[domainMorphismList, compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ domainCompositionsList, 
      Length[reduceObjectsWithDuplicates[objects, quiverObjectEquivalences]]]; 
     domainMorphismList = Select[domainMorphismList, Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        domainMorphismList = Append[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      reduceObjectsWithDuplicates[objects, quiverObjectEquivalences]; domainMorphismList = 
      reduceArrowsFinalWithDuplicates[reduceArrowsInitialWithDuplicates[domainMorphismList, morphismEquivalences], 
       objectEquivalences]; leftImageMorphismList = Select[reduceArrowsFinalWithDuplicates[
        reduceArrowsInitialWithDuplicates[leftArrowListWithDuplicates, arrowEquivalences /. Normal[leftArrowMappings]], 
        quiverObjectEquivalences /. Normal[leftObjectMappings]], First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[leftImageCompositions = Select[Tuples[leftImageMorphismList, 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ leftImageMorphismList, 
            StringDelete[ToString[newCompositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], leftImageMorphismList = 
           Append[leftImageMorphismList, newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ leftImageCompositions, 
      Length[reduceObjectsWithDuplicates[leftObjectListWithDuplicates, quiverObjectEquivalences /. 
         Normal[leftObjectMappings]]]]; leftImageMorphismList = Select[leftImageMorphismList, 
       Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[leftImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        leftImageMorphismList = Append[leftImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      reduceObjectsWithDuplicates[leftObjectListWithDuplicates, quiverObjectEquivalences /. Normal[leftObjectMappings]]; 
     leftImageMorphismList = reduceArrowsFinalWithDuplicates[reduceArrowsInitialWithDuplicates[leftImageMorphismList, 
        If[covariant === True, DeleteDuplicates[Join[morphismEquivalences /. compositionSymbol -> newCompositionSymbol /. 
            Normal[leftArrowMappings], leftMorphismEquivalences]], DeleteDuplicates[
          Join[morphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[leftArrowMappings] /. 
            {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> newCompositionSymbol[z, newCompositionSymbol[y, 
                x]], newCompositionSymbol[newCompositionSymbol[x_, y_], z_] :> newCompositionSymbol[newCompositionSymbol[
                z, y], x], newCompositionSymbol[x_, y_] :> newCompositionSymbol[y, x]}, leftMorphismEquivalences]]]], 
       DeleteDuplicates[Join[objectEquivalences /. Normal[leftObjectMappings], leftObjectEquivalences]]]; 
     leftMorphismFunction = Association[Normal[Association[Thread[First /@ domainMorphismList -> 
            First /@ leftImageMorphismList]]] //. {compositionSymbol[x_, compositionSymbol[y_, z_]] :> 
          compositionSymbol[compositionSymbol[x, y], z], newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
          newCompositionSymbol[newCompositionSymbol[x, y], z]}]; rightImageMorphismList = 
      Select[reduceArrowsFinalWithDuplicates[reduceArrowsInitialWithDuplicates[rightArrowListWithDuplicates, 
         arrowEquivalences /. Normal[rightArrowMappings]], quiverObjectEquivalences /. Normal[rightObjectMappings]], 
       First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[rightImageCompositions = Select[Tuples[rightImageMorphismList, 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ rightImageMorphismList, 
            StringDelete[ToString[newCompositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], rightImageMorphismList = 
           Append[rightImageMorphismList, newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ rightImageCompositions, 
      Length[reduceObjectsWithDuplicates[rightObjectListWithDuplicates, quiverObjectEquivalences /. 
         Normal[rightObjectMappings]]]]; rightImageMorphismList = Select[rightImageMorphismList, 
       Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[rightImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        rightImageMorphismList = Append[rightImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      reduceObjectsWithDuplicates[rightObjectListWithDuplicates, quiverObjectEquivalences /. 
        Normal[rightObjectMappings]]; rightImageMorphismList = reduceArrowsFinalWithDuplicates[
       reduceArrowsInitialWithDuplicates[rightImageMorphismList, If[covariant === True, 
         DeleteDuplicates[Join[morphismEquivalences /. compositionSymbol -> newCompositionSymbol /. 
            Normal[rightArrowMappings], rightMorphismEquivalences]], DeleteDuplicates[
          Join[morphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[rightArrowMappings] /. 
            {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> newCompositionSymbol[z, newCompositionSymbol[y, 
                x]], newCompositionSymbol[newCompositionSymbol[x_, y_], z_] :> newCompositionSymbol[newCompositionSymbol[
                z, y], x], newCompositionSymbol[x_, y_] :> newCompositionSymbol[y, x]}, rightMorphismEquivalences]]]], 
       DeleteDuplicates[Join[objectEquivalences /. Normal[rightObjectMappings], rightObjectEquivalences]]]; 
     rightMorphismFunction = Association[Normal[Association[Thread[First /@ domainMorphismList -> 
            First /@ rightImageMorphismList]]] //. {compositionSymbol[x_, compositionSymbol[y_, z_]] :> 
          compositionSymbol[compositionSymbol[x, y], z], newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
          newCompositionSymbol[newCompositionSymbol[x, y], z]}]; naturalArrows = {}; naturalMorphismEquivalences = {}; 
     (Module[{morphism = #1 //. {compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[
              compositionSymbol[x, y], z], newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
             newCompositionSymbol[newCompositionSymbol[x, y], z]}}, 
        naturalArrows = Join[naturalArrows, {reduceComponentNames[reduceComponentNames[componentNames, 
                quiverObjectEquivalences], objectEquivalences][First[Last[morphism]]] -> 
             DirectedEdge[leftObjectFunction[First[Last[morphism]]], rightObjectFunction[First[Last[morphism]]]], 
            reduceComponentNames[reduceComponentNames[componentNames, quiverObjectEquivalences], objectEquivalences][
              Last[Last[morphism]]] -> DirectedEdge[leftObjectFunction[Last[Last[morphism]]], rightObjectFunction[Last[
                Last[morphism]]]]}]; naturalArrows = Join[naturalArrows, {leftMorphismFunction[First[morphism]] -> 
             DirectedEdge[leftObjectFunction[First[Last[morphism]]], leftObjectFunction[Last[Last[morphism]]]], 
            rightMorphismFunction[First[morphism]] -> DirectedEdge[rightObjectFunction[First[Last[morphism]]], 
              rightObjectFunction[Last[Last[morphism]]]]}]; naturalMorphismEquivalences = 
          Append[naturalMorphismEquivalences, newCompositionSymbol[reduceComponentNames[reduceComponentNames[
                componentNames, quiverObjectEquivalences], objectEquivalences][Last[Last[morphism]]], 
             leftMorphismFunction[First[morphism]]] == newCompositionSymbol[rightMorphismFunction[First[morphism]], 
             reduceComponentNames[reduceComponentNames[componentNames, quiverObjectEquivalences], objectEquivalences][
              First[Last[morphism]]]]]] & ) /@ Normal[reduceArrowsFinal[reduceArrowsInitial[domainMorphismAssociation, 
         morphismEquivalences], objectEquivalences]]; naturalArrows = Association[DeleteDuplicates[naturalArrows]]; 
     naturalMorphismAssociation = Association[Select[Normal[naturalArrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[naturalCompositions = Select[Tuples[Normal[naturalMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[naturalMorphismAssociation], StringDelete[ToString[newCompositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          naturalMorphismAssociation = Association[Append[Normal[naturalMorphismAssociation], 
             newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ naturalCompositions, Length[objects]]; 
     naturalMorphismAssociation = Association[Normal[Association[Select[Normal[naturalMorphismAssociation], 
           Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == Length[DeleteDuplicates[Flatten[
                {First[#1] /. newCompositionSymbol -> List}]]] & ]]] //. 
        {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> newCompositionSymbol[newCompositionSymbol[x, y], z]}]; 
     (If[ !MemberQ[Normal[naturalMorphismAssociation], newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        naturalMorphismAssociation = Association[Append[Normal[naturalMorphismAssociation], 
           newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ DeleteDuplicates[
       Catenate[({First[Last[#1]], Last[Last[#1]]} & ) /@ Normal[naturalMorphismAssociation]]]; 
     EdgeTaggedGraph[DeleteDuplicates[Catenate[({First[Last[#1]], Last[Last[#1]]} & ) /@ 
         Normal[naturalMorphismAssociation]]], (DirectedEdge @@ Last[#1] & ) /@ 
       Normal[reduceArrowsInitial[reduceArrowsInitial[reduceArrowsInitial[Association[
            Select[DeleteDuplicatesBy[Normal[naturalMorphismAssociation], DirectedEdge @@ Last[#1] & ], 
             First[Last[#1]] =!= Last[Last[#1]] & ]], naturalMorphismEquivalences //. 
            {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> newCompositionSymbol[newCompositionSymbol[x, 
                y], z]}], Join[morphismEquivalences /. Normal[leftMorphismFunction], morphismEquivalences /. 
            Normal[rightMorphismFunction]]], componentEquivalences]], VertexSize -> 0.3, 
      VertexStyle -> Directive[Transparent, EdgeForm[None]], VertexLabels -> Placed["Name", Center], 
      VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
      EdgeStyle -> Directive[Black, Thick], GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractNaturalTransformation /: 
  MakeBoxes[abstractNaturalTransformation:AbstractNaturalTransformation[
      Association["Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
          "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> morphismEquivalences_List, 
          "ObjectEquivalences" -> objectEquivalences_List, "Quiver" -> (abstractQuiver_)[
            Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
             "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
       "ComponentEquivalences" -> componentEquivalences_List, "ComponentNames" -> componentNames_Association, 
       "Covariant" -> covariant_, "LeftArrowMappings" -> leftArrowMappings_Association, 
       "LeftMorphismEquivalences" -> leftMorphismEquivalences_List, "LeftNewArrows" -> leftNewArrows_Association, 
       "LeftNewObjects" -> leftNewObjects_List, "LeftObjectEquivalences" -> leftObjectEquivalences_List, 
       "LeftObjectMappings" -> leftObjectMappings_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
       "NewIdentitySymbol" -> newIdentitySymbol_, "RightArrowMappings" -> rightArrowMappings_Association, 
       "RightMorphismEquivalences" -> rightMorphismEquivalences_List, "RightNewArrows" -> rightNewArrows_Association, 
       "RightNewObjects" -> rightNewObjects_List, "RightObjectEquivalences" -> rightObjectEquivalences_List, 
       "RightObjectMappings" -> rightObjectMappings_Association]], format_] := 
   Module[{domainMorphismAssociation, domainCompositions, leftObjectFunction, rightObjectFunction, 
      leftObjectListWithDuplicates, leftArrowListWithDuplicates, rightObjectListWithDuplicates, 
      rightArrowListWithDuplicates, domainMorphismList, domainCompositionsList, leftImageMorphismList, 
      leftImageCompositions, leftMorphismFunction, rightImageMorphismList, rightImageCompositions, rightMorphismFunction, 
      naturalArrows, naturalMorphismAssociation, naturalCompositions, icon, type, objectCount, morphismCount}, 
     domainMorphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
      Do[domainCompositions = Select[Tuples[Normal[domainMorphismAssociation], 2], 
          Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
        (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
              Normal[domainMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                 First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
           domainMorphismAssociation = Association[Append[Normal[domainMorphismAssociation], compositionSymbol[
                First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], 
                Last[Last[Last[#1]]]]]]] & ) /@ domainCompositions, Length[objects]]; 
      domainMorphismAssociation = Association[Select[Normal[domainMorphismAssociation], 
         Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == Length[DeleteDuplicates[
             Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
      (If[ !MemberQ[Normal[domainMorphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
         domainMorphismAssociation = Association[Append[Normal[domainMorphismAssociation], identitySymbol[#1] -> 
             DirectedEdge[#1, #1]]]] & )[objects]; leftObjectFunction = Join[Association[(#1 -> #1 & ) /@ objects], 
        leftObjectMappings]; rightObjectFunction = Join[Association[(#1 -> #1 & ) /@ objects], rightObjectMappings]; 
      leftObjectListWithDuplicates = objects /. Normal[leftObjectMappings]; leftArrowListWithDuplicates = 
       If[covariant === True, Normal[arrows] /. Normal[leftArrowMappings] /. Normal[leftObjectMappings], 
        (First[#1] -> Reverse[Last[#1]] & ) /@ (Normal[arrows] /. Normal[leftArrowMappings] /. 
          Normal[leftObjectMappings])]; rightObjectListWithDuplicates = objects /. Normal[rightObjectMappings]; 
      rightArrowListWithDuplicates = If[covariant === True, Normal[arrows] /. Normal[rightArrowMappings] /. 
         Normal[rightObjectMappings], (First[#1] -> Reverse[Last[#1]] & ) /@ 
         (Normal[arrows] /. Normal[rightArrowMappings] /. Normal[rightObjectMappings])]; 
      domainMorphismList = Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]; 
      Do[domainCompositionsList = Select[Tuples[domainMorphismList, 2], 
          Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
        (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ domainMorphismList, 
             StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], domainMorphismList = 
            Append[domainMorphismList, compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[
                Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ domainCompositionsList, Length[objects]]; 
      domainMorphismList = Select[domainMorphismList, Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]; 
      (If[ !MemberQ[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]], 
         domainMorphismList = Append[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ objects; 
      leftImageMorphismList = Select[leftArrowListWithDuplicates, First[Last[#1]] =!= Last[Last[#1]] & ]; 
      Do[leftImageCompositions = Select[Tuples[leftImageMorphismList, 2], 
          Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
        (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ leftImageMorphismList, 
             StringDelete[ToString[newCompositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], leftImageMorphismList = 
            Append[leftImageMorphismList, newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ leftImageCompositions, 
       Length[leftObjectListWithDuplicates]]; leftImageMorphismList = Select[leftImageMorphismList, 
        Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]; 
      (If[ !MemberQ[leftImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
         leftImageMorphismList = Append[leftImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
       leftObjectListWithDuplicates; leftMorphismFunction = 
       Association[Normal[Association[Thread[First /@ domainMorphismList -> First /@ leftImageMorphismList]]] //. 
         {compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[compositionSymbol[x, y], z], 
          newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> newCompositionSymbol[newCompositionSymbol[x, y], 
            z]}]; rightImageMorphismList = Select[rightArrowListWithDuplicates, First[Last[#1]] =!= Last[Last[#1]] & ]; 
      Do[rightImageCompositions = Select[Tuples[rightImageMorphismList, 2], 
          Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
        (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ rightImageMorphismList, 
             StringDelete[ToString[newCompositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], rightImageMorphismList = 
            Append[rightImageMorphismList, newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ rightImageCompositions, 
       Length[rightObjectListWithDuplicates]]; rightImageMorphismList = Select[rightImageMorphismList, 
        Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]; 
      (If[ !MemberQ[rightImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
         rightImageMorphismList = Append[rightImageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
       rightObjectListWithDuplicates; rightMorphismFunction = 
       Association[Normal[Association[Thread[First /@ domainMorphismList -> First /@ rightImageMorphismList]]] //. 
         {compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[compositionSymbol[x, y], z], 
          newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> newCompositionSymbol[newCompositionSymbol[x, y], 
            z]}]; naturalArrows = {}; 
      (Module[{morphism = #1 //. {compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[compositionSymbol[
                x, y], z], newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> newCompositionSymbol[
               newCompositionSymbol[x, y], z]}}, naturalArrows = Join[naturalArrows, 
            {componentNames[First[Last[morphism]]] -> DirectedEdge[leftObjectFunction[First[Last[morphism]]], 
               rightObjectFunction[First[Last[morphism]]]], componentNames[Last[Last[morphism]]] -> 
              DirectedEdge[leftObjectFunction[Last[Last[morphism]]], rightObjectFunction[Last[Last[morphism]]]]}]; 
          naturalArrows = Join[naturalArrows, {leftMorphismFunction[First[morphism]] -> DirectedEdge[leftObjectFunction[
                First[Last[morphism]]], leftObjectFunction[Last[Last[morphism]]]], 
             rightMorphismFunction[First[morphism]] -> DirectedEdge[rightObjectFunction[First[Last[morphism]]], 
               rightObjectFunction[Last[Last[morphism]]]]}]] & ) /@ Normal[domainMorphismAssociation]; 
      naturalArrows = Association[DeleteDuplicates[naturalArrows]]; naturalMorphismAssociation = 
       Association[Select[Normal[naturalArrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
      Do[naturalCompositions = Select[Tuples[Normal[naturalMorphismAssociation], 2], 
          Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
        (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
              Normal[naturalMorphismAssociation], StringDelete[ToString[newCompositionSymbol[First[Last[#1]], 
                 First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
           naturalMorphismAssociation = Association[Append[Normal[naturalMorphismAssociation], newCompositionSymbol[
                First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], 
                Last[Last[Last[#1]]]]]]] & ) /@ naturalCompositions, Length[objects]]; 
      naturalMorphismAssociation = Association[Select[Normal[naturalMorphismAssociation], 
         Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
           Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]]; 
      (If[ !MemberQ[Normal[naturalMorphismAssociation], newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
         naturalMorphismAssociation = Association[Append[Normal[naturalMorphismAssociation], 
            newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ DeleteDuplicates[
        Union[objects /. Normal[leftObjectMappings], objects /. Normal[rightObjectMappings]]]; 
      icon = GraphPlot[EdgeTaggedGraph[DeleteDuplicates[Union[objects /. Normal[leftObjectMappings], 
           objects /. Normal[rightObjectMappings]]], (DirectedEdge @@ Last[#1] & ) /@ Normal[naturalMorphismAssociation], 
         VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], EdgeShapeFunction -> 
          GraphElementData["ShortFilledArrow", "ArrowSize" -> 0.05], EdgeStyle -> Black, 
         GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]]; If[covariant === True, type = "Covariant", 
       type = "Contravariant"]; objectCount = Length[DeleteDuplicates[Union[objects /. Normal[leftObjectMappings], 
          objects /. Normal[rightObjectMappings]]]]; morphismCount = Length[Normal[naturalMorphismAssociation]]; 
      BoxForm`ArrangeSummaryBox["AbstractNaturalTransformation", abstractNaturalTransformation, icon, 
       {{BoxForm`SummaryItem[{"Type: ", type}]}, {BoxForm`SummaryItem[{"Objects: ", objectCount}], 
         BoxForm`SummaryItem[{"Morphisms: ", morphismCount}]}}, {{}}, format, "Interpretable" -> Automatic]] /; 
    SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractNaturalTransformation[(abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]], leftFunctorSymbol_, rightFunctorSymbol_] := 
  AbstractNaturalTransformation[Association["Category" -> ResourceFunction["AbstractCategory"][
       Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
        "MorphismEquivalences" -> morphismEquivalences, "ObjectEquivalences" -> objectEquivalences, 
        "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> arrowEquivalences, 
           "Arrows" -> arrows, "ObjectEquivalences" -> quiverObjectEquivalences, "Objects" -> objects]]]], 
     "ComponentEquivalences" -> {}, "ComponentNames" -> Association[(#1 -> Subscript["\[Eta]", ToString[#1]] & ) /@ objects], 
     "Covariant" -> True, "LeftArrowMappings" -> Association[(First[#1] -> leftFunctorSymbol[First[#1]] & ) /@ 
        Normal[arrows]], "LeftMorphismEquivalences" -> {}, "LeftNewArrows" -> Association[], "LeftNewObjects" -> {}, 
     "LeftObjectEquivalences" -> {}, "LeftObjectMappings" -> Association[(#1 -> leftFunctorSymbol[#1] & ) /@ objects], 
     "NewCompositionSymbol" -> compositionSymbol, "NewIdentitySymbol" -> identitySymbol, 
     "RightArrowMappings" -> Association[(First[#1] -> rightFunctorSymbol[First[#1]] & ) /@ Normal[arrows]], 
     "RightMorphismEquivalences" -> {}, "RightNewArrows" -> Association[], "RightNewObjects" -> {}, 
     "RightObjectEquivalences" -> {}, "RightObjectMappings" -> Association[(#1 -> rightFunctorSymbol[#1] & ) /@ 
        objects]]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === 
     "AbstractCategory"
AbstractNaturalTransformation[(abstractFunctor_)[Association["ArrowMappings" -> leftArrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> morphismEquivalences_List, 
        "ObjectEquivalences" -> objectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> leftMorphismEquivalences_List, 
     "NewArrows" -> leftNewArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> leftNewObjects_List, 
     "ObjectEquivalences" -> leftObjectEquivalences_List, "ObjectMappings" -> leftObjectMappings_Association]], 
   (abstractFunctor_)[Association["ArrowMappings" -> rightArrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> morphismEquivalences_List, 
        "ObjectEquivalences" -> objectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> rightMorphismEquivalences_List, 
     "NewArrows" -> rightNewArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> rightNewObjects_List, 
     "ObjectEquivalences" -> rightObjectEquivalences_List, "ObjectMappings" -> rightObjectMappings_Association]]] := 
  AbstractNaturalTransformation[Association["Category" -> ResourceFunction["AbstractCategory"][
       Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
        "MorphismEquivalences" -> morphismEquivalences, "ObjectEquivalences" -> objectEquivalences, 
        "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> arrowEquivalences, 
           "Arrows" -> arrows, "ObjectEquivalences" -> quiverObjectEquivalences, "Objects" -> objects]]]], 
     "ComponentEquivalences" -> {}, "ComponentNames" -> Association[(#1 -> Subscript["\[Eta]", ToString[#1]] & ) /@ objects], 
     "Covariant" -> covariant, "LeftArrowMappings" -> leftArrowMappings, "LeftMorphismEquivalences" -> 
      leftMorphismEquivalences, "LeftNewArrows" -> leftNewArrows, "LeftNewObjects" -> leftNewObjects, 
     "LeftObjectEquivalences" -> leftObjectEquivalences, "LeftObjectMappings" -> leftObjectMappings, 
     "NewCompositionSymbol" -> newCompositionSymbol, "NewIdentitySymbol" -> newIdentitySymbol, 
     "RightArrowMappings" -> rightArrowMappings, "RightMorphismEquivalences" -> rightMorphismEquivalences, 
     "RightNewArrows" -> rightNewArrows, "RightNewObjects" -> rightNewObjects, 
     "RightObjectEquivalences" -> rightObjectEquivalences, "RightObjectMappings" -> rightObjectMappings]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractNaturalTransformation[(abstractFunctor_)[Association["ArrowMappings" -> leftArrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> morphismEquivalences_List, 
        "ObjectEquivalences" -> objectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> leftMorphismEquivalences_List, 
     "NewArrows" -> leftNewArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> leftNewObjects_List, 
     "ObjectEquivalences" -> leftObjectEquivalences_List, "ObjectMappings" -> leftObjectMappings_Association]], 
   (abstractFunctor_)[Association["ArrowMappings" -> rightArrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> morphismEquivalences_List, 
        "ObjectEquivalences" -> objectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> rightMorphismEquivalences_List, 
     "NewArrows" -> rightNewArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> rightNewObjects_List, 
     "ObjectEquivalences" -> rightObjectEquivalences_List, "ObjectMappings" -> rightObjectMappings_Association]], 
   componentEquivalences_List] := AbstractNaturalTransformation[
    Association["Category" -> ResourceFunction["AbstractCategory"][Association["CompositionSymbol" -> compositionSymbol, 
        "IdentitySymbol" -> identitySymbol, "MorphismEquivalences" -> morphismEquivalences, 
        "ObjectEquivalences" -> objectEquivalences, "Quiver" -> ResourceFunction["AbstractQuiver"][
          Association["ArrowEquivalences" -> arrowEquivalences, "Arrows" -> arrows, "ObjectEquivalences" -> 
            quiverObjectEquivalences, "Objects" -> objects]]]], "ComponentEquivalences" -> componentEquivalences, 
     "ComponentNames" -> Association[(#1 -> Subscript["\[Eta]", ToString[#1]] & ) /@ objects], "Covariant" -> covariant, 
     "LeftArrowMappings" -> leftArrowMappings, "LeftMorphismEquivalences" -> leftMorphismEquivalences, 
     "LeftNewArrows" -> leftNewArrows, "LeftNewObjects" -> leftNewObjects, "LeftObjectEquivalences" -> 
      leftObjectEquivalences, "LeftObjectMappings" -> leftObjectMappings, "NewCompositionSymbol" -> newCompositionSymbol, 
     "NewIdentitySymbol" -> newIdentitySymbol, "RightArrowMappings" -> rightArrowMappings, 
     "RightMorphismEquivalences" -> rightMorphismEquivalences, "RightNewArrows" -> rightNewArrows, 
     "RightNewObjects" -> rightNewObjects, "RightObjectEquivalences" -> rightObjectEquivalences, 
     "RightObjectMappings" -> rightObjectMappings]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"

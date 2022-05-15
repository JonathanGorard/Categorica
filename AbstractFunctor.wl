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
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]]["ObjectCount"] := 
  (Length[objects] -> Length[DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]]) /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   "MorphismCount"] := Module[{domainMorphismAssociation, domainCompositions, imageMorphismAssociation, 
     imageCompositions}, domainMorphismAssociation = Association[Select[Normal[arrows], 
        First[Last[#1]] =!= Last[Last[#1]] & ]]; 
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
           identitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ objects; imageMorphismAssociation = 
      Association[Select[Normal[Association[DeleteDuplicates[Join[If[covariant === True, 
             Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], (First[#1] -> Reverse[Last[#1]] & ) /@ 
              (Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings])], Normal[newArrows]]]]], 
        First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[imageCompositions = Select[Tuples[Normal[imageMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[imageMorphismAssociation], StringDelete[ToString[newCompositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], 
             newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ imageCompositions, 
      Length[DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]]]; 
     imageMorphismAssociation = Association[Select[Normal[imageMorphismAssociation], 
        Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[imageMorphismAssociation], newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], newIdentitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]; 
     Length[Normal[domainMorphismAssociation]] -> Length[Normal[imageMorphismAssociation]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   "ObjectEquivalences"] := Union[quiverObjectEquivalences /. Normal[objectMappings], 
    DeleteDuplicates[Join[categoryObjectEquivalences /. Normal[objectMappings], objectEquivalences]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   "ObjectEquivalenceCount"] := Length[Union[quiverObjectEquivalences /. Normal[objectMappings], 
     DeleteDuplicates[Join[categoryObjectEquivalences /. Normal[objectMappings], objectEquivalences]]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   "MorphismEquivalences"] := Union[arrowEquivalences /. Normal[arrowMappings], 
    If[covariant === True, DeleteDuplicates[
      Join[categoryMorphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[arrowMappings] /. 
        Normal[objectMappings], morphismEquivalences]], DeleteDuplicates[
      Join[categoryMorphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[arrowMappings] /. 
         Normal[objectMappings] /. {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
          newCompositionSymbol[z, newCompositionSymbol[y, x]], newCompositionSymbol[newCompositionSymbol[x_, y_], z_] :> 
          newCompositionSymbol[newCompositionSymbol[z, y], x], newCompositionSymbol[x_, y_] :> 
          newCompositionSymbol[y, x]}, morphismEquivalences]]]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalneces_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   "MorphismEquivalenceCount"] := Length[Union[arrowEquivalences /. Normal[arrowMappings], 
     If[covariant === True, DeleteDuplicates[
       Join[categoryMorphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[arrowMappings] /. 
         Normal[objectMappings], morphismEquivalences]], DeleteDuplicates[
       Join[categoryMorphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[arrowMappings] /. 
          Normal[objectMappings] /. {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
           newCompositionSymbol[z, newCompositionSymbol[y, x]], newCompositionSymbol[newCompositionSymbol[x_, y_], z_] :> 
           newCompositionSymbol[newCompositionSymbol[z, y], x], newCompositionSymbol[x_, y_] :> 
           newCompositionSymbol[y, x]}, morphismEquivalences]]]]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   "ReducedObjectCount"] := (Length[reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
      categoryObjectEquivalences]] -> 
    Length[reduceObjects[reduceObjects[DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]], 
       quiverObjectEquivalences /. Normal[objectMappings]], DeleteDuplicates[
       Join[categoryObjectEquivalences /. Normal[objectMappings], objectEquivalences]]]]) /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   "ReducedMorphismCount"] := Module[{domainMorphismAssociation, domainCompositions, imageObjects, imageArrows, 
     imageQuiverObjectEquivalences, imageObjectEquivalences, imageArrowEquivalences, imageMorphismEquivalences, 
     imageMorphismAssociation, imageCompositions}, 
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
     imageObjects = DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]; 
     imageArrows = Association[DeleteDuplicates[Join[Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], 
         Normal[newArrows]]]]; imageQuiverObjectEquivalences = quiverObjectEquivalences /. Normal[objectMappings]; 
     imageObjectEquivalences = DeleteDuplicates[Join[categoryObjectEquivalences /. Normal[objectMappings], 
        objectEquivalences]]; imageArrowEquivalences = arrowEquivalences /. Normal[arrowMappings]; 
     imageMorphismEquivalences = If[covariant === True, DeleteDuplicates[
        Join[categoryMorphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[arrowMappings] /. 
          Normal[objectMappings], morphismEquivalences]], DeleteDuplicates[
        Join[categoryMorphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[arrowMappings] /. 
           Normal[objectMappings] /. {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
            newCompositionSymbol[z, newCompositionSymbol[y, x]], newCompositionSymbol[newCompositionSymbol[x_, y_], 
             z_] :> newCompositionSymbol[newCompositionSymbol[z, y], x], newCompositionSymbol[x_, y_] :> 
            newCompositionSymbol[y, x]}, morphismEquivalences]]]; imageMorphismAssociation = 
      Association[Select[Normal[Association[DeleteDuplicates[Join[If[covariant === True, 
             Normal[reduceArrowsFinal[reduceArrowsInitial[imageArrows, imageArrowEquivalences], 
               imageQuiverObjectEquivalences]], (First[#1] -> Reverse[Last[#1]] & ) /@ Normal[reduceArrowsFinal[
                reduceArrowsInitial[imageArrows, imageArrowEquivalences], imageQuiverObjectEquivalences]]], 
            Normal[newArrows]]]]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[imageCompositions = Select[Tuples[Normal[imageMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[imageMorphismAssociation], StringDelete[ToString[newCompositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], 
             newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ imageCompositions, Length[reduceObjects[imageObjects, 
        imageQuiverObjectEquivalences]]]; imageMorphismAssociation = 
      Association[Select[Normal[imageMorphismAssociation], 
        Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[imageMorphismAssociation], newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], newIdentitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[imageObjects, imageQuiverObjectEquivalences]; 
     Length[Normal[reduceArrowsFinal[reduceArrowsInitial[domainMorphismAssociation, categoryMorphismEquivalences], 
         categoryObjectEquivalences]]] -> Length[Normal[reduceArrowsFinal[reduceArrowsInitial[imageMorphismAssociation, 
          imageMorphismEquivalences], imageObjectEquivalences]]]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   "CompositionSymbol"] := (compositionSymbol -> newCompositionSymbol) /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   "IdentitySymbol"] := (identitySymbol -> newIdentitySymbol) /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]]["NewObjects"] := 
  Complement[DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]], 
    DeleteDuplicates[objects /. Normal[objectMappings]]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   "NewObjectCount"] := Length[Complement[DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]], 
     DeleteDuplicates[objects /. Normal[objectMappings]]]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   "ReducedNewObjects"] := 
  Complement[reduceObjects[reduceObjects[DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]], 
      quiverObjectEquivalences /. Normal[objectMappings]], DeleteDuplicates[
      Join[categoryObjectEquivalences /. Normal[objectMappings], objectEquivalences]]], 
    reduceObjects[reduceObjects[DeleteDuplicates[objects /. Normal[objectMappings]], 
      quiverObjectEquivalences /. Normal[objectMappings]], DeleteDuplicates[
      Join[categoryObjectEquivalences /. Normal[objectMappings], objectEquivalences]]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   "ReducedNewObjectCount"] := 
  Length[Complement[reduceObjects[reduceObjects[DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]], 
       quiverObjectEquivalences /. Normal[objectMappings]], DeleteDuplicates[
       Join[categoryObjectEquivalences /. Normal[objectMappings], objectEquivalences]]], 
     reduceObjects[reduceObjects[DeleteDuplicates[objects /. Normal[objectMappings]], 
       quiverObjectEquivalences /. Normal[objectMappings]], DeleteDuplicates[
       Join[categoryObjectEquivalences /. Normal[objectMappings], objectEquivalences]]]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]]["NewArrows"] := 
  Association[(First[#1] -> DirectedEdge @@ Last[#1] & ) /@ 
     Complement[Normal[Association[DeleteDuplicates[Join[If[covariant === True, 
           Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], (First[#1] -> Reverse[Last[#1]] & ) /@ 
            (Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings])], Normal[newArrows]]]]], 
      Normal[Association[DeleteDuplicates[If[covariant === True, Normal[arrows] /. Normal[arrowMappings] /. 
           Normal[objectMappings], (First[#1] -> Reverse[Last[#1]] & ) /@ (Normal[arrows] /. Normal[arrowMappings] /. 
            Normal[objectMappings])]]]]]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   "NewArrowCount"] := 
  Length[Normal[Association[(First[#1] -> DirectedEdge @@ Last[#1] & ) /@ 
       Complement[Normal[Association[DeleteDuplicates[Join[If[covariant === True, 
             Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], (First[#1] -> Reverse[Last[#1]] & ) /@ 
              (Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings])], Normal[newArrows]]]]], 
        Normal[Association[DeleteDuplicates[If[covariant === True, Normal[arrows] /. Normal[arrowMappings] /. 
             Normal[objectMappings], (First[#1] -> Reverse[Last[#1]] & ) /@ (Normal[arrows] /. Normal[arrowMappings] /. 
              Normal[objectMappings])]]]]]]]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]]["NewMorphisms"] := 
  Module[{oldMorphismAssociation, oldCompositions, morphismAssociation, compositions}, 
    oldMorphismAssociation = Association[Select[Normal[Association[DeleteDuplicates[If[covariant === True, 
            Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], (First[#1] -> Reverse[Last[#1]] & ) /@ 
             (Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings])]]]], 
        First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[oldCompositions = Select[Tuples[Normal[oldMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[oldMorphismAssociation], StringDelete[ToString[newCompositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          oldMorphismAssociation = Association[Append[Normal[oldMorphismAssociation], 
             newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ oldCompositions, Length[DeleteDuplicates[objects /. Normal[objectMappings]]]]; 
     oldMorphismAssociation = Association[Select[Normal[oldMorphismAssociation], 
        Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[oldMorphismAssociation], newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        oldMorphismAssociation = Association[Append[Normal[oldMorphismAssociation], newIdentitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ DeleteDuplicates[objects /. Normal[objectMappings]]; 
     morphismAssociation = Association[Select[Normal[Association[DeleteDuplicates[
           Join[If[covariant === True, Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], 
             (First[#1] -> Reverse[Last[#1]] & ) /@ (Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings])], 
            Normal[newArrows]]]]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[newCompositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, 
      Length[DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], newIdentitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]; 
     Association[Complement[(First[#1] -> DirectedEdge @@ Last[#1] & ) /@ Normal[morphismAssociation], 
       (First[#1] -> DirectedEdge @@ Last[#1] & ) /@ Normal[oldMorphismAssociation]]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   "NewMorphismCount"] := Module[{oldMorphismAssociation, oldCompositions, morphismAssociation, compositions}, 
    oldMorphismAssociation = Association[Select[Normal[Association[DeleteDuplicates[If[covariant === True, 
            Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], (First[#1] -> Reverse[Last[#1]] & ) /@ 
             (Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings])]]]], 
        First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[oldCompositions = Select[Tuples[Normal[oldMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[oldMorphismAssociation], StringDelete[ToString[newCompositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          oldMorphismAssociation = Association[Append[Normal[oldMorphismAssociation], 
             newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ oldCompositions, Length[DeleteDuplicates[objects /. Normal[objectMappings]]]]; 
     oldMorphismAssociation = Association[Select[Normal[oldMorphismAssociation], 
        Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[oldMorphismAssociation], newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        oldMorphismAssociation = Association[Append[Normal[oldMorphismAssociation], newIdentitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ DeleteDuplicates[objects /. Normal[objectMappings]]; 
     morphismAssociation = Association[Select[Normal[Association[DeleteDuplicates[
           Join[If[covariant === True, Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], 
             (First[#1] -> Reverse[Last[#1]] & ) /@ (Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings])], 
            Normal[newArrows]]]]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[newCompositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, 
      Length[DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], newIdentitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]; 
     Length[Normal[Association[Complement[(First[#1] -> DirectedEdge @@ Last[#1] & ) /@ Normal[morphismAssociation], 
         (First[#1] -> DirectedEdge @@ Last[#1] & ) /@ Normal[oldMorphismAssociation]]]]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   "ReducedNewMorphisms"] := Module[{oldObjects, oldArrows, oldQuiverObjectEquivalences, oldObjectEquivalences, 
     oldArrowEquivalences, oldMorphismEquivalences, oldMorphismAssociation, oldCompositions, imageObjects, imageArrows, 
     morphismAssociation, compositions}, oldObjects = DeleteDuplicates[objects /. Normal[objectMappings]]; 
     oldArrows = Association[DeleteDuplicates[Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings]]]; 
     oldQuiverObjectEquivalences = quiverObjectEquivalences /. Normal[objectMappings]; 
     oldObjectEquivalences = DeleteDuplicates[Join[categoryObjectEquivalences /. Normal[objectMappings], 
        objectEquivalences]]; oldArrowEquivalences = arrowEquivalences /. Normal[arrowMappings]; 
     oldMorphismEquivalences = If[covariant === True, DeleteDuplicates[
        Join[categoryMorphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[arrowMappings] /. 
          Normal[objectMappings], morphismEquivalences]], DeleteDuplicates[
        Join[categoryMorphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[arrowMappings] /. 
           Normal[objectMappings] /. {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
            newCompositionSymbol[z, newCompositionSymbol[y, x]], newCompositionSymbol[newCompositionSymbol[x_, y_], 
             z_] :> newCompositionSymbol[newCompositionSymbol[z, y], x], newCompositionSymbol[x_, y_] :> 
            newCompositionSymbol[y, x]}, morphismEquivalences]]]; oldMorphismAssociation = 
      Association[Select[Normal[Association[DeleteDuplicates[If[covariant === True, 
            Normal[reduceArrowsFinal[reduceArrowsInitial[oldArrows, oldArrowEquivalences], oldQuiverObjectEquivalences]], 
            (First[#1] -> Reverse[Last[#1]] & ) /@ Normal[reduceArrowsFinal[reduceArrowsInitial[oldArrows, 
                oldArrowEquivalences], oldQuiverObjectEquivalences]]]]]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[oldCompositions = Select[Tuples[Normal[oldMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[oldMorphismAssociation], StringDelete[ToString[newCompositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          oldMorphismAssociation = Association[Append[Normal[oldMorphismAssociation], 
             newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ oldCompositions, Length[reduceObjects[oldObjects, 
        oldQuiverObjectEquivalences]]]; oldMorphismAssociation = Association[Select[Normal[oldMorphismAssociation], 
        Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[oldMorphismAssociation], newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        oldMorphismAssociation = Association[Append[Normal[oldMorphismAssociation], newIdentitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[oldObjects, oldQuiverObjectEquivalences]; 
     imageObjects = DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]; 
     imageArrows = Association[DeleteDuplicates[Join[Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], 
         Normal[newArrows]]]]; morphismAssociation = 
      Association[Select[Normal[Association[DeleteDuplicates[Join[If[covariant === True, 
             Normal[reduceArrowsFinal[reduceArrowsInitial[imageArrows, oldArrowEquivalences], 
               oldQuiverObjectEquivalences]], (First[#1] -> Reverse[Last[#1]] & ) /@ Normal[reduceArrowsFinal[
                reduceArrowsInitial[imageArrows, oldArrowEquivalences], oldQuiverObjectEquivalences]]], 
            Normal[newArrows]]]]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[newCompositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, 
      Length[reduceObjects[imageObjects, oldQuiverObjectEquivalences]]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], newIdentitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[imageObjects, oldQuiverObjectEquivalences]; 
     Association[Complement[(First[#1] -> DirectedEdge @@ Last[#1] & ) /@ 
        Normal[reduceArrowsFinal[reduceArrowsInitial[morphismAssociation, oldMorphismEquivalences], 
          oldObjectEquivalences]], (First[#1] -> DirectedEdge @@ Last[#1] & ) /@ 
        Normal[reduceArrowsFinal[reduceArrowsInitial[oldMorphismAssociation, oldMorphismEquivalences], 
          oldObjectEquivalences]]]]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   "ReducedNewMorphismCount"] := Module[{oldObjects, oldArrows, oldQuiverObjectEquivalences, oldObjectEquivalences, 
     oldArrowEquivalences, oldMorphismEquivalences, oldMorphismAssociation, oldCompositions, imageObjects, imageArrows, 
     morphismAssociation, compositions}, oldObjects = DeleteDuplicates[objects /. Normal[objectMappings]]; 
     oldArrows = Association[DeleteDuplicates[Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings]]]; 
     oldQuiverObjectEquivalences = quiverObjectEquivalences /. Normal[objectMappings]; 
     oldObjectEquivalences = DeleteDuplicates[Join[categoryObjectEquivalences /. Normal[objectMappings], 
        objectEquivalences]]; oldArrowEquivalences = arrowEquivalences /. Normal[arrowMappings]; 
     oldMorphismEquivalences = If[covariant === True, DeleteDuplicates[
        Join[categoryMorphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[arrowMappings] /. 
          Normal[objectMappings], morphismEquivalences]], DeleteDuplicates[
        Join[categoryMorphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[arrowMappings] /. 
           Normal[objectMappings] /. {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
            newCompositionSymbol[z, newCompositionSymbol[y, x]], newCompositionSymbol[newCompositionSymbol[x_, y_], 
             z_] :> newCompositionSymbol[newCompositionSymbol[z, y], x], newCompositionSymbol[x_, y_] :> 
            newCompositionSymbol[y, x]}, morphismEquivalences]]]; oldMorphismAssociation = 
      Association[Select[Normal[Association[DeleteDuplicates[If[covariant === True, 
            Normal[reduceArrowsFinal[reduceArrowsInitial[oldArrows, oldArrowEquivalences], oldQuiverObjectEquivalences]], 
            (First[#1] -> Reverse[Last[#1]] & ) /@ Normal[reduceArrowsFinal[reduceArrowsInitial[oldArrows, 
                oldArrowEquivalences], oldQuiverObjectEquivalences]]]]]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[oldCompositions = Select[Tuples[Normal[oldMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[oldMorphismAssociation], StringDelete[ToString[newCompositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          oldMorphismAssociation = Association[Append[Normal[oldMorphismAssociation], 
             newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ oldCompositions, Length[reduceObjects[oldObjects, 
        oldQuiverObjectEquivalences]]]; oldMorphismAssociation = Association[Select[Normal[oldMorphismAssociation], 
        Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[oldMorphismAssociation], newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        oldMorphismAssociation = Association[Append[Normal[oldMorphismAssociation], newIdentitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[oldObjects, oldQuiverObjectEquivalences]; 
     imageObjects = DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]; 
     imageArrows = Association[DeleteDuplicates[Join[Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], 
         Normal[newArrows]]]]; morphismAssociation = 
      Association[Select[Normal[Association[DeleteDuplicates[Join[If[covariant === True, 
             Normal[reduceArrowsFinal[reduceArrowsInitial[imageArrows, oldArrowEquivalences], 
               oldQuiverObjectEquivalences]], (First[#1] -> Reverse[Last[#1]] & ) /@ Normal[reduceArrowsFinal[
                reduceArrowsInitial[imageArrows, oldArrowEquivalences], oldQuiverObjectEquivalences]]], 
            Normal[newArrows]]]]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[newCompositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, 
      Length[reduceObjects[imageObjects, oldQuiverObjectEquivalences]]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], newIdentitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[imageObjects, oldQuiverObjectEquivalences]; 
     Length[Normal[Association[Complement[(First[#1] -> DirectedEdge @@ Last[#1] & ) /@ 
          Normal[reduceArrowsFinal[reduceArrowsInitial[morphismAssociation, oldMorphismEquivalences], 
            oldObjectEquivalences]], (First[#1] -> DirectedEdge @@ Last[#1] & ) /@ 
          Normal[reduceArrowsFinal[reduceArrowsInitial[oldMorphismAssociation, oldMorphismEquivalences], 
            oldObjectEquivalences]]]]]]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   "ObjectMappings"] := Join[Association[(#1 -> #1 & ) /@ objects], objectMappings] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphsmEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   "ObjectMappingCount"] := Length[Normal[Join[Association[(#1 -> #1 & ) /@ objects], objectMappings]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   "ReducedObjectMappings"] := 
  Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, 
            quiverObjectEquivalences], categoryObjectEquivalences]]] -> reduceObjectsWithDuplicates[
        Values[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
            categoryObjectEquivalences]]], objectEquivalences]]], 
    Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[objectMappings], 
         quiverObjectEquivalences], categoryObjectEquivalences] -> reduceObjectsWithDuplicates[Values[objectMappings], 
        objectEquivalences]]]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   "ReducedObjectMappingCount"] := 
  Length[Normal[Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, 
              quiverObjectEquivalences], categoryObjectEquivalences]]] -> reduceObjectsWithDuplicates[
          Values[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
              categoryObjectEquivalences]]], objectEquivalences]]], 
      Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[objectMappings], 
           quiverObjectEquivalences], categoryObjectEquivalences] -> reduceObjectsWithDuplicates[Values[objectMappings], 
          objectEquivalences]]]]]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   "ArrowMappings"] := Join[Association[(#1 -> #1 & ) /@ Keys[arrows]], arrowMappings] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   "ArrowMappingCount"] := Length[Normal[Join[Association[(#1 -> #1 & ) /@ Keys[arrows]], arrowMappings]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   "MorphismMappings"] := Module[{objectListWithDuplicates, arrowListWithDuplicates, domainMorphismList, 
     domainCompositions, imageMorphismList, imageCompositions}, 
    objectListWithDuplicates = objects /. Normal[objectMappings]; arrowListWithDuplicates = 
      If[covariant === True, Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], 
       (First[#1] -> Reverse[Last[#1]] & ) /@ (Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings])]; 
     domainMorphismList = Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[domainCompositions = Select[Tuples[domainMorphismList, 2], Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ domainMorphismList, 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], domainMorphismList = 
           Append[domainMorphismList, compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ domainCompositions, Length[objects]]; 
     domainMorphismList = Select[domainMorphismList, Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        domainMorphismList = Append[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ objects; 
     imageMorphismList = Select[arrowListWithDuplicates, First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[imageCompositions = Select[Tuples[imageMorphismList, 2], Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ imageMorphismList, 
            StringDelete[ToString[newCompositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], imageMorphismList = 
           Append[imageMorphismList, newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ imageCompositions, 
      Length[objectListWithDuplicates]]; imageMorphismList = Select[imageMorphismList, 
       Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[imageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        imageMorphismList = Append[imageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      objectListWithDuplicates; Association[Thread[First /@ domainMorphismList -> First /@ imageMorphismList]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   "MorphismMappingCount"] := Module[{objectListWithDuplicates, arrowListWithDuplicates, domainMorphismList, 
     domainCompositions, imageMorphismList, imageCompositions}, 
    objectListWithDuplicates = objects /. Normal[objectMappings]; arrowListWithDuplicates = 
      If[covariant === True, Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], 
       (First[#1] -> Reverse[Last[#1]] & ) /@ (Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings])]; 
     domainMorphismList = Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[domainCompositions = Select[Tuples[domainMorphismList, 2], Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ domainMorphismList, 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], domainMorphismList = 
           Append[domainMorphismList, compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ domainCompositions, Length[objects]]; 
     domainMorphismList = Select[domainMorphismList, Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        domainMorphismList = Append[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ objects; 
     imageMorphismList = Select[arrowListWithDuplicates, First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[imageCompositions = Select[Tuples[imageMorphismList, 2], Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ imageMorphismList, 
            StringDelete[ToString[newCompositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], imageMorphismList = 
           Append[imageMorphismList, newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ imageCompositions, 
      Length[objectListWithDuplicates]]; imageMorphismList = Select[imageMorphismList, 
       Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[imageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        imageMorphismList = Append[imageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      objectListWithDuplicates; Length[Normal[Association[Thread[First /@ domainMorphismList -> 
          First /@ imageMorphismList]]]]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   "ReducedMorphismMappings"] := Module[{objectListWithDuplicates, arrowListWithDuplicates, domainMorphismList, 
     domainCompositions, imageMorphismList, imageCompositions}, 
    objectListWithDuplicates = objects /. Normal[objectMappings]; arrowListWithDuplicates = 
      If[covariant === True, Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], 
       (First[#1] -> Reverse[Last[#1]] & ) /@ (Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings])]; 
     domainMorphismList = Select[reduceArrowsFinalWithDuplicates[reduceArrowsInitialWithDuplicates[Normal[arrows], 
         arrowEquivalences], quiverObjectEquivalences], First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[domainCompositions = Select[Tuples[domainMorphismList, 2], Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ domainMorphismList, 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], domainMorphismList = 
           Append[domainMorphismList, compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ domainCompositions, 
      Length[reduceObjectsWithDuplicates[objects, quiverObjectEquivalences]]]; 
     domainMorphismList = Select[domainMorphismList, Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        domainMorphismList = Append[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      reduceObjectsWithDuplicates[objects, quiverObjectEquivalences]; domainMorphismList = 
      reduceArrowsFinalWithDuplicates[reduceArrowsInitialWithDuplicates[domainMorphismList, 
        categoryMorphismEquivalences], categoryObjectEquivalences]; imageMorphismList = 
      Select[reduceArrowsFinalWithDuplicates[reduceArrowsInitialWithDuplicates[arrowListWithDuplicates, 
         arrowEquivalences /. Normal[arrowMappings]], quiverObjectEquivalences /. Normal[objectMappings]], 
       First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[imageCompositions = Select[Tuples[imageMorphismList, 2], Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ imageMorphismList, 
            StringDelete[ToString[newCompositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], imageMorphismList = 
           Append[imageMorphismList, newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ imageCompositions, 
      Length[reduceObjectsWithDuplicates[objectListWithDuplicates, quiverObjectEquivalences /. Normal[objectMappings]]]]; 
     imageMorphismList = Select[imageMorphismList, Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[imageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        imageMorphismList = Append[imageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      reduceObjectsWithDuplicates[objectListWithDuplicates, quiverObjectEquivalences /. Normal[objectMappings]]; 
     imageMorphismList = reduceArrowsFinalWithDuplicates[reduceArrowsInitialWithDuplicates[imageMorphismList, 
        If[covariant === True, DeleteDuplicates[Join[categoryMorphismEquivalences /. compositionSymbol -> 
               newCompositionSymbol /. Normal[arrowMappings] /. Normal[objectMappings], morphismEquivalences]], 
         DeleteDuplicates[Join[categoryMorphismEquivalences /. compositionSymbol -> newCompositionSymbol /. 
              Normal[arrowMappings] /. Normal[objectMappings] /. {newCompositionSymbol[x_, newCompositionSymbol[y_, 
                z_]] :> newCompositionSymbol[z, newCompositionSymbol[y, x]], newCompositionSymbol[newCompositionSymbol[
                x_, y_], z_] :> newCompositionSymbol[newCompositionSymbol[z, y], x], newCompositionSymbol[x_, y_] :> 
              newCompositionSymbol[y, x]}, morphismEquivalences]]]], DeleteDuplicates[
        Join[categoryObjectEquivalences /. Normal[objectMappings], objectEquivalences]]]; 
     Association[Thread[First /@ domainMorphismList -> First /@ imageMorphismList]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   "ReducedMorphismMappingCount"] := Module[{objectListWithDuplicates, arrowListWithDuplicates, domainMorphismList, 
     domainCompositions, imageMorphismList, imageCompositions}, 
    objectListWithDuplicates = objects /. Normal[objectMappings]; arrowListWithDuplicates = 
      If[covariant === True, Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], 
       (First[#1] -> Reverse[Last[#1]] & ) /@ (Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings])]; 
     domainMorphismList = Select[reduceArrowsFinalWithDuplicates[reduceArrowsInitialWithDuplicates[Normal[arrows], 
         arrowEquivalences], quiverObjectEquivalences], First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[domainCompositions = Select[Tuples[domainMorphismList, 2], Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ domainMorphismList, 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], domainMorphismList = 
           Append[domainMorphismList, compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ domainCompositions, 
      Length[reduceObjectsWithDuplicates[objects, quiverObjectEquivalences]]]; 
     domainMorphismList = Select[domainMorphismList, Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        domainMorphismList = Append[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      reduceObjectsWithDuplicates[objects, quiverObjectEquivalences]; domainMorphismList = 
      reduceArrowsFinalWithDuplicates[reduceArrowsInitialWithDuplicates[domainMorphismList, 
        categoryMorphismEquivalences], categoryObjectEquivalences]; imageMorphismList = 
      Select[reduceArrowsFinalWithDuplicates[reduceArrowsInitialWithDuplicates[arrowListWithDuplicates, 
         arrowEquivalences /. Normal[arrowMappings]], quiverObjectEquivalences /. Normal[objectMappings]], 
       First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[imageCompositions = Select[Tuples[imageMorphismList, 2], Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ imageMorphismList, 
            StringDelete[ToString[newCompositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], imageMorphismList = 
           Append[imageMorphismList, newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ imageCompositions, 
      Length[reduceObjectsWithDuplicates[objectListWithDuplicates, quiverObjectEquivalences /. Normal[objectMappings]]]]; 
     imageMorphismList = Select[imageMorphismList, Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[imageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        imageMorphismList = Append[imageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      reduceObjectsWithDuplicates[objectListWithDuplicates, quiverObjectEquivalences /. Normal[objectMappings]]; 
     imageMorphismList = reduceArrowsFinalWithDuplicates[reduceArrowsInitialWithDuplicates[imageMorphismList, 
        If[covariant === True, DeleteDuplicates[Join[categoryMorphismEquivalences /. compositionSymbol -> 
               newCompositionSymbol /. Normal[arrowMappings] /. Normal[objectMappings], morphismEquivalences]], 
         DeleteDuplicates[Join[categoryMorphismEquivalences /. compositionSymbol -> newCompositionSymbol /. 
              Normal[arrowMappings] /. Normal[objectMappings] /. {newCompositionSymbol[x_, newCompositionSymbol[y_, 
                z_]] :> newCompositionSymbol[z, newCompositionSymbol[y, x]], newCompositionSymbol[newCompositionSymbol[
                x_, y_], z_] :> newCompositionSymbol[newCompositionSymbol[z, y], x], newCompositionSymbol[x_, y_] :> 
              newCompositionSymbol[y, x]}, morphismEquivalences]]]], DeleteDuplicates[
        Join[categoryObjectEquivalences /. Normal[objectMappings], objectEquivalences]]]; 
     Length[Normal[Association[Thread[First /@ domainMorphismList -> First /@ imageMorphismList]]]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   "DomainCategory"] := ResourceFunction["AbstractCategory"][Association["CompositionSymbol" -> compositionSymbol, 
     "IdentitySymbol" -> identitySymbol, "MorphismEquivalences" -> categoryMorphismEquivalences, 
     "ObjectEquivalences" -> categoryObjectEquivalences, "Quiver" -> ResourceFunction["AbstractQuiver"][
       Association["ArrowEquivalences" -> arrowEquivalences, "Arrows" -> arrows, "ObjectEquivalences" -> 
         quiverObjectEquivalences, "Objects" -> objects]]]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   "CodomainCategory"] := ResourceFunction["AbstractCategory"][Association["CompositionSymbol" -> newCompositionSymbol, 
     "IdentitySymbol" -> newIdentitySymbol, "MorphismEquivalences" -> If[covariant === True, 
       DeleteDuplicates[Join[categoryMorphismEquivalences /. compositionSymbol -> newCompositionSymbol /. 
           Normal[arrowMappings] /. Normal[objectMappings], morphismEquivalences]], 
       DeleteDuplicates[Join[categoryMorphismEquivalences /. compositionSymbol -> newCompositionSymbol /. 
            Normal[arrowMappings] /. Normal[objectMappings] /. {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
            newCompositionSymbol[z, newCompositionSymbol[y, x]], newCompositionSymbol[newCompositionSymbol[x_, y_], 
             z_] :> newCompositionSymbol[newCompositionSymbol[z, y], x], newCompositionSymbol[x_, y_] :> 
            newCompositionSymbol[y, x]}, morphismEquivalences]]], "ObjectEquivalences" -> 
      DeleteDuplicates[Join[categoryObjectEquivalences /. Normal[objectMappings], objectEquivalences]], 
     "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> 
         (arrowEquivalences /. Normal[arrowMappings]), "Arrows" -> Association[DeleteDuplicates[
           Join[If[covariant === True, Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], 
             (First[#1] -> Reverse[Last[#1]] & ) /@ (Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings])], 
            Normal[newArrows]]]], "ObjectEquivalences" -> (quiverObjectEquivalences /. Normal[objectMappings]), 
        "Objects" -> DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]]]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]]["EndofunctorQ"] := 
  Module[{domainMorphismAssociation, domainCompositions, imageObjects, imageArrows, imageQuiverObjectEquivalences, 
     imageArrowEquivalences, imageObjectEquivalences, imageMorphismEquivalences, imageMorphismAssociation, 
     imageCompositions}, domainMorphismAssociation = 
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
     imageObjects = DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]; 
     imageArrows = Association[DeleteDuplicates[Join[Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], 
         If[covariant === True, Normal[newArrows], (First[#1] -> Reverse[Last[#1]] & ) /@ Normal[newArrows]]]]]; 
     imageQuiverObjectEquivalences = quiverObjectEquivalences /. Normal[objectMappings]; 
     imageArrowEquivalences = arrowEquivalences /. Normal[arrowMappings]; imageObjectEquivalences = 
      DeleteDuplicates[Join[categoryObjectEquivalences /. Normal[objectMappings], objectEquivalences]]; 
     imageMorphismEquivalences = DeleteDuplicates[
       Join[categoryMorphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[arrowMappings] /. 
         Normal[objectMappings], If[covariant === True, morphismEquivalences, morphismEquivalences /. 
          {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> newCompositionSymbol[z, newCompositionSymbol[y, z]], 
           newCompositionSymbol[newCompositionSymbol[x_, y_], z_] :> newCompositionSymbol[newCompositionSymbol[z, y], x], 
           newCompositionSymbol[x_, y_] :> newCompositionSymbol[y, x]}]]]; imageMorphismAssociation = 
      Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[imageArrows, imageArrowEquivalences], 
          imageQuiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[imageCompositions = Select[Tuples[Normal[imageMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[imageMorphismAssociation], StringDelete[ToString[newCompositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], 
             newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ imageCompositions, Length[reduceObjects[imageObjects, 
        imageQuiverObjectEquivalences]]]; imageMorphismAssociation = 
      Association[Select[Normal[imageMorphismAssociation], 
        Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[imageMorphismAssociation], newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], newIdentitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[imageObjects, imageQuiverObjectEquivalences]; 
     Sort[reduceObjects[reduceObjects[objects, quiverObjectEquivalences], objectEquivalences]] === 
       Sort[reduceObjects[reduceObjects[imageObjects, imageQuiverObjectEquivalences], imageObjectEquivalences]] && 
      Sort[Normal[reduceArrowsFinal[reduceArrowsInitial[domainMorphismAssociation, categoryMorphismEquivalences], 
          objectEquivalences]]] === Sort[Normal[reduceArrowsFinal[reduceArrowsInitial[imageMorphismAssociation, 
           imageMorphismEquivalences], imageObjectEquivalences]]]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   "IdentityFunctorQ"] := Module[{reducedNewObjects, reducedObjectMappings, oldObjects, oldArrows, 
     oldQuiverObjectEquivalences, oldObjectEquivalences, oldArrowEquivalences, oldMorphismEquivalences, 
     oldMorphismAssociation, oldCompositions, imageObjects, imageArrows, morphismAssociation, compositions, 
     reducedNewMorphisms, objectListWithDuplicates, arrowListWithDuplicates, domainMorphismList, domainCompositions, 
     imageMorphismList, imageCompositions, reducedMorphismMappings}, 
    reducedNewObjects = Complement[reduceObjects[reduceObjects[DeleteDuplicates[Join[objects /. Normal[objectMappings], 
           newObjects]], quiverObjectEquivalences /. Normal[objectMappings]], 
        DeleteDuplicates[Join[categoryObjectEquivalences /. Normal[objectMappings], objectEquivalences]]], 
       reduceObjects[reduceObjects[DeleteDuplicates[objects /. Normal[objectMappings]], 
         quiverObjectEquivalences /. Normal[objectMappings]], DeleteDuplicates[
         Join[categoryObjectEquivalences /. Normal[objectMappings], objectEquivalences]]]]; 
     reducedObjectMappings = 
      Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, 
               quiverObjectEquivalences], categoryObjectEquivalences]]] -> reduceObjectsWithDuplicates[
           Values[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
               categoryObjectEquivalences]]], objectEquivalences]]], 
       Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[objectMappings], 
            quiverObjectEquivalences], categoryObjectEquivalences] -> reduceObjectsWithDuplicates[Values[objectMappings], 
           objectEquivalences]]]]; oldObjects = DeleteDuplicates[objects /. Normal[objectMappings]]; 
     oldArrows = Association[DeleteDuplicates[Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings]]]; 
     oldQuiverObjectEquivalences = quiverObjectEquivalences /. Normal[objectMappings]; 
     oldObjectEquivalences = DeleteDuplicates[Join[categoryObjectEquivalences /. Normal[objectMappings], 
        objectEquivalences]]; oldArrowEquivalences = arrowEquivalences /. Normal[arrowMappings]; 
     oldMorphismEquivalences = DeleteDuplicates[
       Join[categoryMorphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[arrowMappings] /. 
         Normal[objectMappings], If[covariant === True, morphismEquivalences, morphismEquivalences /. 
          {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> newCompositionSymbol[z, newCompositionSymbol[y, x]], 
           newCompositionSymbol[newCompositionSymbol[x_, y_], z_] :> newCompositionSymbol[newCompositionSymbol[z, y], x], 
           newCompositionSymbol[x_, y_] :> newCompositionSymbol[y, x]}]]]; oldMorphismAssociation = 
      Association[Select[Normal[Association[DeleteDuplicates[Normal[reduceArrowsFinal[reduceArrowsInitial[oldArrows, 
              oldArrowEquivalences], oldQuiverObjectEquivalences]]]]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[oldCompositions = Select[Tuples[Normal[oldMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[oldMorphismAssociation], StringDelete[ToString[newCompositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          oldMorphismAssociation = Association[Append[Normal[oldMorphismAssociation], 
             newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ oldCompositions, Length[reduceObjects[oldObjects, 
        oldQuiverObjectEquivalences]]]; oldMorphismAssociation = Association[Select[Normal[oldMorphismAssociation], 
        Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[oldMorphismAssociation], newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        oldMorphismAssociation = Association[Append[Normal[oldMorphismAssociation], newIdentitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[oldObjects, oldQuiverObjectEquivalences]; 
     imageObjects = DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]; 
     imageArrows = Association[DeleteDuplicates[Join[Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], 
         If[covariant === True, Normal[newArrows], (First[#1] -> Reverse[Last[#1]] & ) /@ Normal[newArrows]]]]]; 
     morphismAssociation = Association[Select[Normal[Association[DeleteDuplicates[
           Join[Normal[reduceArrowsFinal[reduceArrowsInitial[imageArrows, oldArrowEquivalences], 
              oldQuiverObjectEquivalences]], If[covariant === True, Normal[newArrows], 
             (First[#1] -> Reverse[Last[#1]] & ) /@ Normal[newArrows]]]]]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
            StringDelete[ToString[newCompositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, 
      Length[reduceObjects[imageObjects, oldQuiverObjectEquivalences]]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], newIdentitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[imageObjects, oldQuiverObjectEquivalences]; 
     reducedNewMorphisms = Association[Complement[(First[#1] -> DirectedEdge @@ Last[#1] & ) /@ 
         Normal[reduceArrowsFinal[reduceArrowsInitial[morphismAssociation, oldMorphismEquivalences], 
           oldObjectEquivalences]], (First[#1] -> DirectedEdge @@ Last[#1] & ) /@ 
         Normal[reduceArrowsFinal[reduceArrowsInitial[oldMorphismAssociation, oldMorphismEquivalences], 
           oldObjectEquivalences]]]]; objectListWithDuplicates = objects /. Normal[objectMappings]; 
     arrowListWithDuplicates = Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings]; 
     domainMorphismList = Select[reduceArrowsFinalWithDuplicates[reduceArrowsInitialWithDuplicates[Normal[arrows], 
         arrowEquivalences], quiverObjectEquivalences], First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[domainCompositions = Select[Tuples[domainMorphismList, 2], Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ domainMorphismList, 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], domainMorphismList = 
           Append[domainMorphismList, compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ domainCompositions, 
      Length[reduceObjectsWithDuplicates[objects, quiverObjectEquivalences]]]; 
     domainMorphismList = Select[domainMorphismList, Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        domainMorphismList = Append[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      reduceObjectsWithDuplicates[objects, quiverObjectEquivalences]; domainMorphismList = 
      reduceArrowsFinalWithDuplicates[reduceArrowsInitialWithDuplicates[domainMorphismList, 
        categoryMorphismEquivalences], categoryObjectEquivalences]; imageMorphismList = 
      Select[reduceArrowsFinalWithDuplicates[reduceArrowsInitialWithDuplicates[arrowListWithDuplicates, 
         arrowEquivalences /. Normal[arrowMappings]], quiverObjectEquivalences /. Normal[objectMappings]], 
       First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[imageCompositions = Select[Tuples[imageMorphismList, 2], Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ imageMorphismList, 
            StringDelete[ToString[newCompositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], imageMorphismList = 
           Append[imageMorphismList, newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ imageCompositions, 
      Length[reduceObjectsWithDuplicates[objectListWithDuplicates, quiverObjectEquivalences /. Normal[objectMappings]]]]; 
     imageMorphismList = Select[imageMorphismList, Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[imageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        imageMorphismList = Append[imageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      reduceObjectsWithDuplicates[objectListWithDuplicates, quiverObjectEquivalences /. Normal[objectMappings]]; 
     imageMorphismList = reduceArrowsFinalWithDuplicates[reduceArrowsInitialWithDuplicates[imageMorphismList, 
        DeleteDuplicates[Join[categoryMorphismEquivalences /. compositionSymbol -> newCompositionSymbol /. 
            Normal[arrowMappings] /. Normal[objectMappings], If[covariant === True, morphismEquivalences, 
           morphismEquivalences /. {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> newCompositionSymbol[z, 
               newCompositionSymbol[y, x]], newCompositionSymbol[newCompositionSymbol[x_, y_], z_] :> 
              newCompositionSymbol[newCompositionSymbol[z, y], x], newCompositionSymbol[x_, y_] :> 
              newCompositionSymbol[y, x]}]]]], DeleteDuplicates[Join[categoryObjectEquivalences /. 
          Normal[objectMappings], objectEquivalences]]]; reducedMorphismMappings = 
      Association[Thread[First /@ domainMorphismList -> First /@ imageMorphismList]]; 
     Length[reducedNewObjects] == 0 && Length[reducedNewMorphisms] == 0 && 
      Length[Select[Normal[reducedObjectMappings], First[#1] === Last[#1] & ]] == 
       Length[Normal[reducedObjectMappings]] && Length[Select[Normal[reducedMorphismMappings], 
         First[#1] === Last[#1] & ]] == Length[Normal[reducedMorphismMappings]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjecs_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   "ConstantFunctorQ"] := Module[{reducedObjectMappings, objectListWithDuplicates, arrowListWithDuplicates, 
     domainMorphismList, domainCompositions, imageMorphismList, imageCompositions, reducedMorphismMappings, 
     isConstantFunctor}, reducedObjectMappings = 
      Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, 
               quiverObjectEquivalences], categoryObjectEquivalences]]] -> reduceObjectsWithDuplicates[
           Values[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
               categoryObjectEquivalences]]], objectEquivalences]]], 
       Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[objectMappings], 
            quiverObjectEquivalences], categoryObjectEquivalences] -> reduceObjectsWithDuplicates[Values[objectMappings], 
           objectEquivalences]]]]; objectListWithDuplicates = objects /. Normal[objectMappings]; 
     arrowListWithDuplicates = If[covariant == True, Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], 
       (First[#1] -> Reverse[Last[#1]] & ) /@ (Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings])]; 
     domainMorphismList = Select[reduceArrowsFinalWithDuplicates[reduceArrowsInitialWithDuplicates[Normal[arrows], 
         arrowEquivalences], quiverObjectEquivalences], First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[domainCompositions = Select[Tuples[domainMorphismList, 2], Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ domainMorphismList, 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], domainMorphismList = 
           Append[domainMorphismList, compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ domainCompositions, 
      Length[reduceObjectsWithDuplicates[objects, quiverObjectEquivalences]]]; 
     domainMorphismList = Select[domainMorphismList, Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        domainMorphismList = Append[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      reduceObjectsWithDuplicates[objects, quiverObjectEquivalences]; domainMorphismList = 
      reduceArrowsFinalWithDuplicates[reduceArrowsInitialWithDuplicates[domainMorphismList, 
        categoryMorphismEquivalences], categoryObjectEquivalences]; imageMorphismList = 
      Select[reduceArrowsFinalWithDuplicates[reduceArrowsInitialWithDuplicates[arrowListWithDuplicates, 
         arrowEquivalences /. Normal[arrowMappings]], quiverObjectEquivalences /. Normal[objectMappings]], 
       First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[imageCompositions = Select[Tuples[imageMorphismList, 2], Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ imageMorphismList, 
            StringDelete[ToString[newCompositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], imageMorphismList = 
           Append[imageMorphismList, newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ imageCompositions, 
      Length[reduceObjectsWithDuplicates[objectListWithDuplicates, quiverObjectEquivalences /. Normal[objectMappings]]]]; 
     imageMorphismList = Select[imageMorphismList, Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[imageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        imageMorphismList = Append[imageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      reduceObjectsWithDuplicates[objectListWithDuplicates, quiverObjectEquivalences /. Normal[objectMappings]]; 
     imageMorphismList = reduceArrowsFinalWithDuplicates[reduceArrowsInitialWithDuplicates[imageMorphismList, 
        If[covariant === True, DeleteDuplicates[Join[categoryMorphismEquivalences /. compositionSymbol -> 
               newCompositionSymbol /. Normal[arrowMappings] /. Normal[objectMappings], morphismEquivalences]], 
         DeleteDuplicates[Join[categoryMorphismEquivalences /. compositionSymbol -> newCompositionSymbol /. 
              Normal[arrowMappings] /. Normal[objectMappings] /. {newCompositionSymbol[x_, newCompositionSymbol[y_, 
                z_]] :> newCompositionSymbol[z, newCompositionSymbol[y, x]], newCompositionSymbol[newCompositionSymbol[
                x_, y_], z_] :> newCompositionSymbol[newCompositionSymbol[z, y], x], newCompositionSymbol[x_, y_] :> 
              newCompositionSymbol[y, x]}, morphismEquivalences]]]], DeleteDuplicates[
        Join[categoryObjectEquivalences /. Normal[objectMappings], objectEquivalences]]]; 
     reducedMorphismMappings = Association[Thread[First /@ domainMorphismList -> First /@ imageMorphismList]]; 
     isConstantFunctor = True; If[Length[DeleteDuplicates[Last /@ Normal[reducedObjectMappings]]] != 1, 
      isConstantFunctor = False]; If[Length[DeleteDuplicates[Last /@ Normal[reducedMorphismMappings]]] != 1, 
      isConstantFunctor = False]; If[First[DeleteDuplicates[Last /@ Normal[reducedMorphismMappings]]] =!= 
       newIdentitySymbol[First[DeleteDuplicates[Last /@ Normal[reducedObjectMappings]]]], isConstantFunctor = False]; 
     isConstantFunctor] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]]["FullFunctorQ"] := 
  Module[{domainMorphismAssociation, domainCompositions, imageObjects, imageArrows, imageQuiverObjectEquivalences, 
     imageObjectEquivalences, imageArrowEquivalences, imageMorphismEquivalences, imageMorphismAssociation, 
     imageCompositions, reducedObjectMappings, objectPairs, isFullFunctor}, 
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
     domainMorphismAssociation = reduceArrowsFinal[reduceArrowsInitial[domainMorphismAssociation, 
        categoryMorphismEquivalences], categoryObjectEquivalences]; 
     imageObjects = DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]; 
     imageArrows = Association[DeleteDuplicates[Join[Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], 
         If[covariant === True, Normal[newArrows], (First[#1] -> Reverse[Last[#1]] & ) /@ Normal[newArrows]]]]]; 
     imageQuiverObjectEquivalences = quiverObjectEquivalences /. Normal[objectMappings]; 
     imageObjectEquivalences = DeleteDuplicates[Join[categoryObjectEquivalences /. Normal[objectMappings], 
        objectEquivalences]]; imageArrowEquivalences = arrowEquivalences /. Normal[arrowMappings]; 
     imageMorphismEquivalences = DeleteDuplicates[
       Join[categoryMorphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[arrowMappings] /. 
         Normal[objectMappings], If[covariant === True, morphismEquivalences, morphismEquivalences /. 
          {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> newCompositionSymbol[z, newCompositionSymbol[y, x]], 
           newCompositionSymbol[newCompositionSymbol[x_, y_], z_] :> newCompositionSymbol[newCompositionSymbol[z, y], x], 
           newCompositionSymbol[x_, y_] :> newCompositionSymbol[y, x]}]]]; imageMorphismAssociation = 
      Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[imageArrows, imageArrowEquivalences], 
          imageQuiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[imageCompositions = Select[Tuples[Normal[imageMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[imageMorphismAssociation], StringDelete[ToString[newCompositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], 
             newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ imageCompositions, Length[reduceObjects[imageObjects, 
        imageQuiverObjectEquivalences]]]; imageMorphismAssociation = 
      Association[Select[Normal[imageMorphismAssociation], 
        Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[imageMorphismAssociation], newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], newIdentitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[imageObjects, imageQuiverObjectEquivalences]; 
     imageMorphismAssociation = reduceArrowsFinal[reduceArrowsInitial[imageMorphismAssociation, 
        imageMorphismEquivalences], imageObjectEquivalences]; reducedObjectMappings = 
      Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, 
               quiverObjectEquivalences], categoryObjectEquivalences]]] -> reduceObjectsWithDuplicates[
           Values[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
               categoryObjectEquivalences]]], objectEquivalences]]], 
       Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[objectMappings], 
            quiverObjectEquivalences], categoryObjectEquivalences] -> reduceObjectsWithDuplicates[Values[objectMappings], 
           objectEquivalences]]]]; objectPairs = Tuples[reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
        categoryObjectEquivalences], 2]; isFullFunctor = True; 
     (Module[{objectPair = #1}, If[Length[Select[Normal[domainMorphismAssociation], 
            First[Last[#1]] === First[objectPair] && Last[Last[#1]] === Last[objectPair] & ]] < 
          Length[Select[Normal[imageMorphismAssociation], First[Last[#1]] === (First[objectPair] /. 
                Normal[reducedObjectMappings]) && Last[Last[#1]] === (Last[objectPair] /. 
                Normal[reducedObjectMappings]) & ]], isFullFunctor = False]] & ) /@ objectPairs; isFullFunctor] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   "FaithfulFunctorQ"] := Module[{domainMorphismAssociation, domainCompositions, imageObjects, imageArrows, 
     imageQuiverObjectEquivalences, imageObjectEquivalences, imageArrowEquivalences, imageMorphismEquivalences, 
     imageMorphismAssociation, imageCompositions, reducedObjectMappings, objectPairs, isFaithfulFunctor}, 
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
     domainMorphismAssociation = reduceArrowsFinal[reduceArrowsInitial[domainMorphismAssociation, 
        categoryMorphismEquivalences], categoryObjectEquivalences]; 
     imageObjects = DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]; 
     imageArrows = Association[DeleteDuplicates[Join[Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], 
         If[covariant === True, Normal[newArrows], (First[#1] -> Reverse[Last[#1]] & ) /@ Normal[newArrows]]]]]; 
     imageQuiverObjectEquivalences = quiverObjectEquivalences /. Normal[objectMappings]; 
     imageObjectEquivalences = DeleteDuplicates[Join[categoryObjectEquivalences /. Normal[objectMappings], 
        objectEquivalences]]; imageArrowEquivalences = arrowEquivalences /. Normal[arrowMappings]; 
     imageMorphismEquivalences = DeleteDuplicates[
       Join[categoryMorphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[arrowMappings] /. 
         Normal[objectMappings], If[covariant === True, morphismEquivalences, morphismEquivalences /. 
          {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> newCompositionSymbol[z, newCompositionSymbol[y, x]], 
           newCompositionSymbol[newCompositionSymbol[x_, y_], z_] :> newCompositionSymbol[newCompositionSymbol[z, y], x], 
           newCompositionSymbol[x_, y_] :> newCompositionSymbol[y, x]}]]]; imageMorphismAssociation = 
      Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[imageArrows, imageArrowEquivalences], 
          imageQuiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[imageCompositions = Select[Tuples[Normal[imageMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[imageMorphismAssociation], StringDelete[ToString[newCompositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], 
             newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ imageCompositions, Length[reduceObjects[imageObjects, 
        imageQuiverObjectEquivalences]]]; imageMorphismAssociation = 
      Association[Select[Normal[imageMorphismAssociation], 
        Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[imageMorphismAssociation], newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], newIdentitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[imageObjects, imageQuiverObjectEquivalences]; 
     imageMorphismAssociation = reduceArrowsFinal[reduceArrowsInitial[imageMorphismAssociation, 
        imageMorphismEquivalences], imageObjectEquivalences]; reducedObjectMappings = 
      Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, 
               quiverObjectEquivalences], categoryObjectEquivalences]]] -> reduceObjectsWithDuplicates[
           Values[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
               categoryObjectEquivalences]]], objectEquivalences]]], 
       Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[objectMappings], 
            quiverObjectEquivalences], categoryObjectEquivalences] -> reduceObjectsWithDuplicates[Values[objectMappings], 
           objectEquivalences]]]]; objectPairs = Tuples[reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
        categoryObjectEquivalences], 2]; isFaithfulFunctor = True; 
     (Module[{objectPair = #1}, If[Length[Select[Normal[domainMorphismAssociation], 
            First[Last[#1]] === First[objectPair] && Last[Last[#1]] === Last[objectPair] & ]] > 
          Length[Select[Normal[imageMorphismAssociation], First[Last[#1]] === (First[objectPair] /. 
                Normal[reducedObjectMappings]) && Last[Last[#1]] === (Last[objectPair] /. 
                Normal[reducedObjectMappings]) & ]], isFaithfulFunctor = False]] & ) /@ objectPairs; 
     isFaithfulFunctor] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   "FullyFaithfulFunctorQ"] := Module[{domainMorphismAssociation, domainCompositions, imageObjects, imageArrows, 
     imageQuiverObjectEquivalences, imageObjectEquivalences, imageArrowEquivalences, imageMorphismEquivalences, 
     imageMorphismAssociation, imageCompositions, reducedObjectMappings, objectPairs, isFullyFaithfulFunctor}, 
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
     domainMorphismAssociation = reduceArrowsFinal[reduceArrowsInitial[domainMorphismAssociation, 
        categoryMorphismEquivalences], categoryObjectEquivalences]; 
     imageObjects = DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]; 
     imageArrows = Association[DeleteDuplicates[Join[Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], 
         If[covariant === True, Normal[newArrows], (First[#1] -> Reverse[Last[#1]] & ) /@ Normal[newArrows]]]]]; 
     imageQuiverObjectEquivalences = quiverObjectEquivalences /. Normal[objectMappings]; 
     imageObjectEquivalences = DeleteDuplicates[Join[categoryObjectEquivalences /. Normal[objectMappings], 
        objectEquivalences]]; imageArrowEquivalences = arrowEquivalences /. Normal[arrowMappings]; 
     imageMorphismEquivalences = DeleteDuplicates[
       Join[categoryMorphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[arrowMappings] /. 
         Normal[objectMappings], If[covariant === True, morphismEquivalences, morphismEquivalences /. 
          {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> newCompositionSymbol[z, newCompositionSymbol[y, x]], 
           newCompositionSymbol[newCompositionSymbol[x_, y_], z_] :> newCompositionSymbol[newCompositionSymbol[z, y], x], 
           newCompositionSymbol[x_, y_] :> newCompositionSymbol[y, x]}]]]; imageMorphismAssociation = 
      Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[imageArrows, imageArrowEquivalences], 
          imageQuiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[imageCompositions = Select[Tuples[Normal[imageMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[imageMorphismAssociation], StringDelete[ToString[newCompositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], 
             newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ imageCompositions, Length[reduceObjects[imageObjects, 
        imageQuiverObjectEquivalences]]]; imageMorphismAssociation = 
      Association[Select[Normal[imageMorphismAssociation], 
        Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[imageMorphismAssociation], newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], newIdentitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[imageObjects, imageQuiverObjectEquivalences]; 
     imageMorphismAssociation = reduceArrowsFinal[reduceArrowsInitial[imageMorphismAssociation, 
        imageMorphismEquivalences], imageObjectEquivalences]; reducedObjectMappings = 
      Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, 
               quiverObjectEquivalences], categoryObjectEquivalences]]] -> reduceObjectsWithDuplicates[
           Values[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
               categoryObjectEquivalences]]], objectEquivalences]]], 
       Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[objectMappings], 
            quiverObjectEquivalences], categoryObjectEquivalences] -> reduceObjectsWithDuplicates[Values[objectMappings], 
           objectEquivalences]]]]; objectPairs = Tuples[reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
        categoryObjectEquivalences], 2]; isFullyFaithfulFunctor = True; 
     (Module[{objectPair = #1}, If[Length[Select[Normal[domainMorphismAssociation], 
            First[Last[#1]] === First[objectPair] && Last[Last[#1]] === Last[objectPair] & ]] != 
          Length[Select[Normal[imageMorphismAssociation], First[Last[#1]] === (First[objectPair] /. 
                Normal[reducedObjectMappings]) && Last[Last[#1]] === (Last[objectPair] /. 
                Normal[reducedObjectMappings]) & ]], isFullyFaithfulFunctor = False]] & ) /@ objectPairs; 
     isFullyFaithfulFunctor] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   "InjectiveOnObjectsQ"] := Module[{objectFunction, domainObjectEquivalenceGraph, imageObjectEquivalenceGraph, 
     objectPairs, isInjectiveOnObjects}, objectFunction = Join[Association[(#1 -> #1 & ) /@ objects], objectMappings]; 
     domainObjectEquivalenceGraph = Graph[Join[EdgeList[TransitiveClosureGraph[
          Graph[Apply[UndirectedEdge, Join[quiverObjectEquivalences, categoryObjectEquivalences], {1}]]]], 
        (UndirectedEdge[#1, #1] & ) /@ objects]]; imageObjectEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Join[quiverObjectEquivalences /. 
              Normal[objectMappings], DeleteDuplicates[Join[categoryObjectEquivalences /. Normal[objectMappings], 
               objectEquivalences]]], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ DeleteDuplicates[
          Join[objects /. Normal[objectMappings], newObjects]]]]; 
     objectPairs = Tuples[DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]], 2]; 
     isInjectiveOnObjects = True; 
     (Module[{objectPair = #1}, If[MemberQ[VertexList[imageObjectEquivalenceGraph], First[objectPair]] && 
          MemberQ[VertexList[imageObjectEquivalenceGraph], Last[objectPair]], 
         If[Length[FindShortestPath[imageObjectEquivalenceGraph, First[objectPair], Last[objectPair]]] > 0, 
          If[MemberQ[VertexList[domainObjectEquivalenceGraph], First[objectPair] /. Reverse /@ Normal[objectFunction]] && 
            MemberQ[VertexList[domainObjectEquivalenceGraph], Last[objectPair] /. Reverse /@ Normal[objectFunction]], 
           If[Length[FindShortestPath[domainObjectEquivalenceGraph, First[objectPair] /. Reverse /@ 
                 Normal[objectFunction], Last[objectPair] /. Reverse /@ Normal[objectFunction]]] == 0, 
            isInjectiveOnObjects = False]]]]] & ) /@ objectPairs; isInjectiveOnObjects] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   "EssentiallyInjectiveFunctorQ"] := Module[{domainMorphismAssociation, domainCompositions, 
     domainObjectEquivalenceGraph, domainMorphismEquivalenceGraph, domainIsomorphisms, imageMorphismAssociation, 
     imageCompositions, imageQuiverObjectEquivalences, imageObjectEquivalences, imageArrowEquivalences, 
     imageMorphismEquivalences, imageObjectEquivalenceGraph, imageMorphismEquivalenceGraph, imageIsomorphisms, 
     objectFunction, domainObjectIsomorphismGraph, imageObjectIsomorphismGraph, objectPairs, 
     isEssentiallyInjectiveFunctor}, domainMorphismAssociation = 
      Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
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
           identitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ objects; domainObjectEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Join[quiverObjectEquivalences, 
             categoryObjectEquivalences], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ objects]]; 
     domainMorphismEquivalenceGraph = Graph[Join[EdgeList[TransitiveClosureGraph[
          Graph[Apply[UndirectedEdge, Join[arrowEquivalences, categoryMorphismEquivalences], {1}]]]], 
        (UndirectedEdge[#1, #1] & ) /@ First /@ Normal[domainMorphismAssociation]]]; domainIsomorphisms = {}; 
     (Module[{morphism = #1, morphisms, isRetraction, isSection}, 
        morphisms = Select[Normal[domainMorphismAssociation], Length[FindShortestPath[domainObjectEquivalenceGraph, 
                Last[Last[#1]], First[Last[morphism]]]] > 0 && Length[FindShortestPath[domainObjectEquivalenceGraph, 
                First[Last[#1]], Last[Last[morphism]]]] > 0 & ]; isRetraction = False; isSection = False; 
         (If[morphism === (identitySymbol[#1] -> DirectedEdge[#1, #1]), isRetraction = True] & ) /@ objects; 
         (If[morphism === (identitySymbol[#1] -> DirectedEdge[#1, #1]), isSection = True] & ) /@ objects; 
         (Module[{newMorphism = #1, equivalentObjects}, If[MemberQ[VertexList[domainMorphismEquivalenceGraph], 
               compositionSymbol[First[morphism], First[newMorphism]]], equivalentObjects = Union[VertexComponent[
                  domainObjectEquivalenceGraph, Last[Last[morphism]]], VertexComponent[domainObjectEquivalenceGraph, 
                  First[Last[newMorphism]]]]; (If[MemberQ[VertexList[domainMorphismEquivalenceGraph], identitySymbol[
                    #1]], If[Length[FindShortestPath[domainMorphismEquivalenceGraph, compositionSymbol[First[morphism], 
                       First[newMorphism]], identitySymbol[#1]]] > 0, isRetraction = True]] & ) /@ equivalentObjects]; 
             If[MemberQ[VertexList[domainMorphismEquivalenceGraph], compositionSymbol[First[newMorphism], 
                First[morphism]]], equivalentObjects = Union[VertexComponent[domainObjectEquivalenceGraph, 
                  First[Last[morphism]]], VertexComponent[domainObjectEquivalenceGraph, Last[Last[newMorphism]]]]; 
               (If[MemberQ[VertexList[domainMorphismEquivalenceGraph], identitySymbol[#1]], 
                  If[Length[FindShortestPath[domainMorphismEquivalenceGraph, compositionSymbol[First[newMorphism], 
                       First[morphism]], identitySymbol[#1]]] > 0, isSection = True]] & ) /@ equivalentObjects]] & ) /@ 
          morphisms; If[isRetraction && isSection, domainIsomorphisms = Append[domainIsomorphisms, 
            Last[morphism]]]] & ) /@ Normal[domainMorphismAssociation]; 
     domainIsomorphisms = Select[Apply[Equal, DeleteDuplicates[domainIsomorphisms], {1}], #1 =!= True & ]; 
     imageMorphismAssociation = Association[Select[Normal[Association[DeleteDuplicates[
           Join[If[covariant === True, Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], 
             (First[#1] -> Reverse[Last[#1]] & ) /@ (Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings])], 
            Normal[newArrows]]]]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[imageCompositions = Select[Tuples[Normal[imageMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[imageMorphismAssociation], StringDelete[ToString[newCompositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], 
             newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ imageCompositions, 
      Length[DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]]]; 
     imageMorphismAssociation = Association[Select[Normal[imageMorphismAssociation], 
        Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[imageMorphismAssociation], newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], newIdentitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]; 
     imageQuiverObjectEquivalences = quiverObjectEquivalences /. Normal[objectMappings]; 
     imageObjectEquivalences = DeleteDuplicates[Join[categoryObjectEquivalences /. Normal[objectMappings], 
        objectEquivalences]]; imageArrowEquivalences = arrowEquivalences /. Normal[arrowMappings]; 
     imageMorphismEquivalences = If[covariant === True, DeleteDuplicates[
        Join[categoryMorphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[arrowMappings] /. 
          Normal[objectMappings], morphismEquivalences]], DeleteDuplicates[
        Join[categoryMorphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[arrowMappings] /. 
           Normal[objectMappings] /. {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
            newCompositionSymbol[z, newCompositionSymbol[y, x]], newCompositionSymbol[newCompositionSymbol[x_, y_], 
             z_] :> newCompositionSymbol[newCompositionSymbol[z, y], x], newCompositionSymbol[x_, y_] :> 
            newCompositionSymbol[y, x]}, morphismEquivalences]]]; imageObjectEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Join[imageQuiverObjectEquivalences, 
             imageObjectEquivalences], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ DeleteDuplicates[
          Join[objects /. Normal[objectMappings], newObjects]]]]; imageMorphismEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Join[imageArrowEquivalences, 
             imageMorphismEquivalences], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ 
         First /@ Normal[imageMorphismAssociation]]]; imageIsomorphisms = {}; 
     (Module[{morphism = #1, morphisms, isRetraction, isSection}, 
        morphisms = Select[Normal[imageMorphismAssociation], Length[FindShortestPath[imageObjectEquivalenceGraph, 
                Last[Last[#1]], First[Last[morphism]]]] > 0 && Length[FindShortestPath[imageObjectEquivalenceGraph, 
                First[Last[#1]], Last[Last[morphism]]]] > 0 & ]; isRetraction = False; isSection = False; 
         (If[morphism === (newIdentitySymbol[#1] -> DirectedEdge[#1, #1]), isRetraction = True] & ) /@ 
          DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]; 
         (If[morphism === (newIdentitySymbol[#1] -> DirectedEdge[#1, #1]), isSection = True] & ) /@ 
          DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]; 
         (Module[{newMorphism = #1, equivalentObjects}, If[MemberQ[VertexList[imageMorphismEquivalenceGraph], 
               newCompositionSymbol[First[morphism], First[newMorphism]]], equivalentObjects = 
                Union[VertexComponent[imageObjectEquivalenceGraph, Last[Last[morphism]]], VertexComponent[
                  imageObjectEquivalenceGraph, First[Last[newMorphism]]]]; (If[MemberQ[VertexList[
                    imageMorphismEquivalenceGraph], newIdentitySymbol[#1]], If[Length[FindShortestPath[
                      imageMorphismEquivalenceGraph, newCompositionSymbol[First[morphism], First[newMorphism]], 
                      newIdentitySymbol[#1]]] > 0, isRetraction = True]] & ) /@ equivalentObjects]; 
             If[MemberQ[VertexList[imageMorphismEquivalenceGraph], newCompositionSymbol[First[newMorphism], 
                First[morphism]]], equivalentObjects = Union[VertexComponent[imageObjectEquivalenceGraph, 
                  First[Last[morphism]]], VertexComponent[imageObjectEquivalenceGraph, Last[Last[newMorphism]]]]; 
               (If[MemberQ[VertexList[imageMorphismEquivalenceGraph], newIdentitySymbol[#1]], 
                  If[Length[FindShortestPath[imageMorphismEquivalenceGraph, newCompositionSymbol[First[newMorphism], 
                       First[morphism]], newIdentitySymbol[#1]]] > 0, isSection = True]] & ) /@ 
                equivalentObjects]] & ) /@ morphisms; If[isRetraction && isSection, imageIsomorphisms = 
           Append[imageIsomorphisms, Last[morphism]]]] & ) /@ Normal[imageMorphismAssociation]; 
     imageIsomorphisms = Select[Apply[Equal, DeleteDuplicates[Sort /@ imageIsomorphisms], {1}], #1 =!= True & ]; 
     objectFunction = Join[Association[(#1 -> #1 & ) /@ objects], objectMappings]; 
     domainObjectIsomorphismGraph = Graph[Join[EdgeList[TransitiveClosureGraph[
          Graph[Apply[UndirectedEdge, Join[quiverObjectEquivalences, categoryObjectEquivalences, domainIsomorphisms], 
            {1}]]]], (UndirectedEdge[#1, #1] & ) /@ objects]]; imageObjectIsomorphismGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Join[quiverObjectEquivalences /. 
              Normal[objectMappings], DeleteDuplicates[Join[categoryObjectEquivalences /. Normal[objectMappings], 
               objectEquivalences]], imageIsomorphisms], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ 
         DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]]]; 
     objectPairs = Tuples[DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]], 2]; 
     isEssentiallyInjectiveFunctor = True; 
     (Module[{objectPair = #1}, If[MemberQ[VertexList[imageObjectIsomorphismGraph], First[objectPair]] && 
          MemberQ[VertexList[imageObjectIsomorphismGraph], Last[objectPair]], 
         If[Length[FindShortestPath[imageObjectIsomorphismGraph, First[objectPair], Last[objectPair]]] > 0, 
          If[MemberQ[VertexList[domainObjectIsomorphismGraph], First[objectPair] /. Reverse /@ Normal[objectFunction]] && 
            MemberQ[VertexList[domainObjectIsomorphismGraph], Last[objectPair] /. Reverse /@ Normal[objectFunction]], 
           If[Length[FindShortestPath[domainObjectIsomorphismGraph, First[objectPair] /. Reverse /@ 
                 Normal[objectFunction], Last[objectPair] /. Reverse /@ Normal[objectFunction]]] == 0, 
            isEssentiallyInjectiveFunctor = False]]]]] & ) /@ objectPairs; isEssentiallyInjectiveFunctor] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   "SurjectiveOnObjectsQ"] := 
  Length[Complement[reduceObjects[reduceObjects[DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]], 
        quiverObjectEquivalences /. Normal[objectMappings]], DeleteDuplicates[
        Join[categoryObjectEquivalences /. Normal[objectMappings], objectEquivalences]]], 
      reduceObjects[reduceObjects[DeleteDuplicates[objects /. Normal[objectMappings]], 
        quiverObjectEquivalences /. Normal[objectMappings]], DeleteDuplicates[
        Join[categoryObjectEquivalences /. Normal[objectMappings], objectEquivalences]]]]] == 0 /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   "EssentiallySurjectiveFunctorQ"] := 
  Module[{imageMorphismAssociation, imageCompositions, imageQuiverObjectEquivalences, imageObjectEquivalences, 
     imageArrowEquivalences, imageMorphismEquivalences, imageObjectEquivalenceGraph, imageMorphismEquivalenceGraph, 
     imageIsomorphisms}, imageMorphismAssociation = Association[
       Select[Normal[Association[DeleteDuplicates[Join[If[covariant === True, Normal[arrows] /. Normal[arrowMappings] /. 
              Normal[objectMappings], (First[#1] -> Reverse[Last[#1]] & ) /@ (Normal[arrows] /. Normal[arrowMappings] /. 
               Normal[objectMappings])], Normal[newArrows]]]]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[imageCompositions = Select[Tuples[Normal[imageMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[imageMorphismAssociation], StringDelete[ToString[newCompositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], 
             newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ imageCompositions, 
      Length[DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]]]; 
     imageMorphismAssociation = Association[Select[Normal[imageMorphismAssociation], 
        Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[imageMorphismAssociation], newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], newIdentitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]; 
     imageQuiverObjectEquivalences = quiverObjectEquivalences /. Normal[objectMappings]; 
     imageObjectEquivalences = DeleteDuplicates[Join[categoryObjectEquivalences /. Normal[objectMappings], 
        objectEquivalences]]; imageArrowEquivalences = arrowEquivalences /. Normal[arrowMappings]; 
     imageMorphismEquivalences = If[covariant === True, DeleteDuplicates[
        Join[categoryMorphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[arrowMappings] /. 
          Normal[objectMappings], morphismEquivalences]], DeleteDuplicates[
        Join[categoryMorphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[arrowMappings] /. 
           Normal[objectMappings] /. {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
            newCompositionSymbol[z, newCompositionSymbol[y, x]], newCompositionSymbol[newCompositionSymbol[x_, y_], 
             z_] :> newCompositionSymbol[newCompositionSymbol[z, y], x], newCompositionSymbol[x_, y_] :> 
            newCompositionSymbol[y, x]}, morphismEquivalences]]]; imageObjectEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Join[imageQuiverObjectEquivalences, 
             imageObjectEquivalences], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ DeleteDuplicates[
          Join[objects /. Normal[objectMappings], newObjects]]]]; imageMorphismEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Join[imageArrowEquivalences, 
             imageMorphismEquivalences], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ 
         First /@ Normal[imageMorphismAssociation]]]; imageIsomorphisms = {}; 
     (Module[{morphism = #1, morphisms, isRetraction, isSection}, 
        morphisms = Select[Normal[imageMorphismAssociation], Length[FindShortestPath[imageObjectEquivalenceGraph, 
                Last[Last[#1]], First[Last[morphism]]]] > 0 && Length[FindShortestPath[imageObjectEquivalenceGraph, 
                First[Last[#1]], Last[Last[morphism]]]] > 0 & ]; isRetraction = False; isSection = False; 
         (If[morphism === (newIdentitySymbol[#1] -> DirectedEdge[#1, #1]), isRetraction = True] & ) /@ 
          DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]; 
         (If[morphism === (newIdentitySymbol[#1] -> DirectedEdge[#1, #1]), isSection = True] & ) /@ 
          DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]; 
         (Module[{newMorphism = #1, equivalentObjects}, If[MemberQ[VertexList[imageMorphismEquivalenceGraph], 
               newCompositionSymbol[First[morphism], First[newMorphism]]], equivalentObjects = 
                Union[VertexComponent[imageObjectEquivalenceGraph, Last[Last[morphism]]], VertexComponent[
                  imageObjectEquivalenceGraph, First[Last[newMorphism]]]]; (If[MemberQ[VertexList[
                    imageMorphismEquivalenceGraph], newIdentitySymbol[#1]], If[Length[FindShortestPath[
                      imageMorphismEquivalenceGraph, newCompositionSymbol[First[morphism], First[newMorphism]], 
                      newIdentitySymbol[#1]]] > 0, isRetraction = True]] & ) /@ equivalentObjects]; 
             If[MemberQ[VertexList[imageMorphismEquivalenceGraph], newCompositionSymbol[First[newMorphism], 
                First[morphism]]], equivalentObjects = Union[VertexComponent[imageObjectEquivalenceGraph, 
                  First[Last[morphism]]], VertexComponent[imageObjectEquivalenceGraph, Last[Last[newMorphism]]]]; 
               (If[MemberQ[VertexList[imageMorphismEquivalenceGraph], newIdentitySymbol[#1]], 
                  If[Length[FindShortestPath[imageMorphismEquivalenceGraph, newCompositionSymbol[First[newMorphism], 
                       First[morphism]], newIdentitySymbol[#1]]] > 0, isSection = True]] & ) /@ 
                equivalentObjects]] & ) /@ morphisms; If[isRetraction && isSection, imageIsomorphisms = 
           Append[imageIsomorphisms, Last[morphism]]]] & ) /@ Normal[imageMorphismAssociation]; 
     Length[Complement[reduceObjects[reduceObjects[DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]], 
          quiverObjectEquivalences /. Normal[objectMappings]], 
         Join[DeleteDuplicates[Join[categoryObjectEquivalences /. Normal[objectMappings], objectEquivalences]], 
          imageIsomorphisms]], reduceObjects[reduceObjects[DeleteDuplicates[objects /. Normal[objectMappings]], 
          quiverObjectEquivalences /. Normal[objectMappings]], 
         Join[DeleteDuplicates[Join[categoryObjectEquivalences /. Normal[objectMappings], objectEquivalences]], 
          imageIsomorphisms]]]] == 0] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   "BijectiveOnObjectsQ"] := Module[{objectFunction, domainObjectEquivalenceGraph, imageObjectEquivalenceGraph, 
     objectPairs, isInjectiveOnObjects}, objectFunction = Join[Association[(#1 -> #1 & ) /@ objects], objectMappings]; 
     domainObjectEquivalenceGraph = Graph[Join[EdgeList[TransitiveClosureGraph[
          Graph[Apply[UndirectedEdge, Join[quiverObjectEquivalences, categoryObjectEquivalences], {1}]]]], 
        (UndirectedEdge[#1, #1] & ) /@ objects]]; imageObjectEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Join[quiverObjectEquivalences /. 
              Normal[objectMappings], DeleteDuplicates[Join[categoryObjectEquivalences /. Normal[objectMappings], 
               objectEquivalences]]], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ DeleteDuplicates[
          Join[objects /. Normal[objectMappings], newObjects]]]]; 
     objectPairs = Tuples[DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]], 2]; 
     isInjectiveOnObjects = True; 
     (Module[{objectPair = #1}, If[MemberQ[VertexList[imageObjectEquivalenceGraph], First[objectPair]] && 
          MemberQ[VertexList[imageObjectEquivalenceGraph], Last[objectPair]], 
         If[Length[FindShortestPath[imageObjectEquivalenceGraph, First[objectPair], Last[objectPair]]] > 0, 
          If[MemberQ[VertexList[domainObjectEquivalenceGraph], First[objectPair] /. Reverse /@ Normal[objectFunction]] && 
            MemberQ[VertexList[domainObjectEquivalenceGraph], Last[objectPair] /. Reverse /@ Normal[objectFunction]], 
           If[Length[FindShortestPath[domainObjectEquivalenceGraph, First[objectPair] /. Reverse /@ 
                 Normal[objectFunction], Last[objectPair] /. Reverse /@ Normal[objectFunction]]] == 0, 
            isInjectiveOnObjects = False]]]]] & ) /@ objectPairs; isInjectiveOnObjects && 
      Length[Complement[reduceObjects[reduceObjects[DeleteDuplicates[Join[objects /. Normal[objectMappings], 
             newObjects]], quiverObjectEquivalences /. Normal[objectMappings]], DeleteDuplicates[
           Join[categoryObjectEquivalences /. Normal[objectMappings], objectEquivalences]]], 
         reduceObjects[reduceObjects[DeleteDuplicates[objects /. Normal[objectMappings]], quiverObjectEquivalences /. 
            Normal[objectMappings]], DeleteDuplicates[Join[categoryObjectEquivalences /. Normal[objectMappings], 
            objectEquivalences]]]]] == 0] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   "EssentiallyBijectiveFunctorQ"] := Module[{domainMorphismAssociation, domainCompositions, 
     domainObjectEquivalenceGraph, domainMorphismEquivalenceGraph, domainIsomorphisms, imageMorphismAssociation, 
     imageCompositions, imageQuiverObjectEquivalences, imageObjectEquivalences, imageArrowEquivalences, 
     imageMorphismEquivalences, imageObjectEquivalenceGraph, imageMorphismEquivalenceGraph, imageIsomorphisms, 
     objectFunction, domainObjectIsomorphismGraph, imageObjectIsomorphismGraph, objectPairs, 
     isEssentiallyInjectiveFunctor}, domainMorphismAssociation = 
      Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
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
           identitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ objects; domainObjectEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Join[quiverObjectEquivalences, 
             categoryObjectEquivalences], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ objects]]; 
     domainMorphismEquivalenceGraph = Graph[Join[EdgeList[TransitiveClosureGraph[
          Graph[Apply[UndirectedEdge, Join[arrowEquivalences, categoryMorphismEquivalences], {1}]]]], 
        (UndirectedEdge[#1, #1] & ) /@ First /@ Normal[domainMorphismAssociation]]]; domainIsomorphisms = {}; 
     (Module[{morphism = #1, morphisms, isRetraction, isSection}, 
        morphisms = Select[Normal[domainMorphismAssociation], Length[FindShortestPath[domainObjectEquivalenceGraph, 
                Last[Last[#1]], First[Last[morphism]]]] > 0 && Length[FindShortestPath[domainObjectEquivalenceGraph, 
                First[Last[#1]], Last[Last[morphism]]]] > 0 & ]; isRetraction = False; isSection = False; 
         (If[morphism === (identitySymbol[#1] -> DirectedEdge[#1, #1]), isRetraction = True] & ) /@ objects; 
         (If[morphism === (identitySymbol[#1] -> DirectedEdge[#1, #1]), isSection = True] & ) /@ objects; 
         (Module[{newMorphism = #1, equivalentObjects}, If[MemberQ[VertexList[domainMorphismEquivalenceGraph], 
               compositionSymbol[First[morphism], First[newMorphism]]], equivalentObjects = Union[VertexComponent[
                  domainObjectEquivalenceGraph, Last[Last[morphism]]], VertexComponent[domainObjectEquivalenceGraph, 
                  First[Last[newMorphism]]]]; (If[MemberQ[VertexList[domainMorphismEquivalenceGraph], identitySymbol[
                    #1]], If[Length[FindShortestPath[domainMorphismEquivalenceGraph, compositionSymbol[First[morphism], 
                       First[newMorphism]], identitySymbol[#1]]] > 0, isRetraction = True]] & ) /@ equivalentObjects]; 
             If[MemberQ[VertexList[domainMorphismEquivalenceGraph], compositionSymbol[First[newMorphism], 
                First[morphism]]], equivalentObjects = Union[VertexComponent[domainObjectEquivalenceGraph, 
                  First[Last[morphism]]], VertexComponent[domainObjectEquivalenceGraph, Last[Last[newMorphism]]]]; 
               (If[MemberQ[VertexList[domainMorphismEquivalenceGraph], identitySymbol[#1]], 
                  If[Length[FindShortestPath[domainMorphismEquivalenceGraph, compositionSymbol[First[newMorphism], 
                       First[morphism]], identitySymbol[#1]]] > 0, isSection = True]] & ) /@ equivalentObjects]] & ) /@ 
          morphisms; If[isRetraction && isSection, domainIsomorphisms = Append[domainIsomorphisms, 
            Last[morphism]]]] & ) /@ Normal[domainMorphismAssociation]; 
     domainIsomorphisms = Select[Apply[Equal, DeleteDuplicates[Sort /@ domainIsomorphisms], {1}], #1 =!= True & ]; 
     imageMorphismAssociation = Association[Select[Normal[Association[DeleteDuplicates[
           Join[If[covariant === True, Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], 
             (First[#1] -> Reverse[Last[#1]] & ) /@ (Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings])], 
            Normal[newArrows]]]]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[imageCompositions = Select[Tuples[Normal[imageMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[imageMorphismAssociation], StringDelete[ToString[newCompositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], 
             newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ imageCompositions, 
      Length[DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]]]; 
     imageMorphismAssociation = Association[Select[Normal[imageMorphismAssociation], 
        Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[imageMorphismAssociation], newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], newIdentitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]; 
     imageQuiverObjectEquivalences = quiverObjectEquivalences /. Normal[objectMappings]; 
     imageObjectEquivalences = DeleteDuplicates[Join[categoryObjectEquivalences /. Normal[objectMappings], 
        objectEquivalences]]; imageArrowEquivalences = arrowEquivalences /. Normal[arrowMappings]; 
     imageMorphismEquivalences = If[covariant === True, DeleteDuplicates[
        Join[categoryMorphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[arrowMappings] /. 
          Normal[objectMappings], morphismEquivalences]], DeleteDuplicates[
        Join[categoryMorphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[arrowMappings] /. 
           Normal[objectMappings] /. {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
            newCompositionSymbol[z, newCompositionSymbol[y, x]], newCompositionSymbol[newCompositionSymbol[x_, y_], 
             z_] :> newCompositionSymbol[newCompositionSymbol[z, y], x], newCompositionSymbol[x_, y_] :> 
            newCompositionSymbol[y, x]}, morphismEquivalences]]]; imageObjectEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Join[imageQuiverObjectEquivalences, 
             imageObjectEquivalences], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ DeleteDuplicates[
          Join[objects /. Normal[objectMappings], newObjects]]]]; imageMorphismEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Join[imageArrowEquivalences, 
             imageMorphismEquivalences], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ 
         First /@ Normal[imageMorphismAssociation]]]; imageIsomorphisms = {}; 
     (Module[{morphism = #1, morphisms, isRetraction, isSection}, 
        morphisms = Select[Normal[imageMorphismAssociation], Length[FindShortestPath[imageObjectEquivalenceGraph, 
                Last[Last[#1]], First[Last[morphism]]]] > 0 && Length[FindShortestPath[imageObjectEquivalenceGraph, 
                First[Last[#1]], Last[Last[morphism]]]] > 0 & ]; isRetraction = False; isSection = False; 
         (If[morphism === (newIdentitySymbol[#1] -> DirectedEdge[#1, #1]), isRetraction = True] & ) /@ 
          DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]; 
         (If[morphism === (newIdentitySymbol[#1] -> DirectedEdge[#1, #1]), isSection = True] & ) /@ 
          DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]; 
         (Module[{newMorphism = #1, equivalentObjects}, If[MemberQ[VertexList[imageMorphismEquivalenceGraph], 
               newCompositionSymbol[First[morphism], First[newMorphism]]], equivalentObjects = 
                Union[VertexComponent[imageObjectEquivalenceGraph, Last[Last[morphism]]], VertexComponent[
                  imageObjectEquivalenceGraph, First[Last[newMorphism]]]]; (If[MemberQ[VertexList[
                    imageMorphismEquivalenceGraph], newIdentitySymbol[#1]], If[Length[FindShortestPath[
                      imageMorphismEquivalenceGraph, newCompositionSymbol[First[morphism], First[newMorphism]], 
                      newIdentitySymbol[#1]]] > 0, isRetraction = True]] & ) /@ equivalentObjects]; 
             If[MemberQ[VertexList[imageMorphismEquivalenceGraph], newCompositionSymbol[First[newMorphism], 
                First[morphism]]], equivalentObjects = Union[VertexComponent[imageObjectEquivalenceGraph, 
                  First[Last[morphism]]], VertexComponent[imageObjectEquivalenceGraph, Last[Last[newMorphism]]]]; 
               (If[MemberQ[VertexList[imageMorphismEquivalenceGraph], newIdentitySymbol[#1]], 
                  If[Length[FindShortestPath[imageMorphismEquivalenceGraph, newCompositionSymbol[First[newMorphism], 
                       First[morphism]], newIdentitySymbol[#1]]] > 0, isSection = True]] & ) /@ 
                equivalentObjects]] & ) /@ morphisms; If[isRetraction && isSection, imageIsomorphisms = 
           Append[imageIsomorphisms, Last[morphism]]]] & ) /@ Normal[imageMorphismAssociation]; 
     imageIsomorphisms = Select[Apply[Equal, DeleteDuplicates[Sort /@ imageIsomorphisms], {1}], #1 =!= True & ]; 
     objectFunction = Join[Association[(#1 -> #1 & ) /@ objects], objectMappings]; 
     domainObjectIsomorphismGraph = Graph[Join[EdgeList[TransitiveClosureGraph[
          Graph[Apply[UndirectedEdge, Join[quiverObjectEquivalences, categoryObjectEquivalences, domainIsomorphisms], 
            {1}]]]], (UndirectedEdge[#1, #1] & ) /@ objects]]; imageObjectIsomorphismGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Join[quiverObjectEquivalences /. 
              Normal[objectMappings], DeleteDuplicates[Join[categoryObjectEquivalences /. Normal[objectMappings], 
               objectEquivalences]], imageIsomorphisms], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ 
         DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]]]; 
     objectPairs = Tuples[DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]], 2]; 
     isEssentiallyInjectiveFunctor = True; 
     (Module[{objectPair = #1}, If[MemberQ[VertexList[imageObjectIsomorphismGraph], First[objectPair]] && 
          MemberQ[VertexList[imageObjectIsomorphismGraph], Last[objectPair]], 
         If[Length[FindShortestPath[imageObjectIsomorphismGraph, First[objectPair], Last[objectPair]]] > 0, 
          If[MemberQ[VertexList[domainObjectIsomorphismGraph], First[objectPair] /. Reverse /@ Normal[objectFunction]] && 
            MemberQ[VertexList[domainObjectIsomorphismGraph], Last[objectPair] /. Reverse /@ Normal[objectFunction]], 
           If[Length[FindShortestPath[domainObjectIsomorphismGraph, First[objectPair] /. Reverse /@ 
                 Normal[objectFunction], Last[objectPair] /. Reverse /@ Normal[objectFunction]]] == 0, 
            isEssentiallyInjectiveFunctor = False]]]]] & ) /@ objectPairs; isEssentiallyInjectiveFunctor && 
      Length[Complement[reduceObjects[reduceObjects[DeleteDuplicates[Join[objects /. Normal[objectMappings], 
             newObjects]], quiverObjectEquivalences /. Normal[objectMappings]], 
          Join[DeleteDuplicates[Join[categoryObjectEquivalences /. Normal[objectMappings], objectEquivalences]], 
           imageIsomorphisms]], reduceObjects[reduceObjects[DeleteDuplicates[objects /. Normal[objectMappings]], 
           quiverObjectEquivalences /. Normal[objectMappings]], Join[DeleteDuplicates[
            Join[categoryObjectEquivalences /. Normal[objectMappings], objectEquivalences]], imageIsomorphisms]]]] == 
       0] /; SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   "ConservativeFunctorQ"] := Module[{domainMorphismAssociation, domainCompositions, domainObjectEquivalenceGraph, 
     domainMorphismEquivalenceGraph, domainIsomorphisms, imageMorphismAssociation, imageCompositions, 
     imageQuiverObjectEquivalences, imageObjectEquivalences, imageArrowEquivalences, imageMorphismEquivalences, 
     imageObjectEquivalenceGraph, imageMorphismEquivalenceGraph, imageIsomorphisms, objectListWithDuplicates, 
     arrowListWithDuplicates, domainMorphismList, domainCompositionsList, imageMorphismList, imageCompositionsList, 
     morphismFunction, isConservativeFunctor}, 
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
           identitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ objects; domainObjectEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Join[quiverObjectEquivalences, 
             categoryObjectEquivalences], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ objects]]; 
     domainMorphismEquivalenceGraph = Graph[Join[EdgeList[TransitiveClosureGraph[
          Graph[Apply[UndirectedEdge, Join[arrowEquivalences, categoryMorphismEquivalences], {1}]]]], 
        (UndirectedEdge[#1, #1] & ) /@ First /@ Normal[domainMorphismAssociation]]]; domainIsomorphisms = {}; 
     (Module[{morphism = #1, morphisms, isRetraction, isSection}, 
        morphisms = Select[Normal[domainMorphismAssociation], Length[FindShortestPath[domainObjectEquivalenceGraph, 
                Last[Last[#1]], First[Last[morphism]]]] > 0 && Length[FindShortestPath[domainObjectEquivalenceGraph, 
                First[Last[#1]], Last[Last[morphism]]]] > 0 & ]; isRetraction = False; isSection = False; 
         (If[morphism === (identitySymbol[#1] -> DirectedEdge[#1, #1]), isRetraction = True] & ) /@ objects; 
         (If[morphism === (identitySymbol[#1] -> DirectedEdge[#1, #1]), isSection = True] & ) /@ objects; 
         (Module[{newMorphism = #1, equivalentObjects}, If[MemberQ[VertexList[domainMorphismEquivalenceGraph], 
               compositionSymbol[First[morphism], First[newMorphism]]], equivalentObjects = Union[VertexComponent[
                  domainObjectEquivalenceGraph, Last[Last[morphism]]], VertexComponent[domainObjectEquivalenceGraph, 
                  First[Last[newMorphism]]]]; (If[MemberQ[VertexList[domainMorphismEquivalenceGraph], identitySymbol[
                    #1]], If[Length[FindShortestPath[domainMorphismEquivalenceGraph, compositionSymbol[First[morphism], 
                       First[newMorphism]], identitySymbol[#1]]] > 0, isRetraction = True]] & ) /@ equivalentObjects]; 
             If[MemberQ[VertexList[domainMorphismEquivalenceGraph], compositionSymbol[First[newMorphism], 
                First[morphism]]], equivalentObjects = Union[VertexComponent[domainObjectEquivalenceGraph, 
                  First[Last[morphism]]], VertexComponent[domainObjectEquivalenceGraph, Last[Last[newMorphism]]]]; 
               (If[MemberQ[VertexList[domainMorphismEquivalenceGraph], identitySymbol[#1]], 
                  If[Length[FindShortestPath[domainMorphismEquivalenceGraph, compositionSymbol[First[newMorphism], 
                       First[morphism]], identitySymbol[#1]]] > 0, isSection = True]] & ) /@ equivalentObjects]] & ) /@ 
          morphisms; If[isRetraction && isSection, domainIsomorphisms = Append[domainIsomorphisms, 
            First[morphism]]]] & ) /@ Normal[domainMorphismAssociation]; imageMorphismAssociation = 
      Association[Select[Normal[Association[DeleteDuplicates[Join[If[covariant === True, 
             Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], (First[#1] -> Reverse[Last[#1]] & ) /@ 
              (Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings])], Normal[newArrows]]]]], 
        First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[imageCompositions = Select[Tuples[Normal[imageMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[imageMorphismAssociation], StringDelete[ToString[newCompositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], 
             newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ imageCompositions, 
      Length[DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]]]; 
     imageMorphismAssociation = Association[Select[Normal[imageMorphismAssociation], 
        Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[imageMorphismAssociation], newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], newIdentitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]; 
     imageQuiverObjectEquivalences = quiverObjectEquivalences /. Normal[objectMappings]; 
     imageObjectEquivalences = DeleteDuplicates[Join[categoryObjectEquivalences /. Normal[objectMappings], 
        objectEquivalences]]; imageArrowEquivalences = arrowEquivalences /. Normal[arrowMappings]; 
     imageMorphismEquivalences = If[covariant === True, DeleteDuplicates[
        Join[categoryMorphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[arrowMappings] /. 
          Normal[objectMappings], morphismEquivalences]], DeleteDuplicates[
        Join[categoryMorphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[arrowMappings] /. 
           Normal[objectMappings] /. {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
            newCompositionSymbol[z, newCompositionSymbol[y, x]], newCompositionSymbol[newCompositionSymbol[x_, y_], 
             z_] :> newCompositionSymbol[newCompositionSymbol[z, y], x], newCompositionSymbol[x_, y_] :> 
            newCompositionSymbol[y, x]}, morphismEquivalences]]]; imageObjectEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Join[imageQuiverObjectEquivalences, 
             imageObjectEquivalences], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ DeleteDuplicates[
          Join[objects /. Normal[objectMappings], newObjects]]]]; imageMorphismEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Join[imageArrowEquivalences, 
             imageMorphismEquivalences], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ 
         First /@ Normal[imageMorphismAssociation]]]; imageIsomorphisms = {}; 
     (Module[{morphism = #1, morphisms, isRetraction, isSection}, 
        morphisms = Select[Normal[imageMorphismAssociation], Length[FindShortestPath[imageObjectEquivalenceGraph, 
                Last[Last[#1]], First[Last[morphism]]]] > 0 && Length[FindShortestPath[imageObjectEquivalenceGraph, 
                First[Last[#1]], Last[Last[morphism]]]] > 0 & ]; isRetraction = False; isSection = False; 
         (If[morphism === (newIdentitySymbol[#1] -> DirectedEdge[#1, #1]), isRetraction = True] & ) /@ 
          DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]; 
         (If[morphism === (newIdentitySymbol[#1] -> DirectedEdge[#1, #1]), isSection = True] & ) /@ 
          DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]; 
         (Module[{newMorphism = #1, equivalentObjects}, If[MemberQ[VertexList[imageMorphismEquivalenceGraph], 
               newCompositionSymbol[First[morphism], First[newMorphism]]], equivalentObjects = 
                Union[VertexComponent[imageObjectEquivalenceGraph, Last[Last[morphism]]], VertexComponent[
                  imageObjectEquivalenceGraph, First[Last[newMorphism]]]]; (If[MemberQ[VertexList[
                    imageMorphismEquivalenceGraph], newIdentitySymbol[#1]], If[Length[FindShortestPath[
                      imageMorphismEquivalenceGraph, newCompositionSymbol[First[morphism], First[newMorphism]], 
                      newIdentitySymbol[#1]]] > 0, isRetraction = True]] & ) /@ equivalentObjects]; 
             If[MemberQ[VertexList[imageMorphismEquivalenceGraph], newCompositionSymbol[First[newMorphism], 
                First[morphism]]], equivalentObjects = Union[VertexComponent[imageObjectEquivalenceGraph, 
                  First[Last[morphism]]], VertexComponent[imageObjectEquivalenceGraph, Last[Last[newMorphism]]]]; 
               (If[MemberQ[VertexList[imageMorphismEquivalenceGraph], newIdentitySymbol[#1]], 
                  If[Length[FindShortestPath[imageMorphismEquivalenceGraph, newCompositionSymbol[First[newMorphism], 
                       First[morphism]], newIdentitySymbol[#1]]] > 0, isSection = True]] & ) /@ 
                equivalentObjects]] & ) /@ morphisms; If[isRetraction && isSection, imageIsomorphisms = 
           Append[imageIsomorphisms, First[morphism]]]] & ) /@ Normal[imageMorphismAssociation]; 
     objectListWithDuplicates = objects /. Normal[objectMappings]; arrowListWithDuplicates = 
      If[covariant === True, Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], 
       (First[#1] -> Reverse[Last[#1]] & ) /@ (Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings])]; 
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
     imageMorphismList = Select[arrowListWithDuplicates, First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[imageCompositionsList = Select[Tuples[imageMorphismList, 2], Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ imageMorphismList, 
            StringDelete[ToString[newCompositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], imageMorphismList = 
           Append[imageMorphismList, newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ imageCompositionsList, 
      Length[objectListWithDuplicates]]; imageMorphismList = Select[imageMorphismList, 
       Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[imageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        imageMorphismList = Append[imageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      objectListWithDuplicates; morphismFunction = Association[Thread[First /@ domainMorphismList -> 
         First /@ imageMorphismList]]; isConservativeFunctor = True; 
     (Module[{imageIsomorphism = #1}, If[ !MemberQ[domainIsomorphisms, imageIsomorphism /. 
            Reverse /@ Normal[morphismFunction]], isConservativeFunctor = False]] & ) /@ imageIsomorphisms; 
     isConservativeFunctor] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   "EquivalenceFunctorQ"] := Module[{reducedDomainMorphismAssociation, reducedDomainCompositions, imageObjects, 
     imageArrows, imageQuiverObjectEquivalences, imageObjectEquivalences, imageArrowEquivalences, 
     imageMorphismEquivalences, reducedImageMorphismAssociation, reducedImageCompositions, reducedObjectMappings, 
     objectPairs, isFullyFaithfulFunctor, imageMorphismAssociation, imageCompositions, newImageMorphismEquivalences, 
     imageObjectEquivalenceGraph, imageMorphismEquivalenceGraph, imageIsomorphisms}, 
    reducedDomainMorphismAssociation = Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[arrows, 
           arrowEquivalences], quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[reducedDomainCompositions = Select[Tuples[Normal[reducedDomainMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[reducedDomainMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          reducedDomainMorphismAssociation = Association[Append[Normal[reducedDomainMorphismAssociation], 
             compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ reducedDomainCompositions, 
      Length[reduceObjects[objects, quiverObjectEquivalences]]]; reducedDomainMorphismAssociation = 
      Association[Select[Normal[reducedDomainMorphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[reducedDomainMorphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        reducedDomainMorphismAssociation = Association[Append[Normal[reducedDomainMorphismAssociation], 
           identitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[objects, quiverObjectEquivalences]; 
     reducedDomainMorphismAssociation = reduceArrowsFinal[reduceArrowsInitial[reducedDomainMorphismAssociation, 
        categoryMorphismEquivalences], categoryObjectEquivalences]; 
     imageObjects = DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]; 
     imageArrows = Association[DeleteDuplicates[Join[Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], 
         If[covariant === True, Normal[newArrows], (First[#1] -> Reverse[Last[#1]] & ) /@ Normal[newArrows]]]]]; 
     imageQuiverObjectEquivalences = quiverObjectEquivalences /. Normal[objectMappings]; 
     imageObjectEquivalences = DeleteDuplicates[Join[categoryObjectEquivalences /. Normal[objectMappings], 
        objectEquivalences]]; imageArrowEquivalences = arrowEquivalences /. Normal[arrowMappings]; 
     imageMorphismEquivalences = DeleteDuplicates[
       Join[categoryMorphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[arrowMappings] /. 
         Normal[objectMappings], If[covariant === True, morphismEquivalences, morphismEquivalences /. 
          {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> newCompositionSymbol[z, newCompositionSymbol[y, x]], 
           newCompositionSymbol[newCompositionSymbol[x_, y_], z_] :> newCompositionSymbol[newCompositionSymbol[z, y], x], 
           newCompositionSymbol[x_, y_] :> newCompositionSymbol[y, x]}]]]; reducedImageMorphismAssociation = 
      Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[imageArrows, imageArrowEquivalences], 
          imageQuiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[reducedImageCompositions = Select[Tuples[Normal[reducedImageMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[reducedImageMorphismAssociation], StringDelete[ToString[newCompositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          reducedImageMorphismAssociation = Association[Append[Normal[reducedImageMorphismAssociation], 
             newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ reducedImageCompositions, 
      Length[reduceObjects[imageObjects, imageQuiverObjectEquivalences]]]; reducedImageMorphismAssociation = 
      Association[Select[Normal[reducedImageMorphismAssociation], 
        Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[reducedImageMorphismAssociation], newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        reducedImageMorphismAssociation = Association[Append[Normal[reducedImageMorphismAssociation], 
           newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[imageObjects, 
       imageQuiverObjectEquivalences]; reducedImageMorphismAssociation = 
      reduceArrowsFinal[reduceArrowsInitial[reducedImageMorphismAssociation, imageMorphismEquivalences], 
       imageObjectEquivalences]; reducedObjectMappings = 
      Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, 
               quiverObjectEquivalences], categoryObjectEquivalences]]] -> reduceObjectsWithDuplicates[
           Values[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
               categoryObjectEquivalences]]], objectEquivalences]]], 
       Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[objectMappings], 
            quiverObjectEquivalences], categoryObjectEquivalences] -> reduceObjectsWithDuplicates[Values[objectMappings], 
           objectEquivalences]]]]; objectPairs = Tuples[reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
        categoryObjectEquivalences], 2]; isFullyFaithfulFunctor = True; 
     (Module[{objectPair = #1}, If[Length[Select[Normal[reducedDomainMorphismAssociation], 
            First[Last[#1]] === First[objectPair] && Last[Last[#1]] === Last[objectPair] & ]] != 
          Length[Select[Normal[reducedImageMorphismAssociation], First[Last[#1]] === (First[objectPair] /. 
                Normal[reducedObjectMappings]) && Last[Last[#1]] === (Last[objectPair] /. 
                Normal[reducedObjectMappings]) & ]], isFullyFaithfulFunctor = False]] & ) /@ objectPairs; 
     imageMorphismAssociation = Association[Select[Normal[Association[DeleteDuplicates[
           Join[If[covariant === True, Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], 
             (First[#1] -> Reverse[Last[#1]] & ) /@ (Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings])], 
            Normal[newArrows]]]]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[imageCompositions = Select[Tuples[Normal[imageMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[imageMorphismAssociation], StringDelete[ToString[newCompositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], 
             newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ imageCompositions, 
      Length[DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]]]; 
     imageMorphismAssociation = Association[Select[Normal[imageMorphismAssociation], 
        Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[imageMorphismAssociation], newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], newIdentitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]; 
     newImageMorphismEquivalences = If[covariant === True, DeleteDuplicates[
        Join[categoryMorphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[arrowMappings] /. 
          Normal[objectMappings], morphismEquivalences]], DeleteDuplicates[
        Join[categoryMorphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[arrowMappings] /. 
           Normal[objectMappings] /. {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
            newCompositionSymbol[z, newCompositionSymbol[y, x]], newCompositionSymbol[newCompositionSymbol[x_, y_], 
             z_] :> newCompositionSymbol[newCompositionSymbol[z, y], x], newCompositionSymbol[x_, y_] :> 
            newCompositionSymbol[y, x]}, morphismEquivalences]]]; imageObjectEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Join[imageQuiverObjectEquivalences, 
             imageObjectEquivalences], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ DeleteDuplicates[
          Join[objects /. Normal[objectMappings], newObjects]]]]; imageMorphismEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Join[imageArrowEquivalences, 
             newImageMorphismEquivalences], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ 
         First /@ Normal[imageMorphismAssociation]]]; imageIsomorphisms = {}; 
     (Module[{morphism = #1, morphisms, isRetraction, isSection}, 
        morphisms = Select[Normal[imageMorphismAssociation], Length[FindShortestPath[imageObjectEquivalenceGraph, 
                Last[Last[#1]], First[Last[morphism]]]] > 0 && Length[FindShortestPath[imageObjectEquivalenceGraph, 
                First[Last[#1]], Last[Last[morphism]]]] > 0 & ]; isRetraction = False; isSection = False; 
         (If[morphism === (newIdentitySymbol[#1] -> DirectedEdge[#1, #1]), isRetraction = True] & ) /@ 
          DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]; 
         (If[morphism === (newIdentitySymbol[#1] -> DirectedEdge[#1, #1]), isSection = True] & ) /@ 
          DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]; 
         (Module[{newMorphism = #1, equivalentObjects}, If[MemberQ[VertexList[imageMorphismEquivalenceGraph], 
               newCompositionSymbol[First[morphism], First[newMorphism]]], equivalentObjects = 
                Union[VertexComponent[imageObjectEquivalenceGraph, Last[Last[morphism]]], VertexComponent[
                  imageObjectEquivalenceGraph, First[Last[newMorphism]]]]; (If[MemberQ[VertexList[
                    imageMorphismEquivalenceGraph], newIdentitySymbol[#1]], If[Length[FindShortestPath[
                      imageMorphismEquivalenceGraph, newCompositionSymbol[First[morphism], First[newMorphism]], 
                      newIdentitySymbol[#1]]] > 0, isRetraction = True]] & ) /@ equivalentObjects]; 
             If[MemberQ[VertexList[imageMorphismEquivalenceGraph], newCompositionSymbol[First[newMorphism], 
                First[morphism]]], equivalentObjects = Union[VertexComponent[imageObjectEquivalenceGraph, 
                  First[Last[morphism]]], VertexComponent[imageObjectEquivalenceGraph, Last[Last[newMorphism]]]]; 
               (If[MemberQ[VertexList[imageMorphismEquivalenceGraph], newIdentitySymbol[#1]], 
                  If[Length[FindShortestPath[imageMorphismEquivalenceGraph, newCompositionSymbol[First[newMorphism], 
                       First[morphism]], newIdentitySymbol[#1]]] > 0, isSection = True]] & ) /@ 
                equivalentObjects]] & ) /@ morphisms; If[isRetraction && isSection, imageIsomorphisms = 
           Append[imageIsomorphisms, Last[morphism]]]] & ) /@ Normal[imageMorphismAssociation]; 
     isFullyFaithfulFunctor && Length[Complement[reduceObjects[reduceObjects[DeleteDuplicates[
            Join[objects /. Normal[objectMappings], newObjects]], quiverObjectEquivalences /. Normal[objectMappings]], 
          Join[DeleteDuplicates[Join[categoryObjectEquivalences /. Normal[objectMappings], objectEquivalences]], 
           imageIsomorphisms]], reduceObjects[reduceObjects[DeleteDuplicates[objects /. Normal[objectMappings]], 
           quiverObjectEquivalences /. Normal[objectMappings]], Join[DeleteDuplicates[
            Join[categoryObjectEquivalences /. Normal[objectMappings], objectEquivalences]], imageIsomorphisms]]]] == 
       0] /; SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   "FiberCategories"] := Module[{objectFunction, objectListWithDuplicates, arrowListWithDuplicates, domainMorphismList, 
     domainCompositions, imageMorphismList, imageCompositions, morphismFunction, domainObjectEquivalenceGraph, 
     domainMorphismEquivalenceGraph, imageQuiverObjectEquivalences, imageObjectEquivalences, imageArrowEquivalences, 
     imageMorphismEquivalences, imageObjectEquivalenceGraph, imageMorphismEquivalenceGraph, fiberCategories}, 
    objectFunction = Join[Association[(#1 -> #1 & ) /@ objects], objectMappings]; 
     objectListWithDuplicates = objects /. Normal[objectMappings]; arrowListWithDuplicates = 
      If[covariant === True, Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], 
       (First[#1] -> Reverse[Last[#1]] & ) /@ (Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings])]; 
     domainMorphismList = Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[domainCompositions = Select[Tuples[domainMorphismList, 2], Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ domainMorphismList, 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], domainMorphismList = 
           Append[domainMorphismList, compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ domainCompositions, Length[objects]]; 
     domainMorphismList = Select[domainMorphismList, Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        domainMorphismList = Append[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ objects; 
     imageMorphismList = Select[arrowListWithDuplicates, First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[imageCompositions = Select[Tuples[imageMorphismList, 2], Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ imageMorphismList, 
            StringDelete[ToString[newCompositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], imageMorphismList = 
           Append[imageMorphismList, newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ imageCompositions, 
      Length[objectListWithDuplicates]]; imageMorphismList = Select[imageMorphismList, 
       Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[imageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        imageMorphismList = Append[imageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      objectListWithDuplicates; morphismFunction = Association[Thread[First /@ domainMorphismList -> 
         First /@ imageMorphismList]]; domainObjectEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Join[quiverObjectEquivalences, 
             categoryObjectEquivalences], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ objects]]; 
     domainMorphismEquivalenceGraph = Graph[Join[EdgeList[TransitiveClosureGraph[
          Graph[Apply[UndirectedEdge, Join[arrowEquivalences, categoryMorphismEquivalences], {1}]]]], 
        (UndirectedEdge[#1, #1] & ) /@ First /@ Normal[Association[DeleteDuplicates[domainMorphismList]]]]]; 
     imageQuiverObjectEquivalences = quiverObjectEquivalences /. Normal[objectMappings]; 
     imageObjectEquivalences = DeleteDuplicates[Join[categoryObjectEquivalences /. Normal[objectMappings], 
        objectEquivalences]]; imageArrowEquivalences = arrowEquivalences /. Normal[arrowMappings]; 
     imageMorphismEquivalences = If[covariant === True, DeleteDuplicates[
        Sort /@ Join[categoryMorphismEquivalences /. compositionSymbol -> newCompositionSymbol /. 
            Normal[arrowMappings] /. Normal[objectMappings], morphismEquivalences]], 
       DeleteDuplicates[Sort /@ Join[categoryMorphismEquivalences /. compositionSymbol -> newCompositionSymbol /. 
             Normal[arrowMappings] /. Normal[objectMappings] /. {newCompositionSymbol[x_, newCompositionSymbol[y_, 
               z_]] :> newCompositionSymbol[z, newCompositionSymbol[y, x]], 
            newCompositionSymbol[newCompositionSymbol[x_, y_], z_] :> newCompositionSymbol[newCompositionSymbol[z, y], 
              x], newCompositionSymbol[x_, y_] :> newCompositionSymbol[y, x]}, morphismEquivalences]]]; 
     imageObjectEquivalenceGraph = Graph[Join[EdgeList[TransitiveClosureGraph[
          Graph[Apply[UndirectedEdge, Join[imageQuiverObjectEquivalences, imageObjectEquivalences], {1}]]]], 
        (UndirectedEdge[#1, #1] & ) /@ DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]]]; 
     imageMorphismEquivalenceGraph = Graph[Join[EdgeList[TransitiveClosureGraph[
          Graph[Apply[UndirectedEdge, Join[imageArrowEquivalences, imageMorphismEquivalences], {1}]]]], 
        (UndirectedEdge[#1, #1] & ) /@ First /@ Normal[Association[DeleteDuplicates[imageMorphismList]]]]]; 
     fiberCategories = {}; (Module[{imageObject = #1, fiberObjects, fiberMorphisms}, 
        fiberObjects = {}; fiberMorphisms = {}; (Module[{domainObject = #1, equivalentObjects}, 
            If[MemberQ[VertexList[domainObjectEquivalenceGraph], domainObject], equivalentObjects = VertexComponent[
                domainObjectEquivalenceGraph, domainObject]; If[MemberQ[VertexList[imageObjectEquivalenceGraph], 
                 domainObject /. Normal[objectFunction]] && MemberQ[VertexList[imageObjectEquivalenceGraph], 
                 imageObject], If[Length[FindShortestPath[imageObjectEquivalenceGraph, domainObject /. 
                    Normal[objectFunction], imageObject]] > 0, fiberObjects = Union[fiberObjects, 
                  equivalentObjects]]]]] & ) /@ objects; (Module[{domainMorphism = #1, equivalentMorphisms}, 
            If[MemberQ[VertexList[domainMorphismEquivalenceGraph], domainMorphism], equivalentMorphisms = VertexComponent[
                domainMorphismEquivalenceGraph, domainMorphism]; If[MemberQ[VertexList[imageMorphismEquivalenceGraph], 
                 domainMorphism /. Normal[morphismFunction]] && MemberQ[VertexList[imageMorphismEquivalenceGraph], 
                 newIdentitySymbol[imageObject]], If[Length[FindShortestPath[imageMorphismEquivalenceGraph, 
                   domainMorphism /. Normal[morphismFunction], newIdentitySymbol[imageObject]]] > 0, fiberMorphisms = 
                 Union[fiberMorphisms, Select[Normal[Association[DeleteDuplicates[domainMorphismList]]], 
                   MemberQ[equivalentMorphisms, First[#1]] & ]]]]]] & ) /@ 
          First /@ Normal[Association[DeleteDuplicates[domainMorphismList]]]; fiberCategories = 
          Append[fiberCategories, imageObject -> ResourceFunction["AbstractCategory"][
             Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
              "MorphismEquivalences" -> categoryMorphismEquivalences, "ObjectEquivalences" -> categoryObjectEquivalences, 
              "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> arrowEquivalences, 
                 "Arrows" -> Association[DeleteDuplicates[fiberMorphisms]], "ObjectEquivalences" -> 
                  quiverObjectEquivalences, "Objects" -> fiberObjects]]]]]] & ) /@ 
      DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]; Association[fiberCategories]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   "ReducedFiberCategories"] := Module[{objectFunction, objectListWithDuplicates, arrowListWithDuplicates, 
     domainMorphismList, domainCompositions, imageMorphismList, imageCompositions, morphismFunction, 
     domainObjectEquivalenceGraph, domainMorphismEquivalenceGraph, imageQuiverObjectEquivalences, 
     imageObjectEquivalences, imageArrowEquivalences, imageMorphismEquivalences, imageObjectEquivalenceGraph, 
     imageMorphismEquivalenceGraph, reducedFiberCategories}, 
    objectFunction = Join[Association[(#1 -> #1 & ) /@ objects], objectMappings]; 
     objectListWithDuplicates = objects /. Normal[objectMappings]; arrowListWithDuplicates = 
      If[covariant === True, Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], 
       (First[#1] -> Reverse[Last[#1]] & ) /@ (Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings])]; 
     domainMorphismList = Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[domainCompositions = Select[Tuples[domainMorphismList, 2], Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ domainMorphismList, 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], domainMorphismList = 
           Append[domainMorphismList, compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ domainCompositions, Length[objects]]; 
     domainMorphismList = Select[domainMorphismList, Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        domainMorphismList = Append[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ objects; 
     imageMorphismList = Select[arrowListWithDuplicates, First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[imageCompositions = Select[Tuples[imageMorphismList, 2], Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ imageMorphismList, 
            StringDelete[ToString[newCompositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], imageMorphismList = 
           Append[imageMorphismList, newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ imageCompositions, 
      Length[objectListWithDuplicates]]; imageMorphismList = Select[imageMorphismList, 
       Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[imageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        imageMorphismList = Append[imageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      objectListWithDuplicates; morphismFunction = Association[Thread[First /@ domainMorphismList -> 
         First /@ imageMorphismList]]; domainObjectEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Join[quiverObjectEquivalences, 
             categoryObjectEquivalences], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ objects]]; 
     domainMorphismEquivalenceGraph = Graph[Join[EdgeList[TransitiveClosureGraph[
          Graph[Apply[UndirectedEdge, Join[arrowEquivalences, categoryMorphismEquivalences], {1}]]]], 
        (UndirectedEdge[#1, #1] & ) /@ First /@ Normal[Association[DeleteDuplicates[domainMorphismList]]]]]; 
     imageQuiverObjectEquivalences = quiverObjectEquivalences /. Normal[objectMappings]; 
     imageObjectEquivalences = DeleteDuplicates[Join[categoryObjectEquivalences /. Normal[objectMappings], 
        objectEquivalences]]; imageArrowEquivalences = arrowEquivalences /. Normal[arrowMappings]; 
     imageMorphismEquivalences = If[covariant === True, DeleteDuplicates[
        Sort /@ Join[categoryMorphismEquivalences /. compositionSymbol -> newCompositionSymbol /. 
            Normal[arrowMappings] /. Normal[objectMappings], morphismEquivalences]], 
       DeleteDuplicates[Sort /@ Join[categoryMorphismEquivalences /. compositionSymbol -> newCompositionSymbol /. 
             Normal[arrowMappings] /. Normal[objectMappings] /. {newCompositionSymbol[x_, newCompositionSymbol[y_, 
               z_]] :> newCompositionSymbol[z, newCompositionSymbol[y, x]], 
            newCompositionSymbol[newCompositionSymbol[x_, y_], z_] :> newCompositionSymbol[newCompositionSymbol[z, y], 
              x], newCompositionSymbol[x_, y_] :> newCompositionSymbol[y, x]}, morphismEquivalences]]]; 
     imageObjectEquivalenceGraph = Graph[Join[EdgeList[TransitiveClosureGraph[
          Graph[Apply[UndirectedEdge, Join[imageQuiverObjectEquivalences, imageObjectEquivalences], {1}]]]], 
        (UndirectedEdge[#1, #1] & ) /@ DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]]]; 
     imageMorphismEquivalenceGraph = Graph[Join[EdgeList[TransitiveClosureGraph[
          Graph[Apply[UndirectedEdge, Join[imageArrowEquivalences, imageMorphismEquivalences], {1}]]]], 
        (UndirectedEdge[#1, #1] & ) /@ First /@ Normal[Association[DeleteDuplicates[imageMorphismList]]]]]; 
     reducedFiberCategories = {}; (Module[{imageObject = #1, fiberObjects, fiberMorphisms}, 
        fiberObjects = {}; fiberMorphisms = {}; (Module[{domainObject = #1, equivalentObjects}, 
            If[MemberQ[VertexList[domainObjectEquivalenceGraph], domainObject], equivalentObjects = VertexComponent[
                domainObjectEquivalenceGraph, domainObject]; If[MemberQ[VertexList[imageObjectEquivalenceGraph], 
                 domainObject /. Normal[objectFunction]] && MemberQ[VertexList[imageObjectEquivalenceGraph], 
                 imageObject], If[Length[FindShortestPath[imageObjectEquivalenceGraph, domainObject /. 
                    Normal[objectFunction], imageObject]] > 0, fiberObjects = Union[fiberObjects, 
                  equivalentObjects]]]]] & ) /@ objects; (Module[{domainMorphism = #1, equivalentMorphisms}, 
            If[MemberQ[VertexList[domainMorphismEquivalenceGraph], domainMorphism], equivalentMorphisms = VertexComponent[
                domainMorphismEquivalenceGraph, domainMorphism]; If[MemberQ[VertexList[imageMorphismEquivalenceGraph], 
                 domainMorphism /. Normal[morphismFunction]] && MemberQ[VertexList[imageMorphismEquivalenceGraph], 
                 newIdentitySymbol[imageObject]], If[Length[FindShortestPath[imageMorphismEquivalenceGraph, 
                   domainMorphism /. Normal[morphismFunction], newIdentitySymbol[imageObject]]] > 0, fiberMorphisms = 
                 Union[fiberMorphisms, Select[Normal[Association[DeleteDuplicates[domainMorphismList]]], 
                   MemberQ[equivalentMorphisms, First[#1]] & ]]]]]] & ) /@ 
          First /@ Normal[Association[DeleteDuplicates[domainMorphismList]]]; reducedFiberCategories = 
          Append[reducedFiberCategories, imageObject -> ResourceFunction["AbstractCategory"][
             Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
              "MorphismEquivalences" -> categoryMorphismEquivalences, "ObjectEquivalences" -> categoryObjectEquivalences, 
              "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> arrowEquivalences, 
                 "Arrows" -> Association[DeleteDuplicates[fiberMorphisms]], "ObjectEquivalences" -> 
                  quiverObjectEquivalences, "Objects" -> fiberObjects]]]]]] & ) /@ 
      reduceObjects[reduceObjects[DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]], 
        quiverObjectEquivalences /. Normal[objectMappings]], DeleteDuplicates[
        Join[categoryObjectEquivalences /. Normal[objectMappings], objectEquivalences]]]; 
     Association[reducedFiberCategories]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   "DiscreteFibrationQ"] := Module[{domainMorphismAssociation, domainCompositions, imageObjects, imageArrows, 
     imageQuiverObjectEquivalences, imageObjectEquivalences, imageArrowEquivalences, imageMorphismEquivalences, 
     imageMorphismAssociation, imageCompositions, objectFunction, objectListWithDuplicates, arrowListWithDuplicates, 
     domainMorphismList, domainCompositionsList, imageMorphismList, imageCompositionsList, morphismFunction, 
     isDiscreteFibration}, domainMorphismAssociation = 
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
     imageObjects = DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]; 
     imageArrows = Association[DeleteDuplicates[Join[Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], 
         If[covariant === True, Normal[newArrows], (First[#1] -> Reverse[Last[#1]] & ) /@ Normal[newArrows]]]]]; 
     imageQuiverObjectEquivalences = quiverObjectEquivalences /. Normal[objectMappings]; 
     imageObjectEquivalences = DeleteDuplicates[Join[categoryObjectEquivalences /. Normal[objectMappings], 
        objectEquivalences]]; imageArrowEquivalences = arrowEquivalences /. Normal[arrowMappings]; 
     imageMorphismEquivalences = DeleteDuplicates[
       Join[categoryMorphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[arrowMappings] /. 
         Normal[objectMappings], If[covariant === True, morphismEquivalences, morphismEquivalences /. 
          {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> newCompositionSymbol[z, newCompositionSymbol[y, x]], 
           newCompositionSymbol[newCompositionSymbol[x_, y_], z_] :> newCompositionSymbol[newCompositionSymbol[z, y], x], 
           newCompositionSymbol[x_, y_] :> newCompositionSymbol[y, x]}]]]; imageMorphismAssociation = 
      Association[Select[Normal[Association[Normal[reduceArrowsFinal[reduceArrowsInitial[imageArrows, 
             imageArrowEquivalences], imageQuiverObjectEquivalences]]]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[imageCompositions = Select[Tuples[Normal[imageMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[imageMorphismAssociation], StringDelete[ToString[newCompositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], 
             newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ imageCompositions, Length[reduceObjects[imageObjects, 
        imageQuiverObjectEquivalences]]]; imageMorphismAssociation = 
      Association[Select[Normal[imageMorphismAssociation], 
        Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[imageMorphismAssociation], newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], newIdentitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[imageObjects, imageQuiverObjectEquivalences]; 
     objectFunction = Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, 
               quiverObjectEquivalences], categoryObjectEquivalences]]] -> reduceObjectsWithDuplicates[
           Values[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
               categoryObjectEquivalences]]], objectEquivalences]]], 
       Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[objectMappings], 
            quiverObjectEquivalences], categoryObjectEquivalences] -> reduceObjectsWithDuplicates[Values[objectMappings], 
           objectEquivalences]]]]; objectListWithDuplicates = objects /. Normal[objectMappings]; 
     arrowListWithDuplicates = Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings]; 
     domainMorphismList = Select[reduceArrowsFinalWithDuplicates[reduceArrowsInitialWithDuplicates[Normal[arrows], 
         arrowEquivalences], quiverObjectEquivalences], First[Last[#1]] =!= Last[Last[#1]] & ]; 
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
      reduceArrowsFinalWithDuplicates[reduceArrowsInitialWithDuplicates[domainMorphismList, 
        categoryMorphismEquivalences], categoryObjectEquivalences]; imageMorphismList = 
      Select[reduceArrowsFinalWithDuplicates[reduceArrowsInitialWithDuplicates[arrowListWithDuplicates, 
         arrowEquivalences /. Normal[arrowMappings]], quiverObjectEquivalences /. Normal[objectMappings]], 
       First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[imageCompositionsList = Select[Tuples[imageMorphismList, 2], Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ imageMorphismList, 
            StringDelete[ToString[newCompositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], imageMorphismList = 
           Append[imageMorphismList, newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ imageCompositionsList, 
      Length[reduceObjectsWithDuplicates[objectListWithDuplicates, quiverObjectEquivalences /. Normal[objectMappings]]]]; 
     imageMorphismList = Select[imageMorphismList, Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[imageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        imageMorphismList = Append[imageMorphismList, newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      reduceObjectsWithDuplicates[objectListWithDuplicates, quiverObjectEquivalences /. Normal[objectMappings]]; 
     imageMorphismList = reduceArrowsFinalWithDuplicates[reduceArrowsInitialWithDuplicates[imageMorphismList, 
        DeleteDuplicates[Join[categoryMorphismEquivalences /. compositionSymbol -> newCompositionSymbol /. 
            Normal[arrowMappings] /. Normal[objectMappings], If[covariant === True, morphismEquivalences, 
           morphismEquivalences /. {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> newCompositionSymbol[z, 
               newCompositionSymbol[y, x]], newCompositionSymbol[newCompositionSymbol[x_, y_], z_] :> 
              newCompositionSymbol[newCompositionSymbol[z, y], x], newCompositionSymbol[x_, y_] :> 
              newCompositionSymbol[y, x]}]]]], DeleteDuplicates[Join[categoryObjectEquivalences /. 
          Normal[objectMappings], objectEquivalences]]]; morphismFunction = 
      Association[Thread[First /@ domainMorphismList -> First /@ imageMorphismList]]; isDiscreteFibration = True; 
     (Module[{object = #1, morphisms}, morphisms = Select[Normal[reduceArrowsFinal[reduceArrowsInitial[
              imageMorphismAssociation, imageMorphismEquivalences], imageObjectEquivalences]], 
           Last[Last[#1]] === (object /. Normal[objectFunction]) & ]; 
         (Module[{morphism = #1}, If[Length[Select[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[
                    domainMorphismAssociation, categoryMorphismEquivalences], categoryObjectEquivalences]], 
                 Last[Last[#1]] === object & ], (First[#1] /. Normal[morphismFunction]) === First[morphism] & ]] != 1, 
             isDiscreteFibration = False]] & ) /@ morphisms] & ) /@ 
      reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences]; 
     isDiscreteFibration] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   "InclusionFunctorQ"] := Module[{domainMorphismAssociation, domainCompositions, imageObjects, imageArrows, 
     imageQuiverObjectEquivalences, imageObjectEquivalences, imageArrowEquivalences, imageMorphismEquivalences, 
     imageMorphismAssociation, imageCompositions}, 
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
     imageObjects = DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]; 
     imageArrows = Association[DeleteDuplicates[Join[Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], 
         If[covariant === True, Normal[newArrows], (First[#1] -> Reverse[Last[#1]] & ) /@ Normal[newArrows]]]]]; 
     imageQuiverObjectEquivalences = quiverObjectEquivalences /. Normal[objectMappings]; 
     imageObjectEquivalences = DeleteDuplicates[Join[categoryObjectEquivalences /. Normal[objectMappings], 
        objectEquivalences]]; imageArrowEquivalences = arrowEquivalences /. Normal[arrowMappings]; 
     imageMorphismEquivalences = DeleteDuplicates[
       Join[categoryMorphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[arrowMappings] /. 
         Normal[objectMappings], If[covariant === True, morphismEquivalences, morphismEquivalences /. 
          {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> newCompositionSymbol[z, newCompositionSymbol[y, x]], 
           newCompositionSymbol[newCompositionSymbol[x_, y_], z_] :> newCompositionSymbol[newCompositionSymbol[z, y], x], 
           newCompositionSymbol[x_, y_] :> newCompositionSymbol[y, x]}]]]; imageMorphismAssociation = 
      Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[imageArrows, imageArrowEquivalences], 
          imageQuiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[imageCompositions = Select[Tuples[Normal[imageMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[imageMorphismAssociation], StringDelete[ToString[newCompositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], 
             newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ imageCompositions, Length[reduceObjects[imageObjects, 
        imageQuiverObjectEquivalences]]]; imageMorphismAssociation = 
      Association[Select[Normal[imageMorphismAssociation], 
        Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[imageMorphismAssociation], newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], newIdentitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[imageObjects, imageQuiverObjectEquivalences]; 
     SubsetQ[reduceObjects[reduceObjects[imageObjects, imageQuiverObjectEquivalences], imageObjectEquivalences], 
       reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences]] && 
      SubsetQ[Normal[reduceArrowsFinal[reduceArrowsInitial[imageMorphismAssociation, imageMorphismEquivalences], 
         imageObjectEquivalences]], Normal[reduceArrowsFinal[reduceArrowsInitial[domainMorphismAssociation, 
          categoryMorphismEquivalences], categoryObjectEquivalences]]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   "FullInclusionFunctorQ"] := Module[{domainMorphismAssociation, domainCompositions, imageObjects, imageArrows, 
     imageQuiverObjectEquivalences, imageObjectEquivalences, imageArrowEquivalences, imageMorphismEquivalences, 
     imageMorphismAssociation, imageCompositions, reducedObjectMappings, objectPairs, isFullFunctor}, 
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
     domainMorphismAssociation = reduceArrowsFinal[reduceArrowsInitial[domainMorphismAssociation, 
        categoryMorphismEquivalences], categoryObjectEquivalences]; 
     imageObjects = DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]; 
     imageArrows = Association[DeleteDuplicates[Join[Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], 
         If[covariant === True, Normal[newArrows], (First[#1] -> Reverse[Last[#1]] & ) /@ Normal[newArrows]]]]]; 
     imageQuiverObjectEquivalences = quiverObjectEquivalences /. Normal[objectMappings]; 
     imageObjectEquivalences = DeleteDuplicates[Join[categoryObjectEquivalences /. Normal[objectMappings], 
        objectEquivalences]]; imageArrowEquivalences = arrowEquivalences /. Normal[arrowMappings]; 
     imageMorphismEquivalences = DeleteDuplicates[
       Join[categoryMorphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[arrowMappings] /. 
         Normal[objectMappings], If[covariant === True, morphismEquivalences, morphismEquivalences /. 
          {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> newCompositionSymbol[z, newCompositionSymbol[y, x]], 
           newCompositionSymbol[newCompositionSymbol[x_, y_], z_] :> newCompositionSymbol[newCompositionSymbol[z, y], x], 
           newCompositionSymbol[x_, y_] :> newCompositionSymbol[y, x]}]]]; imageMorphismAssociation = 
      Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[imageArrows, imageArrowEquivalences], 
          imageQuiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[imageCompositions = Select[Tuples[Normal[imageMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[imageMorphismAssociation], StringDelete[ToString[newCompositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], 
             newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ imageCompositions, Length[reduceObjects[imageObjects, 
        imageQuiverObjectEquivalences]]]; imageMorphismAssociation = 
      Association[Select[Normal[imageMorphismAssociation], 
        Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[imageMorphismAssociation], newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], newIdentitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[imageObjects, imageQuiverObjectEquivalences]; 
     imageMorphismAssociation = reduceArrowsFinal[reduceArrowsInitial[imageMorphismAssociation, 
        imageMorphismEquivalences], imageObjectEquivalences]; reducedObjectMappings = 
      Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, 
               quiverObjectEquivalences], categoryObjectEquivalences]]] -> reduceObjectsWithDuplicates[
           Values[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
               categoryObjectEquivalences]]], objectEquivalences]]], 
       Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[objectMappings], 
            quiverObjectEquivalences], categoryObjectEquivalences] -> reduceObjectsWithDuplicates[Values[objectMappings], 
           objectEquivalences]]]]; objectPairs = Tuples[reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
        categoryObjectEquivalences], 2]; isFullFunctor = True; 
     (Module[{objectPair = #1}, If[Length[Select[Normal[domainMorphismAssociation], 
            First[Last[#1]] === First[objectPair] && Last[Last[#1]] === Last[objectPair] & ]] < 
          Length[Select[Normal[imageMorphismAssociation], First[Last[#1]] === (First[objectPair] /. 
                Normal[reducedObjectMappings]) && Last[Last[#1]] === (Last[objectPair] /. 
                Normal[reducedObjectMappings]) & ]], isFullFunctor = False]] & ) /@ objectPairs; 
     isFullFunctor && (SubsetQ[reduceObjects[reduceObjects[imageObjects, imageQuiverObjectEquivalences], 
         imageObjectEquivalences], reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
         imageObjectEquivalences]] && SubsetQ[Normal[imageMorphismAssociation], Normal[domainMorphismAssociation]])] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   "EmbeddingFunctorQ"] := Module[{objectFunction, domainObjectEquivalenceGraph, imageObjectEquivalenceGraph, 
     objectPairs, isInjectiveOnObjects, domainMorphismAssociation, domainCompositions, imageObjects, imageArrows, 
     imageQuiverObjectEquivalences, imageObjectEquivalences, imageArrowEquivalences, imageMorphismEquivalences, 
     imageMorphismAssociation, imageCompositions, reducedObjectMappings, newObjectPairs, isFaithfulFunctor}, 
    objectFunction = Join[Association[(#1 -> #1 & ) /@ objects], objectMappings]; 
     domainObjectEquivalenceGraph = Graph[Join[EdgeList[TransitiveClosureGraph[
          Graph[Apply[UndirectedEdge, Join[quiverObjectEquivalences, categoryObjectEquivalences], {1}]]]], 
        (UndirectedEdge[#1, #1] & ) /@ objects]]; imageObjectEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Join[quiverObjectEquivalences /. 
              Normal[objectMappings], DeleteDuplicates[Join[categoryObjectEquivalences /. Normal[objectMappings], 
               objectEquivalences]]], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ DeleteDuplicates[
          Join[objects /. Normal[objectMappings], newObjects]]]]; 
     objectPairs = Tuples[DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]], 2]; 
     isInjectiveOnObjects = True; 
     (Module[{objectPair = #1}, If[MemberQ[VertexList[imageObjectEquivalenceGraph], First[objectPair]] && 
          MemberQ[VertexList[imageObjectEquivalenceGraph], Last[objectPair]], 
         If[Length[FindShortestPath[imageObjectEquivalenceGraph, First[objectPair], Last[objectPair]]] > 0, 
          If[MemberQ[VertexList[domainObjectEquivalenceGraph], First[objectPair] /. Reverse /@ Normal[objectFunction]] && 
            MemberQ[VertexList[domainObjectEquivalenceGraph], Last[objectPair] /. Reverse /@ Normal[objectFunction]], 
           If[Length[FindShortestPath[domainObjectEquivalenceGraph, First[objectPair] /. Reverse /@ 
                 Normal[objectFunction], Last[objectPair] /. Reverse /@ Normal[objectFunction]]] == 0, 
            isInjectiveOnObjects = False]]]]] & ) /@ objectPairs; domainMorphismAssociation = 
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
     domainMorphismAssociation = reduceArrowsFinal[reduceArrowsInitial[domainMorphismAssociation, 
        categoryMorphismEquivalences], categoryObjectEquivalences]; 
     imageObjects = DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]; 
     imageArrows = Association[DeleteDuplicates[Join[Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], 
         If[covariant === True, Normal[newArrows], (First[#1] -> Reverse[Last[#1]] & ) /@ Normal[newArrows]]]]]; 
     imageQuiverObjectEquivalences = quiverObjectEquivalences /. Normal[objectMappings]; 
     imageObjectEquivalences = DeleteDuplicates[Join[categoryObjectEquivalences /. Normal[objectMappings], 
        objectEquivalences]]; imageArrowEquivalences = arrowEquivalences /. Normal[arrowMappings]; 
     imageMorphismEquivalences = DeleteDuplicates[
       Join[categoryMorphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[arrowMappings] /. 
         Normal[objectMappings], If[covariant === True, morphismEquivalences, morphismEquivalences /. 
          {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> newCompositionSymbol[z, newCompositionSymbol[y, z]], 
           newCompositionSymbol[newCompositionSymbol[x_, y_], z_] :> newCompositionSymbol[newCompositionSymbol[z, y], x], 
           newCompositionSymbol[x_, y_] :> newCompositionSymbol[y, x]}]]]; imageMorphismAssociation = 
      Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[imageArrows, imageArrowEquivalences], 
          imageQuiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[imageCompositions = Select[Tuples[Normal[imageMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[imageMorphismAssociation], StringDelete[ToString[newCompositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], 
             newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ imageCompositions, Length[reduceObjects[imageObjects, 
        imageQuiverObjectEquivalences]]]; imageMorphismAssociation = 
      Association[Select[Normal[imageMorphismAssociation], 
        Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[imageMorphismAssociation], newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], newIdentitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[imageObjects, imageQuiverObjectEquivalences]; 
     imageMorphismAssociation = reduceArrowsFinal[reduceArrowsInitial[imageMorphismAssociation, 
        imageMorphismEquivalences], imageObjectEquivalences]; reducedObjectMappings = 
      Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, 
               quiverObjectEquivalences], categoryObjectEquivalences]]] -> reduceObjectsWithDuplicates[
           Values[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
               categoryObjectEquivalences]]], objectEquivalences]]], 
       Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[objectMappings], 
            quiverObjectEquivalences], categoryObjectEquivalences] -> reduceObjectsWithDuplicates[Values[objectMappings], 
           objectEquivalences]]]]; newObjectPairs = Tuples[reduceObjects[reduceObjects[objects, 
         quiverObjectEquivalences], categoryObjectEquivalences], 2]; isFaithfulFunctor = True; 
     (Module[{objectPair = #1}, If[Length[Select[Normal[domainMorphismAssociation], 
            First[Last[#1]] === First[objectPair] && Last[Last[#1]] === Last[objectPair] & ]] > 
          Length[Select[Normal[imageMorphismAssociation], First[Last[#1]] === (First[objectPair] /. 
                Normal[reducedObjectMappings]) && Last[Last[#1]] === (Last[objectPair] /. 
                Normal[reducedObjectMappings]) & ]], isFaithfulFunctor = False]] & ) /@ newObjectPairs; 
     isInjectiveOnObjects && isFaithfulFunctor] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   "FullEmbeddingFunctorQ"] := Module[{objectFunction, domainObjectEquivalenceGraph, imageObjectEquivalenceGraph, 
     objectPairs, isInjectiveOnObjects, domainMorphismAssociation, domainCompositions, imageObjects, imageArrows, 
     imageQuiverObjectEquivalences, imageObjectEquivalences, imageArrowEquivalences, imageMorphismEquivalences, 
     imageMorphismAssociation, imageCompositions, reducedObjectMappings, newObjectPairs, isFullyFaithfulFunctor}, 
    objectFunction = Join[Association[(#1 -> #1 & ) /@ objects], objectMappings]; 
     domainObjectEquivalenceGraph = Graph[Join[EdgeList[TransitiveClosureGraph[
          Graph[Apply[UndirectedEdge, Join[quiverObjectEquivalences, categoryObjectEquivalences], {1}]]]], 
        (UndirectedEdge[#1, #1] & ) /@ objects]]; imageObjectEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, Join[quiverObjectEquivalences /. 
              Normal[objectMappings], DeleteDuplicates[Join[categoryObjectEquivalences /. Normal[objectMappings], 
               objectEquivalences]]], {1}]]]], (UndirectedEdge[#1, #1] & ) /@ DeleteDuplicates[
          Join[objects /. Normal[objectMappings], newObjects]]]]; 
     objectPairs = Tuples[DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]], 2]; 
     isInjectiveOnObjects = True; 
     (Module[{objectPair = #1}, If[MemberQ[VertexList[imageObjectEquivalenceGraph], First[objectPair]] && 
          MemberQ[VertexList[imageObjectEquivalenceGraph], Last[objectPair]], 
         If[Length[FindShortestPath[imageObjectEquivalenceGraph, First[objectPair], Last[objectPair]]] > 0, 
          If[MemberQ[VertexList[domainObjectEquivalenceGraph], First[objectPair] /. Reverse /@ Normal[objectFunction]] && 
            MemberQ[VertexList[domainObjectEquivalenceGraph], Last[objectPair] /. Reverse /@ Normal[objectFunction]], 
           If[Length[FindShortestPath[domainObjectEquivalenceGraph, First[objectPair] /. Reverse /@ 
                 Normal[objectFunction], Last[objectPair] /. Reverse /@ Normal[objectFunction]]] == 0, 
            isInjectiveOnObjects = False]]]]] & ) /@ objectPairs; domainMorphismAssociation = 
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
     domainMorphismAssociation = reduceArrowsFinal[reduceArrowsInitial[domainMorphismAssociation, 
        categoryMorphismEquivalences], categoryObjectEquivalences]; 
     imageObjects = DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]; 
     imageArrows = Association[DeleteDuplicates[Join[Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], 
         If[covariant === True, Normal[newArrows], (First[#1] -> Reverse[Last[#1]] & ) /@ Normal[newArrows]]]]]; 
     imageQuiverObjectEquivalences = quiverObjectEquivalences /. Normal[objectMappings]; 
     imageObjectEquivalences = DeleteDuplicates[Join[categoryObjectEquivalences /. Normal[objectMappings], 
        objectEquivalences]]; imageArrowEquivalences = arrowEquivalences /. Normal[arrowMappings]; 
     imageMorphismEquivalences = DeleteDuplicates[
       Join[categoryMorphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[arrowMappings] /. 
         Normal[objectMappings], If[covariant === True, morphismEquivalences, morphismEquivalences /. 
          {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> newCompositionSymbol[z, newCompositionSymbol[y, x]], 
           newCompositionSymbol[newCompositionSymbol[x_, y_], z_] :> newCompositionSymbol[newCompositionSymbol[z, y], x], 
           newCompositionSymbol[x_, y_] :> newCompositionSymbol[y, x]}]]]; imageMorphismAssociation = 
      Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[imageArrows, imageArrowEquivalences], 
          imageQuiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[imageCompositions = Select[Tuples[Normal[imageMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[imageMorphismAssociation], StringDelete[ToString[newCompositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], 
             newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ imageCompositions, Length[reduceObjects[imageObjects, 
        imageQuiverObjectEquivalences]]]; imageMorphismAssociation = 
      Association[Select[Normal[imageMorphismAssociation], 
        Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[imageMorphismAssociation], newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], newIdentitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[imageObjects, imageQuiverObjectEquivalences]; 
     imageMorphismAssociation = reduceArrowsFinal[reduceArrowsInitial[imageMorphismAssociation, 
        imageMorphismEquivalences], imageObjectEquivalences]; reducedObjectMappings = 
      Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, 
               quiverObjectEquivalences], categoryObjectEquivalences]]] -> reduceObjectsWithDuplicates[
           Values[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
               categoryObjectEquivalences]]], objectEquivalences]]], 
       Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[objectMappings], 
            quiverObjectEquivalences], categoryObjectEquivalences] -> reduceObjectsWithDuplicates[Values[objectMappings], 
           objectEquivalences]]]]; newObjectPairs = Tuples[reduceObjects[reduceObjects[objects, 
         quiverObjectEquivalences], categoryObjectEquivalences], 2]; isFullyFaithfulFunctor = True; 
     (Module[{objectPair = #1}, If[Length[Select[Normal[domainMorphismAssociation], 
            First[Last[#1]] === First[objectPair] && Last[Last[#1]] === Last[objectPair] & ]] != 
          Length[Select[Normal[imageMorphismAssociation], First[Last[#1]] === (First[objectPair] /. 
                Normal[reducedObjectMappings]) && Last[Last[#1]] === (Last[objectPair] /. 
                Normal[reducedObjectMappings]) & ]], isFullyFaithfulFunctor = False]] & ) /@ newObjectPairs; 
     isInjectiveOnObjects && isFullyFaithfulFunctor] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]]["SwapVariance"] := 
  AbstractFunctor[Association["ArrowMappings" -> arrowMappings, "Category" -> ResourceFunction["AbstractCategory"][
       Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
        "MorphismEquivalences" -> categoryMorphismEquivalences, "ObjectEquivalences" -> categoryObjectEquivalences, 
        "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> arrowEquivalences, 
           "Arrows" -> arrows, "ObjectEquivalences" -> quiverObjectEquivalences, "Objects" -> objects]]]], 
     "Covariant" -> If[covariant === True, False, True], "MorphismEquivalences" -> 
      (morphismEquivalences /. {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
         newCompositionSymbol[z, newCompositionSymbol[y, x]], newCompositionSymbol[newCompositionSymbol[x_, y_], z_] :> 
         newCompositionSymbol[newCompositionSymbol[z, y], x], newCompositionSymbol[x_, y_] :> 
         newCompositionSymbol[y, x]}), "NewArrows" -> newArrows, "NewCompositionSymbol" -> newCompositionSymbol, 
     "NewIdentitySymbol" -> newIdentitySymbol, "NewObjects" -> newObjects, "ObjectEquivalences" -> objectEquivalences, 
     "ObjectMappings" -> objectMappings]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   "CovariantFunctorQ"] := If[covariant === True, True, False] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   "ContravariantFunctorQ"] := If[covariant === True, False, True] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   "FullLabeledGraph"] := Module[{domainMorphismAssociation, domainCompositions, imageMorphismAssociation, 
     imageCompositions}, domainMorphismAssociation = Association[Select[Normal[arrows], 
        First[Last[#1]] =!= Last[Last[#1]] & ]]; 
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
           identitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ objects; imageMorphismAssociation = 
      Association[Select[Normal[Association[DeleteDuplicates[Join[If[covariant === True, 
             Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], (First[#1] -> Reverse[Last[#1]] & ) /@ 
              (Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings])], Normal[newArrows]]]]], 
        First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[imageCompositions = Select[Tuples[Normal[imageMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[imageMorphismAssociation], StringDelete[ToString[newCompositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], 
             newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ imageCompositions, 
      Length[DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]]]; 
     imageMorphismAssociation = Association[Select[Normal[imageMorphismAssociation], 
        Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[imageMorphismAssociation], newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], newIdentitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]; 
     EdgeTaggedGraph[objects, (Labeled[DirectedEdge @@ Last[#1], Placed[First[#1], 0.5]] & ) /@ 
        Normal[domainMorphismAssociation], VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], 
       VertexLabels -> Placed["Name", Center], VertexLabelStyle -> Directive[Bold, 20], 
       EdgeLabelStyle -> Directive[Bold, 20], EdgeStyle -> Directive[Black, Thick], 
       GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}] -> 
      EdgeTaggedGraph[DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]], 
       (Labeled[DirectedEdge @@ Last[#1], Placed[First[#1], 0.5]] & ) /@ Normal[imageMorphismAssociation], 
       VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], VertexLabels -> Placed["Name", Center], 
       VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
       EdgeStyle -> Directive[Black, Thick], GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   "FullUnlabeledGraph"] := Module[{domainMorphismAssociation, domainCompositions, imageMorphismAssociation, 
     imageCompositions}, domainMorphismAssociation = Association[Select[Normal[arrows], 
        First[Last[#1]] =!= Last[Last[#1]] & ]]; 
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
           identitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ objects; imageMorphismAssociation = 
      Association[Select[Normal[Association[DeleteDuplicates[Join[If[covariant === True, 
             Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], (First[#1] -> Reverse[Last[#1]] & ) /@ 
              (Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings])], Normal[newArrows]]]]], 
        First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[imageCompositions = Select[Tuples[Normal[imageMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[imageMorphismAssociation], StringDelete[ToString[newCompositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], 
             newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ imageCompositions, 
      Length[DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]]]; 
     imageMorphismAssociation = Association[Select[Normal[imageMorphismAssociation], 
        Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[imageMorphismAssociation], newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], newIdentitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]; 
     EdgeTaggedGraph[objects, (DirectedEdge @@ Last[#1] & ) /@ Normal[domainMorphismAssociation], VertexSize -> 0.3, 
       VertexStyle -> Directive[Transparent, EdgeForm[None]], VertexLabels -> Placed["Name", Center], 
       VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
       EdgeStyle -> Directive[Black, Thick], GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}] -> 
      EdgeTaggedGraph[DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]], 
       (DirectedEdge @@ Last[#1] & ) /@ Normal[imageMorphismAssociation], VertexSize -> 0.3, 
       VertexStyle -> Directive[Transparent, EdgeForm[None]], VertexLabels -> Placed["Name", Center], 
       VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
       EdgeStyle -> Directive[Black, Thick], GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   "ReducedLabeledGraph"] := Module[{domainMorphismAssociation, domainCompositions, imageObjects, imageArrows, 
     imageQuiverObjectEquivalences, imageObjectEquivalences, imageArrowEquivalences, imageMorphismEquivalences, 
     imageMorphismAssociation, imageCompositions}, 
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
     imageObjects = DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]; 
     imageArrows = Association[DeleteDuplicates[Join[Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], 
         Normal[newArrows]]]]; imageQuiverObjectEquivalences = quiverObjectEquivalences /. Normal[objectMappings]; 
     imageObjectEquivalences = DeleteDuplicates[Join[categoryObjectEquivalences /. Normal[objectMappings], 
        objectEquivalences]]; imageArrowEquivalences = arrowEquivalences /. Normal[arrowMappings]; 
     imageMorphismEquivalences = If[covariant === True, DeleteDuplicates[
        Join[categoryMorphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[arrowMappings] /. 
          Normal[objectMappings], morphismEquivalences]], DeleteDuplicates[
        Join[categoryMorphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[arrowMappings] /. 
           Normal[objectMappings] /. {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
            newCompositionSymbol[z, newCompositionSymbol[y, x]], newCompositionSymbol[newCompositionSymbol[x_, y_], 
             z_] :> newCompositionSymbol[newCompositionSymbol[z, y], x], newCompositionSymbol[x_, y_] :> 
            newCompositionSymbol[y, x]}, morphismEquivalences]]]; imageMorphismAssociation = 
      Association[Select[Normal[Association[DeleteDuplicates[Join[If[covariant === True, 
             Normal[reduceArrowsFinal[reduceArrowsInitial[imageArrows, imageArrowEquivalences], 
               imageQuiverObjectEquivalences]], (First[#1] -> Reverse[Last[#1]] & ) /@ Normal[reduceArrowsFinal[
                reduceArrowsInitial[imageArrows, imageArrowEquivalences], imageQuiverObjectEquivalences]]], 
            Normal[newArrows]]]]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[imageCompositions = Select[Tuples[Normal[imageMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[imageMorphismAssociation], StringDelete[ToString[newCompositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], 
             newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ imageCompositions, Length[reduceObjects[imageObjects, 
        imageQuiverObjectEquivalences]]]; imageMorphismAssociation = 
      Association[Select[Normal[imageMorphismAssociation], 
        Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[imageMorphismAssociation], newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], newIdentitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[imageObjects, imageQuiverObjectEquivalences]; 
     EdgeTaggedGraph[reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 
       (Labeled[DirectedEdge @@ Last[#1], Placed[First[#1], 0.5]] & ) /@ 
        Normal[reduceArrowsFinal[reduceArrowsInitial[domainMorphismAssociation, categoryMorphismEquivalences], 
          categoryObjectEquivalences]], VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], 
       VertexLabels -> Placed["Name", Center], VertexLabelStyle -> Directive[Bold, 20], 
       EdgeLabelStyle -> Directive[Bold, 20], EdgeStyle -> Directive[Black, Thick], 
       GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}] -> 
      EdgeTaggedGraph[reduceObjects[reduceObjects[imageObjects, imageQuiverObjectEquivalences], imageObjectEquivalences], 
       (Labeled[DirectedEdge @@ Last[#1], Placed[First[#1], 0.5]] & ) /@ 
        Normal[reduceArrowsFinal[reduceArrowsInitial[imageMorphismAssociation, imageMorphismEquivalences], 
          imageObjectEquivalences]], VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], 
       VertexLabels -> Placed["Name", Center], VertexLabelStyle -> Directive[Bold, 20], 
       EdgeLabelStyle -> Directive[Bold, 20], EdgeStyle -> Directive[Black, Thick], 
       GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   "ReducedUnlabeledGraph"] := Module[{domainMorphismAssociation, domainCompositions, imageObjects, imageArrows, 
     imageQuiverObjectEquivalences, imageObjectEquivalences, imageArrowEquivalences, imageMorphismEquivalences, 
     imageMorphismAssociation, imageCompositions}, 
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
     imageObjects = DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]; 
     imageArrows = Association[DeleteDuplicates[Join[Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], 
         Normal[newArrows]]]]; imageQuiverObjectEquivalences = quiverObjectEquivalences /. Normal[objectMappings]; 
     imageObjectEquivalences = DeleteDuplicates[Join[categoryObjectEquivalences /. Normal[objectMappings], 
        objectEquivalences]]; imageArrowEquivalences = arrowEquivalences /. Normal[arrowMappings]; 
     imageMorphismEquivalences = If[covariant === True, DeleteDuplicates[
        Join[categoryMorphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[arrowMappings] /. 
          Normal[objectMappings], morphismEquivalences]], DeleteDuplicates[
        Join[categoryMorphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[arrowMappings] /. 
           Normal[objectMappings] /. {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
            newCompositionSymbol[z, newCompositionSymbol[y, x]], newCompositionSymbol[newCompositionSymbol[x_, y_], 
             z_] :> newCompositionSymbol[newCompositionSymbol[z, y], x], newCompositionSymbol[x_, y_] :> 
            newCompositionSymbol[y, x]}, morphismEquivalences]]]; imageMorphismAssociation = 
      Association[Select[Normal[Association[DeleteDuplicates[Join[If[covariant === True, 
             Normal[reduceArrowsFinal[reduceArrowsInitial[imageArrows, imageArrowEquivalences], 
               imageQuiverObjectEquivalences]], (First[#1] -> Reverse[Last[#1]] & ) /@ Normal[reduceArrowsFinal[
                reduceArrowsInitial[imageArrows, imageArrowEquivalences], imageQuiverObjectEquivalences]]], 
            Normal[newArrows]]]]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[imageCompositions = Select[Tuples[Normal[imageMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[imageMorphismAssociation], StringDelete[ToString[newCompositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], 
             newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ imageCompositions, Length[reduceObjects[imageObjects, 
        imageQuiverObjectEquivalences]]]; imageMorphismAssociation = 
      Association[Select[Normal[imageMorphismAssociation], 
        Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[imageMorphismAssociation], newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
        imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], newIdentitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[imageObjects, imageQuiverObjectEquivalences]; 
     EdgeTaggedGraph[reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 
       (DirectedEdge @@ Last[#1] & ) /@ Normal[reduceArrowsFinal[reduceArrowsInitial[domainMorphismAssociation, 
           categoryMorphismEquivalences], categoryObjectEquivalences]], VertexSize -> 0.3, 
       VertexStyle -> Directive[Transparent, EdgeForm[None]], VertexLabels -> Placed["Name", Center], 
       VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
       EdgeStyle -> Directive[Black, Thick], GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}] -> 
      EdgeTaggedGraph[reduceObjects[reduceObjects[imageObjects, imageQuiverObjectEquivalences], imageObjectEquivalences], 
       (DirectedEdge @@ Last[#1] & ) /@ Normal[reduceArrowsFinal[reduceArrowsInitial[imageMorphismAssociation, 
           imageMorphismEquivalences], imageObjectEquivalences]], VertexSize -> 0.3, 
       VertexStyle -> Directive[Transparent, EdgeForm[None]], VertexLabels -> Placed["Name", Center], 
       VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
       EdgeStyle -> Directive[Black, Thick], GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   "SimpleLabeledGraph"] := Module[{domainMorphismAssociation, domainCompositions, imageMorphismAssociation, 
     imageCompositions}, domainMorphismAssociation = Association[Select[Normal[arrows], 
        First[Last[#1]] =!= Last[Last[#1]] & ]]; 
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
     imageMorphismAssociation = Association[Select[Normal[Association[DeleteDuplicates[
           Join[If[covariant === True, Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], 
             (First[#1] -> Reverse[Last[#1]] & ) /@ (Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings])], 
            Normal[newArrows]]]]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[imageCompositions = Select[Tuples[Normal[imageMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[imageMorphismAssociation], StringDelete[ToString[newCompositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], 
             newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ imageCompositions, 
      Length[DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]]]; 
     imageMorphismAssociation = Association[Select[Normal[imageMorphismAssociation], 
        Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]]; 
     EdgeTaggedGraph[objects, (Labeled[DirectedEdge @@ Last[#1], Placed[First[#1], 0.5]] & ) /@ 
        Select[DeleteDuplicatesBy[Normal[domainMorphismAssociation], DirectedEdge @@ Last[#1] & ], 
         First[Last[#1]] =!= Last[Last[#1]] & ], VertexSize -> 0.3, VertexStyle -> Directive[Transparent, 
         EdgeForm[None]], VertexLabels -> Placed["Name", Center], VertexLabelStyle -> Directive[Bold, 20], 
       EdgeLabelStyle -> Directive[Bold, 20], EdgeStyle -> Directive[Black, Thick], 
       GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}] -> 
      EdgeTaggedGraph[DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]], 
       (Labeled[DirectedEdge @@ Last[#1], Placed[First[#1], 0.5]] & ) /@ 
        Select[DeleteDuplicatesBy[Normal[imageMorphismAssociation], DirectedEdge @@ Last[#1] & ], 
         First[Last[#1]] =!= Last[Last[#1]] & ], VertexSize -> 0.3, VertexStyle -> Directive[Transparent, 
         EdgeForm[None]], VertexLabels -> Placed["Name", Center], VertexLabelStyle -> Directive[Bold, 20], 
       EdgeLabelStyle -> Directive[Bold, 20], EdgeStyle -> Directive[Black, Thick], 
       GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   "SimpleUnlabeledGraph"] := Module[{domainMorphismAssociation, domainCompositions, imageMorphismAssociation, 
     imageCompositions}, domainMorphismAssociation = Association[Select[Normal[arrows], 
        First[Last[#1]] =!= Last[Last[#1]] & ]]; 
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
     imageMorphismAssociation = Association[Select[Normal[Association[DeleteDuplicates[
           Join[If[covariant === True, Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], 
             (First[#1] -> Reverse[Last[#1]] & ) /@ (Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings])], 
            Normal[newArrows]]]]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[imageCompositions = Select[Tuples[Normal[imageMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[imageMorphismAssociation], StringDelete[ToString[newCompositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], 
             newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ imageCompositions, 
      Length[DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]]]; 
     imageMorphismAssociation = Association[Select[Normal[imageMorphismAssociation], 
        Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]]; 
     EdgeTaggedGraph[objects, (DirectedEdge @@ Last[#1] & ) /@ 
        Select[DeleteDuplicatesBy[Normal[domainMorphismAssociation], DirectedEdge @@ Last[#1] & ], 
         First[Last[#1]] =!= Last[Last[#1]] & ], VertexSize -> 0.3, VertexStyle -> Directive[Transparent, 
         EdgeForm[None]], VertexLabels -> Placed["Name", Center], VertexLabelStyle -> Directive[Bold, 20], 
       EdgeLabelStyle -> Directive[Bold, 20], EdgeStyle -> Directive[Black, Thick], 
       GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}] -> 
      EdgeTaggedGraph[DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]], 
       (DirectedEdge @@ Last[#1] & ) /@ Select[DeleteDuplicatesBy[Normal[imageMorphismAssociation], 
          DirectedEdge @@ Last[#1] & ], First[Last[#1]] =!= Last[Last[#1]] & ], VertexSize -> 0.3, 
       VertexStyle -> Directive[Transparent, EdgeForm[None]], VertexLabels -> Placed["Name", Center], 
       VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
       EdgeStyle -> Directive[Black, Thick], GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   "ReducedSimpleLabeledGraph"] := Module[{domainMorphismAssociation, domainCompositions, imageObjects, imageArrows, 
     imageQuiverObjectEquivalences, imageObjectEquivalences, imageArrowEquivalences, imageMorphismEquivalences, 
     imageMorphismAssociation, imageCompositions}, 
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
     imageObjects = DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]; 
     imageArrows = Association[DeleteDuplicates[Join[Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], 
         Normal[newArrows]]]]; imageQuiverObjectEquivalences = quiverObjectEquivalences /. Normal[objectMappings]; 
     imageObjectEquivalences = DeleteDuplicates[Join[categoryObjectEquivalences /. Normal[objectMappings], 
        objectEquivalences]]; imageArrowEquivalences = arrowEquivalences /. Normal[arrowMappings]; 
     imageMorphismEquivalences = If[covariant === True, DeleteDuplicates[
        Join[categoryMorphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[arrowMappings] /. 
          Normal[objectMappings], morphismEquivalences]], DeleteDuplicates[
        Join[categoryMorphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[arrowMappings] /. 
           Normal[objectMappings] /. {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
            newCompositionSymbol[z, newCompositionSymbol[y, x]], newCompositionSymbol[newCompositionSymbol[x_, y_], 
             z_] :> newCompositionSymbol[newCompositionSymbol[z, y], x], newCompositionSymbol[x_, y_] :> 
            newCompositionSymbol[y, x]}, morphismEquivalences]]]; imageMorphismAssociation = 
      Association[Select[Normal[Association[DeleteDuplicates[Join[If[covariant === True, 
             Normal[reduceArrowsFinal[reduceArrowsInitial[imageArrows, imageArrowEquivalences], 
               imageQuiverObjectEquivalences]], (First[#1] -> Reverse[Last[#1]] & ) /@ Normal[reduceArrowsFinal[
                reduceArrowsInitial[imageArrows, imageArrowEquivalences], imageQuiverObjectEquivalences]]], 
            Normal[newArrows]]]]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[imageCompositions = Select[Tuples[Normal[imageMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[imageMorphismAssociation], StringDelete[ToString[newCompositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], 
             newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ imageCompositions, Length[reduceObjects[imageObjects, 
        imageQuiverObjectEquivalences]]]; imageMorphismAssociation = 
      Association[Select[Normal[imageMorphismAssociation], 
        Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]]; 
     EdgeTaggedGraph[reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 
       (Labeled[DirectedEdge @@ Last[#1], Placed[First[#1], 0.5]] & ) /@ 
        Normal[reduceArrowsFinal[reduceArrowsInitial[Association[Select[DeleteDuplicatesBy[
              Normal[domainMorphismAssociation], DirectedEdge @@ Last[#1] & ], First[Last[#1]] =!= Last[Last[#1]] & ]], 
           categoryMorphismEquivalences], categoryObjectEquivalences]], VertexSize -> 0.3, 
       VertexStyle -> Directive[Transparent, EdgeForm[None]], VertexLabels -> Placed["Name", Center], 
       VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
       EdgeStyle -> Directive[Black, Thick], GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}] -> 
      EdgeTaggedGraph[reduceObjects[reduceObjects[imageObjects, imageQuiverObjectEquivalences], imageObjectEquivalences], 
       (Labeled[DirectedEdge @@ Last[#1], Placed[First[#1], 0.5]] & ) /@ 
        Normal[reduceArrowsFinal[reduceArrowsInitial[Association[Select[DeleteDuplicatesBy[
              Normal[imageMorphismAssociation], DirectedEdge @@ Last[#1] & ], First[Last[#1]] =!= Last[Last[#1]] & ]], 
           imageMorphismEquivalences], imageObjectEquivalences]], VertexSize -> 0.3, 
       VertexStyle -> Directive[Transparent, EdgeForm[None]], VertexLabels -> Placed["Name", Center], 
       VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
       EdgeStyle -> Directive[Black, Thick], GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   "ReducedSimpleUnlabeledGraph"] := Module[{domainMorphismAssociation, domainCompositions, imageObjects, imageArrows, 
     imageQuiverObjectEquivalences, imageObjectEquivalences, imageArrowEquivalences, imageMorphismEquivalences, 
     imageMorphismAssociation, imageCompositions}, 
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
     imageObjects = DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]; 
     imageArrows = Association[DeleteDuplicates[Join[Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], 
         Normal[newArrows]]]]; imageQuiverObjectEquivalences = quiverObjectEquivalences /. Normal[objectMappings]; 
     imageObjectEquivalences = DeleteDuplicates[Join[categoryObjectEquivalences /. Normal[objectMappings], 
        objectEquivalences]]; imageArrowEquivalences = arrowEquivalences /. Normal[arrowMappings]; 
     imageMorphismEquivalences = If[covariant === True, DeleteDuplicates[
        Join[categoryMorphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[arrowMappings] /. 
          Normal[objectMappings], morphismEquivalences]], DeleteDuplicates[
        Join[categoryMorphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[arrowMappings] /. 
           Normal[objectMappings] /. {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
            newCompositionSymbol[z, newCompositionSymbol[y, x]], newCompositionSymbol[newCompositionSymbol[x_, y_], 
             z_] :> newCompositionSymbol[newCompositionSymbol[z, y], x], newCompositionSymbol[x_, y_] :> 
            newCompositionSymbol[y, x]}, morphismEquivalences]]]; imageMorphismAssociation = 
      Association[Select[Normal[Association[DeleteDuplicates[Join[If[covariant === True, 
             Normal[reduceArrowsFinal[reduceArrowsInitial[imageArrows, imageArrowEquivalences], 
               imageQuiverObjectEquivalences]], (First[#1] -> Reverse[Last[#1]] & ) /@ Normal[reduceArrowsFinal[
                reduceArrowsInitial[imageArrows, imageArrowEquivalences], imageQuiverObjectEquivalences]]], 
            Normal[newArrows]]]]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[imageCompositions = Select[Tuples[Normal[imageMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[imageMorphismAssociation], StringDelete[ToString[newCompositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], 
             newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ imageCompositions, Length[reduceObjects[imageObjects, 
        imageQuiverObjectEquivalences]]]; imageMorphismAssociation = 
      Association[Select[Normal[imageMorphismAssociation], 
        Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]]; 
     EdgeTaggedGraph[reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 
       (DirectedEdge @@ Last[#1] & ) /@ Normal[reduceArrowsFinal[reduceArrowsInitial[
           Association[Select[DeleteDuplicatesBy[Normal[domainMorphismAssociation], DirectedEdge @@ Last[#1] & ], 
             First[Last[#1]] =!= Last[Last[#1]] & ]], categoryMorphismEquivalences], categoryObjectEquivalences]], 
       VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], VertexLabels -> Placed["Name", Center], 
       VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
       EdgeStyle -> Directive[Black, Thick], GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}] -> 
      EdgeTaggedGraph[reduceObjects[reduceObjects[imageObjects, imageQuiverObjectEquivalences], imageObjectEquivalences], 
       (DirectedEdge @@ Last[#1] & ) /@ Normal[reduceArrowsFinal[reduceArrowsInitial[
           Association[Select[DeleteDuplicatesBy[Normal[imageMorphismAssociation], DirectedEdge @@ Last[#1] & ], 
             First[Last[#1]] =!= Last[Last[#1]] & ]], imageMorphismEquivalences], imageObjectEquivalences]], 
       VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], VertexLabels -> Placed["Name", Center], 
       VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
       EdgeStyle -> Directive[Black, Thick], GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   "AssociationForm"] := Association["Covariant" -> covariant, 
    "Category" -> ResourceFunction["AbstractCategory"][Association["CompositionSymbol" -> compositionSymbol, 
       "IdentitySymbol" -> identitySymbol, "MorphismEquivalences" -> categoryMorphismEquivalences, 
       "ObjectEquivalences" -> categoryObjectEquivalences, "Quiver" -> ResourceFunction["AbstractQuiver"][
         Association["ArrowEquivalences" -> arrowEquivalences, "Arrows" -> arrows, "ObjectEquivalences" -> 
           quiverObjectEquivalences, "Objects" -> objects]]]], "ObjectMappings" -> objectMappings, 
    "ArrowMappings" -> arrowMappings, "NewObjects" -> newObjects, "NewArrows" -> newArrows, 
    "NewCompositionSymbol" -> newCompositionSymbol, "NewIdentitySymbol" -> newIdentitySymbol, 
    "ObjectEquivalences" -> objectEquivalences, "MorphismEquivalences" -> morphismEquivalences] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]]["Properties"] := 
  {"ObjectCount", "MorphismCount", "ObjectEquivalences", "ObjectEquivalenceCount", "MorphismEquivalences", 
    "MorphismEquivalenceCount", "ReducedObjectCount", "ReducedMorphismCount", "CompositionSymbol", "IdentitySymbol", 
    "NewObjects", "NewObjectCount", "ReducedNewObjects", "ReducedNewObjectCount", "NewArrows", "NewArrowCount", 
    "NewMorphisms", "NewMorphismCount", "ReducedNewMorphisms", "ReducedNewMorphismCount", "ObjectMappings", 
    "ObjectMappingCount", "ReducedObjectMappings", "ReducedObjectMappingCount", "ArrowMappings", "ArrowMappingCount", 
    "MorphismMappings", "MorphismMappingCount", "ReducedMorphismMappings", "ReducedMorphismMappingCount", 
    "DomainCategory", "CodomainCategory", "EndofunctorQ", "IdentityFunctorQ", "ConstantFunctorQ", "FullFunctorQ", 
    "FaithfulFunctorQ", "FullyFaithfulFunctorQ", "InjectiveOnObjectsQ", "EssentiallyInjectiveFunctorQ", 
    "SurjectiveOnObjectsQ", "EssentiallySurjectiveFunctorQ", "BijectiveOnObjectsQ", "EssentiallyBijectiveFunctorQ", 
    "ConservativeFunctorQ", "EquivalenceFunctorQ", "FiberCategories", "ReducedFiberCategories", "DiscreteFibrationQ", 
    "InclusionFunctorQ", "FullInclusionFunctorQ", "EmbeddingFunctorQ", "FullEmbeddingFunctorQ", "SwapVariance", 
    "CovariantFunctorQ", "ContravariantFunctorQ", "FullLabeledGraph", "FullUnlabeledGraph", "ReducedLabeledGraph", 
    "ReducedUnlabeledGraph", "SimpleLabeledGraph", "SimpleUnlabeledGraph", "ReducedSimpleLabeledGraph", 
    "ReducedSimpleUnlabeledGraph", "AssociationForm", "Properties"} /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor /: MakeBoxes[abstractFunctor:AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
       "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
          "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
          "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
            Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
             "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
       "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
       "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
       "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
       "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]], format_] := 
   Module[{domainMorphismAssociation, domainCompositions, imageMorphismAssociation, imageCompositions, 
      reducedDomainMorphismAssociation, reducedDomainCompositions, imageObjects, imageArrows, 
      imageQuiverObjectEquivalences, imageObjectEquivalences, imageArrowEquivalences, imageMorphismEquivalences, 
      reducedImageMorphismAssociation, reducedImageCompositions, icon, type, objectCount, morphismCount, 
      reducedObjectCount, reducedMorphismCount}, domainMorphismAssociation = 
       Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
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
             DirectedEdge[#1, #1]]]] & ) /@ objects; imageMorphismAssociation = 
       Association[Select[Normal[Association[Join[If[covariant === True, Normal[arrows] /. Normal[arrowMappings] /. 
              Normal[objectMappings], (First[#1] -> Reverse[Last[#1]] & ) /@ (Normal[arrows] /. Normal[arrowMappings] /. 
               Normal[objectMappings])], Normal[newArrows]]]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
      Do[imageCompositions = Select[Tuples[Normal[imageMorphismAssociation], 2], 
          Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
        (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
              Normal[imageMorphismAssociation], StringDelete[ToString[newCompositionSymbol[First[Last[#1]], 
                 First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
           imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], newCompositionSymbol[
                First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], 
                Last[Last[Last[#1]]]]]]] & ) /@ imageCompositions, Length[Join[objects /. Normal[objectMappings], 
         newObjects]]]; imageMorphismAssociation = Association[Select[Normal[imageMorphismAssociation], 
         Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
           Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]]; 
      (If[ !MemberQ[Normal[imageMorphismAssociation], newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
         imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], newIdentitySymbol[#1] -> 
             DirectedEdge[#1, #1]]]] & ) /@ Join[objects /. Normal[objectMappings], newObjects]; 
      reducedDomainMorphismAssociation = Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[arrows, 
            arrowEquivalences], quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
      Do[reducedDomainCompositions = Select[Tuples[Normal[reducedDomainMorphismAssociation], 2], 
          Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
        (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
              Normal[reducedDomainMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                 First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
           reducedDomainMorphismAssociation = Association[Append[Normal[reducedDomainMorphismAssociation], 
              compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], 
                Last[Last[Last[#1]]]]]]] & ) /@ reducedDomainCompositions, 
       Length[reduceObjects[objects, quiverObjectEquivalences]]]; reducedDomainMorphismAssociation = 
       Association[Select[Normal[reducedDomainMorphismAssociation], 
         Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == Length[DeleteDuplicates[
             Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
      (If[ !MemberQ[Normal[reducedDomainMorphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
         reducedDomainMorphismAssociation = Association[Append[Normal[reducedDomainMorphismAssociation], 
            identitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[objects, quiverObjectEquivalences]; 
      imageObjects = DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]; 
      imageArrows = Association[DeleteDuplicates[Join[Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], 
          Normal[newArrows]]]]; imageQuiverObjectEquivalences = quiverObjectEquivalences /. Normal[objectMappings]; 
      imageObjectEquivalences = DeleteDuplicates[Join[categoryObjectEquivalences /. Normal[objectMappings], 
         objectEquivalences]]; imageArrowEquivalences = arrowEquivalences /. Normal[arrowMappings]; 
      imageMorphismEquivalences = If[covariant === True, DeleteDuplicates[
         Join[categoryMorphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[arrowMappings] /. 
           Normal[objectMappings], morphismEquivalences]], DeleteDuplicates[
         Join[categoryMorphismEquivalences /. compositionSymbol -> newCompositionSymbol /. Normal[arrowMappings] /. 
            Normal[objectMappings] /. {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
             newCompositionSymbol[z, newCompositionSymbol[y, x]], newCompositionSymbol[newCompositionSymbol[x_, y_], 
              z_] :> newCompositionSymbol[newCompositionSymbol[z, y], x], newCompositionSymbol[x_, y_] :> 
             newCompositionSymbol[y, x]}, morphismEquivalences]]]; reducedImageMorphismAssociation = 
       Association[Select[Normal[Association[DeleteDuplicates[Join[If[covariant === True, Normal[reduceArrowsFinal[
                reduceArrowsInitial[imageArrows, imageArrowEquivalences], imageQuiverObjectEquivalences]], 
              (First[#1] -> Reverse[Last[#1]] & ) /@ Normal[reduceArrowsFinal[reduceArrowsInitial[imageArrows, 
                   imageArrowEquivalences], imageQuiverObjectEquivalences]] /. Normal[arrowMappings]], 
             Normal[newArrows]]]]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
      Do[reducedImageCompositions = Select[Tuples[Normal[reducedImageMorphismAssociation], 2], 
          Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
        (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
              Normal[reducedImageMorphismAssociation], StringDelete[ToString[newCompositionSymbol[First[Last[#1]], 
                 First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
           reducedImageMorphismAssociation = Association[Append[Normal[reducedImageMorphismAssociation], 
              newCompositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], 
                Last[Last[Last[#1]]]]]]] & ) /@ reducedImageCompositions, 
       Length[reduceObjects[imageObjects, imageQuiverObjectEquivalences]]]; reducedImageMorphismAssociation = 
       Association[Select[Normal[reducedImageMorphismAssociation], 
         Length[Flatten[{First[#1] /. newCompositionSymbol -> List}]] == 
           Length[DeleteDuplicates[Flatten[{First[#1] /. newCompositionSymbol -> List}]]] & ]]; 
      (If[ !MemberQ[Normal[reducedImageMorphismAssociation], newIdentitySymbol[#1] -> DirectedEdge[#1, #1]], 
         reducedImageMorphismAssociation = Association[Append[Normal[reducedImageMorphismAssociation], 
            newIdentitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[imageObjects, 
        imageQuiverObjectEquivalences]; icon = GraphPlot[EdgeTaggedGraph[objects, (DirectedEdge @@ Last[#1] & ) /@ 
           Normal[domainMorphismAssociation], VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], 
          EdgeShapeFunction -> GraphElementData["ShortFilledArrow", "ArrowSize" -> 0.05], EdgeStyle -> Black, 
          GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]] -> 
        GraphPlot[EdgeTaggedGraph[Join[objects /. Normal[objectMappings], newObjects], (DirectedEdge @@ Last[#1] & ) /@ 
           Normal[imageMorphismAssociation], VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], 
          EdgeShapeFunction -> GraphElementData["ShortFilledArrow", "ArrowSize" -> 0.05], EdgeStyle -> Black, 
          GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]]; If[covariant === True, type = "Covariant", 
       type = "Contravariant"]; objectCount = Length[objects] -> 
        Length[DeleteDuplicates[Join[objects /. Normal[objectMappings], newObjects]]]; 
      morphismCount = Length[Normal[domainMorphismAssociation]] -> 
        Length[DeleteDuplicates[Normal[imageMorphismAssociation]]]; reducedObjectCount = 
       Length[reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences]] -> 
        Length[reduceObjects[reduceObjects[imageObjects, imageQuiverObjectEquivalences], imageObjectEquivalences]]; 
      reducedMorphismCount = Length[Normal[reduceArrowsFinal[reduceArrowsInitial[reducedDomainMorphismAssociation, 
            categoryMorphismEquivalences], categoryObjectEquivalences]]] -> 
        Length[Normal[reduceArrowsFinal[reduceArrowsInitial[reducedImageMorphismAssociation, imageMorphismEquivalences], 
           imageObjectEquivalences]]]; BoxForm`ArrangeSummaryBox["AbstractFunctor", abstractFunctor, icon, 
       {{BoxForm`SummaryItem[{"Type: ", type}]}, {BoxForm`SummaryItem[{"Objects: ", objectCount}], 
         BoxForm`SummaryItem[{"Morphisms: ", morphismCount}]}}, 
       {{BoxForm`SummaryItem[{"Reduced Objects: ", reducedObjectCount}], BoxForm`SummaryItem[
          {"Reduced Morphisms: ", reducedMorphismCount}]}}, format, "Interpretable" -> Automatic]] /; 
    SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[(abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
     "ObjectEquivalences" -> categoryObjectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]] := 
  AbstractFunctor[Association["ArrowMappings" -> Association[], "Category" -> ResourceFunction["AbstractCategory"][
       Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
        "MorphismEquivalences" -> categoryMorphismEquivalences, "ObjectEquivalences" -> categoryObjectEquivalences, 
        "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> arrowEquivalences, 
           "Arrows" -> arrows, "ObjectEquivalences" -> quiverObjectEquivalences, "Objects" -> objects]]]], 
     "Covariant" -> True, "MorphismEquivalences" -> {}, "NewArrows" -> Association[], 
     "NewCompositionSymbol" -> compositionSymbol, "NewIdentitySymbol" -> identitySymbol, "NewObjects" -> {}, 
     "ObjectEquivalences" -> {}, "ObjectMappings" -> Association[]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[(abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
     "ObjectEquivalences" -> categoryObjectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]], objectMappings_Association] := 
  AbstractFunctor[Association["ArrowMappings" -> Association[], "Category" -> ResourceFunction["AbstractCategory"][
       Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
        "MorphismEquivalences" -> categoryMorphismEquivalences, "ObjectEquivalences" -> categoryObjectEquivalences, 
        "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> arrowEquivalences, 
           "Arrows" -> arrows, "ObjectEquivalences" -> quiverObjectEquivalences, "Objects" -> objects]]]], 
     "Covariant" -> True, "MorphismEquivalences" -> {}, "NewArrows" -> Association[], 
     "NewCompositionSymbol" -> compositionSymbol, "NewIdentitySymbol" -> identitySymbol, "NewObjects" -> {}, 
     "ObjectEquivalences" -> {}, "ObjectMappings" -> objectMappings]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[(abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
     "ObjectEquivalences" -> categoryObjectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]], objectMappings_Association, arrowMappings_Association] := 
  AbstractFunctor[Association["ArrowMappings" -> arrowMappings, "Category" -> ResourceFunction["AbstractCategory"][
       Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
        "MorphismEquivalences" -> categoryMorphismEquivalences, "ObjectEquivalences" -> categoryObjectEquivalences, 
        "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> arrowEquivalences, 
           "Arrows" -> arrows, "ObjectEquivalences" -> quiverObjectEquivalences, "Objects" -> objects]]]], 
     "Covariant" -> True, "MorphismEquivalences" -> {}, "NewArrows" -> Association[], 
     "NewCompositionSymbol" -> compositionSymbol, "NewIdentitySymbol" -> identitySymbol, "NewObjects" -> {}, 
     "ObjectEquivalences" -> {}, "ObjectMappings" -> objectMappings]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[(abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
     "ObjectEquivalences" -> categoryObjectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]], objectMappings_Association, arrowMappings_Association, newObjects_List] := 
  AbstractFunctor[Association["ArrowMappings" -> arrowMappings, "Category" -> ResourceFunction["AbstractCategory"][
       Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
        "MorphismEquivalences" -> categoryMorphismEquivalences, "ObjectEquivalences" -> categoryObjectEquivalences, 
        "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> arrowEquivalences, 
           "Arrows" -> arrows, "ObjectEquivalences" -> quiverObjectEquivalences, "Objects" -> objects]]]], 
     "Covariant" -> True, "MorphismEquivalences" -> {}, "NewArrows" -> Association[], 
     "NewCompositionSymbol" -> compositionSymbol, "NewIdentitySymbol" -> identitySymbol, "NewObjects" -> newObjects, 
     "ObjectEquivalences" -> {}, "ObjectMappings" -> objectMappings]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[(abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
     "ObjectEquivalences" -> categoryObjectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]], objectMappings_Association, arrowMappings_Association, newObjects_List, 
   newArrows_Association] := AbstractFunctor[Association["ArrowMappings" -> arrowMappings, 
     "Category" -> ResourceFunction["AbstractCategory"][Association["CompositionSymbol" -> compositionSymbol, 
        "IdentitySymbol" -> identitySymbol, "MorphismEquivalences" -> categoryMorphismEquivalences, 
        "ObjectEquivalences" -> categoryObjectEquivalences, "Quiver" -> ResourceFunction["AbstractQuiver"][
          Association["ArrowEquivalences" -> arrowEquivalences, "Arrows" -> arrows, "ObjectEquivalences" -> 
            quiverObjectEquivalences, "Objects" -> objects]]]], "Covariant" -> True, "MorphismEquivalences" -> {}, 
     "NewArrows" -> newArrows, "NewCompositionSymbol" -> compositionSymbol, "NewIdentitySymbol" -> identitySymbol, 
     "NewObjects" -> newObjects, "ObjectEquivalences" -> {}, "ObjectMappings" -> objectMappings]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[(abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
     "ObjectEquivalences" -> categoryObjectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]], objectMappings_Association, arrowMappings_Association, newObjects_List, 
   newArrows_Association, objectEquivalences_List] := 
  AbstractFunctor[Association["ArrowMappings" -> arrowMappings, "Category" -> ResourceFunction["AbstractCategory"][
       Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
        "MorphismEquivalences" -> categoryMorphismEquivalences, "ObjectEquivalences" -> categoryObjectEquivalences, 
        "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> arrowEquivalences, 
           "Arrows" -> arrows, "ObjectEquivalences" -> quiverObjectEquivalences, "Objects" -> objects]]]], 
     "Covariant" -> True, "MorphismEquivalences" -> {}, "NewArrows" -> newArrows, 
     "NewCompositionSymbol" -> compositionSymbol, "NewIdentitySymbol" -> identitySymbol, "NewObjects" -> newObjects, 
     "ObjectEquivalences" -> objectEquivalences, "ObjectMappings" -> objectMappings]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[(abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
     "ObjectEquivalences" -> categoryObjectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]], objectMappings_Association, arrowMappings_Association, newObjects_List, 
   newArrows_Association, objectEquivalences_List, morphismEquivalences_List] := 
  AbstractFunctor[Association["ArrowMappings" -> arrowMappings, "Category" -> ResourceFunction["AbstractCategory"][
       Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
        "MorphismEquivalences" -> categoryMorphismEquivalences, "ObjectEquivalences" -> categoryObjectEquivalences, 
        "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> arrowEquivalences, 
           "Arrows" -> arrows, "ObjectEquivalences" -> quiverObjectEquivalences, "Objects" -> objects]]]], 
     "Covariant" -> True, "MorphismEquivalences" -> morphismEquivalences, "NewArrows" -> newArrows, 
     "NewCompositionSymbol" -> compositionSymbol, "NewIdentitySymbol" -> identitySymbol, "NewObjects" -> newObjects, 
     "ObjectEquivalences" -> objectEquivalences, "ObjectMappings" -> objectMappings]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[(abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
     "ObjectEquivalences" -> categoryObjectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]], objectMappings_Association, arrowMappings_Association, newObjects_List, 
   newArrows_Association, newCompositionSymbol_] := 
  AbstractFunctor[Association["ArrowMappings" -> arrowMappings, "Category" -> ResourceFunction["AbstractCategory"][
       Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
        "MorphismEquivalences" -> categoryMorphismEquivalences, "ObjectEquivalences" -> categoryObjectEquivalences, 
        "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> arrowEquivalences, 
           "Arrows" -> arrows, "ObjectEquivalences" -> quiverObjectEquivalences, "Objects" -> objects]]]], 
     "Covariant" -> True, "MorphismEquivalences" -> {}, "NewArrows" -> newArrows, 
     "NewCompositionSymbol" -> newCompositionSymbol, "NewIdentitySymbol" -> identitySymbol, "NewObjects" -> newObjects, 
     "ObjectEquivalences" -> {}, "ObjectMappings" -> objectMappings]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory" && 
     !ListQ[newCompositionSymbol]
AbstractFunctor[(abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
     "ObjectEquivalences" -> categoryObjectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]], objectMappings_Association, arrowMappings_Association, newObjects_List, 
   newArrows_Association, newCompositionSymbol_, objectEquivalences_List] := 
  AbstractFunctor[Association["ArrowMappings" -> arrowMappings, "Category" -> ResourceFunction["AbstractCategory"][
       Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
        "MorphismEquivalences" -> categoryMorphismEquivalences, "ObjectEquivalences" -> categoryObjectEquivalences, 
        "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> arrowEquivalences, 
           "Arrows" -> arrows, "ObjectEquivalences" -> quiverObjectEquivalences, "Objects" -> objects]]]], 
     "Covariant" -> True, "MorphismEquivalences" -> {}, "NewArrows" -> newArrows, 
     "NewCompositionSymbol" -> newCompositionSymbol, "NewIdentitySymbol" -> identitySymbol, "NewObjects" -> newObjects, 
     "ObjectEquivalences" -> objectEquivalences, "ObjectMappings" -> objectMappings]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory" && 
     !ListQ[newCompositionSymbol]
AbstractFunctor[(abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
     "ObjectEquivalences" -> categoryObjectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]], objectMappings_Association, arrowMappings_Association, newObjects_List, 
   newArrows_Association, newCompositionSymbol_, objectEquivalences_List, morphismEquivalences_List] := 
  AbstractFunctor[Association["ArrowMappings" -> arrowMappings, "Category" -> ResourceFunction["AbstractCategory"][
       Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
        "MorphismEquivalences" -> categoryMorphismEquivalences, "ObjectEquivalences" -> categoryObjectEquivalences, 
        "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> arrowEquivalences, 
           "Arrows" -> arrows, "ObjectEquivalences" -> quiverObjectEquivalences, "Objects" -> objects]]]], 
     "Covariant" -> True, "MorphismEquivalences" -> morphismEquivalences, "NewArrows" -> newArrows, 
     "NewCompositionSymbol" -> newCompositionSymbol, "NewIdentitySymbol" -> identitySymbol, "NewObjects" -> newObjects, 
     "ObjectEquivalences" -> objectEquivalences, "ObjectMappings" -> objectMappings]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory" && 
     !ListQ[newCompositionSymbol]
AbstractFunctor[(abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
     "ObjectEquivalences" -> categoryObjectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]], objectMappings_Association, arrowMappings_Association, newObjects_List, 
   newArrows_Association, newCompositionSymbol_, newIdentitySymbol_] := 
  AbstractFunctor[Association["ArrowMappings" -> arrowMappings, "Category" -> ResourceFunction["AbstractCategory"][
       Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
        "MorphismEquivalences" -> categoryMorphismEquivalences, "ObjectEquivalences" -> categoryObjectEquivalences, 
        "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> arrowEquivalences, 
           "Arrows" -> arrows, "ObjectEquivalences" -> quiverObjectEquivalences, "Objects" -> objects]]]], 
     "Covariant" -> True, "MorphismEquivalences" -> {}, "NewArrows" -> newArrows, 
     "NewCompositionSymbol" -> newCompositionSymbol, "NewIdentitySymbol" -> newIdentitySymbol, 
     "NewObjects" -> newObjects, "ObjectEquivalences" -> {}, "ObjectMappings" -> objectMappings]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory" && 
     !ListQ[newCompositionSymbol] &&  !ListQ[newIdentitySymbol]
AbstractFunctor[(abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
     "ObjectEquivalences" -> categoryObjectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]], objectMappings_Association, arrowMappings_Association, newObjects_List, 
   newArrows_Association, newCompositionSymbol_, newIdentitySymbol_, objectEquivalences_List] := 
  AbstractFunctor[Association["ArrowMappings" -> arrowMappings, "Category" -> ResourceFunction["AbstractCategory"][
       Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
        "MorphismEquivalences" -> categoryMorphismEquivalences, "ObjectEquivalences" -> categoryObjectEquivalences, 
        "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> arrowEquivalences, 
           "Arrows" -> arrows, "ObjectEquivalences" -> quiverObjectEquivalences, "Objects" -> objects]]]], 
     "Covariant" -> True, "MorphismEquivalences" -> {}, "NewArrows" -> newArrows, 
     "NewCompositionSymbol" -> newCompositionSymbol, "NewIdentitySymbol" -> newIdentitySymbol, 
     "NewObjects" -> newObjects, "ObjectEquivalences" -> objectEquivalences, "ObjectMappings" -> objectMappings]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory" && 
     !ListQ[newCompositionSymbol] &&  !ListQ[newIdentitySymbol]
AbstractFunctor[(abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
     "ObjectEquivalences" -> categoryObjectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]], objectMappings_Association, arrowMappings_Association, newObjects_List, 
   newArrows_Association, newCompositionSymbol_, newIdentitySymbol_, objectEquivalences_List, 
   morphismEquivalences_List] := AbstractFunctor[Association["ArrowMappings" -> arrowMappings, 
     "Category" -> ResourceFunction["AbstractCategory"][Association["CompositionSymbol" -> compositionSymbol, 
        "IdentitySymbol" -> identitySymbol, "MorphismEquivalences" -> categoryMorphismEquivalences, 
        "ObjectEquivalences" -> categoryObjectEquivalences, "Quiver" -> ResourceFunction["AbstractQuiver"][
          Association["ArrowEquivalences" -> arrowEquivalences, "Arrows" -> arrows, "ObjectEquivalences" -> 
            quiverObjectEquivalences, "Objects" -> objects]]]], "Covariant" -> True, 
     "MorphismEquivalences" -> morphismEquivalences, "NewArrows" -> newArrows, 
     "NewCompositionSymbol" -> newCompositionSymbol, "NewIdentitySymbol" -> newIdentitySymbol, 
     "NewObjects" -> newObjects, "ObjectEquivalences" -> objectEquivalences, "ObjectMappings" -> objectMappings]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory" && 
     !ListQ[newCompositionSymbol] &&  !ListQ[newIdentitySymbol]
AbstractFunctor[covariant_, (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
     "ObjectEquivalences" -> categoryObjectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]] := 
  AbstractFunctor[Association["ArrowMappings" -> Association[], "Category" -> ResourceFunction["AbstractCategory"][
       Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
        "MorphismEquivalences" -> categoryMorphismEquivalences, "ObjectEquivalences" -> categoryObjectEquivalences, 
        "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> arrowEquivalences, 
           "Arrows" -> arrows, "ObjectEquivalences" -> quiverObjectEquivalences, "Objects" -> objects]]]], 
     "Covariant" -> covariant, "MorphismEquivalences" -> {}, "NewArrows" -> Association[], 
     "NewCompositionSymbol" -> compositionSymbol, "NewIdentitySymbol" -> identitySymbol, "NewObjects" -> {}, 
     "ObjectEquivalences" -> {}, "ObjectMappings" -> Association[]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[covariant_, (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
     "ObjectEquivalences" -> categoryObjectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]], objectMappings_Association] := 
  AbstractFunctor[Association["ArrowMappings" -> Association[], "Category" -> ResourceFunction["AbstractCategory"][
       Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
        "MorphismEquivalences" -> categoryMorphismEquivalences, "ObjectEquivalences" -> categoryObjectEquivalences, 
        "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> arrowEquivalences, 
           "Arrows" -> arrows, "ObjectEquivalences" -> quiverObjectEquivalences, "Objects" -> objects]]]], 
     "Covariant" -> covariant, "MorphismEquivalences" -> {}, "NewArrows" -> Association[], 
     "NewCompositionSymbol" -> compositionSymbol, "NewIdentitySymbol" -> identitySymbol, "NewObjects" -> {}, 
     "ObjectEquivalences" -> {}, "ObjectMappings" -> objectMappings]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[covariant_, (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
     "ObjectEquivalences" -> categoryObjectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]], objectMappings_Association, arrowMappings_Association] := 
  AbstractFunctor[Association["ArrowMappings" -> arrowMappings, "Category" -> ResourceFunction["AbstractCategory"][
       Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
        "MorphismEquivalences" -> categoryMorphismEquivalences, "ObjectEquivalences" -> categoryObjectEquivalences, 
        "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> arrowEquivalences, 
           "Arrows" -> arrows, "ObjectEquivalences" -> quiverObjectEquivalences, "Objects" -> objects]]]], 
     "Covariant" -> covariant, "MorphismEquivalences" -> {}, "NewArrows" -> Association[], 
     "NewCompositionSymbol" -> compositionSymbol, "NewIdentitySymbol" -> identitySymbol, "NewObjects" -> {}, 
     "ObjectEquivalences" -> {}, "ObjectMappings" -> objectMappings]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[covariant_, (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
     "ObjectEquivalences" -> categoryObjectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]], objectMappings_Association, arrowMappings_Association, newObjects_List] := 
  AbstractFunctor[Association["ArrowMappings" -> arrowMappings, "Category" -> ResourceFunction["AbstractCategory"][
       Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
        "MorphismEquivalences" -> categoryMorphismEquivalences, "ObjectEquivalences" -> categoryObjectEquivalences, 
        "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> arrowEquivalences, 
           "Arrows" -> arrows, "ObjectEquivalences" -> quiverObjectEquivalences, "Objects" -> objects]]]], 
     "Covariant" -> covariant, "MorphismEquivalences" -> {}, "NewArrows" -> Association[], 
     "NewCompositionSymbol" -> compositionSymbol, "NewIdentitySymbol" -> identitySymbol, "NewObjects" -> newObjects, 
     "ObjectEquivalences" -> {}, "ObjectMappings" -> objectMappings]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[covariant_, (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
     "ObjectEquivalences" -> categoryObjectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]], objectMappings_Association, arrowMappings_Association, newObjects_List, 
   newArrows_Association] := AbstractFunctor[Association["ArrowMappings" -> arrowMappings, 
     "Category" -> ResourceFunction["AbstractCategory"][Association["CompositionSymbol" -> compositionSymbol, 
        "IdentitySymbol" -> identitySymbol, "MorphismEquivalences" -> categoryMorphismEquivalences, 
        "ObjectEquivalences" -> categoryObjectEquivalences, "Quiver" -> ResourceFunction["AbstractQuiver"][
          Association["ArrowEquivalences" -> arrowEquivalences, "Arrows" -> arrows, "ObjectEquivalences" -> 
            quiverObjectEquivalences, "Objects" -> objects]]]], "Covariant" -> covariant, "MorphismEquivalences" -> {}, 
     "NewArrows" -> newArrows, "NewCompositionSymbol" -> compositionSymbol, "NewIdentitySymbol" -> identitySymbol, 
     "NewObjects" -> newObjects, "ObjectEquivalences" -> {}, "ObjectMappings" -> objectMappings]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[covariant_, (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
     "ObjectEquivalences" -> categoryObjectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]], objectMappings_Association, arrowMappings_Association, newObjects_List, 
   newArrows_Association, objectEquivalences_List] := 
  AbstractFunctor[Association["ArrowMappings" -> arrowMappings, "Category" -> ResourceFunction["AbstractCategory"][
       Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
        "MorphismEquivalences" -> categoryMorphismEquivalences, "ObjectEquivalences" -> categoryObjectEquivalences, 
        "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> arrowEquivalences, 
           "Arrows" -> arrows, "ObjectEquivalences" -> quiverObjectEquivalences, "Objects" -> objects]]]], 
     "Covariant" -> covariant, "MorphismEquivalences" -> {}, "NewArrows" -> newArrows, 
     "NewCompositionSymbol" -> compositionSymbol, "NewIdentitySymbol" -> identitySymbol, "NewObjects" -> newObjects, 
     "ObjectEquivalences" -> objectEquivalences, "ObjectMappings" -> objectMappings]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[covariant_, (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
     "ObjectEquivalences" -> categoryObjectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]], objectMappings_Association, arrowMappings_Association, newObjects_List, 
   newArrows_Association, objectEquivalences_List, morphismEquivalences_List] := 
  AbstractFunctor[Association["ArrowMappings" -> arrowMappings, "Category" -> ResourceFunction["AbstractCategory"][
       Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
        "MorphismEquivalences" -> categoryMorphismEquivalences, "ObjectEquivalences" -> categoryObjectEquivalences, 
        "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> arrowEquivalences, 
           "Arrows" -> arrows, "ObjectEquivalences" -> quiverObjectEquivalences, "Objects" -> objects]]]], 
     "Covariant" -> covariant, "MorphismEquivalences" -> morphismEquivalences, "NewArrows" -> newArrows, 
     "NewCompositionSymbol" -> compositionSymbol, "NewIdentitySymbol" -> identitySymbol, "NewObjects" -> newObjects, 
     "ObjectEquivalences" -> objectEquivalences, "ObjectMappings" -> objectMappings]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[covariant_, (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
     "ObjectEquivalences" -> categoryObjectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]], objectMappings_Association, arrowMappings_Association, newObjects_List, 
   newArrows_Association, newCompositionSymbol_] := 
  AbstractFunctor[Association["ArrowMappings" -> arrowMappings, "Category" -> ResourceFunction["AbstractCategory"][
       Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
        "MorphismEquivalences" -> categoryMorphismEquivalences, "ObjectEquivalences" -> categoryObjectEquivalences, 
        "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> arrowEquivalences, 
           "Arrows" -> arrows, "ObjectEquivalences" -> quiverObjectEquivalences, "Objects" -> objects]]]], 
     "Covariant" -> covariant, "MorphismEquivalences" -> {}, "NewArrows" -> newArrows, 
     "NewCompositionSymbol" -> newCompositionSymbol, "NewIdentitySymbol" -> identitySymbol, "NewObjects" -> newObjects, 
     "ObjectEquivalences" -> {}, "ObjectMappings" -> objectMappings]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory" && 
     !ListQ[newCompositionSymbol]
AbstractFunctor[covariant_, (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
     "ObjectEquivalences" -> categoryObjectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]], objectMappings_Association, arrowMappings_Association, newObjects_List, 
   newArrows_Association, newCompositionSymbol_, objectEquivalences_List] := 
  AbstractFunctor[Association["ArrowMappings" -> arrowMappings, "Category" -> ResourceFunction["AbstractCategory"][
       Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
        "MorphismEquivalences" -> categoryMorphismEquivalences, "ObjectEquivalences" -> categoryObjectEquivalences, 
        "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> arrowEquivalences, 
           "Arrows" -> arrows, "ObjectEquivalences" -> quiverObjectEquivalences, "Objects" -> objects]]]], 
     "Covariant" -> covariant, "MorphismEquivalences" -> {}, "NewArrows" -> newArrows, 
     "NewCompositionSymbol" -> newCompositionSymbol, "NewIdentitySymbol" -> identitySymbol, "NewObjects" -> newObjects, 
     "ObjectEquivalences" -> objectEquivalences, "ObjectMappings" -> objectMappings]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory" && 
     !ListQ[newCompositionSymbol]
AbstractFunctor[covariant_, (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
     "ObjectEquivalences" -> categoryObjectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]], objectMappings_Association, arrowMappings_Association, newObjects_List, 
   newArrows_Association, newCompositionSymbol_, objectEquivalences_List, morphismEquivalences_List] := 
  AbstractFunctor[Association["ArrowMappings" -> arrowMappings, "Category" -> ResourceFunction["AbstractCategory"][
       Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
        "MorphismEquivalences" -> categoryMorphismEquivalences, "ObjectEquivalences" -> categoryObjectEquivalences, 
        "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> arrowEquivalences, 
           "Arrows" -> arrows, "ObjectEquivalences" -> quiverObjectEquivalences, "Objects" -> objects]]]], 
     "Covariant" -> covariant, "MorphismEquivalences" -> morphismEquivalences, "NewArrows" -> newArrows, 
     "NewCompositionSymbol" -> newCompositionSymbol, "NewIdentitySymbol" -> identitySymbol, "NewObjects" -> newObjects, 
     "ObjectEquivalences" -> objectEquivalences, "ObjectMappings" -> objectMappings]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory" && 
     !ListQ[newCompositionSymbol]
AbstractFunctor[covariant_, (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
     "ObjectEquivalences" -> categoryObjectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]], objectMappings_Association, arrowMappings_Association, newObjects_List, 
   newArrows_Association, newCompositionSymbol_, newIdentitySymbol_] := 
  AbstractFunctor[Association["ArrowMappings" -> arrowMappings, "Category" -> ResourceFunction["AbstractCategory"][
       Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
        "MorphismEquivalences" -> categoryMorphismEquivalences, "ObjectEquivalences" -> categoryObjectEquivalences, 
        "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> arrowEquivalences, 
           "Arrows" -> arrows, "ObjectEquivalences" -> quiverObjectEquivalences, "Objects" -> objects]]]], 
     "Covariant" -> covariant, "MorphismEquivalences" -> {}, "NewArrows" -> newArrows, 
     "NewCompositionSymbol" -> newCompositionSymbol, "NewIdentitySymbol" -> newIdentitySymbol, 
     "NewObjects" -> newObjects, "ObjectEquivalences" -> {}, "ObjectMappings" -> objectMappings]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory" && 
     !ListQ[newCompositionSymbol] &&  !ListQ[newIdentitySymbol]
AbstractFunctor[covariant_, (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
     "ObjectEquivalences" -> categoryObjectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]], objectMappings_Association, arrowMappings_Association, newObjects_List, 
   newArrows_Association, newCompositionSymbol_, newIdentitySymbol_, objectEquivalences_List] := 
  AbstractFunctor[Association["ArrowMappings" -> arrowMappings, "Category" -> ResourceFunction["AbstractCategory"][
       Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
        "MorphismEquivalences" -> categoryMorphismEquivalences, "ObjectEquivalences" -> categoryObjectEquivalences, 
        "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> arrowEquivalences, 
           "Arrows" -> arrows, "ObjectEquivalences" -> quiverObjectEquivalences, "Objects" -> objects]]]], 
     "Covariant" -> covariant, "MorphismEquivalences" -> {}, "NewArrows" -> newArrows, 
     "NewCompositionSymbol" -> newCompositionSymbol, "NewIdentitySymbol" -> newIdentitySymbol, 
     "NewObjects" -> newObjects, "ObjectEquivalences" -> objectEquivalences, "ObjectMappings" -> objectMappings]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory" && 
     !ListQ[newCompositionSymbol] &&  !ListQ[newIdentitySymbol]
AbstractFunctor[covariant_, (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
     "ObjectEquivalences" -> categoryObjectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]], objectMappings_Association, arrowMappings_Association, newObjects_List, 
   newArrows_Association, newCompositionSymbol_, newIdentitySymbol_, objectEquivalences_List, 
   morphismEquivalences_List] := AbstractFunctor[Association["ArrowMappings" -> arrowMappings, 
     "Category" -> ResourceFunction["AbstractCategory"][Association["CompositionSymbol" -> compositionSymbol, 
        "IdentitySymbol" -> identitySymbol, "MorphismEquivalences" -> categoryMorphismEquivalences, 
        "ObjectEquivalences" -> categoryObjectEquivalences, "Quiver" -> ResourceFunction["AbstractQuiver"][
          Association["ArrowEquivalences" -> arrowEquivalences, "Arrows" -> arrows, "ObjectEquivalences" -> 
            quiverObjectEquivalences, "Objects" -> objects]]]], "Covariant" -> covariant, 
     "MorphismEquivalences" -> morphismEquivalences, "NewArrows" -> newArrows, 
     "NewCompositionSymbol" -> newCompositionSymbol, "NewIdentitySymbol" -> newIdentitySymbol, 
     "NewObjects" -> newObjects, "ObjectEquivalences" -> objectEquivalences, "ObjectMappings" -> objectMappings]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory" && 
     !ListQ[newCompositionSymbol] &&  !ListQ[newIdentitySymbol]
AbstractFunctor[covariant_, (functorSymbol_)[(abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
      "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
      "ObjectEquivalences" -> categoryObjectEquivalences_List, 
      "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
         "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
         "Objects" -> objects_List]]]]]] := 
  AbstractFunctor[Association["ArrowMappings" -> Association[(First[#1] -> functorSymbol[First[#1]] & ) /@ 
        Normal[arrows]], "Category" -> ResourceFunction["AbstractCategory"][
       Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
        "MorphismEquivalences" -> categoryMorphismEquivalences, "ObjectEquivalences" -> categoryObjectEquivalences, 
        "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> arrowEquivalences, 
           "Arrows" -> arrows, "ObjectEquivalences" -> quiverObjectEquivalences, "Objects" -> objects]]]], 
     "Covariant" -> covariant, "MorphismEquivalences" -> {}, "NewArrows" -> Association[], 
     "NewCompositionSymbol" -> compositionSymbol, "NewIdentitySymbol" -> identitySymbol, "NewObjects" -> {}, 
     "ObjectEquivalences" -> {}, "ObjectMappings" -> Association[(#1 -> functorSymbol[#1] & ) /@ objects]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[(functorSymbol_)[(abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
      "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
      "ObjectEquivalences" -> categoryObjectEquivalences_List, 
      "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
         "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
         "Objects" -> objects_List]]]]]] := 
  AbstractFunctor[Association["ArrowMappings" -> Association[(First[#1] -> functorSymbol[First[#1]] & ) /@ 
        Normal[arrows]], "Category" -> ResourceFunction["AbstractCategory"][
       Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
        "MorphismEquivalences" -> categoryMorphismEquivalences, "ObjectEquivalences" -> categoryObjectEquivalences, 
        "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> arrowEquivalences, 
           "Arrows" -> arrows, "ObjectEquivalences" -> quiverObjectEquivalences, "Objects" -> objects]]]], 
     "Covariant" -> True, "MorphismEquivalences" -> {}, "NewArrows" -> Association[], 
     "NewCompositionSymbol" -> compositionSymbol, "NewIdentitySymbol" -> identitySymbol, "NewObjects" -> {}, 
     "ObjectEquivalences" -> {}, "ObjectMappings" -> Association[(#1 -> functorSymbol[#1] & ) /@ objects]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[functor_Association] := AbstractFunctor[KeySort[functor]] /; 
   KeyExistsQ[functor, "Covariant"] && KeyExistsQ[functor, "Category"] && KeyExistsQ[functor, "ObjectMappings"] && 
    KeyExistsQ[functor, "ArrowMappings"] && KeyExistsQ[functor, "NewObjects"] && KeyExistsQ[functor, "NewArrows"] && 
    KeyExistsQ[functor, "NewCompositionSymbol"] && KeyExistsQ[functor, "NewIdentitySymbol"] && 
    KeyExistsQ[functor, "ObjectEquivalences"] && KeyExistsQ[functor, "MorphismEquivalences"] && 
    Keys[KeySort[functor]] =!= Keys[functor]
AbstractFunctor[AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]], 
   newObjectEquivalences_List] := AbstractFunctor[Association["ArrowMappings" -> arrowMappings, 
     "Category" -> ResourceFunction["AbstractCategory"][Association["CompositionSymbol" -> compositionSymbol, 
        "IdentitySymbol" -> identitySymbol, "MorphismEquivalences" -> categoryMorphismEquivalences, 
        "ObjectEquivalences" -> categoryObjectEquivalences, "Quiver" -> ResourceFunction["AbstractQuiver"][
          Association["ArrowEquivalences" -> arrowEquivalences, "Arrows" -> arrows, "ObjectEquivalences" -> 
            quiverObjectEquivalences, "Objects" -> objects]]]], "Covariant" -> covariant, 
     "MorphismEquivalences" -> morphismEquivalences, "NewArrows" -> newArrows, 
     "NewCompositionSymbol" -> newCompositionSymbol, "NewIdentitySymbol" -> newIdentitySymbol, 
     "NewObjects" -> newObjects, "ObjectEquivalences" -> newObjectEquivalences, "ObjectMappings" -> objectMappings]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]], 
   newObjectEquivalences_List, newMorphismEquivalences_List] := 
  AbstractFunctor[Association["ArrowMappings" -> arrowMappings, "Category" -> ResourceFunction["AbstractCategory"][
       Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
        "MorphismEquivalences" -> categoryMorphismEquivalences, "ObjectEquivalences" -> categoryObjectEquivalences, 
        "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> arrowEquivalences, 
           "Arrows" -> arrows, "ObjectEquivalences" -> quiverObjectEquivalences, "Objects" -> objects]]]], 
     "Covariant" -> covariant, "MorphismEquivalences" -> newMorphismEquivalences, "NewArrows" -> newArrows, 
     "NewCompositionSymbol" -> newCompositionSymbol, "NewIdentitySymbol" -> newIdentitySymbol, 
     "NewObjects" -> newObjects, "ObjectEquivalences" -> newObjectEquivalences, "ObjectMappings" -> objectMappings]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractFunctor[AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]], 
   functorCompositionSymbol_] := AbstractFunctor[Association["ArrowMappings" -> arrowMappings, 
     "Category" -> ResourceFunction["AbstractCategory"][Association["CompositionSymbol" -> compositionSymbol, 
        "IdentitySymbol" -> identitySymbol, "MorphismEquivalences" -> categoryMorphismEquivalences, 
        "ObjectEquivalences" -> categoryObjectEquivalences, "Quiver" -> ResourceFunction["AbstractQuiver"][
          Association["ArrowEquivalences" -> arrowEquivalences, "Arrows" -> arrows, "ObjectEquivalences" -> 
            quiverObjectEquivalences, "Objects" -> objects]]]], "Covariant" -> covariant, 
     "MorphismEquivalences" -> morphismEquivalences, "NewArrows" -> newArrows, 
     "NewCompositionSymbol" -> functorCompositionSymbol, "NewIdentitySymbol" -> newIdentitySymbol, 
     "NewObjects" -> newObjects, "ObjectEquivalences" -> objectEquivalences, "ObjectMappings" -> objectMappings]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory" && 
     !ListQ[functorCompositionSymbol]
AbstractFunctor[AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]], 
   functorCompositionSymbol_, newObjectEquivalences_List] := 
  AbstractFunctor[Association["ArrowMappings" -> arrowMappings, "Category" -> ResourceFunction["AbstractCategory"][
       Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
        "MorphismEquivalences" -> categoryMorphismEquivalences, "ObjectEquivalences" -> categoryObjectEquivalences, 
        "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> arrowEquivalences, 
           "Arrows" -> arrows, "ObjectEquivalences" -> quiverObjectEquivalences, "Objects" -> objects]]]], 
     "Covariant" -> covariant, "MorphismEquivalences" -> morphismEquivalences, "NewArrows" -> newArrows, 
     "NewCompositionSymbol" -> functorCompositionSymbol, "NewIdentitySymbol" -> newIdentitySymbol, 
     "NewObjects" -> newObjects, "ObjectEquivalences" -> newObjectEquivalences, "ObjectMappings" -> objectMappings]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory" && 
     !ListQ[functorCompositionSymbol]
AbstractFunctor[AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]], 
   functorCompositionSymbol_, newObjectEquivalences_List, newMorphismEquivalences_List] := 
  AbstractFunctor[Association["ArrowMappings" -> arrowMappings, "Category" -> ResourceFunction["AbstractCategory"][
       Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
        "MorphismEquivalences" -> categoryMorphismEquivalences, "ObjectEquivalences" -> categoryObjectEquivalences, 
        "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> arrowEquivalences, 
           "Arrows" -> arrows, "ObjectEquivalences" -> quiverObjectEquivalences, "Objects" -> objects]]]], 
     "Covariant" -> covariant, "MorphismEquivalences" -> newMorphismEquivalences, "NewArrows" -> newArrows, 
     "NewCompositionSymbol" -> functorCompositionSymbol, "NewIdentitySymbol" -> newIdentitySymbol, 
     "NewObjects" -> newObjects, "ObjectEquivalences" -> newObjectEquivalences, "ObjectMappings" -> objectMappings]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory" && 
     !ListQ[functorCompositionSymbol]
AbstractFunctor[AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]], 
   functorCompositionSymbol_, functorIdentitySymbol_] := 
  AbstractFunctor[Association["ArrowMappings" -> arrowMappings, "Category" -> ResourceFunction["AbstractCategory"][
       Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
        "MorphismEquivalences" -> categoryMorphismEquivalences, "ObjectEquivalences" -> categoryObjectEquivalences, 
        "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> arrowEquivalences, 
           "Arrows" -> arrows, "ObjectEquivalences" -> quiverObjectEquivalences, "Objects" -> objects]]]], 
     "Covariant" -> covariant, "MorphismEquivalences" -> morphismEquivalences, "NewArrows" -> newArrows, 
     "NewCompositionSymbol" -> functorCompositionSymbol, "NewIdentitySymbol" -> functorIdentitySymbol, 
     "NewObjects" -> newObjects, "ObjectEquivalences" -> objectEquivalences, "ObjectMappings" -> objectMappings]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory" && 
     !ListQ[functorCompositionSymbol] &&  !ListQ[functorIdentitySymbol]
AbstractFunctor[AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]], 
   functorCompositionSymbol_, functorIdentitySymbol_, newObjectEquivalences_List] := 
  AbstractFunctor[Association["ArrowMappings" -> arrowMappings, "Category" -> ResourceFunction["AbstractCategory"][
       Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
        "MorphismEquivalences" -> categoryMorphismEquivalences, "ObjectEquivalences" -> categoryObjectEquivalences, 
        "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> arrowEquivalences, 
           "Arrows" -> arrows, "ObjectEquivalences" -> quiverObjectEquivalences, "Objects" -> objects]]]], 
     "Covariant" -> covariant, "MorphismEquivalences" -> morphismEquivalences, "NewArrows" -> newArrows, 
     "NewCompositionSymbol" -> functorCompositionSymbol, "NewIdentitySymbol" -> functorIdentitySymbol, 
     "NewObjects" -> newObjects, "ObjectEquivalences" -> newObjectEquivalences, "ObjectMappings" -> objectMappings]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory" && 
     !ListQ[functorCompositionSymbol] &&  !ListQ[functorIdentitySymbol]
AbstractFunctor[AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]], 
   functorCompositionSymbol_, functorIdentitySymbol_, newObjectEquivalences_List, newMorphismEquivalences_List] := 
  AbstractFunctor[Association["ArrowMappings" -> arrowMappings, "Category" -> ResourceFunction["AbstractCategory"][
       Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
        "MorphismEquivalences" -> categoryMorphismEquivalences, "ObjectEquivalences" -> categoryObjectEquivalences, 
        "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> arrowEquivalences, 
           "Arrows" -> arrows, "ObjectEquivalences" -> quiverObjectEquivalences, "Objects" -> objects]]]], 
     "Covariant" -> covariant, "MorphismEquivalences" -> newMorphismEquivalences, "NewArrows" -> newArrows, 
     "NewCompositionSymbol" -> functorCompositionSymbol, "NewIdentitySymbol" -> functorIdentitySymbol, 
     "NewObjects" -> newObjects, "ObjectEquivalences" -> newObjectEquivalences, "ObjectMappings" -> objectMappings]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory" && 
     !ListQ[functorCompositionSymbol] &&  !ListQ[functorIdentitySymbol]
AbstractFunctor[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]][
   (abstractCategory_)[Association["CompositionSymbol" -> inputCompositionSymbol_, 
     "IdentitySymbol" -> inputIdentitySymbol_, "MorphismEquivalences" -> inputMorphismEquivalences_List, 
     "ObjectEquivalences" -> inputObjectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> inputArrowEquivalences_List, 
        "Arrows" -> inputArrows_Association, "ObjectEquivalences" -> inputQuiverObjectEquivalences_List, 
        "Objects" -> inputObjects_List]]]]] := 
  ResourceFunction["AbstractCategory"][Association["CompositionSymbol" -> newCompositionSymbol, 
     "IdentitySymbol" -> newIdentitySymbol, "MorphismEquivalences" -> If[covariant === True, 
       DeleteDuplicates[Join[inputMorphismEquivalences /. inputCompositionSymbol -> newCompositionSymbol /. 
           Normal[arrowMappings] /. Normal[objectMappings], morphismEquivalences]], 
       DeleteDuplicates[Join[inputMorphismEquivalences /. inputCompositionSymbol -> newCompositionSymbol /. 
            Normal[arrowMappings] /. Normal[objectMappings] /. {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
            newCompositionSymbol[z, newCompositionSymbol[y, x]], newCompositionSymbol[newCompositionSymbol[x_, y_], 
             z_] :> newCompositionSymbol[newCompositionSymbol[z, y], x], newCompositionSymbol[x_, y_] :> 
            newCompositionSymbol[y, x]}, morphismEquivalences]]], "ObjectEquivalences" -> 
      DeleteDuplicates[Join[inputObjectEquivalences /. Normal[objectMappings], objectEquivalences]], 
     "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> (inputArrowEquivalences /. 
          Normal[arrowMappings]), "Arrows" -> Association[DeleteDuplicates[Join[If[covariant === True, 
             Normal[inputArrows] /. Normal[arrowMappings] /. Normal[objectMappings], 
             (First[#1] -> Reverse[Last[#1]] & ) /@ (Normal[inputArrows] /. Normal[arrowMappings] /. Normal[
                objectMappings])], Normal[newArrows]]]], "ObjectEquivalences" -> (inputQuiverObjectEquivalences /. 
          Normal[objectMappings]), "Objects" -> DeleteDuplicates[Join[inputObjects /. Normal[objectMappings], 
           newObjects]]]]]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"

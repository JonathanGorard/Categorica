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
AbstractLimit[Association["Functor" -> (abstractFunctor_)[Association["ArrowMappings" -> arrowMappings_Association, 
        "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
           "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
           "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
             Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
              "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
        "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
        "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
        "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
        "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]], 
     "LimitMorphismNames" -> limitMorphismNames_Association, "LimitObjectName" -> limitObjectName_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_Association, 
     "UniversalObjectName" -> universalObjectName_]]["Objects"] := 
  Module[{objectFunction, limitObjects}, objectFunction = Join[Association[(#1 -> #1 & ) /@ objects], objectMappings]; 
     limitObjects = {limitObjectName}; 
     (Module[{object = #1}, limitObjects = Append[limitObjects, object /. Normal[objectFunction]]] & ) /@ objects; 
     DeleteDuplicates[limitObjects]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory" && SymbolName[abstractFunctor] === "AbstractFunctor"
AbstractLimit[Association["Functor" -> (abstractFunctor_)[Association["ArrowMappings" -> arrowMappings_Association, 
        "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
           "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
           "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
             Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
              "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
        "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
        "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
        "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
        "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]], 
     "LimitMorphismNames" -> limitMorphismNames_Association, "LimitObjectName" -> limitObjectName_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_Association, 
     "UniversalObjectName" -> universalObjectName_]]["ObjectCount"] := 
  Module[{objectFunction, limitObjects}, objectFunction = Join[Association[(#1 -> #1 & ) /@ objects], objectMappings]; 
     limitObjects = {limitObjectName}; 
     (Module[{object = #1}, limitObjects = Append[limitObjects, object /. Normal[objectFunction]]] & ) /@ objects; 
     Length[DeleteDuplicates[limitObjects]]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory" && SymbolName[abstractFunctor] === "AbstractFunctor"
AbstractLimit[Association["Functor" -> (abstractFunctor_)[Association["ArrowMappings" -> arrowMappings_Association, 
        "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
           "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
           "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
             Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
              "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
        "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
        "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
        "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
        "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]], 
     "LimitMorphismNames" -> limitMorphismNames_Association, "LimitObjectName" -> limitObjectName_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_Association, 
     "UniversalObjectName" -> universalObjectName_]]["ReducedObjects"] := 
  Module[{objectFunction, limitObjects}, 
    objectFunction = Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, 
               quiverObjectEquivalences], categoryObjectEquivalences]]] -> reduceObjectsWithDuplicates[
           Values[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
               categoryObjectEquivalences]]], objectEquivalences]]], 
       Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[objectMappings], 
            quiverObjectEquivalences], categoryObjectEquivalences] -> reduceObjectsWithDuplicates[Values[objectMappings], 
           objectEquivalences]]]]; limitObjects = {limitObjectName}; 
     (Module[{object = #1}, limitObjects = Append[limitObjects, object /. Normal[objectFunction]]] & ) /@ 
      reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences]; 
     DeleteDuplicates[limitObjects]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory" && SymbolName[abstractFunctor] === "AbstractFunctor"
AbstractLimit[Association["Functor" -> (abstractFunctor_)[Association["ArrowMappings" -> arrowMappings_Association, 
        "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
           "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
           "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
             Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
              "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
        "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
        "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
        "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
        "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]], 
     "LimitMorphismNames" -> limitMorphismNames_Association, "LimitObjectName" -> limitObjectName_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_Association, 
     "UniversalObjectName" -> universalObjectName_]]["ReducedObjectCount"] := 
  Module[{objectFunction, limitObjects}, 
    objectFunction = Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, 
               quiverObjectEquivalences], categoryObjectEquivalences]]] -> reduceObjectsWithDuplicates[
           Values[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
               categoryObjectEquivalences]]], objectEquivalences]]], 
       Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[objectMappings], 
            quiverObjectEquivalences], categoryObjectEquivalences] -> reduceObjectsWithDuplicates[Values[objectMappings], 
           objectEquivalences]]]]; limitObjects = {limitObjectName}; 
     (Module[{object = #1}, limitObjects = Append[limitObjects, object /. Normal[objectFunction]]] & ) /@ 
      reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences]; 
     Length[DeleteDuplicates[limitObjects]]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory" && SymbolName[abstractFunctor] === "AbstractFunctor"
AbstractLimit[Association["Functor" -> (abstractFunctor_)[Association["ArrowMappings" -> arrowMappings_Association, 
        "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
           "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
           "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
             Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
              "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
        "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
        "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
        "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
        "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]], 
     "LimitMorphismNames" -> limitMorphismNames_Association, "LimitObjectName" -> limitObjectName_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_Association, 
     "UniversalObjectName" -> universalObjectName_]]["MorphismAssociation"] := 
  Module[{morphismAssociation, compositions, objectFunction, objectListWithDuplicates, arrowListWithDuplicates, 
     domainMorphismList, domainCompositions, imageMorphismList, imageCompositions, morphismFunction, 
     limitMorphismAssociation}, morphismAssociation = Association[Select[Normal[arrows], 
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
            DirectedEdge[#1, #1]]]] & ) /@ objects; objectFunction = Join[Association[(#1 -> #1 & ) /@ objects], 
       objectMappings]; objectListWithDuplicates = objects /. Normal[objectMappings]; 
     arrowListWithDuplicates = If[covariant === True, Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], 
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
         First /@ imageMorphismList]]; limitMorphismAssociation = {}; 
     (Module[{morphism = #1}, limitMorphismAssociation = Join[limitMorphismAssociation, 
           {limitMorphismNames[First[Last[morphism]]] -> DirectedEdge[limitObjectName, First[Last[morphism]] /. Normal[
                objectFunction]], limitMorphismNames[Last[Last[morphism]]] -> DirectedEdge[limitObjectName, 
              Last[Last[morphism]] /. Normal[objectFunction]]}]; limitMorphismAssociation = 
          Append[limitMorphismAssociation, (First[morphism] /. Normal[morphismFunction]) -> 
            If[covariant === True, DirectedEdge[First[Last[morphism]] /. Normal[objectFunction], 
              Last[Last[morphism]] /. Normal[objectFunction]], DirectedEdge[Last[Last[morphism]] /. Normal[
                objectFunction], First[Last[morphism]] /. Normal[objectFunction]]]]; 
         If[(First[morphism] /. Normal[morphismFunction]) =!= newIdentitySymbol[First[Last[morphism]] /. 
             Normal[objectFunction]], limitMorphismAssociation = Append[limitMorphismAssociation, 
            If[covariant === True, newCompositionSymbol[First[morphism] /. Normal[morphismFunction], limitMorphismNames[
                First[Last[morphism]]]] -> DirectedEdge[limitObjectName, Last[Last[morphism]] /. Normal[objectFunction]], 
             newCompositionSymbol[First[morphism] /. Normal[morphismFunction], limitMorphismNames[
                Last[Last[morphism]]]] -> DirectedEdge[limitObjectName, First[Last[morphism]] /. 
                Normal[objectFunction]]]]]] & ) /@ Normal[morphismAssociation]; 
     Association[Append[DeleteDuplicates[limitMorphismAssociation], newIdentitySymbol[limitObjectName] -> 
        DirectedEdge[limitObjectName, limitObjectName]]]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory" && SymbolName[abstractFunctor] === "AbstractFunctor"
AbstractLimit[Association["Functor" -> (abstractFunctor_)[Association["ArrowMappings" -> arrowMappings_Association, 
        "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
           "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
           "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
             Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
              "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
        "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
        "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
        "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
        "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]], 
     "LimitMorphismNames" -> limitMorphismNames_Association, "LimitObjectName" -> limitObjectName_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_Association, 
     "UniversalObjectName" -> universalObjectName_]]["MorphismNames"] := 
  Module[{morphismAssociation, compositions, objectFunction, objectListWithDuplicates, arrowListWithDuplicates, 
     domainMorphismList, domainCompositions, imageMorphismList, imageCompositions, morphismFunction, 
     limitMorphismAssociation}, morphismAssociation = Association[Select[Normal[arrows], 
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
            DirectedEdge[#1, #1]]]] & ) /@ objects; objectFunction = Join[Association[(#1 -> #1 & ) /@ objects], 
       objectMappings]; objectListWithDuplicates = objects /. Normal[objectMappings]; 
     arrowListWithDuplicates = If[covariant === True, Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], 
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
         First /@ imageMorphismList]]; limitMorphismAssociation = {}; 
     (Module[{morphism = #1}, limitMorphismAssociation = Join[limitMorphismAssociation, 
           {limitMorphismNames[First[Last[morphism]]] -> DirectedEdge[limitObjectName, First[Last[morphism]] /. Normal[
                objectFunction]], limitMorphismNames[Last[Last[morphism]]] -> DirectedEdge[limitObjectName, 
              Last[Last[morphism]] /. Normal[objectFunction]]}]; limitMorphismAssociation = 
          Append[limitMorphismAssociation, (First[morphism] /. Normal[morphismFunction]) -> 
            If[covariant === True, DirectedEdge[First[Last[morphism]] /. Normal[objectFunction], 
              Last[Last[morphism]] /. Normal[objectFunction]], DirectedEdge[Last[Last[morphism]] /. Normal[
                objectFunction], First[Last[morphism]] /. Normal[objectFunction]]]]; 
         If[(First[morphism] /. Normal[morphismFunction]) =!= newIdentitySymbol[First[Last[morphism]] /. 
             Normal[objectFunction]], limitMorphismAssociation = Append[limitMorphismAssociation, 
            If[covariant === True, newCompositionSymbol[First[morphism] /. Normal[morphismFunction], limitMorphismNames[
                First[Last[morphism]]]] -> DirectedEdge[limitObjectName, Last[Last[morphism]] /. Normal[objectFunction]], 
             newCompositionSymbol[First[morphism] /. Normal[morphismFunction], limitMorphismNames[
                Last[Last[morphism]]]] -> DirectedEdge[limitObjectName, First[Last[morphism]] /. 
                Normal[objectFunction]]]]]] & ) /@ Normal[morphismAssociation]; 
     First /@ Normal[Association[Append[DeleteDuplicates[limitMorphismAssociation], newIdentitySymbol[limitObjectName] -> 
          DirectedEdge[limitObjectName, limitObjectName]]]]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory" && SymbolName[abstractFunctor] === "AbstractFunctor"
AbstractLimit[Association["Functor" -> (abstractFunctor_)[Association["ArrowMappings" -> arrowMappings_Association, 
        "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
           "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
           "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
             Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
              "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
        "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
        "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
        "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
        "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]], 
     "LimitMorphismNames" -> limitMorphismNames_Association, "LimitObjectName" -> limitObjectName_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_Association, 
     "UniversalObjectName" -> universalObjectName_]]["MorphismEdges"] := 
  Module[{morphismAssociation, compositions, objectFunction, objectListWithDuplicates, arrowListWithDuplicates, 
     domainMorphismList, domainCompositions, imageMorphismList, imageCompositions, morphismFunction, 
     limitMorphismAssociation}, morphismAssociation = Association[Select[Normal[arrows], 
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
            DirectedEdge[#1, #1]]]] & ) /@ objects; objectFunction = Join[Association[(#1 -> #1 & ) /@ objects], 
       objectMappings]; objectListWithDuplicates = objects /. Normal[objectMappings]; 
     arrowListWithDuplicates = If[covariant === True, Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], 
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
         First /@ imageMorphismList]]; limitMorphismAssociation = {}; 
     (Module[{morphism = #1}, limitMorphismAssociation = Join[limitMorphismAssociation, 
           {limitMorphismNames[First[Last[morphism]]] -> DirectedEdge[limitObjectName, First[Last[morphism]] /. Normal[
                objectFunction]], limitMorphismNames[Last[Last[morphism]]] -> DirectedEdge[limitObjectName, 
              Last[Last[morphism]] /. Normal[objectFunction]]}]; limitMorphismAssociation = 
          Append[limitMorphismAssociation, (First[morphism] /. Normal[morphismFunction]) -> 
            If[covariant === True, DirectedEdge[First[Last[morphism]] /. Normal[objectFunction], 
              Last[Last[morphism]] /. Normal[objectFunction]], DirectedEdge[Last[Last[morphism]] /. Normal[
                objectFunction], First[Last[morphism]] /. Normal[objectFunction]]]]; 
         If[(First[morphism] /. Normal[morphismFunction]) =!= newIdentitySymbol[First[Last[morphism]] /. 
             Normal[objectFunction]], limitMorphismAssociation = Append[limitMorphismAssociation, 
            If[covariant === True, newCompositionSymbol[First[morphism] /. Normal[morphismFunction], limitMorphismNames[
                First[Last[morphism]]]] -> DirectedEdge[limitObjectName, Last[Last[morphism]] /. Normal[objectFunction]], 
             newCompositionSymbol[First[morphism] /. Normal[morphismFunction], limitMorphismNames[
                Last[Last[morphism]]]] -> DirectedEdge[limitObjectName, First[Last[morphism]] /. 
                Normal[objectFunction]]]]]] & ) /@ Normal[morphismAssociation]; (DirectedEdge @@ Last[#1] & ) /@ 
      Normal[Association[Append[DeleteDuplicates[limitMorphismAssociation], newIdentitySymbol[limitObjectName] -> 
          DirectedEdge[limitObjectName, limitObjectName]]]]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory" && SymbolName[abstractFunctor] === "AbstractFunctor"
AbstractLimit[Association["Functor" -> (abstractFunctor_)[Association["ArrowMappings" -> arrowMappings_Association, 
        "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
           "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
           "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
             Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
              "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
        "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
        "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
        "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
        "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]], 
     "LimitMorphismNames" -> limitMorphismNames_Association, "LimitObjectName" -> limitObjectName_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_Association, 
     "UniversalObjectName" -> universalObjectName_]]["MorphismCount"] := 
  Module[{morphismAssociation, compositions, objectFunction, objectListWithDuplicates, arrowListWithDuplicates, 
     domainMorphismList, domainCompositions, imageMorphismList, imageCompositions, morphismFunction, 
     limitMorphismAssociation}, morphismAssociation = Association[Select[Normal[arrows], 
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
            DirectedEdge[#1, #1]]]] & ) /@ objects; objectFunction = Join[Association[(#1 -> #1 & ) /@ objects], 
       objectMappings]; objectListWithDuplicates = objects /. Normal[objectMappings]; 
     arrowListWithDuplicates = If[covariant === True, Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], 
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
         First /@ imageMorphismList]]; limitMorphismAssociation = {}; 
     (Module[{morphism = #1}, limitMorphismAssociation = Join[limitMorphismAssociation, 
           {limitMorphismNames[First[Last[morphism]]] -> DirectedEdge[limitObjectName, First[Last[morphism]] /. Normal[
                objectFunction]], limitMorphismNames[Last[Last[morphism]]] -> DirectedEdge[limitObjectName, 
              Last[Last[morphism]] /. Normal[objectFunction]]}]; limitMorphismAssociation = 
          Append[limitMorphismAssociation, (First[morphism] /. Normal[morphismFunction]) -> 
            If[covariant === True, DirectedEdge[First[Last[morphism]] /. Normal[objectFunction], 
              Last[Last[morphism]] /. Normal[objectFunction]], DirectedEdge[Last[Last[morphism]] /. Normal[
                objectFunction], First[Last[morphism]] /. Normal[objectFunction]]]]; 
         If[(First[morphism] /. Normal[morphismFunction]) =!= newIdentitySymbol[First[Last[morphism]] /. 
             Normal[objectFunction]], limitMorphismAssociation = Append[limitMorphismAssociation, 
            If[covariant === True, newCompositionSymbol[First[morphism] /. Normal[morphismFunction], limitMorphismNames[
                First[Last[morphism]]]] -> DirectedEdge[limitObjectName, Last[Last[morphism]] /. Normal[objectFunction]], 
             newCompositionSymbol[First[morphism] /. Normal[morphismFunction], limitMorphismNames[
                Last[Last[morphism]]]] -> DirectedEdge[limitObjectName, First[Last[morphism]] /. 
                Normal[objectFunction]]]]]] & ) /@ Normal[morphismAssociation]; 
     Length[Normal[Association[Append[DeleteDuplicates[limitMorphismAssociation], newIdentitySymbol[limitObjectName] -> 
          DirectedEdge[limitObjectName, limitObjectName]]]]]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory" && SymbolName[abstractFunctor] === "AbstractFunctor"
AbstractLimit[Association["Functor" -> (abstractFunctor_)[Association["ArrowMappings" -> arrowMappings_Association, 
        "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
           "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
           "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
             Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
              "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
        "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
        "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
        "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
        "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]], 
     "LimitMorphismNames" -> limitMorphismNames_Association, "LimitObjectName" -> limitObjectName_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_Association, 
     "UniversalObjectName" -> universalObjectName_]]["ReducedMorphismAssociation"] := 
  Module[{morphismAssociation, compositions, objectFunction, objectListWithDuplicates, arrowListWithDuplicates, 
     domainMorphismList, domainCompositions, imageMorphismList, imageCompositions, morphismFunction, 
     limitMorphismAssociation, limitEquations}, 
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
     objectFunction = Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, 
               quiverObjectEquivalences], categoryObjectEquivalences]]] -> reduceObjectsWithDuplicates[
           Values[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
               categoryObjectEquivalences]]], objectEquivalences]]], 
       Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[objectMappings], 
            quiverObjectEquivalences], categoryObjectEquivalences] -> reduceObjectsWithDuplicates[Values[objectMappings], 
           objectEquivalences]]]]; objectListWithDuplicates = objects /. Normal[objectMappings]; 
     arrowListWithDuplicates = If[covariant === True, Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], 
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
              newCompositionSymbol /. Normal[arrowMappings], morphismEquivalences]], 
         DeleteDuplicates[Join[categoryMorphismEquivalences /. compositionSymbol -> newCompositionSymbol /. 
             Normal[arrowMappings] /. {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
              newCompositionSymbol[z, newCompositionSymbol[y, x]], newCompositionSymbol[newCompositionSymbol[x_, y_], 
               z_] :> newCompositionSymbol[newCompositionSymbol[z, y], x], newCompositionSymbol[x_, y_] :> 
              newCompositionSymbol[y, x]}, morphismEquivalences]]]], DeleteDuplicates[
        Join[categoryObjectEquivalences /. Normal[objectMappings], objectEquivalences]]]; 
     morphismFunction = Association[Thread[First /@ domainMorphismList -> First /@ imageMorphismList]]; 
     limitMorphismAssociation = {}; limitEquations = {}; 
     (Module[{morphism = #1}, limitMorphismAssociation = Join[limitMorphismAssociation, 
           {limitMorphismNames[First[Last[morphism]]] -> DirectedEdge[limitObjectName, First[Last[morphism]] /. Normal[
                objectFunction]], limitMorphismNames[Last[Last[morphism]]] -> DirectedEdge[limitObjectName, 
              Last[Last[morphism]] /. Normal[objectFunction]]}]; limitMorphismAssociation = 
          Append[limitMorphismAssociation, (First[morphism] /. Normal[morphismFunction]) -> 
            If[covariant === True, DirectedEdge[First[Last[morphism]] /. Normal[objectFunction], 
              Last[Last[morphism]] /. Normal[objectFunction]], DirectedEdge[Last[Last[morphism]] /. Normal[
                objectFunction], First[Last[morphism]] /. Normal[objectFunction]]]]; 
         If[(First[morphism] /. Normal[morphismFunction]) =!= newIdentitySymbol[First[Last[morphism]] /. 
             Normal[objectFunction]], limitMorphismAssociation = Append[limitMorphismAssociation, 
             If[covariant === True, newCompositionSymbol[First[morphism] /. Normal[morphismFunction], 
                limitMorphismNames[First[Last[morphism]]]] -> DirectedEdge[limitObjectName, Last[Last[morphism]] /. 
                 Normal[objectFunction]], newCompositionSymbol[First[morphism] /. Normal[morphismFunction], 
                limitMorphismNames[Last[Last[morphism]]]] -> DirectedEdge[limitObjectName, First[Last[morphism]] /. 
                 Normal[objectFunction]]]]; limitEquations = Append[limitEquations, If[covariant === True, 
              limitMorphismNames[Last[Last[morphism]]] == newCompositionSymbol[First[morphism] /. 
                 Normal[morphismFunction], limitMorphismNames[First[Last[morphism]]]], limitMorphismNames[
                First[Last[morphism]]] == newCompositionSymbol[First[morphism] /. Normal[morphismFunction], 
                limitMorphismNames[Last[Last[morphism]]]]]]]] & ) /@ 
      Normal[reduceArrowsFinal[reduceArrowsInitial[morphismAssociation, categoryMorphismEquivalences], 
        categoryObjectEquivalences]]; limitMorphismAssociation = 
      Association[Append[DeleteDuplicates[limitMorphismAssociation], newIdentitySymbol[limitObjectName] -> 
         DirectedEdge[limitObjectName, limitObjectName]]]; reduceArrowsInitial[limitMorphismAssociation, 
      limitEquations]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === 
     "AbstractCategory" && SymbolName[abstractFunctor] === "AbstractFunctor"
AbstractLimit[Association["Functor" -> (abstractFunctor_)[Association["ArrowMappings" -> arrowMappings_Association, 
        "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
           "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
           "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
             Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
              "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
        "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
        "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
        "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
        "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]], 
     "LimitMorphismNames" -> limitMorphismNames_Association, "LimitObjectName" -> limitObjectName_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_Association, 
     "UniversalObjectName" -> universalObjectName_]]["ReducedMorphismNames"] := 
  Module[{morphismAssociation, compositions, objectFunction, objectListWithDuplicates, arrowListWithDuplicates, 
     domainMorphismList, domainCompositions, imageMorphismList, imageCompositions, morphismFunction, 
     limitMorphismAssociation, limitEquations}, 
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
     objectFunction = Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, 
               quiverObjectEquivalences], categoryObjectEquivalences]]] -> reduceObjectsWithDuplicates[
           Values[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
               categoryObjectEquivalences]]], objectEquivalences]]], 
       Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[objectMappings], 
            quiverObjectEquivalences], categoryObjectEquivalences] -> reduceObjectsWithDuplicates[Values[objectMappings], 
           objectEquivalences]]]]; objectListWithDuplicates = objects /. Normal[objectMappings]; 
     arrowListWithDuplicates = If[covariant === True, Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], 
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
              newCompositionSymbol /. Normal[arrowMappings], morphismEquivalences]], 
         DeleteDuplicates[Join[categoryMorphismEquivalences /. compositionSymbol -> newCompositionSymbol /. 
             Normal[arrowMappings] /. {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
              newCompositionSymbol[z, newCompositionSymbol[y, x]], newCompositionSymbol[newCompositionSymbol[x_, y_], 
               z_] :> newCompositionSymbol[newCompositionSymbol[z, y], x], newCompositionSymbol[x_, y_] :> 
              newCompositionSymbol[y, x]}, morphismEquivalences]]]], DeleteDuplicates[
        Join[categoryObjectEquivalences /. Normal[objectMappings], objectEquivalences]]]; 
     morphismFunction = Association[Thread[First /@ domainMorphismList -> First /@ imageMorphismList]]; 
     limitMorphismAssociation = {}; limitEquations = {}; 
     (Module[{morphism = #1}, limitMorphismAssociation = Join[limitMorphismAssociation, 
           {limitMorphismNames[First[Last[morphism]]] -> DirectedEdge[limitObjectName, First[Last[morphism]] /. Normal[
                objectFunction]], limitMorphismNames[Last[Last[morphism]]] -> DirectedEdge[limitObjectName, 
              Last[Last[morphism]] /. Normal[objectFunction]]}]; limitMorphismAssociation = 
          Append[limitMorphismAssociation, (First[morphism] /. Normal[morphismFunction]) -> 
            If[covariant === True, DirectedEdge[First[Last[morphism]] /. Normal[objectFunction], 
              Last[Last[morphism]] /. Normal[objectFunction]], DirectedEdge[Last[Last[morphism]] /. Normal[
                objectFunction], First[Last[morphism]] /. Normal[objectFunction]]]]; 
         If[(First[morphism] /. Normal[morphismFunction]) =!= newIdentitySymbol[First[Last[morphism]] /. 
             Normal[objectFunction]], limitMorphismAssociation = Append[limitMorphismAssociation, 
             If[covariant === True, newCompositionSymbol[First[morphism] /. Normal[morphismFunction], 
                limitMorphismNames[First[Last[morphism]]]] -> DirectedEdge[limitObjectName, Last[Last[morphism]] /. 
                 Normal[objectFunction]], newCompositionSymbol[First[morphism] /. Normal[morphismFunction], 
                limitMorphismNames[Last[Last[morphism]]]] -> DirectedEdge[limitObjectName, First[Last[morphism]] /. 
                 Normal[objectFunction]]]]; limitEquations = Append[limitEquations, If[covariant === True, 
              limitMorphismNames[Last[Last[morphism]]] == newCompositionSymbol[First[morphism] /. 
                 Normal[morphismFunction], limitMorphismNames[First[Last[morphism]]]], limitMorphismNames[
                First[Last[morphism]]] == newCompositionSymbol[First[morphism] /. Normal[morphismFunction], 
                limitMorphismNames[Last[Last[morphism]]]]]]]] & ) /@ 
      Normal[reduceArrowsFinal[reduceArrowsInitial[morphismAssociation, categoryMorphismEquivalences], 
        categoryObjectEquivalences]]; limitMorphismAssociation = 
      Association[Append[DeleteDuplicates[limitMorphismAssociation], newIdentitySymbol[limitObjectName] -> 
         DirectedEdge[limitObjectName, limitObjectName]]]; 
     First /@ Normal[reduceArrowsInitial[limitMorphismAssociation, limitEquations]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory" && 
    SymbolName[abstractFunctor] === "AbstractFunctor"
AbstractLimit[Association["Functor" -> (abstractFunctor_)[Association["ArrowMappings" -> arrowMappings_Association, 
        "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
           "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
           "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
             Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
              "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
        "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
        "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
        "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
        "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]], 
     "LimitMorphismNames" -> limitMorphismNames_Association, "LimitObjectName" -> limitObjectName_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_Association, 
     "UniversalObjectName" -> universalObjectName_]]["ReducedMorphismEdges"] := 
  Module[{morphismAssociation, compositions, objectFunction, objectListWithDuplicates, arrowListWithDuplicates, 
     domainMorphismList, domainCompositions, imageMorphismList, imageCompositions, morphismFunction, 
     limitMorphismAssociation, limitEquations}, 
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
     objectFunction = Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, 
               quiverObjectEquivalences], categoryObjectEquivalences]]] -> reduceObjectsWithDuplicates[
           Values[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
               categoryObjectEquivalences]]], objectEquivalences]]], 
       Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[objectMappings], 
            quiverObjectEquivalences], categoryObjectEquivalences] -> reduceObjectsWithDuplicates[Values[objectMappings], 
           objectEquivalences]]]]; objectListWithDuplicates = objects /. Normal[objectMappings]; 
     arrowListWithDuplicates = If[covariant === True, Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], 
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
              newCompositionSymbol /. Normal[arrowMappings], morphismEquivalences]], 
         DeleteDuplicates[Join[categoryMorphismEquivalences /. compositionSymbol -> newCompositionSymbol /. 
             Normal[arrowMappings] /. {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
              newCompositionSymbol[z, newCompositionSymbol[y, x]], newCompositionSymbol[newCompositionSymbol[x_, y_], 
               z_] :> newCompositionSymbol[newCompositionSymbol[z, y], x], newCompositionSymbol[x_, y_] :> 
              newCompositionSymbol[y, x]}, morphismEquivalences]]]], DeleteDuplicates[
        Join[categoryObjectEquivalences /. Normal[objectMappings], objectEquivalences]]]; 
     morphismFunction = Association[Thread[First /@ domainMorphismList -> First /@ imageMorphismList]]; 
     limitMorphismAssociation = {}; limitEquations = {}; 
     (Module[{morphism = #1}, limitMorphismAssociation = Join[limitMorphismAssociation, 
           {limitMorphismNames[First[Last[morphism]]] -> DirectedEdge[limitObjectName, First[Last[morphism]] /. Normal[
                objectFunction]], limitMorphismNames[Last[Last[morphism]]] -> DirectedEdge[limitObjectName, 
              Last[Last[morphism]] /. Normal[objectFunction]]}]; limitMorphismAssociation = 
          Append[limitMorphismAssociation, (First[morphism] /. Normal[morphismFunction]) -> 
            If[covariant === True, DirectedEdge[First[Last[morphism]] /. Normal[objectFunction], 
              Last[Last[morphism]] /. Normal[objectFunction]], DirectedEdge[Last[Last[morphism]] /. Normal[
                objectFunction], First[Last[morphism]] /. Normal[objectFunction]]]]; 
         If[(First[morphism] /. Normal[morphismFunction]) =!= newIdentitySymbol[First[Last[morphism]] /. 
             Normal[objectFunction]], limitMorphismAssociation = Append[limitMorphismAssociation, 
             If[covariant === True, newCompositionSymbol[First[morphism] /. Normal[morphismFunction], 
                limitMorphismNames[First[Last[morphism]]]] -> DirectedEdge[limitObjectName, Last[Last[morphism]] /. 
                 Normal[objectFunction]], newCompositionSymbol[First[morphism] /. Normal[morphismFunction], 
                limitMorphismNames[Last[Last[morphism]]]] -> DirectedEdge[limitObjectName, First[Last[morphism]] /. 
                 Normal[objectFunction]]]]; limitEquations = Append[limitEquations, If[covariant === True, 
              limitMorphismNames[Last[Last[morphism]]] == newCompositionSymbol[First[morphism] /. 
                 Normal[morphismFunction], limitMorphismNames[First[Last[morphism]]]], limitMorphismNames[
                First[Last[morphism]]] == newCompositionSymbol[First[morphism] /. Normal[morphismFunction], 
                limitMorphismNames[Last[Last[morphism]]]]]]]] & ) /@ 
      Normal[reduceArrowsFinal[reduceArrowsInitial[morphismAssociation, categoryMorphismEquivalences], 
        categoryObjectEquivalences]]; limitMorphismAssociation = 
      Association[Append[DeleteDuplicates[limitMorphismAssociation], newIdentitySymbol[limitObjectName] -> 
         DirectedEdge[limitObjectName, limitObjectName]]]; (DirectedEdge @@ Last[#1] & ) /@ 
      Normal[reduceArrowsInitial[limitMorphismAssociation, limitEquations]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory" && 
    SymbolName[abstractFunctor] === "AbstractFunctor"
AbstractLimit[Association["Functor" -> (abstractFunctor_)[Association["ArrowMappings" -> arrowMappings_Association, 
        "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
           "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
           "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
             Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
              "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
        "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
        "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
        "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
        "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]], 
     "LimitMorphismNames" -> limitMorphismNames_Association, "LimitObjectName" -> limitObjectName_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_Association, 
     "UniversalObjectName" -> universalObjectName_]]["ReducedMorphismCount"] := 
  Module[{morphismAssociation, compositions, objectFunction, objectListWithDuplicates, arrowListWithDuplicates, 
     domainMorphismList, domainCompositions, imageMorphismList, imageCompositions, morphismFunction, 
     limitMorphismAssociation, limitEquations}, 
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
     objectFunction = Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, 
               quiverObjectEquivalences], categoryObjectEquivalences]]] -> reduceObjectsWithDuplicates[
           Values[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
               categoryObjectEquivalences]]], objectEquivalences]]], 
       Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[objectMappings], 
            quiverObjectEquivalences], categoryObjectEquivalences] -> reduceObjectsWithDuplicates[Values[objectMappings], 
           objectEquivalences]]]]; objectListWithDuplicates = objects /. Normal[objectMappings]; 
     arrowListWithDuplicates = If[covariant === True, Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], 
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
              newCompositionSymbol /. Normal[arrowMappings], morphismEquivalences]], 
         DeleteDuplicates[Join[categoryMorphismEquivalences /. compositionSymbol -> newCompositionSymbol /. 
             Normal[arrowMappings] /. {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
              newCompositionSymbol[z, newCompositionSymbol[y, x]], newCompositionSymbol[newCompositionSymbol[x_, y_], 
               z_] :> newCompositionSymbol[newCompositionSymbol[z, y], x], newCompositionSymbol[x_, y_] :> 
              newCompositionSymbol[y, x]}, morphismEquivalences]]]], DeleteDuplicates[
        Join[categoryObjectEquivalences /. Normal[objectMappings], objectEquivalences]]]; 
     morphismFunction = Association[Thread[First /@ domainMorphismList -> First /@ imageMorphismList]]; 
     limitMorphismAssociation = {}; limitEquations = {}; 
     (Module[{morphism = #1}, limitMorphismAssociation = Join[limitMorphismAssociation, 
           {limitMorphismNames[First[Last[morphism]]] -> DirectedEdge[limitObjectName, First[Last[morphism]] /. Normal[
                objectFunction]], limitMorphismNames[Last[Last[morphism]]] -> DirectedEdge[limitObjectName, 
              Last[Last[morphism]] /. Normal[objectFunction]]}]; limitMorphismAssociation = 
          Append[limitMorphismAssociation, (First[morphism] /. Normal[morphismFunction]) -> 
            If[covariant === True, DirectedEdge[First[Last[morphism]] /. Normal[objectFunction], 
              Last[Last[morphism]] /. Normal[objectFunction]], DirectedEdge[Last[Last[morphism]] /. Normal[
                objectFunction], First[Last[morphism]] /. Normal[objectFunction]]]]; 
         If[(First[morphism] /. Normal[morphismFunction]) =!= newIdentitySymbol[First[Last[morphism]] /. 
             Normal[objectFunction]], limitMorphismAssociation = Append[limitMorphismAssociation, 
             If[covariant === True, newCompositionSymbol[First[morphism] /. Normal[morphismFunction], 
                limitMorphismNames[First[Last[morphism]]]] -> DirectedEdge[limitObjectName, Last[Last[morphism]] /. 
                 Normal[objectFunction]], newCompositionSymbol[First[morphism] /. Normal[morphismFunction], 
                limitMorphismNames[Last[Last[morphism]]]] -> DirectedEdge[limitObjectName, First[Last[morphism]] /. 
                 Normal[objectFunction]]]]; limitEquations = Append[limitEquations, If[covariant === True, 
              limitMorphismNames[Last[Last[morphism]]] == newCompositionSymbol[First[morphism] /. 
                 Normal[morphismFunction], limitMorphismNames[First[Last[morphism]]]], limitMorphismNames[
                First[Last[morphism]]] === newCompositionSymbol[First[morphism] /. Normal[morphismFunction], 
                limitMorphismNames[Last[Last[morphism]]]]]]]] & ) /@ 
      Normal[reduceArrowsFinal[reduceArrowsInitial[morphismAssociation, categoryMorphismEquivalences], 
        categoryObjectEquivalences]]; limitMorphismAssociation = 
      Association[Append[DeleteDuplicates[limitMorphismAssociation], newIdentitySymbol[limitObjectName] -> 
         DirectedEdge[limitObjectName, limitObjectName]]]; 
     Length[Normal[reduceArrowsInitial[limitMorphismAssociation, limitEquations]]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory" && 
    SymbolName[abstractFunctor] === "AbstractFunctor"
AbstractLimit[Association["Functor" -> (abstractFunctor_)[Association["ArrowMappings" -> arrowMappings_Association, 
        "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
           "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
           "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
             Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
              "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
        "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
        "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
        "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
        "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]], 
     "LimitMorphismNames" -> limitMorphismNames_Association, "LimitObjectName" -> limitObjectName_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_Association, 
     "UniversalObjectName" -> universalObjectName_]]["UniversalObjects"] := 
  Module[{objectFunction, limitObjects}, objectFunction = Join[Association[(#1 -> #1 & ) /@ objects], objectMappings]; 
     limitObjects = {limitObjectName, Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]}; 
     (Module[{object = #1}, limitObjects = Append[limitObjects, object /. Normal[objectFunction]]] & ) /@ objects; 
     DeleteDuplicates[limitObjects]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory" && SymbolName[abstractFunctor] === "AbstractFunctor"
AbstractLimit[Association["Functor" -> (abstractFunctor_)[Association["ArrowMappings" -> arrowMappings_Association, 
        "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
           "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
           "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
             Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
              "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
        "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
        "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
        "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
        "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]], 
     "LimitMorphismNames" -> limitMorphismNames_Association, "LimitObjectName" -> limitObjectName_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_Association, 
     "UniversalObjectName" -> universalObjectName_]]["UniversalObjectCount"] := 
  Module[{objectFunction, limitObjects}, objectFunction = Join[Association[(#1 -> #1 & ) /@ objects], objectMappings]; 
     limitObjects = {limitObjectName, Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]}; 
     (Module[{object = #1}, limitObjects = Append[limitObjects, object /. Normal[objectFunction]]] & ) /@ objects; 
     Length[DeleteDuplicates[limitObjects]]] /; (SymbolName[abstractQuiver] === "AbstractQuiver" && 
     SymbolName[abstractCategory] === "AbstractCategory" && SymbolName[abstractFunctor] === "AbstractFunctor")*J
AbstractLimit[Association["Functor" -> (abstractFunctor_)[Association["ArrowMappings" -> arrowMappings_Association, 
        "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
           "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalecnes_List, 
           "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
             Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
              "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
        "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
        "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
        "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
        "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]], 
     "LimitMorphismNames" -> limitMorphismNames_Association, "LimitObjectName" -> limitObjectName_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_Association, 
     "UniversalObjectName" -> universalObjectName_]]["UniversalMorphismAssociation"] := 
  Module[{morphismAssociation, compositions, objectFunction, objectListWithDuplicates, arrowListWithDuplicates, 
     domainMorphismList, domainCompositions, imageMorphismList, imageCompositions, morphismFunction, 
     universalLimitMorphismAssociation}, 
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
            DirectedEdge[#1, #1]]]] & ) /@ objects; objectFunction = Join[Association[(#1 -> #1 & ) /@ objects], 
       objectMappings]; objectListWithDuplicates = objects /. Normal[objectMappings]; 
     arrowListWithDuplicates = If[covariant === True, Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], 
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
         First /@ imageMorphismList]]; universalLimitMorphismAssociation = 
      {Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> 
        DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], limitObjectName]}; 
     (Module[{morphism = #1}, universalLimitMorphismAssociation = Join[universalLimitMorphismAssociation, 
           {limitMorphismNames[First[Last[morphism]]] -> DirectedEdge[limitObjectName, First[Last[morphism]] /. Normal[
                objectFunction]], limitMorphismNames[Last[Last[morphism]]] -> DirectedEdge[limitObjectName, 
              Last[Last[morphism]] /. Normal[objectFunction]]}]; universalLimitMorphismAssociation = 
          Join[universalLimitMorphismAssociation, {Subscript["\[ForAll]", ToString[universalMorphismNames[
                First[Last[morphism]]], StandardForm]] -> DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, 
                StandardForm]], First[Last[morphism]] /. Normal[objectFunction]], 
            Subscript["\[ForAll]", ToString[universalMorphismNames[Last[Last[morphism]]], StandardForm]] -> 
             DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], Last[Last[morphism]] /. Normal[
                objectFunction]]}]; universalLimitMorphismAssociation = Join[universalLimitMorphismAssociation, 
           {compositionSymbol[limitMorphismNames[First[Last[morphism]]], uniqueMorphismName] -> 
             DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], First[Last[morphism]] /. Normal[
                objectFunction]], compositionSymbol[limitMorphismNames[Last[Last[morphism]]], uniqueMorphismName] -> 
             DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], Last[Last[morphism]] /. Normal[
                objectFunction]]}]; universalLimitMorphismAssociation = Append[universalLimitMorphismAssociation, 
           (First[morphism] /. Normal[morphismFunction]) -> If[covariant === True, DirectedEdge[
              First[Last[morphism]] /. Normal[objectFunction], Last[Last[morphism]] /. Normal[objectFunction]], 
             DirectedEdge[Last[Last[morphism]] /. Normal[objectFunction], First[Last[morphism]] /. Normal[
                objectFunction]]]]; If[(First[morphism] /. Normal[morphismFunction]) =!= 
           newIdentitySymbol[First[Last[morphism]] /. Normal[objectFunction]], 
          universalLimitMorphismAssociation = Append[universalLimitMorphismAssociation, If[covariant === True, 
              newCompositionSymbol[First[morphism] /. Normal[morphismFunction], limitMorphismNames[
                 First[Last[morphism]]]] -> DirectedEdge[limitObjectName, Last[Last[morphism]] /. 
                 Normal[objectFunction]], newCompositionSymbol[First[morphism] /. Normal[morphismFunction], 
                limitMorphismNames[Last[Last[morphism]]]] -> DirectedEdge[limitObjectName, First[Last[morphism]] /. 
                 Normal[objectFunction]]]]; universalLimitMorphismAssociation = Join[universalLimitMorphismAssociation, 
             {If[covariant === True, newCompositionSymbol[newCompositionSymbol[First[morphism] /. 
                   Normal[morphismFunction], limitMorphismNames[First[Last[morphism]]]], uniqueMorphismName] -> 
                DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], Last[Last[morphism]] /. 
                  Normal[objectFunction]], newCompositionSymbol[newCompositionSymbol[First[morphism] /. 
                   Normal[morphismFunction], limitMorphismNames[Last[Last[morphism]]]], uniqueMorphismName] -> 
                DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], First[Last[morphism]] /. 
                  Normal[objectFunction]]], If[covariant === True, newCompositionSymbol[First[morphism] /. 
                  Normal[morphismFunction], universalMorphismNames[First[Last[morphism]]]] -> DirectedEdge[
                 Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], Last[Last[morphism]] /. 
                  Normal[objectFunction]], newCompositionSymbol[First[morphism] /. Normal[morphismFunction], 
                 universalMorphismNames[Last[Last[morphism]]]] -> DirectedEdge[Subscript["\[ForAll]", ToString[
                   universalObjectName, StandardForm]], First[Last[morphism]] /. Normal[objectFunction]]]}]]] & ) /@ 
      Normal[morphismAssociation]; Association[Join[DeleteDuplicates[universalLimitMorphismAssociation], 
       {newIdentitySymbol[limitObjectName] -> DirectedEdge[limitObjectName, limitObjectName], 
        newIdentitySymbol[universalObjectName] -> DirectedEdge[Subscript["\[ForAll]", ToString[universalObjectName, 
            StandardForm]], Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]]]}]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory" && 
    SymbolName[abstractFunctor] === "AbstractFunctor"
AbstractLimit[Association["Functor" -> (abstractFunctor_)[Association["ArrowMappings" -> arrowMappings_Association, 
        "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
           "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
           "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
             Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
              "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
        "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
        "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
        "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
        "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]], 
     "LimitMorphismNames" -> limitMorphismNames_Association, "LimitObjectName" -> limitObjectName_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_Association, 
     "UniversalObjectName" -> universalObjectName_]]["LimitEquations"] := 
  Module[{morphismAssociation, compositions, objectFunction, objectListWithDuplicates, arrowListWithDuplicates, 
     domainMorphismList, domainCompositions, imageMorphismList, imageCompositions, morphismFunction, limitEquations}, 
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
            DirectedEdge[#1, #1]]]] & ) /@ objects; objectFunction = Join[Association[(#1 -> #1 & ) /@ objects], 
       objectMappings]; objectListWithDuplicates = objects /. Normal[objectMappings]; 
     arrowListWithDuplicates = If[covariant === True, Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], 
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
         First /@ imageMorphismList]]; limitEquations = {}; 
     (Module[{morphism = #1}, If[(First[morphism] /. Normal[morphismFunction]) =!= newIdentitySymbol[
           First[Last[morphism]] /. Normal[objectFunction]], limitEquations = Append[limitEquations, 
           If[covariant === True, limitMorphismNames[Last[Last[morphism]]] == newCompositionSymbol[
              First[morphism] /. Normal[morphismFunction], limitMorphismNames[First[Last[morphism]]]], 
            limitMorphismNames[First[Last[morphism]]] == newCompositionSymbol[First[morphism] /. Normal[
                morphismFunction], limitMorphismNames[Last[Last[morphism]]]]]]]] & ) /@ Normal[morphismAssociation]; 
     DeleteDuplicates[limitEquations]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory" && SymbolName[abstractFunctor] === "AbstractFunctor"
AbstractLimit[Association["Functor" -> (abstractFunctor_)[Association["ArrowMappings" -> arrowMappings_Association, 
        "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
           "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
           "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
             Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
              "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
        "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
        "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
        "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
        "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]], 
     "LimitMorphismNames" -> limitMorphismNames_Association, "LimitObjectName" -> limitObjectName_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_Association, 
     "UniversalObjectName" -> universalObjectName_]]["UniversalLimitEquations"] := 
  Module[{morphismAssociation, compositions, objectFunction, objectListWithDuplicates, arrowListWithDuplicates, 
     domainMorphismList, domainCompositions, imageMorphismList, imageCompositions, morphismFunction, 
     universalLimitEquations}, morphismAssociation = Association[Select[Normal[arrows], 
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
            DirectedEdge[#1, #1]]]] & ) /@ objects; objectFunction = Join[Association[(#1 -> #1 & ) /@ objects], 
       objectMappings]; objectListWithDuplicates = objects /. Normal[objectMappings]; 
     arrowListWithDuplicates = If[covariant === True, Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], 
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
         First /@ imageMorphismList]]; universalLimitEquations = {}; 
     (Module[{morphism = #1}, If[(First[morphism] /. Normal[morphismFunction]) =!= newIdentitySymbol[
           First[Last[morphism]] /. Normal[objectFunction]], universalLimitEquations = Append[universalLimitEquations, 
           If[covariant === True, limitMorphismNames[Last[Last[morphism]]] == newCompositionSymbol[
              First[morphism] /. Normal[morphismFunction], limitMorphismNames[First[Last[morphism]]]], 
            limitMorphismNames[First[Last[morphism]]] == newCompositionSymbol[First[morphism] /. Normal[
                morphismFunction], limitMorphismNames[Last[Last[morphism]]]]]]]] & ) /@ Normal[morphismAssociation]; 
     (Module[{morphism = #1}, If[(First[morphism] /. Normal[morphismFunction]) =!= newIdentitySymbol[
           First[Last[morphism]] /. Normal[objectFunction]], universalLimitEquations = Join[universalLimitEquations, 
           {If[covariant === True, ToExpression[StringJoin["HoldForm[ForAll[", ToString[{universalMorphismNames[
                  First[Last[morphism]]], universalMorphismNames[Last[Last[morphism]]]}, StandardForm], ",Implies[", 
               ToString[universalMorphismNames[Last[Last[morphism]]] == newCompositionSymbol[First[morphism] /. 
                   Normal[morphismFunction], universalMorphismNames[First[Last[morphism]]]], StandardForm], ",Exists[", 
               ToString[uniqueMorphismName, StandardForm], ",", ToString[universalMorphismNames[First[Last[morphism]]] == 
                 newCompositionSymbol[limitMorphismNames[First[Last[morphism]]], uniqueMorphismName], StandardForm], 
               "]]]]"]], ToExpression[StringJoin["HoldForm[ForAll[", ToString[{universalMorphismNames[
                  First[Last[morphism]]], universalMorphismNames[Last[Last[morphism]]]}, StandardForm], ",Implies[", 
               ToString[universalMorphismNames[First[Last[morphism]]] == newCompositionSymbol[First[morphism] /. 
                   Normal[morphismFunction], universalMorphismNames[Last[Last[morphism]]]], StandardForm], ",Exists[", 
               ToString[uniqueMorphismName, StandardForm], ",", ToString[universalMorphismNames[First[Last[morphism]]] == 
                 newCompositionSymbol[limitMorphismNames[First[Last[morphism]]], uniqueMorphismName], StandardForm], 
               "]]]]"]]], If[covariant === True, ToExpression[StringJoin["HoldForm[ForAll[", ToString[
                {universalMorphismNames[First[Last[morphism]]], universalMorphismNames[Last[Last[morphism]]]}, 
                StandardForm], ",Implies[", ToString[universalMorphismNames[Last[Last[morphism]]] == newCompositionSymbol[
                  First[morphism] /. Normal[morphismFunction], universalMorphismNames[First[Last[morphism]]]], 
                StandardForm], ",Exists[", ToString[uniqueMorphismName, StandardForm], ",", ToString[
                universalMorphismNames[Last[Last[morphism]]] == newCompositionSymbol[limitMorphismNames[
                   Last[Last[morphism]]], uniqueMorphismName], StandardForm], "]]]]"]], 
             ToExpression[StringJoin["HoldForm[ForAll[", ToString[{universalMorphismNames[First[Last[morphism]]], 
                 universalMorphismNames[Last[Last[morphism]]]}, StandardForm], ",Implies[", ToString[
                universalMorphismNames[First[Last[morphism]]] == newCompositionSymbol[First[morphism] /. 
                   Normal[morphismFunction], universalMorphismNames[Last[Last[morphism]]]], StandardForm], ",Exists[", 
               ToString[uniqueMorphismName, StandardForm], ",", ToString[universalMorphismNames[Last[Last[morphism]]] == 
                 newCompositionSymbol[limitMorphismNames[Last[Last[morphism]]], uniqueMorphismName], StandardForm], 
               "]]]]"]]]}]]] & ) /@ Normal[morphismAssociation]; DeleteDuplicates[universalLimitEquations]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory" && 
    SymbolName[abstractFunctor] === "AbstractFunctor"
AbstractLimit[Association["Functor" -> (abstractFunctor_)[Association["ArrowMappings" -> arrowMappings_Association, 
        "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
           "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
           "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
             Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
              "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
        "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
        "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
        "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
        "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]], 
     "LimitMorphismNames" -> limitMorphismNames_Association, "LimitObjectName" -> limitObjectName_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_Association, 
     "UniversalObjectName" -> universalObjectName_]]["FullLabeledGraph"] := 
  Module[{morphismAssociation, compositions, objectFunction, objectListWithDuplicates, arrowListWithDuplicates, 
     domainMorphismList, domainCompositions, imageMorphismList, imageCompositions, morphismFunction, limitObjects, 
     limitMorphismAssociation}, morphismAssociation = Association[Select[Normal[arrows], 
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
            DirectedEdge[#1, #1]]]] & ) /@ objects; objectFunction = Join[Association[(#1 -> #1 & ) /@ objects], 
       objectMappings]; objectListWithDuplicates = objects /. Normal[objectMappings]; 
     arrowListWithDuplicates = If[covariant === True, Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], 
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
         First /@ imageMorphismList]]; limitObjects = {limitObjectName}; limitMorphismAssociation = {}; 
     (Module[{morphism = #1}, limitObjects = Join[limitObjects, {First[Last[morphism]] /. Normal[objectFunction], 
            Last[Last[morphism]] /. Normal[objectFunction]}]; limitMorphismAssociation = Join[limitMorphismAssociation, 
           {limitMorphismNames[First[Last[morphism]]] -> DirectedEdge[limitObjectName, First[Last[morphism]] /. Normal[
                objectFunction]], limitMorphismNames[Last[Last[morphism]]] -> DirectedEdge[limitObjectName, 
              Last[Last[morphism]] /. Normal[objectFunction]]}]; limitMorphismAssociation = 
          Append[limitMorphismAssociation, (First[morphism] /. Normal[morphismFunction]) -> 
            If[covariant === True, DirectedEdge[First[Last[morphism]] /. Normal[objectFunction], 
              Last[Last[morphism]] /. Normal[objectFunction]], DirectedEdge[Last[Last[morphism]] /. Normal[
                objectFunction], First[Last[morphism]] /. Normal[objectFunction]]]]; 
         If[(First[morphism] /. Normal[morphismFunction]) =!= newIdentitySymbol[First[Last[morphism]] /. 
             Normal[objectFunction]], limitMorphismAssociation = Append[limitMorphismAssociation, 
            If[covariant === True, newCompositionSymbol[First[morphism] /. Normal[morphismFunction], limitMorphismNames[
                First[Last[morphism]]]] -> DirectedEdge[limitObjectName, Last[Last[morphism]] /. Normal[objectFunction]], 
             newCompositionSymbol[First[morphism] /. Normal[morphismFunction], limitMorphismNames[
                Last[Last[morphism]]]] -> DirectedEdge[limitObjectName, First[Last[morphism]] /. 
                Normal[objectFunction]]]]]] & ) /@ Normal[morphismAssociation]; 
     limitObjects = DeleteDuplicates[limitObjects]; limitMorphismAssociation = 
      Association[Append[DeleteDuplicates[limitMorphismAssociation], newIdentitySymbol[limitObjectName] -> 
         DirectedEdge[limitObjectName, limitObjectName]]]; EdgeTaggedGraph[limitObjects, 
      (Labeled[DirectedEdge @@ Last[#1], Placed[First[#1], 0.5]] & ) /@ Normal[limitMorphismAssociation], 
      VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], VertexLabels -> Placed["Name", Center], 
      VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
      EdgeStyle -> Directive[Black, Thick], GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory" && 
    SymbolName[abstractFunctor] === "AbstractFunctor"
AbstractLimit[Association["Functor" -> (abstractFunctor_)[Association["ArrowMappings" -> arrowMappings_Association, 
        "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
           "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
           "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
             Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
              "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
        "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
        "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
        "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
        "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]], 
     "LimitMorphismNames" -> limitMorphismNames_Association, "LimitObjectName" -> limitObjectName_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_Association, 
     "UniversalObjectName" -> universalObjectName_]]["FullUnlabeledGraph"] := 
  Module[{morphismAssociation, compositions, objectFunction, objectListWithDuplicates, arrowListWithDuplicates, 
     domainMorphismList, domainCompositions, imageMorphismList, imageCompositions, morphismFunction, limitObjects, 
     limitMorphismAssociation}, morphismAssociation = Association[Select[Normal[arrows], 
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
            DirectedEdge[#1, #1]]]] & ) /@ objects; objectFunction = Join[Association[(#1 -> #1 & ) /@ objects], 
       objectMappings]; objectListWithDuplicates = objects /. Normal[objectMappings]; 
     arrowListWithDuplicates = If[covariant === True, Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], 
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
         First /@ imageMorphismList]]; limitObjects = {limitObjectName}; limitMorphismAssociation = {}; 
     (Module[{morphism = #1}, limitObjects = Join[limitObjects, {First[Last[morphism]] /. Normal[objectFunction], 
            Last[Last[morphism]] /. Normal[objectFunction]}]; limitMorphismAssociation = Join[limitMorphismAssociation, 
           {limitMorphismNames[First[Last[morphism]]] -> DirectedEdge[limitObjectName, First[Last[morphism]] /. Normal[
                objectFunction]], limitMorphismNames[Last[Last[morphism]]] -> DirectedEdge[limitObjectName, 
              Last[Last[morphism]] /. Normal[objectFunction]]}]; limitMorphismAssociation = 
          Append[limitMorphismAssociation, (First[morphism] /. Normal[morphismFunction]) -> 
            If[covariant === True, DirectedEdge[First[Last[morphism]] /. Normal[objectFunction], 
              Last[Last[morphism]] /. Normal[objectFunction]], DirectedEdge[Last[Last[morphism]] /. Normal[
                objectFunction], First[Last[morphism]] /. Normal[objectFunction]]]]; 
         If[(First[morphism] /. Normal[morphismFunction]) =!= newIdentitySymbol[First[Last[morphism]] /. 
             Normal[objectFunction]], limitMorphismAssociation = Append[limitMorphismAssociation, 
            If[covariant === True, newCompositionSymbol[First[morphism] /. Normal[morphismFunction], limitMorphismNames[
                First[Last[morphism]]]] -> DirectedEdge[limitObjectName, Last[Last[morphism]] /. Normal[objectFunction]], 
             newCompositionSymbol[First[morphism] /. Normal[morphismFunction], limitMorphismNames[
                Last[Last[morphism]]]] -> DirectedEdge[limitObjectName, First[Last[morphism]] /. 
                Normal[objectFunction]]]]]] & ) /@ Normal[morphismAssociation]; 
     limitObjects = DeleteDuplicates[limitObjects]; limitMorphismAssociation = 
      Association[Append[DeleteDuplicates[limitMorphismAssociation], newIdentitySymbol[limitObjectName] -> 
         DirectedEdge[limitObjectName, limitObjectName]]]; EdgeTaggedGraph[limitObjects, 
      (DirectedEdge @@ Last[#1] & ) /@ Normal[limitMorphismAssociation], VertexSize -> 0.3, 
      VertexStyle -> Directive[Transparent, EdgeForm[None]], VertexLabels -> Placed["Name", Center], 
      VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
      EdgeStyle -> Directive[Black, Thick], GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory" && 
    SymbolName[abstractFunctor] === "AbstractFunctor"
AbstractLimit[Association["Functor" -> (abstractFunctor_)[Association["ArrowMappings" -> arrowMappings_Association, 
        "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
           "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
           "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
             Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
              "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
        "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
        "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
        "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
        "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]], 
     "LimitMorphismNames" -> limitMorphismNames_Association, "LimitObjectName" -> limitObjectName_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_Association, 
     "UniversalObjectName" -> universalObjectName_]]["ReducedLabeledGraph"] := 
  Module[{morphismAssociation, compositions, objectFunction, objectListWithDuplicates, arrowListWithDuplicates, 
     domainMorphismList, domainCompositions, imageMorphismList, imageCompositions, morphismFunction, limitObjects, 
     limitMorphismAssociation, limitEquations}, 
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
     objectFunction = Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, 
               quiverObjectEquivalences], categoryObjectEquivalences]]] -> reduceObjectsWithDuplicates[
           Values[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
               categoryObjectEquivalences]]], objectEquivalences]]], 
       Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[objectMappings], 
            quiverObjectEquivalences], categoryObjectEquivalences] -> reduceObjectsWithDuplicates[Values[objectMappings], 
           objectEquivalences]]]]; objectListWithDuplicates = objects /. Normal[objectMappings]; 
     arrowListWithDuplicates = If[covariant === True, Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], 
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
              newCompositionSymbol /. Normal[arrowMappings], morphismEquivalences]], 
         DeleteDuplicates[Join[categoryMorphismEquivalences /. compositionSymbol -> newCompositionSymbol /. 
             Normal[arrowMappings] /. {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
              newCompositionSymbol[z, newCompositionSymbol[y, x]], newCompositionSymbol[newCompositionSymbol[x_, y_], 
               z_] :> newCompositionSymbol[newCompositionSymbol[z, y], x], newCompositionSymbol[x_, y_] :> 
              newCompositionSymbol[y, x]}, morphismEquivalences]]]], DeleteDuplicates[
        Join[categoryObjectEquivalences /. Normal[objectMappings], objectEquivalences]]]; 
     morphismFunction = Association[Thread[First /@ domainMorphismList -> First /@ imageMorphismList]]; 
     limitObjects = {limitObjectName}; limitMorphismAssociation = {}; limitEquations = {}; 
     (Module[{morphism = #1}, limitObjects = Join[limitObjects, {First[Last[morphism]] /. Normal[objectFunction], 
            Last[Last[morphism]] /. Normal[objectFunction]}]; limitMorphismAssociation = Join[limitMorphismAssociation, 
           {limitMorphismNames[First[Last[morphism]]] -> DirectedEdge[limitObjectName, First[Last[morphism]] /. Normal[
                objectFunction]], limitMorphismNames[Last[Last[morphism]]] -> DirectedEdge[limitObjectName, 
              Last[Last[morphism]] /. Normal[objectFunction]]}]; limitMorphismAssociation = 
          Append[limitMorphismAssociation, (First[morphism] /. Normal[morphismFunction]) -> 
            If[covariant === True, DirectedEdge[First[Last[morphism]] /. Normal[objectFunction], 
              Last[Last[morphism]] /. Normal[objectFunction]], DirectedEdge[Last[Last[morphism]] /. Normal[
                objectFunction], First[Last[morphism]] /. Normal[objectFunction]]]]; 
         If[(First[morphism] /. Normal[morphismFunction]) =!= newIdentitySymbol[First[Last[morphism]] /. 
             Normal[objectFunction]], limitMorphismAssociation = Append[limitMorphismAssociation, 
             If[covariant === True, newCompositionSymbol[First[morphism] /. Normal[morphismFunction], 
                limitMorphismNames[First[Last[morphism]]]] -> DirectedEdge[limitObjectName, Last[Last[morphism]] /. 
                 Normal[objectFunction]], newCompositionSymbol[First[morphism] /. Normal[morphismFunction], 
                limitMorphismNames[Last[Last[morphism]]]] -> DirectedEdge[limitObjectName, First[Last[morphism]] /. 
                 Normal[objectFunction]]]]; limitEquations = Append[limitEquations, If[covariant === True, 
              limitMorphismNames[Last[Last[morphism]]] == newCompositionSymbol[First[morphism] /. 
                 Normal[morphismFunction], limitMorphismNames[First[Last[morphism]]]], limitMorphismNames[
                First[Last[morphism]]] == newCompositionSymbol[First[morphism] /. Normal[morphismFunction], 
                limitMorphismNames[Last[Last[morphism]]]]]]]] & ) /@ 
      Normal[reduceArrowsFinal[reduceArrowsInitial[morphismAssociation, categoryMorphismEquivalences], 
        categoryObjectEquivalences]]; limitObjects = DeleteDuplicates[limitObjects]; 
     limitMorphismAssociation = Association[Append[DeleteDuplicates[limitMorphismAssociation], 
        newIdentitySymbol[limitObjectName] -> DirectedEdge[limitObjectName, limitObjectName]]]; 
     EdgeTaggedGraph[limitObjects, (Labeled[DirectedEdge @@ Last[#1], Placed[First[#1], 0.5]] & ) /@ 
       Normal[reduceArrowsInitial[limitMorphismAssociation, limitEquations]], VertexSize -> 0.3, 
      VertexStyle -> Directive[Transparent, EdgeForm[None]], VertexLabels -> Placed["Name", Center], 
      VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
      EdgeStyle -> Directive[Black, Thick], GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory" && 
    SymbolName[abstractFunctor] === "AbstractFunctor"
AbstractLimit[Association["Functor" -> (abstractFunctor_)[Association["ArrowMappings" -> arrowMappings_Association, 
        "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
           "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
           "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
             Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
              "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
        "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
        "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
        "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
        "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]], 
     "LimitMorphismNames" -> limitMorphismNames_Association, "LimitObjectName" -> limitObjectName_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_Association, 
     "UniversalObjectName" -> universalObjectName_]]["UniversalFullLabeledGraph"] := 
  Module[{morphismAssociation, compositions, objectFunction, objectListWithDuplicates, arrowListWithDuplicates, 
     domainMorphismList, domainCompositions, imageMorphismList, imageCompositions, morphismFunction, 
     universalLimitObjects, universalLimitMorphismAssociation}, 
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
            DirectedEdge[#1, #1]]]] & ) /@ objects; objectFunction = Join[Association[(#1 -> #1 & ) /@ objects], 
       objectMappings]; objectListWithDuplicates = objects /. Normal[objectMappings]; 
     arrowListWithDuplicates = If[covariant === True, Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], 
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
         First /@ imageMorphismList]]; universalLimitObjects = {limitObjectName, universalObjectName}; 
     universalLimitMorphismAssociation = {Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> 
        DirectedEdge[universalObjectName, limitObjectName]}; 
     (Module[{morphism = #1}, universalLimitObjects = Join[universalLimitObjects, 
           {First[Last[morphism]] /. Normal[objectFunction], Last[Last[morphism]] /. Normal[objectFunction]}]; 
         universalLimitMorphismAssociation = Join[universalLimitMorphismAssociation, 
           {limitMorphismNames[First[Last[morphism]]] -> DirectedEdge[limitObjectName, First[Last[morphism]] /. Normal[
                objectFunction]], limitMorphismNames[Last[Last[morphism]]] -> DirectedEdge[limitObjectName, 
              Last[Last[morphism]] /. Normal[objectFunction]]}]; universalLimitMorphismAssociation = 
          Join[universalLimitMorphismAssociation, {Subscript["\[ForAll]", ToString[universalMorphismNames[
                First[Last[morphism]]], StandardForm]] -> DirectedEdge[universalObjectName, First[Last[morphism]] /. 
               Normal[objectFunction]], Subscript["\[ForAll]", ToString[universalMorphismNames[Last[Last[morphism]]], 
               StandardForm]] -> DirectedEdge[universalObjectName, Last[Last[morphism]] /. Normal[objectFunction]]}]; 
         universalLimitMorphismAssociation = Join[universalLimitMorphismAssociation, 
           {compositionSymbol[limitMorphismNames[First[Last[morphism]]], uniqueMorphismName] -> 
             DirectedEdge[universalObjectName, First[Last[morphism]] /. Normal[objectFunction]], 
            compositionSymbol[limitMorphismNames[Last[Last[morphism]]], uniqueMorphismName] -> 
             DirectedEdge[universalObjectName, Last[Last[morphism]] /. Normal[objectFunction]]}]; 
         universalLimitMorphismAssociation = Append[universalLimitMorphismAssociation, 
           (First[morphism] /. Normal[morphismFunction]) -> If[covariant === True, DirectedEdge[
              First[Last[morphism]] /. Normal[objectFunction], Last[Last[morphism]] /. Normal[objectFunction]], 
             DirectedEdge[Last[Last[morphism]] /. Normal[objectFunction], First[Last[morphism]] /. Normal[
                objectFunction]]]]; If[(First[morphism] /. Normal[morphismFunction]) =!= 
           newIdentitySymbol[First[Last[morphism]] /. Normal[objectFunction]], 
          universalLimitMorphismAssociation = Append[universalLimitMorphismAssociation, If[covariant === True, 
              newCompositionSymbol[First[morphism] /. Normal[morphismFunction], limitMorphismNames[
                 First[Last[morphism]]]] -> DirectedEdge[limitObjectName, Last[Last[morphism]] /. 
                 Normal[objectFunction]], newCompositionSymbol[First[morphism] /. Normal[morphismFunction], 
                limitMorphismNames[Last[Last[morphism]]]] -> DirectedEdge[limitObjectName, First[Last[morphism]] /. 
                 Normal[objectFunction]]]]; universalLimitMorphismAssociation = Join[universalLimitMorphismAssociation, 
             {If[covariant === True, newCompositionSymbol[newCompositionSymbol[First[morphism] /. 
                   Normal[morphismFunction], limitMorphismNames[First[Last[morphism]]]], uniqueMorphismName] -> 
                DirectedEdge[universalObjectName, Last[Last[morphism]] /. Normal[objectFunction]], newCompositionSymbol[
                 newCompositionSymbol[First[morphism] /. Normal[morphismFunction], limitMorphismNames[
                   Last[Last[morphism]]]], uniqueMorphismName] -> DirectedEdge[universalObjectName, 
                 First[Last[morphism]] /. Normal[objectFunction]]], If[covariant === True, newCompositionSymbol[
                 First[morphism] /. Normal[morphismFunction], universalMorphismNames[First[Last[morphism]]]] -> 
                DirectedEdge[universalObjectName, Last[Last[morphism]] /. Normal[objectFunction]], newCompositionSymbol[
                 First[morphism] /. Normal[morphismFunction], universalMorphismNames[Last[Last[morphism]]]] -> 
                DirectedEdge[universalObjectName, First[Last[morphism]] /. Normal[objectFunction]]]}]]] & ) /@ 
      Normal[morphismAssociation]; universalLimitObjects = DeleteDuplicates[universalLimitObjects]; 
     universalLimitMorphismAssociation = Association[Join[DeleteDuplicates[universalLimitMorphismAssociation], 
        {newIdentitySymbol[limitObjectName] -> DirectedEdge[limitObjectName, limitObjectName], 
         newIdentitySymbol[universalObjectName] -> DirectedEdge[universalObjectName, universalObjectName]}]]; 
     EdgeTaggedGraph[universalLimitObjects, (Labeled[DirectedEdge @@ Last[#1], Placed[First[#1], 0.5]] & ) /@ 
       Normal[universalLimitMorphismAssociation], VertexSize -> 0.3, 
      VertexStyle -> Directive[Transparent, EdgeForm[None]], VertexLabels -> {Placed["Name", Center], 
        universalObjectName -> Placed[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], Center]}, 
      VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
      EdgeStyle -> {Directive[Black, Thick], DirectedEdge[universalObjectName, limitObjectName] -> Dashed}, 
      GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory" && 
    SymbolName[abstractFunctor] === "AbstractFunctor"
AbstractLimit[Association["Functor" -> (abstractFunctor_)[Association["ArrowMappings" -> arrowMappings_Association, 
        "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
           "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
           "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
             Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
              "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
        "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
        "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
        "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
        "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]], 
     "LimitMorphismNames" -> limitMorphismNames_Association, "LimitObjectName" -> limitObjectName_, 
     "UniqueMorphismName" -> uniqueMorphismName_, "UniversalMorphismNames" -> universalMorphismNames_Association, 
     "UniversalObjectName" -> universalObjectName_]]["UniversalReducedLabeledGraph"] := 
  Module[{morphismAssociation, compositions, objectFunction, objectListWithDuplicates, arrowListWithDuplicates, 
     domainMorphismList, domainCompositions, imageMorphismList, imageCompositions, morphismFunction, 
     universalLimitObjects, universalLimitMorphismAssociation, universalLimitEquations}, 
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
     objectFunction = Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, 
               quiverObjectEquivalences], categoryObjectEquivalences]]] -> reduceObjectsWithDuplicates[
           Values[Association[(#1 -> #1 & ) /@ reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
               categoryObjectEquivalences]]], objectEquivalences]]], 
       Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[objectMappings], 
            quiverObjectEquivalences], categoryObjectEquivalences] -> reduceObjectsWithDuplicates[Values[objectMappings], 
           objectEquivalences]]]]; objectListWithDuplicates = objects /. Normal[objectMappings]; 
     arrowListWithDuplicates = If[covariant === True, Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], 
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
              newCompositionSymbol /. Normal[arrowMappings], morphismEquivalences]], 
         DeleteDuplicates[Join[categoryMorphismEquivalences /. compositionSymbol -> newCompositionSymbol /. 
             Normal[arrowMappings] /. {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
              newCompositionSymbol[z, newCompositionSymbol[y, x]], newCompositionSymbol[newCompositionSymbol[x_, y_], 
               z_] :> newCompositionSymbol[newCompositionSymbol[z, y], x], newCompositionSymbol[x_, y_] :> 
              newCompositionSymbol[y, x]}, morphismEquivalences]]]], DeleteDuplicates[
        Join[categoryObjectEquivalences /. Normal[objectMappings], objectEquivalences]]]; 
     morphismFunction = Association[Thread[First /@ domainMorphismList -> First /@ imageMorphismList]]; 
     universalLimitObjects = {limitObjectName, universalObjectName}; universalLimitMorphismAssociation = 
      {Subscript["\[Exists]!", ToString[uniqueMorphismName, StandardForm]] -> DirectedEdge[universalObjectName, 
         limitObjectName]}; universalLimitEquations = {}; 
     (Module[{morphism = #1}, universalLimitObjects = Join[universalLimitObjects, 
           {First[Last[morphism]] /. Normal[objectFunction], Last[Last[morphism]] /. Normal[objectFunction]}]; 
         universalLimitMorphismAssociation = Join[universalLimitMorphismAssociation, 
           {limitMorphismNames[First[Last[morphism]]] -> DirectedEdge[limitObjectName, First[Last[morphism]] /. Normal[
                objectFunction]], limitMorphismNames[Last[Last[morphism]]] -> DirectedEdge[limitObjectName, 
              Last[Last[morphism]] /. Normal[objectFunction]]}]; universalLimitMorphismAssociation = 
          Join[universalLimitMorphismAssociation, {Subscript["\[ForAll]", ToString[universalMorphismNames[
                First[Last[morphism]]], StandardForm]] -> DirectedEdge[universalObjectName, First[Last[morphism]] /. 
               Normal[objectFunction]], Subscript["\[ForAll]", ToString[universalMorphismNames[Last[Last[morphism]]], 
               StandardForm]] -> DirectedEdge[universalObjectName, Last[Last[morphism]] /. Normal[objectFunction]]}]; 
         universalLimitMorphismAssociation = Join[universalLimitMorphismAssociation, 
           {compositionSymbol[limitMorphismNames[First[Last[morphism]]], uniqueMorphismName] -> 
             DirectedEdge[universalObjectName, First[Last[morphism]] /. Normal[objectFunction]], 
            compositionSymbol[limitMorphismNames[Last[Last[morphism]]], uniqueMorphismName] -> 
             DirectedEdge[universalObjectName, Last[Last[morphism]] /. Normal[objectFunction]]}]; 
         universalLimitMorphismAssociation = Append[universalLimitMorphismAssociation, 
           (First[morphism] /. Normal[morphismFunction]) -> If[covariant === True, DirectedEdge[
              First[Last[morphism]] /. Normal[objectFunction], Last[Last[morphism]] /. Normal[objectFunction]], 
             DirectedEdge[Last[Last[morphism]] /. Normal[objectFunction], First[Last[morphism]] /. Normal[
                objectFunction]]]]; If[(First[morphism] /. Normal[morphismFunction]) =!= 
           newIdentitySymbol[First[Last[morphism]] /. Normal[objectFunction]], 
          universalLimitMorphismAssociation = Append[universalLimitMorphismAssociation, If[covariant === True, 
              newCompositionSymbol[First[morphism] /. Normal[morphismFunction], limitMorphismNames[
                 First[Last[morphism]]]] -> DirectedEdge[limitObjectName, Last[Last[morphism]] /. 
                 Normal[objectFunction]], newCompositionSymbol[First[morphism] /. Normal[morphismFunction], 
                limitMorphismNames[Last[Last[morphism]]]] -> DirectedEdge[limitObjectName, First[Last[morphism]] /. 
                 Normal[objectFunction]]]]; universalLimitMorphismAssociation = Join[universalLimitMorphismAssociation, 
             {If[covariant === True, newCompositionSymbol[newCompositionSymbol[First[morphism] /. 
                   Normal[morphismFunction], limitMorphismNames[First[Last[morphism]]]], uniqueMorphismName] -> 
                DirectedEdge[universalObjectName, Last[Last[morphism]] /. Normal[objectFunction]], newCompositionSymbol[
                 newCompositionSymbol[First[morphism] /. Normal[morphismFunction], limitMorphismNames[
                   Last[Last[morphism]]]], uniqueMorphismName] -> DirectedEdge[universalObjectName, 
                 First[Last[morphism]] /. Normal[objectFunction]]], If[covariant === True, newCompositionSymbol[
                 First[morphism] /. Normal[morphismFunction], universalMorphismNames[First[Last[morphism]]]] -> 
                DirectedEdge[universalObjectName, Last[Last[morphism]] /. Normal[objectFunction]], newCompositionSymbol[
                 First[morphism] /. Normal[morphismFunction], universalMorphismNames[Last[Last[morphism]]]] -> 
                DirectedEdge[universalObjectName, First[Last[morphism]] /. Normal[objectFunction]]]}]; 
           universalLimitEquations = Append[universalLimitEquations, If[covariant === True, limitMorphismNames[
                Last[Last[morphism]]] == newCompositionSymbol[First[morphism] /. Normal[morphismFunction], 
                limitMorphismNames[First[Last[morphism]]]], limitMorphismNames[First[Last[morphism]]] == 
               newCompositionSymbol[First[morphism] /. Normal[morphismFunction], limitMorphismNames[
                 Last[Last[morphism]]]]]]; universalLimitEquations = Append[universalLimitEquations, 
             If[covariant === True, Subscript["\[ForAll]", ToString[universalMorphismNames[Last[Last[morphism]]], 
                 StandardForm]] == newCompositionSymbol[First[morphism] /. Normal[morphismFunction], 
                universalMorphismNames[First[Last[morphism]]]], Subscript["\[ForAll]", ToString[universalMorphismNames[
                  First[Last[morphism]]], StandardForm]] == newCompositionSymbol[First[morphism] /. 
                 Normal[morphismFunction], universalMorphismNames[Last[Last[morphism]]]]]]; 
           universalLimitEquations = Join[universalLimitEquations, {Subscript["\[ForAll]", ToString[universalMorphismNames[
                  First[Last[morphism]]], StandardForm]] == newCompositionSymbol[limitMorphismNames[
                 First[Last[morphism]]], uniqueMorphismName], Subscript["\[ForAll]", ToString[universalMorphismNames[
                  Last[Last[morphism]]], StandardForm]] == newCompositionSymbol[limitMorphismNames[Last[Last[morphism]]], 
                uniqueMorphismName], universalMorphismNames[First[Last[morphism]]] == newCompositionSymbol[
                limitMorphismNames[First[Last[morphism]]], uniqueMorphismName], universalMorphismNames[
                Last[Last[morphism]]] == newCompositionSymbol[limitMorphismNames[Last[Last[morphism]]], 
                uniqueMorphismName]}]]] & ) /@ Normal[reduceArrowsFinal[reduceArrowsInitial[morphismAssociation, 
         categoryMorphismEquivalences], categoryObjectEquivalences]]; universalLimitObjects = 
      DeleteDuplicates[universalLimitObjects]; universalLimitMorphismAssociation = 
      Association[Join[DeleteDuplicates[universalLimitMorphismAssociation], 
        {newIdentitySymbol[limitObjectName] -> DirectedEdge[limitObjectName, limitObjectName], 
         newIdentitySymbol[universalObjectName] -> DirectedEdge[universalObjectName, universalObjectName]}]]; 
     EdgeTaggedGraph[universalLimitObjects, (Labeled[DirectedEdge @@ Last[#1], Placed[First[#1], 0.5]] & ) /@ 
       Normal[Association[DeleteDuplicates[Normal[reduceArrowsInitial[universalLimitMorphismAssociation, 
             universalLimitEquations]] //. {newCompositionSymbol[x_, newCompositionSymbol[y_, z_]] :> 
             newCompositionSymbol[newCompositionSymbol[x, y], z]}]]], VertexSize -> 0.3, 
      VertexStyle -> Directive[Transparent, EdgeForm[None]], VertexLabels -> {Placed["Name", Center], 
        universalObjectName -> Placed[Subscript["\[ForAll]", ToString[universalObjectName, StandardForm]], Center]}, 
      VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
      EdgeStyle -> {Directive[Black, Thick], DirectedEdge[universalObjectName, limitObjectName] -> Dashed}, 
      GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory" && 
    SymbolName[abstractFunctor] === "AbstractFunctor"
AbstractLimit /: 
  MakeBoxes[abstractLimit:AbstractLimit[Association["Functor" -> (abstractFunctor_)[
         Association["ArrowMappings" -> arrowMappings_Association, "Category" -> (abstractCategory_)[
            Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
             "MorphismEquivalences" -> categoryMorphismEquivalences_List, "ObjectEquivalences" -> 
              categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> 
                 arrowEquivalences_List, "Arrows" -> arrows_Association, "ObjectEquivalences" -> 
                 quiverObjectEquivalences_List, "Objects" -> objects_List]]]], "Covariant" -> covariant_, 
          "MorphismEquivalences" -> morphismEquivalences_List, "NewArrows" -> newArrows_Association, 
          "NewCompositionSymbol" -> newCompositionSymbol_, "NewIdentitySymbol" -> newIdentitySymbol_, 
          "NewObjects" -> newObjects_List, "ObjectEquivalences" -> objectEquivalences_List, 
          "ObjectMappings" -> objectMappings_Association]], "LimitMorphismNames" -> limitMorphismNames_Association, 
       "LimitObjectName" -> limitObjectName_, "UniqueMorphismName" -> uniqueMorphismName_, 
       "UniversalMorphismNames" -> universalMorphismNames_Association, "UniversalObjectName" -> universalObjectName_]], 
    format_] := Module[{morphismAssociation, compositions, objectFunction, objectListWithDuplicates, 
      arrowListWithDuplicates, domainMorphismList, domainCompositions, imageMorphismList, imageCompositions, 
      morphismFunction, limitObjects, limitMorphismAssociation, icon, type}, 
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
             DirectedEdge[#1, #1]]]] & ) /@ objects; objectFunction = Join[Association[(#1 -> #1 & ) /@ objects], 
        objectMappings]; objectListWithDuplicates = objects /. Normal[objectMappings]; 
      arrowListWithDuplicates = If[covariant === True, Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings], 
        (First[#1] -> Reverse[Last[#1]] & ) /@ (Normal[arrows] /. Normal[arrowMappings] /. Normal[objectMappings])]; 
      domainMorphismList = Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]; 
      Do[domainCompositions = Select[Tuples[domainMorphismList, 2], Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
        (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ domainMorphismList, 
             StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], domainMorphismList = 
            Append[domainMorphismList, compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[
                Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ domainCompositions, Length[objects]]; 
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
          First /@ imageMorphismList]]; limitObjects = {limitObjectName}; limitMorphismAssociation = {}; 
      (Module[{morphism = #1}, limitObjects = Join[limitObjects, {First[Last[morphism]] /. Normal[objectFunction], 
             Last[Last[morphism]] /. Normal[objectFunction]}]; limitMorphismAssociation = Join[limitMorphismAssociation, 
            {limitMorphismNames[First[Last[morphism]]] -> DirectedEdge[limitObjectName, First[Last[morphism]] /. 
                Normal[objectFunction]], limitMorphismNames[Last[Last[morphism]]] -> DirectedEdge[limitObjectName, 
               Last[Last[morphism]] /. Normal[objectFunction]]}]; limitMorphismAssociation = 
           Append[limitMorphismAssociation, (First[morphism] /. Normal[morphismFunction]) -> If[covariant === True, 
              DirectedEdge[First[Last[morphism]] /. Normal[objectFunction], Last[Last[morphism]] /. 
                Normal[objectFunction]], DirectedEdge[Last[Last[morphism]] /. Normal[objectFunction], 
               First[Last[morphism]] /. Normal[objectFunction]]]]; If[(First[morphism] /. Normal[morphismFunction]) =!= 
            newIdentitySymbol[First[Last[morphism]] /. Normal[objectFunction]], limitMorphismAssociation = 
            Append[limitMorphismAssociation, If[covariant === True, newCompositionSymbol[First[morphism] /. 
                 Normal[morphismFunction], limitMorphismNames[First[Last[morphism]]]] -> DirectedEdge[limitObjectName, 
                Last[Last[morphism]] /. Normal[objectFunction]], newCompositionSymbol[First[morphism] /. 
                 Normal[morphismFunction], limitMorphismNames[Last[Last[morphism]]]] -> DirectedEdge[limitObjectName, 
                First[Last[morphism]] /. Normal[objectFunction]]]]]] & ) /@ Normal[morphismAssociation]; 
      limitObjects = DeleteDuplicates[limitObjects]; limitMorphismAssociation = 
       Association[Append[DeleteDuplicates[limitMorphismAssociation], newIdentitySymbol[limitObjectName] -> 
          DirectedEdge[limitObjectName, limitObjectName]]]; 
      icon = GraphPlot[EdgeTaggedGraph[limitObjects, (DirectedEdge @@ Last[#1] & ) /@ Normal[limitMorphismAssociation], 
         VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], EdgeShapeFunction -> 
          GraphElementData["ShortFilledArrow", "ArrowSize" -> 0.05], EdgeStyle -> Black, 
         GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]]; If[covariant === True, type = "Covariant", 
       type = "Contravariant"]; BoxForm`ArrangeSummaryBox["AbstractLimit", abstractLimit, icon, 
       {{BoxForm`SummaryItem[{"Type: ", type}]}, {}}, {{}}, format, "Interpretable" -> Automatic]] /; 
    SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory" && 
     SymbolName[abstractFunctor] === "AbstractFunctor"
AbstractLimit[(abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "ObjectEquivalences" -> objectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]], functorSymbol_] := 
  AbstractLimit[Association["Functor" -> ResourceFunction["AbstractFunctor"][
       Association["ArrowMappings" -> Association[(First[#1] -> functorSymbol[First[#1]] & ) /@ Normal[arrows]], 
        "Category" -> ResourceFunction["AbstractCategory"][Association["CompositionSymbol" -> compositionSymbol, 
           "IdentitySymbol" -> identitySymbol, "MorphismEquivalences" -> morphismEquivalences, 
           "ObjectEquivalences" -> objectEquivalences, "Quiver" -> ResourceFunction["AbstractQuiver"][
             Association["ArrowEquivalences" -> arrowEquivalences, "Arrows" -> arrows, "ObjectEquivalences" -> 
               quiverObjectEquivalences, "Objects" -> objects]]]], "Covariant" -> True, "MorphismEquivalences" -> {}, 
        "NewArrows" -> Association[], "NewCompositionSymbol" -> compositionSymbol, "NewIdentitySymbol" -> identitySymbol, 
        "NewObjects" -> {}, "ObjectEquivalences" -> {}, "ObjectMappings" -> 
         Association[(#1 -> functorSymbol[#1] & ) /@ objects]]], "LimitMorphismNames" -> 
      Association[(#1 -> Subscript["\[Phi]", ToString[#1, StandardForm]] & ) /@ objects], "LimitObjectName" -> "\[FormalCapitalL]", 
     "UniqueMorphismName" -> "\[FormalU]", "UniversalMorphismNames" -> 
      Association[(#1 -> Subscript["\[Psi]", ToString[#1, StandardForm]] & ) /@ objects], "UniversalObjectName" -> "\[FormalCapitalN]"]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractLimit[(abstractFunctor_)[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "Covariant" -> covariant_, "MorphismEquivalences" -> morphismEquivalences_List, 
     "NewArrows" -> newArrows_Association, "NewCompositionSymbol" -> newCompositionSymbol_, 
     "NewIdentitySymbol" -> newIdentitySymbol_, "NewObjects" -> newObjects_List, 
     "ObjectEquivalences" -> objectEquivalences_List, "ObjectMappings" -> objectMappings_Association]]] := 
  AbstractLimit[Association["Functor" -> ResourceFunction["AbstractFunctor"][
       Association["ArrowMappings" -> arrowMappings, "Category" -> ResourceFunction["AbstractCategory"][
          Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
           "MorphismEquivalences" -> categoryMorphismEquivalences, "ObjectEquivalences" -> categoryObjectEquivalences, 
           "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> arrowEquivalences, 
              "Arrows" -> arrows, "ObjectEquivalences" -> quiverObjectEquivalences, "Objects" -> objects]]]], 
        "Covariant" -> covariant, "MorphismEquivalences" -> morphismEquivalences, "NewArrows" -> newArrows, 
        "NewCompositionSymbol" -> newCompositionSymbol, "NewIdentitySymbol" -> newIdentitySymbol, 
        "NewObjects" -> newObjects, "ObjectEquivalences" -> objectEquivalences, "ObjectMappings" -> objectMappings]], 
     "LimitMorphismNames" -> Association[(#1 -> Subscript["\[Phi]", ToString[#1, StandardForm]] & ) /@ objects], 
     "LimitObjectName" -> "\[FormalCapitalL]", "UniqueMorphismName" -> "\[FormalU]", "UniversalMorphismNames" -> 
      Association[(#1 -> Subscript["\[Psi]", ToString[#1, StandardForm]] & ) /@ objects], "UniversalObjectName" -> "\[FormalCapitalN]"]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory" && 
    SymbolName[abstractFunctor] === "AbstractFunctor"

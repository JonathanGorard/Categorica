(* ::Package:: *)

reduceObjects[objects_List, {}] := objects
reduceObjects[objects_List, objectEquivalences_List] := 
  reduceObjects[DeleteDuplicates[objects /. First[First[objectEquivalences]] -> Last[First[objectEquivalences]]], 
    Select[Drop[DeleteDuplicates[objectEquivalences /. First[First[objectEquivalences]] -> 
         Last[First[objectEquivalences]]], 1], #1 =!= True & ]] /; Length[objectEquivalences] > 0
reduceArrowsInitial[arrows_Association, {}] := arrows
reduceArrowsInitial[arrows_Association, arrowEquivalences_List] := 
  reduceArrowsInitial[Association[DeleteDuplicatesBy[Normal[arrows] /. First[First[arrowEquivalences]] -> 
        Last[First[arrowEquivalences]], First]], 
    Select[Drop[DeleteDuplicates[arrowEquivalences /. First[First[arrowEquivalences]] -> Last[First[arrowEquivalences]]], 
      1], #1 =!= True & ]] /; Length[arrowEquivalences] > 0
reduceArrowsFinal[arrows_Association, {}] := arrows
reduceArrowsFinal[arrows_Association, objectEquivalences_List] := 
  reduceArrowsFinal[Association[Normal[arrows] /. First[First[objectEquivalences]] -> Last[First[objectEquivalences]]], 
    Select[Drop[DeleteDuplicates[objectEquivalences /. First[First[objectEquivalences]] -> 
         Last[First[objectEquivalences]]], 1], #1 =!= True & ]] /; Length[objectEquivalences] > 0
reduceObjectsWithDuplicates[objects_List, {}] := objects
reduceObjectsWithDuplicates[objects_List, objectEquivalences_List] := 
  reduceObjectsWithDuplicates[objects /. First[First[objectEquivalences]] -> Last[First[objectEquivalences]], 
    Select[Drop[objectEquivalences /. First[First[objectEquivalences]] -> Last[First[objectEquivalences]], 1], 
     #1 =!= True & ]] /; Length[objectEquivalences] > 0
reduceArrowsInitialWithDuplicates[arrows_List, {}] := arrows
reduceArrowsInitialWithDuplicates[arrows_List, arrowEquivalences_List] := 
  reduceArrowsInitialWithDuplicates[arrows /. First[First[arrowEquivalences]] -> Last[First[arrowEquivalences]], 
    Select[Drop[arrowEquivalences /. First[First[arrowEquivalences]] -> Last[First[arrowEquivalences]], 1], 
     #1 =!= True & ]] /; Length[arrowEquivalences] > 0
reduceArrowsFinalWithDuplicates[arrows_List, {}] := arrows
reduceArrowsFinalWithDuplicates[arrows_List, objectEquivalences_List] := 
  reduceArrowsFinalWithDuplicates[arrows /. First[First[objectEquivalences]] -> Last[First[objectEquivalences]], 
    Select[Drop[objectEquivalences /. First[First[objectEquivalences]] -> Last[First[objectEquivalences]], 1], 
     #1 =!= True & ]] /; Length[objectEquivalences] > 0
AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "ObjectMappings" -> objectMappings_Association, "TensorProductSymbol" -> tensorProductSymbol_, 
     "UnitObject" -> unitObject_]]["ObjectCount"] := (Length[Catenate[Outer[tensorProductSymbol, objects, objects]]] -> 
    Length[DeleteDuplicates[Catenate[Outer[tensorProductSymbol, objects, objects]] /. Normal[objectMappings]]]) /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "ObjectMappings" -> objectMappings_Association, "TensorProductSymbol" -> tensorProductSymbol_, 
     "UnitObject" -> unitObject_]]["MorphismCount"] := 
  Module[{productArrows, domainMorphismAssociation, domainCompositions, imageMorphismAssociation, imageCompositions}, 
    productArrows = Association[DeleteDuplicates[
        Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ Select[Normal[arrows], First[Last[#1]] =!= 
                 Last[Last[#1]] & ], First /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]] -> 
           Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ], (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ]]], Catenate[Outer[tensorProductSymbol, (Last[Last[#1]] & ) /@ 
                Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ], (Last[Last[#1]] & ) /@ 
                Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]]]]], 
         Thread[Catenate[Outer[tensorProductSymbol, First /@ Select[Normal[arrows], First[Last[#1]] =!= 
                 Last[Last[#1]] & ], identitySymbol /@ objects]] -> 
           Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ], objects]], Catenate[Outer[tensorProductSymbol, 
               (Last[Last[#1]] & ) /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ], objects]]]]], 
         Thread[Catenate[Outer[tensorProductSymbol, identitySymbol /@ objects, First /@ Select[Normal[arrows], 
               First[Last[#1]] =!= Last[Last[#1]] & ]]] -> Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, 
               objects, (First[Last[#1]] & ) /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]], 
             Catenate[Outer[tensorProductSymbol, objects, (Last[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ]]]]]]]]]; domainMorphismAssociation = 
      Association[Select[Normal[productArrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[domainCompositions = Select[Tuples[Normal[domainMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[domainMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          domainMorphismAssociation = Association[Append[Normal[domainMorphismAssociation], 
             compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ domainCompositions, 
      Length[Catenate[Outer[tensorProductSymbol, objects, objects]]]]; domainMorphismAssociation = 
      Association[Select[Normal[domainMorphismAssociation], Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[domainMorphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        domainMorphismAssociation = Association[Append[Normal[domainMorphismAssociation], 
           identitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ Catenate[Outer[tensorProductSymbol, objects, objects]]; 
     domainMorphismAssociation = Association[DeleteDuplicates[Normal[domainMorphismAssociation] //. 
         {compositionSymbol[tensorProductSymbol[x_, y_], tensorProductSymbol[z_, w_]] :> 
           tensorProductSymbol[compositionSymbol[x, z], compositionSymbol[y, w]], 
          compositionSymbol[x_, identitySymbol[y_]] :> x, compositionSymbol[identitySymbol[x_], y_] :> y, 
          compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[compositionSymbol[x, y], z]}]]; 
     imageMorphismAssociation = Association[Select[Normal[Association[DeleteDuplicates[
           Normal[productArrows] /. Normal[arrowMappings] /. Normal[objectMappings]]]], 
        First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[imageCompositions = Select[Tuples[Normal[imageMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[imageMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], 
             compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ imageCompositions, 
      Length[DeleteDuplicates[Catenate[Outer[tensorProductSymbol, objects, objects]] /. Normal[objectMappings]]]]; 
     imageMorphismAssociation = Association[Select[Normal[imageMorphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[imageMorphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ DeleteDuplicates[Catenate[Outer[tensorProductSymbol, objects, objects]] /. 
        Normal[objectMappings]]; imageMorphismAssociation = 
      Association[DeleteDuplicates[Normal[imageMorphismAssociation] //. 
         {compositionSymbol[tensorProductSymbol[x_, y_], tensorProductSymbol[z_, w_]] :> 
           tensorProductSymbol[compositionSymbol[x, z], compositionSymbol[y, w]], 
          compositionSymbol[x_, identitySymbol[y_]] :> x, compositionSymbol[identitySymbol[x_], y_] :> y, 
          compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[compositionSymbol[x, y], z]}]]; 
     Length[Normal[domainMorphismAssociation]] -> Length[Normal[imageMorphismAssociation]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "ObjectMappings" -> objectMappings_Association, "TensorProductSymbol" -> tensorProductSymbol_, 
     "UnitObject" -> unitObject_]]["ObjectEquivalences"] := 
  Module[{objectFunction, associatorEquations, leftUnitorEquations, rightUnitorEquations, monoidalEquations, 
     imageQuiverObjectEquivalences, imageObjectEquivalences}, 
    objectFunction = Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ Catenate[Outer[tensorProductSymbol, 
               reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], reduceObjects[
                reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences]]]]] -> 
          reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Values[Association[(#1 -> #1 & ) /@ Catenate[
                Outer[tensorProductSymbol, reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
                  categoryObjectEquivalences], reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
                  categoryObjectEquivalences]]]]], quiverObjectEquivalences], categoryObjectEquivalences]]], 
       Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[objectMappings], 
            quiverObjectEquivalences], categoryObjectEquivalences] -> reduceObjectsWithDuplicates[
           reduceObjectsWithDuplicates[Values[objectMappings], quiverObjectEquivalences], categoryObjectEquivalences]]]]; 
     associatorEquations = DeleteDuplicates[Select[reduceObjects[
         (tensorProductSymbol[#1[[1]], tensorProductSymbol[#1[[2]], #1[[3]]]] == tensorProductSymbol[
              tensorProductSymbol[#1[[1]], #1[[2]]], #1[[3]]] /. Normal[objectFunction] & ) /@ 
          Tuples[reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 3], 
         objectEquivalences], #1 =!= True & ]]; leftUnitorEquations = 
      DeleteDuplicates[Select[reduceObjects[(tensorProductSymbol[unitObject, #1] == #1 /. Normal[objectFunction] & ) /@ 
          reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 
         objectEquivalences], #1 =!= True & ]]; rightUnitorEquations = 
      DeleteDuplicates[Select[reduceObjects[(tensorProductSymbol[#1, unitObject] == #1 /. Normal[objectFunction] & ) /@ 
          reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 
         objectEquivalences], #1 =!= True & ]]; monoidalEquations = DeleteDuplicates[
       Join[associatorEquations, leftUnitorEquations, rightUnitorEquations]]; imageQuiverObjectEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ quiverObjectEquivalences, 
               objects]] -> Catenate[Outer[tensorProductSymbol, Last /@ quiverObjectEquivalences, objects]]], 
           Thread[Catenate[Outer[tensorProductSymbol, objects, First /@ quiverObjectEquivalences]] -> 
             Catenate[Outer[tensorProductSymbol, objects, Last /@ quiverObjectEquivalences]]]] /. 
          Normal[objectMappings]] /. Rule -> Equal, #1 =!= True & ]; imageObjectEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ categoryObjectEquivalences, 
               objects]] -> Catenate[Outer[tensorProductSymbol, Last /@ categoryObjectEquivalences, objects]]], 
           Thread[Catenate[Outer[tensorProductSymbol, objects, First /@ categoryObjectEquivalences]] -> 
             Catenate[Outer[tensorProductSymbol, objects, Last /@ categoryObjectEquivalences]]]] /. 
          Normal[objectMappings]] /. Rule -> Equal, #1 =!= True & ]; 
     DeleteDuplicates[Join[imageQuiverObjectEquivalences, imageObjectEquivalences, monoidalEquations, 
       objectEquivalences]]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"
AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "ObjectMappings" -> objectMappings_Association, "TensorProductSymbol" -> tensorProductSymbol_, 
     "UnitObject" -> unitObject_]]["ObjectEquivalenceCount"] := 
  Module[{objectFunction, associatorEquations, leftUnitorEquations, rightUnitorEquations, monoidalEquations, 
     imageQuiverObjectEquivalences, imageObjectEquivalences}, 
    objectFunction = Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ Catenate[Outer[tensorProductSymbol, 
               reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], reduceObjects[
                reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences]]]]] -> 
          reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Values[Association[(#1 -> #1 & ) /@ Catenate[
                Outer[tensorProductSymbol, reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
                  categoryObjectEquivalences], reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
                  categoryObjectEquivalences]]]]], quiverObjectEquivalences], categoryObjectEquivalences]]], 
       Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[objectMappings], 
            quiverObjectEquivalences], categoryObjectEquivalences] -> reduceObjectsWithDuplicates[
           reduceObjectsWithDuplicates[Values[objectMappings], quiverObjectEquivalences], categoryObjectEquivalences]]]]; 
     associatorEquations = DeleteDuplicates[Select[reduceObjects[
         (tensorProductSymbol[#1[[1]], tensorProductSymbol[#1[[2]], #1[[3]]]] == tensorProductSymbol[
              tensorProductSymbol[#1[[1]], #1[[2]]], #1[[3]]] /. Normal[objectFunction] & ) /@ 
          Tuples[reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 3], 
         objectEquivalences], #1 =!= True & ]]; leftUnitorEquations = 
      DeleteDuplicates[Select[reduceObjects[(tensorProductSymbol[unitObject, #1] == #1 /. Normal[objectFunction] & ) /@ 
          reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 
         objectEquivalences], #1 =!= True & ]]; rightUnitorEquations = 
      DeleteDuplicates[Select[reduceObjects[(tensorProductSymbol[#1, unitObject] == #1 /. Normal[objectFunction] & ) /@ 
          reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 
         objectEquivalences], #1 =!= True & ]]; monoidalEquations = DeleteDuplicates[
       Join[associatorEquations, leftUnitorEquations, rightUnitorEquations]]; imageQuiverObjectEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ quiverObjectEquivalences, 
               objects]] -> Catenate[Outer[tensorProductSymbol, Last /@ quiverObjectEquivalences, objects]]], 
           Thread[Catenate[Outer[tensorProductSymbol, objects, First /@ quiverObjectEquivalences]] -> 
             Catenate[Outer[tensorProductSymbol, objects, Last /@ quiverObjectEquivalences]]]] /. 
          Normal[objectMappings]] /. Rule -> Equal, #1 =!= True & ]; imageObjectEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ categoryObjectEquivalences, 
               objects]] -> Catenate[Outer[tensorProductSymbol, Last /@ categoryObjectEquivalences, objects]]], 
           Thread[Catenate[Outer[tensorProductSymbol, objects, First /@ categoryObjectEquivalences]] -> 
             Catenate[Outer[tensorProductSymbol, objects, Last /@ categoryObjectEquivalences]]]] /. 
          Normal[objectMappings]] /. Rule -> Equal, #1 =!= True & ]; 
     Length[DeleteDuplicates[Join[imageQuiverObjectEquivalences, imageObjectEquivalences, monoidalEquations, 
        objectEquivalences]]]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"
AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "ObjectMappings" -> objectMappings_Association, "TensorProductSymbol" -> tensorProductSymbol_, 
     "UnitObject" -> unitObject_]]["MorphismEquivalences"] := 
  Module[{morphismAssociation, compositions, imageArrowEquivalences, imageMorphismEquivalences}, 
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
            DirectedEdge[#1, #1]]]] & ) /@ objects; imageArrowEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ arrowEquivalences, First /@ 
                Normal[arrows]]] -> Catenate[Outer[tensorProductSymbol, Last /@ arrowEquivalences, First /@ 
                Normal[arrows]]]], Thread[Catenate[Outer[tensorProductSymbol, First /@ Normal[arrows], First /@ 
                arrowEquivalences]] -> Catenate[Outer[tensorProductSymbol, First /@ Normal[arrows], Last /@ 
                arrowEquivalences]]]] /. Normal[arrowMappings]] /. Rule -> Equal, #1 =!= True & ]; 
     imageMorphismEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ categoryMorphismEquivalences, 
                First /@ Normal[morphismAssociation]]] -> Catenate[Outer[tensorProductSymbol, 
                Last /@ categoryMorphismEquivalences, First /@ Normal[morphismAssociation]]]], 
            Thread[Catenate[Outer[tensorProductSymbol, First /@ Normal[morphismAssociation], First /@ 
                 categoryMorphismEquivalences]] -> Catenate[Outer[tensorProductSymbol, First /@ 
                 Normal[morphismAssociation], Last /@ categoryMorphismEquivalences]]]] /. Normal[arrowMappings] /. 
          Normal[objectMappings]] /. Rule -> Equal, #1 =!= True & ]; 
     DeleteDuplicates[Join[imageArrowEquivalences, imageMorphismEquivalences, morphismEquivalences]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "ObjectMappings" -> objectMappings_Association, "TensorProductSymbol" -> tensorProductSymbol_, 
     "UnitObject" -> unitObject_]]["MorphismEquivalenceCount"] := 
  Module[{morphismAssociation, compositions, imageArrowEquivalences, imageMorphismEquivalences}, 
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
            DirectedEdge[#1, #1]]]] & ) /@ objects; imageArrowEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ arrowEquivalences, First /@ 
                Normal[arrows]]] -> Catenate[Outer[tensorProductSymbol, Last /@ arrowEquivalences, First /@ 
                Normal[arrows]]]], Thread[Catenate[Outer[tensorProductSymbol, First /@ Normal[arrows], First /@ 
                arrowEquivalences]] -> Catenate[Outer[tensorProductSymbol, First /@ Normal[arrows], Last /@ 
                arrowEquivalences]]]] /. Normal[arrowMappings]] /. Rule -> Equal, #1 =!= True & ]; 
     imageMorphismEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ categoryMorphismEquivalences, 
                First /@ Normal[morphismAssociation]]] -> Catenate[Outer[tensorProductSymbol, 
                Last /@ categoryMorphismEquivalences, First /@ Normal[morphismAssociation]]]], 
            Thread[Catenate[Outer[tensorProductSymbol, First /@ Normal[morphismAssociation], First /@ 
                 categoryMorphismEquivalences]] -> Catenate[Outer[tensorProductSymbol, First /@ 
                 Normal[morphismAssociation], Last /@ categoryMorphismEquivalences]]]] /. Normal[arrowMappings] /. 
          Normal[objectMappings]] /. Rule -> Equal, #1 =!= True & ]; 
     Length[DeleteDuplicates[Join[imageArrowEquivalences, imageMorphismEquivalences, morphismEquivalences]]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "ObjectMappings" -> objectMappings_Association, "TensorProductSymbol" -> tensorProductSymbol_, 
     "UnitObject" -> unitObject_]]["ReducedObjectCount"] := 
  Module[{objectFunction, associatorEquations, leftUnitorEquations, rightUnitorEquations, monoidalEquations, 
     imageObjects, imageQuiverObjectEquivalences, imageObjectEquivalences}, 
    objectFunction = Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ Catenate[Outer[tensorProductSymbol, 
               reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], reduceObjects[
                reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences]]]]] -> 
          reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Values[Association[(#1 -> #1 & ) /@ Catenate[
                Outer[tensorProductSymbol, reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
                  categoryObjectEquivalences], reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
                  categoryObjectEquivalences]]]]], quiverObjectEquivalences], categoryObjectEquivalences]]], 
       Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[objectMappings], 
            quiverObjectEquivalences], categoryObjectEquivalences] -> reduceObjectsWithDuplicates[
           reduceObjectsWithDuplicates[Values[objectMappings], quiverObjectEquivalences], categoryObjectEquivalences]]]]; 
     associatorEquations = DeleteDuplicates[Select[reduceObjects[
         (tensorProductSymbol[#1[[1]], tensorProductSymbol[#1[[2]], #1[[3]]]] == tensorProductSymbol[
              tensorProductSymbol[#1[[1]], #1[[2]]], #1[[3]]] /. Normal[objectFunction] & ) /@ 
          Tuples[reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 3], 
         objectEquivalences], #1 =!= True & ]]; leftUnitorEquations = 
      DeleteDuplicates[Select[reduceObjects[(tensorProductSymbol[unitObject, #1] == #1 /. Normal[objectFunction] & ) /@ 
          reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 
         objectEquivalences], #1 =!= True & ]]; rightUnitorEquations = 
      DeleteDuplicates[Select[reduceObjects[(tensorProductSymbol[#1, unitObject] == #1 /. Normal[objectFunction] & ) /@ 
          reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 
         objectEquivalences], #1 =!= True & ]]; monoidalEquations = DeleteDuplicates[
       Join[associatorEquations, leftUnitorEquations, rightUnitorEquations]]; 
     imageObjects = DeleteDuplicates[Catenate[Outer[tensorProductSymbol, objects, objects]] /. Normal[objectMappings]]; 
     imageQuiverObjectEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ quiverObjectEquivalences, 
               objects]] -> Catenate[Outer[tensorProductSymbol, Last /@ quiverObjectEquivalences, objects]]], 
           Thread[Catenate[Outer[tensorProductSymbol, objects, First /@ quiverObjectEquivalences]] -> 
             Catenate[Outer[tensorProductSymbol, objects, Last /@ quiverObjectEquivalences]]]] /. 
          Normal[objectMappings]] /. Rule -> Equal, #1 =!= True & ]; imageObjectEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ categoryObjectEquivalences, 
               objects]] -> Catenate[Outer[tensorProductSymbol, Last /@ categoryObjectEquivalences, objects]]], 
           Thread[Catenate[Outer[tensorProductSymbol, objects, First /@ categoryObjectEquivalences]] -> 
             Catenate[Outer[tensorProductSymbol, objects, Last /@ categoryObjectEquivalences]]]] /. 
          Normal[objectMappings]] /. Rule -> Equal, #1 =!= True & ]; 
     Length[reduceObjects[reduceObjects[Catenate[Outer[tensorProductSymbol, objects, objects]], 
         quiverObjectEquivalences], categoryObjectEquivalences]] -> 
      Length[reduceObjects[reduceObjects[reduceObjects[reduceObjects[imageObjects, imageQuiverObjectEquivalences], 
          imageObjectEquivalences], monoidalEquations], objectEquivalences]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "ObjectMappings" -> objectMappings_Association, "TensorProductSymbol" -> tensorProductSymbol_, 
     "UnitObject" -> unitObject_]]["ReducedMorphismCount"] := 
  Module[{objectFunction, associatorEquations, leftUnitorEquations, rightUnitorEquations, monoidalEquations, 
     productArrows, domainMorphismAssociation, domainCompositions, morphismAssociation, compositions, imageObjects, 
     imageArrows, imageQuiverObjectEquivalences, imageObjectEquivalences, imageArrowEquivalences, 
     imageMorphismEquivalences, imageMorphismAssociation, imageCompositions}, 
    objectFunction = Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ Catenate[Outer[tensorProductSymbol, 
               reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], reduceObjects[
                reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences]]]]] -> 
          reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Values[Association[(#1 -> #1 & ) /@ Catenate[
                Outer[tensorProductSymbol, reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
                  categoryObjectEquivalences], reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
                  categoryObjectEquivalences]]]]], quiverObjectEquivalences], categoryObjectEquivalences]]], 
       Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[objectMappings], 
            quiverObjectEquivalences], categoryObjectEquivalences] -> reduceObjectsWithDuplicates[
           reduceObjectsWithDuplicates[Values[objectMappings], quiverObjectEquivalences], categoryObjectEquivalences]]]]; 
     associatorEquations = DeleteDuplicates[Select[reduceObjects[
         (tensorProductSymbol[#1[[1]], tensorProductSymbol[#1[[2]], #1[[3]]]] == tensorProductSymbol[
              tensorProductSymbol[#1[[1]], #1[[2]]], #1[[3]]] /. Normal[objectFunction] & ) /@ 
          Tuples[reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 3], 
         objectEquivalences], #1 =!= True & ]]; leftUnitorEquations = 
      DeleteDuplicates[Select[reduceObjects[(tensorProductSymbol[unitObject, #1] == #1 /. Normal[objectFunction] & ) /@ 
          reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 
         objectEquivalences], #1 =!= True & ]]; rightUnitorEquations = 
      DeleteDuplicates[Select[reduceObjects[(tensorProductSymbol[#1, unitObject] == #1 /. Normal[objectFunction] & ) /@ 
          reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 
         objectEquivalences], #1 =!= True & ]]; monoidalEquations = DeleteDuplicates[
       Join[associatorEquations, leftUnitorEquations, rightUnitorEquations]]; 
     productArrows = Association[DeleteDuplicates[
        Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ Select[Normal[arrows], First[Last[#1]] =!= 
                 Last[Last[#1]] & ], First /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]] -> 
           Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ], (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ]]], Catenate[Outer[tensorProductSymbol, (Last[Last[#1]] & ) /@ 
                Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ], (Last[Last[#1]] & ) /@ 
                Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]]]]], 
         Thread[Catenate[Outer[tensorProductSymbol, First /@ Select[Normal[arrows], First[Last[#1]] =!= 
                 Last[Last[#1]] & ], identitySymbol /@ objects]] -> 
           Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ], objects]], Catenate[Outer[tensorProductSymbol, 
               (Last[Last[#1]] & ) /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ], objects]]]]], 
         Thread[Catenate[Outer[tensorProductSymbol, identitySymbol /@ objects, First /@ Select[Normal[arrows], 
               First[Last[#1]] =!= Last[Last[#1]] & ]]] -> Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, 
               objects, (First[Last[#1]] & ) /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]], 
             Catenate[Outer[tensorProductSymbol, objects, (Last[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ]]]]]]]]]; domainMorphismAssociation = 
      Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[productArrows, arrowEquivalences], 
          quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[domainCompositions = Select[Tuples[Normal[domainMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[domainMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          domainMorphismAssociation = Association[Append[Normal[domainMorphismAssociation], 
             compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ domainCompositions, 
      Length[reduceObjects[Catenate[Outer[tensorProductSymbol, objects, objects]], quiverObjectEquivalences]]]; 
     domainMorphismAssociation = Association[Select[Normal[domainMorphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[domainMorphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        domainMorphismAssociation = Association[Append[Normal[domainMorphismAssociation], 
           identitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ 
      reduceObjects[Catenate[Outer[tensorProductSymbol, objects, objects]], quiverObjectEquivalences]; 
     domainMorphismAssociation = Association[DeleteDuplicates[Normal[domainMorphismAssociation] //. 
         {compositionSymbol[tensorProductSymbol[x_, y_], tensorProductSymbol[z_, w_]] :> 
           tensorProductSymbol[compositionSymbol[x, z], compositionSymbol[y, w]], 
          compositionSymbol[x_, identitySymbol[y_]] :> x, compositionSymbol[identitySymbol[x_], y_] :> y, 
          compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[compositionSymbol[x, y], z]}]]; 
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
            DirectedEdge[#1, #1]]]] & ) /@ objects; imageObjects = DeleteDuplicates[
       Catenate[Outer[tensorProductSymbol, objects, objects]] /. Normal[objectMappings]]; 
     imageArrows = Association[DeleteDuplicates[Normal[productArrows] /. Normal[arrowMappings] /. 
         Normal[objectMappings]]]; imageQuiverObjectEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ quiverObjectEquivalences, 
               objects]] -> Catenate[Outer[tensorProductSymbol, Last /@ quiverObjectEquivalences, objects]]], 
           Thread[Catenate[Outer[tensorProductSymbol, objects, First /@ quiverObjectEquivalences]] -> 
             Catenate[Outer[tensorProductSymbol, objects, Last /@ quiverObjectEquivalences]]]] /. 
          Normal[objectMappings]] /. Rule -> Equal, #1 =!= True & ]; imageObjectEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ categoryObjectEquivalences, 
               objects]] -> Catenate[Outer[tensorProductSymbol, Last /@ categoryObjectEquivalences, objects]]], 
           Thread[Catenate[Outer[tensorProductSymbol, objects, First /@ categoryObjectEquivalences]] -> 
             Catenate[Outer[tensorProductSymbol, objects, Last /@ categoryObjectEquivalences]]]] /. 
          Normal[objectMappings]] /. Rule -> Equal, #1 =!= True & ]; imageArrowEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ arrowEquivalences, First /@ 
                Normal[arrows]]] -> Catenate[Outer[tensorProductSymbol, Last /@ arrowEquivalences, First /@ 
                Normal[arrows]]]], Thread[Catenate[Outer[tensorProductSymbol, First /@ Normal[arrows], First /@ 
                arrowEquivalences]] -> Catenate[Outer[tensorProductSymbol, First /@ Normal[arrows], Last /@ 
                arrowEquivalences]]]] /. Normal[arrowMappings]] /. Rule -> Equal, #1 =!= True & ]; 
     imageMorphismEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ categoryMorphismEquivalences, 
                First /@ Normal[morphismAssociation]]] -> Catenate[Outer[tensorProductSymbol, 
                Last /@ categoryMorphismEquivalences, First /@ Normal[morphismAssociation]]]], 
            Thread[Catenate[Outer[tensorProductSymbol, First /@ Normal[morphismAssociation], First /@ 
                 categoryMorphismEquivalences]] -> Catenate[Outer[tensorProductSymbol, First /@ 
                 Normal[morphismAssociation], Last /@ categoryMorphismEquivalences]]]] /. Normal[arrowMappings] /. 
          Normal[objectMappings]] /. Rule -> Equal, #1 =!= True & ]; imageMorphismAssociation = 
      Association[Select[DeleteDuplicates[Normal[reduceArrowsFinal[reduceArrowsInitial[imageArrows, 
            imageArrowEquivalences], imageQuiverObjectEquivalences]]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[imageCompositions = Select[Tuples[Normal[imageMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[imageMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], 
             compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ imageCompositions, Length[reduceObjects[imageObjects, 
        imageQuiverObjectEquivalences]]]; imageMorphismAssociation = 
      Association[Select[Normal[imageMorphismAssociation], Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[imageMorphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[imageObjects, imageQuiverObjectEquivalences]; 
     imageMorphismAssociation = Association[DeleteDuplicates[Normal[imageMorphismAssociation] //. 
         {compositionSymbol[tensorProductSymbol[x_, y_], tensorProductSymbol[z_, w_]] :> 
           tensorProductSymbol[compositionSymbol[x, z], compositionSymbol[y, w]], 
          compositionSymbol[x_, identitySymbol[y_]] :> x, compositionSymbol[identitySymbol[x_], y_] :> y, 
          compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[compositionSymbol[x, y], z]}]]; 
     Length[Normal[reduceArrowsFinal[reduceArrowsInitial[domainMorphismAssociation, categoryMorphismEquivalences], 
         categoryObjectEquivalences]]] -> Length[Normal[reduceArrowsFinal[reduceArrowsFinal[
          reduceArrowsFinal[reduceArrowsInitial[reduceArrowsInitial[imageMorphismAssociation, imageMorphismEquivalences], 
            morphismEquivalences], imageObjectEquivalences], monoidalEquations], objectEquivalences]]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "ObjectMappings" -> objectMappings_Association, "TensorProductSymbol" -> tensorProductSymbol_, 
     "UnitObject" -> unitObject_]]["TensorProductSymbol"] := tensorProductSymbol /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "ObjectMappings" -> objectMappings_Association, "TensorProductSymbol" -> tensorProductSymbol_, 
     "UnitObject" -> unitObject_]]["UnitObject"] := unitObject /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"
AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "ObjectMappings" -> objectMappings_Association, "TensorProductSymbol" -> tensorProductSymbol_, 
     "UnitObject" -> unitObject_]]["Category"] := 
  ResourceFunction["AbstractCategory"][Association["CompositionSymbol" -> compositionSymbol, 
     "IdentitySymbol" -> identitySymbol, "MorphismEquivalences" -> categoryMorphismEquivalences, 
     "ObjectEquivalences" -> categoryObjectEquivalences, "Quiver" -> ResourceFunction["AbstractQuiver"][
       Association["ArrowEquivalences" -> arrowEquivalences, "Arrows" -> arrows, "ObjectEquivalences" -> 
         quiverObjectEquivalences, "Objects" -> objects]]]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"
AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "ObjectMappings" -> objectMappings_Association, "TensorProductSymbol" -> tensorProductSymbol_, 
     "UnitObject" -> unitObject_]]["DualStrictMonoidalCategory"] := 
  AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings, 
     "Category" -> ResourceFunction["AbstractCategory"][Association["CompositionSymbol" -> compositionSymbol, 
        "IdentitySymbol" -> identitySymbol, "MorphismEquivalences" -> (categoryMorphismEquivalences /. 
          {compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[z, compositionSymbol[y, x]], 
           compositionSymbol[compositionSymbol[x_, y_], z_] :> compositionSymbol[compositionSymbol[z, y], x], 
           compositionSymbol[x_, y_] :> compositionSymbol[y, x]}), "ObjectEquivalences" -> categoryObjectEquivalences, 
        "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> arrowEquivalences, 
           "Arrows" -> Association[(First[#1] -> Reverse[Last[#1]] & ) /@ Normal[arrows]], 
           "ObjectEquivalences" -> quiverObjectEquivalences, "Objects" -> objects]]]], 
     "MorphismEquivalences" -> (morphismEquivalences /. {compositionSymbol[x_, compositionSymbol[y_, z_]] :> 
         compositionSymbol[z, compositionSymbol[y, x]], compositionSymbol[compositionSymbol[x_, y_], z_] :> 
         compositionSymbol[compositionSymbol[z, y], x], compositionSymbol[x_, y_] :> compositionSymbol[y, x]}), 
     "ObjectEquivalences" -> objectEquivalences, "ObjectMappings" -> objectMappings, 
     "TensorProductSymbol" -> tensorProductSymbol, "UnitObject" -> unitObject]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "ObjectMappings" -> objectMappings_Association, "TensorProductSymbol" -> tensorProductSymbol_, 
     "UnitObject" -> unitObject_]]["ObjectMappings"] := 
  Join[Association[(#1 -> #1 & ) /@ Catenate[Outer[tensorProductSymbol, objects, objects]]], objectMappings] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "ObjectMappings" -> objectMappings_Association, "TensorProductSymbol" -> tensorProductSymbol_, 
     "UnitObject" -> unitObject_]]["ObjectMappingCount"] := 
  Length[Normal[Join[Association[(#1 -> #1 & ) /@ Catenate[Outer[tensorProductSymbol, objects, objects]]], 
      objectMappings]]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"
AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "ObjectMappings" -> objectMappings_Association, "TensorProductSymbol" -> tensorProductSymbol_, 
     "UnitObject" -> unitObject_]]["ReducedObjectMappings"] := 
  Module[{objectFunction, associatorEquations, leftUnitorEquations, rightUnitorEquations, monoidalEquations}, 
    objectFunction = Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ Catenate[Outer[tensorProductSymbol, 
               reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], reduceObjects[
                reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences]]]]] -> 
          reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Values[Association[(#1 -> #1 & ) /@ Catenate[
                Outer[tensorProductSymbol, reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
                  categoryObjectEquivalences], reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
                  categoryObjectEquivalences]]]]], quiverObjectEquivalences], categoryObjectEquivalences]]], 
       Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[objectMappings], 
            quiverObjectEquivalences], categoryObjectEquivalences] -> reduceObjectsWithDuplicates[
           reduceObjectsWithDuplicates[Values[objectMappings], quiverObjectEquivalences], categoryObjectEquivalences]]]]; 
     associatorEquations = DeleteDuplicates[Select[reduceObjects[
         (tensorProductSymbol[#1[[1]], tensorProductSymbol[#1[[2]], #1[[3]]]] == tensorProductSymbol[
              tensorProductSymbol[#1[[1]], #1[[2]]], #1[[3]]] /. Normal[objectFunction] & ) /@ 
          Tuples[reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 3], 
         objectEquivalences], #1 =!= True & ]]; leftUnitorEquations = 
      DeleteDuplicates[Select[reduceObjects[(tensorProductSymbol[unitObject, #1] == #1 /. Normal[objectFunction] & ) /@ 
          reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 
         objectEquivalences], #1 =!= True & ]]; rightUnitorEquations = 
      DeleteDuplicates[Select[reduceObjects[(tensorProductSymbol[#1, unitObject] == #1 /. Normal[objectFunction] & ) /@ 
          reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 
         objectEquivalences], #1 =!= True & ]]; monoidalEquations = DeleteDuplicates[
       Join[associatorEquations, leftUnitorEquations, rightUnitorEquations]]; 
     Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ Catenate[Outer[tensorProductSymbol, 
              reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 
              reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences]]]]] -> 
         reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[
            reduceObjectsWithDuplicates[Values[Association[(#1 -> #1 & ) /@ Catenate[Outer[tensorProductSymbol, 
                  reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 
                  reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences]]]]], 
             quiverObjectEquivalences], categoryObjectEquivalences], monoidalEquations], objectEquivalences]]], 
      Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[objectMappings], 
           quiverObjectEquivalences], categoryObjectEquivalences] -> reduceObjectsWithDuplicates[
          reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Values[objectMappings], 
             quiverObjectEquivalences], categoryObjectEquivalences], monoidalEquations], objectEquivalences]]]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "ObjectMappings" -> objectMappings_Association, "TensorProductSymbol" -> tensorProductSymbol_, 
     "UnitObject" -> unitObject_]]["ReducedObjectMappingCount"] := 
  Module[{objectFunction, associatorEquations, leftUnitorEquations, rightUnitorEquations, monoidalEquations}, 
    objectFunction = Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ Catenate[Outer[tensorProductSymbol, 
               reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], reduceObjects[
                reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences]]]]] -> 
          reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Values[Association[(#1 -> #1 & ) /@ Catenate[
                Outer[tensorProductSymbol, reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
                  categoryObjectEquivalences], reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
                  categoryObjectEquivalences]]]]], quiverObjectEquivalences], categoryObjectEquivalences]]], 
       Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[objectMappings], 
            quiverObjectEquivalences], categoryObjectEquivalences] -> reduceObjectsWithDuplicates[
           reduceObjectsWithDuplicates[Values[objectMappings], quiverObjectEquivalences], categoryObjectEquivalences]]]]; 
     associatorEquations = DeleteDuplicates[Select[reduceObjects[
         (tensorProductSymbol[#1[[1]], tensorProductSymbol[#1[[2]], #1[[3]]]] == tensorProductSymbol[
              tensorProductSymbol[#1[[1]], #1[[2]]], #1[[3]]] /. Normal[objectFunction] & ) /@ 
          Tuples[reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 3], 
         objectEquivalences], #1 =!= True & ]]; leftUnitorEquations = 
      DeleteDuplicates[Select[reduceObjects[(tensorProductSymbol[unitObject, #1] == #1 /. Normal[objectFunction] & ) /@ 
          reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 
         objectEquivalences], #1 =!= True & ]]; rightUnitorEquations = 
      DeleteDuplicates[Select[reduceObjects[(tensorProductSymbol[#1, unitObject] == #1 /. Normal[objectFunction] & ) /@ 
          reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 
         objectEquivalences], #1 =!= True & ]]; monoidalEquations = DeleteDuplicates[
       Join[associatorEquations, leftUnitorEquations, rightUnitorEquations]]; 
     Length[Normal[Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ Catenate[Outer[tensorProductSymbol, 
                reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 
                reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences]]]]] -> 
           reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[
              reduceObjectsWithDuplicates[Values[Association[(#1 -> #1 & ) /@ Catenate[Outer[tensorProductSymbol, 
                    reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 
                    reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences]]]]], 
               quiverObjectEquivalences], categoryObjectEquivalences], monoidalEquations], objectEquivalences]]], 
        Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[objectMappings], 
             quiverObjectEquivalences], categoryObjectEquivalences] -> reduceObjectsWithDuplicates[
            reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Values[objectMappings], 
               quiverObjectEquivalences], categoryObjectEquivalences], monoidalEquations], objectEquivalences]]]]]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "ObjectMappings" -> objectMappings_Association, "TensorProductSymbol" -> tensorProductSymbol_, 
     "UnitObject" -> unitObject_]]["ArrowMappings"] := 
  Module[{productArrows}, productArrows = DeleteDuplicates[
       Join[Catenate[Outer[tensorProductSymbol, First /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ], 
          First /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]], 
        Catenate[Outer[tensorProductSymbol, First /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ], 
          identitySymbol /@ objects]], Catenate[Outer[tensorProductSymbol, identitySymbol /@ objects, 
          First /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]]]]; 
     Join[Association[(#1 -> #1 & ) /@ productArrows], arrowMappings]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "ObjectMappings" -> objectMappings_Association, "TensorProductSymbol" -> tensorProductSymbol_, 
     "UnitObject" -> unitObject_]]["ArrowMappingCount"] := 
  Module[{productArrows}, productArrows = DeleteDuplicates[
       Join[Catenate[Outer[tensorProductSymbol, First /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ], 
          First /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]], 
        Catenate[Outer[tensorProductSymbol, First /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ], 
          identitySymbol /@ objects]], Catenate[Outer[tensorProductSymbol, identitySymbol /@ objects, 
          First /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]]]]; 
     Length[Normal[Join[Association[(#1 -> #1 & ) /@ productArrows], arrowMappings]]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "ObjectMappings" -> objectMappings_Association, "TensorProductSymbol" -> tensorProductSymbol_, 
     "UnitObject" -> unitObject_]]["MorphismMappings"] := 
  Module[{objectListWithDuplicates, productArrows, arrowListWithDuplicates, domainMorphismList, domainCompositions, 
     imageMorphismList, imageCompositions, productMappings}, 
    objectListWithDuplicates = Catenate[Outer[tensorProductSymbol, objects, objects]] /. Normal[objectMappings]; 
     productArrows = Association[DeleteDuplicates[
        Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ Select[Normal[arrows], First[Last[#1]] =!= 
                 Last[Last[#1]] & ], First /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]] -> 
           Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ], (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ]]], Catenate[Outer[tensorProductSymbol, (Last[Last[#1]] & ) /@ 
                Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ], (Last[Last[#1]] & ) /@ 
                Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]]]]], 
         Thread[Catenate[Outer[tensorProductSymbol, First /@ Select[Normal[arrows], First[Last[#1]] =!= 
                 Last[Last[#1]] & ], identitySymbol /@ objects]] -> 
           Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ], objects]], Catenate[Outer[tensorProductSymbol, 
               (Last[Last[#1]] & ) /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ], objects]]]]], 
         Thread[Catenate[Outer[tensorProductSymbol, identitySymbol /@ objects, First /@ Select[Normal[arrows], 
               First[Last[#1]] =!= Last[Last[#1]] & ]]] -> Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, 
               objects, (First[Last[#1]] & ) /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]], 
             Catenate[Outer[tensorProductSymbol, objects, (Last[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ]]]]]]]]]; arrowListWithDuplicates = 
      Normal[productArrows] /. Normal[arrowMappings] /. Normal[objectMappings]; 
     domainMorphismList = Select[Normal[productArrows], First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[domainCompositions = Select[Tuples[domainMorphismList, 2], Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ domainMorphismList, 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], domainMorphismList = 
           Append[domainMorphismList, compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ domainCompositions, 
      Length[Catenate[Outer[tensorProductSymbol, objects, objects]]]]; domainMorphismList = 
      Select[domainMorphismList, Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        domainMorphismList = Append[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      Catenate[Outer[tensorProductSymbol, objects, objects]]; imageMorphismList = Select[arrowListWithDuplicates, 
       First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[imageCompositions = Select[Tuples[imageMorphismList, 2], Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ imageMorphismList, 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], imageMorphismList = 
           Append[imageMorphismList, compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ imageCompositions, 
      Length[objectListWithDuplicates]]; imageMorphismList = Select[imageMorphismList, 
       Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[imageMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        imageMorphismList = Append[imageMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      objectListWithDuplicates; productMappings = DeleteDuplicates[
       Thread[First /@ domainMorphismList -> First /@ imageMorphismList] //. 
        {compositionSymbol[tensorProductSymbol[x_, y_], tensorProductSymbol[z_, w_]] :> 
          tensorProductSymbol[compositionSymbol[x, z], compositionSymbol[y, w]], 
         compositionSymbol[x_, identitySymbol[y_]] :> x, compositionSymbol[identitySymbol[x_], y_] :> y, 
         compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[compositionSymbol[x, y], z]}]; 
     productMappings = Select[productMappings, Counts[First /@ productMappings][First[#1]] == 1 || 
         First[#1] =!= Last[#1] & ]; Association[Thread[First /@ productMappings -> (Last /@ productMappings /. 
         Normal[arrowMappings])]]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"
AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "ObjectMappings" -> objectMappings_Association, "TensorProductSymbol" -> tensorProductSymbol_, 
     "UnitObject" -> unitObject_]]["MorphismMappingCount"] := 
  Module[{objectListWithDuplicates, productArrows, arrowListWithDuplicates, domainMorphismList, domainCompositions, 
     imageMorphismList, imageCompositions, productMappings}, 
    objectListWithDuplicates = Catenate[Outer[tensorProductSymbol, objects, objects]] /. Normal[objectMappings]; 
     productArrows = Association[DeleteDuplicates[
        Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ Select[Normal[arrows], First[Last[#1]] =!= 
                 Last[Last[#1]] & ], First /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]] -> 
           Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ], (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ]]], Catenate[Outer[tensorProductSymbol, (Last[Last[#1]] & ) /@ 
                Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ], (Last[Last[#1]] & ) /@ 
                Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]]]]], 
         Thread[Catenate[Outer[tensorProductSymbol, First /@ Select[Normal[arrows], First[Last[#1]] =!= 
                 Last[Last[#1]] & ], identitySymbol /@ objects]] -> 
           Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ], objects]], Catenate[Outer[tensorProductSymbol, 
               (Last[Last[#1]] & ) /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ], objects]]]]], 
         Thread[Catenate[Outer[tensorProductSymbol, identitySymbol /@ objects, First /@ Select[Normal[arrows], 
               First[Last[#1]] =!= Last[Last[#1]] & ]]] -> Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, 
               objects, (First[Last[#1]] & ) /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]], 
             Catenate[Outer[tensorProductSymbol, objects, (Last[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ]]]]]]]]]; arrowListWithDuplicates = 
      Normal[productArrows] /. Normal[arrowMappings] /. Normal[objectMappings]; 
     domainMorphismList = Select[Normal[productArrows], First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[domainCompositions = Select[Tuples[domainMorphismList, 2], Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ domainMorphismList, 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], domainMorphismList = 
           Append[domainMorphismList, compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ domainCompositions, 
      Length[Catenate[Outer[tensorProductSymbol, objects, objects]]]]; domainMorphismList = 
      Select[domainMorphismList, Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        domainMorphismList = Append[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      Catenate[Outer[tensorProductSymbol, objects, objects]]; imageMorphismList = Select[arrowListWithDuplicates, 
       First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[imageCompositions = Select[Tuples[imageMorphismList, 2], Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ imageMorphismList, 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], imageMorphismList = 
           Append[imageMorphismList, compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ imageCompositions, 
      Length[objectListWithDuplicates]]; imageMorphismList = Select[imageMorphismList, 
       Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[imageMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        imageMorphismList = Append[imageMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      objectListWithDuplicates; productMappings = DeleteDuplicates[
       Thread[First /@ domainMorphismList -> First /@ imageMorphismList] //. 
        {compositionSymbol[tensorProductSymbol[x_, y_], tensorProductSymbol[z_, w_]] :> 
          tensorProductSymbol[compositionSymbol[x, z], compositionSymbol[y, w]], 
         compositionSymbol[x_, identitySymbol[y_]] :> x, compositionSymbol[identitySymbol[x_], y_] :> y, 
         compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[compositionSymbol[x, y], z]}]; 
     productMappings = Select[productMappings, Counts[First /@ productMappings][First[#1]] == 1 || 
         First[#1] =!= Last[#1] & ]; 
     Length[Normal[Association[Thread[First /@ productMappings -> (Last /@ productMappings /. 
           Normal[arrowMappings])]]]]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"
AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "ObjectMappings" -> objectMappings_Association, "TensorProductSymbol" -> tensorProductSymbol_, 
     "UnitObject" -> unitObject_]]["ReducedMorphismMappings"] := 
  Module[{objectFunction, associatorEquations, leftUnitorEquations, rightUnitorEquations, monoidalEquations, 
     objectListWithDuplicates, productArrows, arrowListWithDuplicates, domainMorphismList, domainCompositions, 
     morphismAssociation, compositions, imageQuiverObjectEquivalences, imageObjectEquivalences, imageArrowEquivalences, 
     imageMorphismEquivalences, imageMorphismList, imageCompositions, productMappings}, 
    objectFunction = Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ Catenate[Outer[tensorProductSymbol, 
               reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], reduceObjects[
                reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences]]]]] -> 
          reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Values[Association[(#1 -> #1 & ) /@ Catenate[
                Outer[tensorProductSymbol, reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
                  categoryObjectEquivalences], reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
                  categoryObjectEquivalences]]]]], quiverObjectEquivalences], categoryObjectEquivalences]]], 
       Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[objectMappings], 
            quiverObjectEquivalences], categoryObjectEquivalences] -> reduceObjectsWithDuplicates[
           reduceObjectsWithDuplicates[Values[objectMappings], quiverObjectEquivalences], categoryObjectEquivalences]]]]; 
     associatorEquations = DeleteDuplicates[Select[reduceObjects[
         (tensorProductSymbol[#1[[1]], tensorProductSymbol[#1[[2]], #1[[3]]]] == tensorProductSymbol[
              tensorProductSymbol[#1[[1]], #1[[2]]], #1[[3]]] /. Normal[objectFunction] & ) /@ 
          Tuples[reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 3], 
         objectEquivalences], #1 =!= True & ]]; leftUnitorEquations = 
      DeleteDuplicates[Select[reduceObjects[(tensorProductSymbol[unitObject, #1] == #1 /. Normal[objectFunction] & ) /@ 
          reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 
         objectEquivalences], #1 =!= True & ]]; rightUnitorEquations = 
      DeleteDuplicates[Select[reduceObjects[(tensorProductSymbol[#1, unitObject] == #1 /. Normal[objectFunction] & ) /@ 
          reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 
         objectEquivalences], #1 =!= True & ]]; monoidalEquations = DeleteDuplicates[
       Join[associatorEquations, leftUnitorEquations, rightUnitorEquations]]; 
     objectListWithDuplicates = Catenate[Outer[tensorProductSymbol, objects, objects]] /. Normal[objectMappings]; 
     productArrows = Association[DeleteDuplicates[
        Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ Select[Normal[arrows], First[Last[#1]] =!= 
                 Last[Last[#1]] & ], First /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]] -> 
           Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ], (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ]]], Catenate[Outer[tensorProductSymbol, (Last[Last[#1]] & ) /@ 
                Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ], (Last[Last[#1]] & ) /@ 
                Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]]]]], 
         Thread[Catenate[Outer[tensorProductSymbol, First /@ Select[Normal[arrows], First[Last[#1]] =!= 
                 Last[Last[#1]] & ], identitySymbol /@ objects]] -> 
           Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ], objects]], Catenate[Outer[tensorProductSymbol, 
               (Last[Last[#1]] & ) /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ], objects]]]]], 
         Thread[Catenate[Outer[tensorProductSymbol, identitySymbol /@ objects, First /@ Select[Normal[arrows], 
               First[Last[#1]] =!= Last[Last[#1]] & ]]] -> Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, 
               objects, (First[Last[#1]] & ) /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]], 
             Catenate[Outer[tensorProductSymbol, objects, (Last[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ]]]]]]]]]; arrowListWithDuplicates = 
      Normal[productArrows] /. Normal[arrowMappings] /. Normal[objectMappings]; 
     domainMorphismList = Select[reduceArrowsFinalWithDuplicates[reduceArrowsInitialWithDuplicates[Normal[productArrows], 
         arrowEquivalences], quiverObjectEquivalences], First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[domainCompositions = Select[Tuples[domainMorphismList, 2], Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ domainMorphismList, 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], domainMorphismList = 
           Append[domainMorphismList, compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ domainCompositions, 
      Length[reduceObjects[Catenate[Outer[tensorProductSymbol, objects, objects]], quiverObjectEquivalences]]]; 
     domainMorphismList = Select[domainMorphismList, Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        domainMorphismList = Append[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      reduceObjects[Catenate[Outer[tensorProductSymbol, objects, objects]], quiverObjectEquivalences]; 
     domainMorphismList = reduceArrowsFinalWithDuplicates[reduceArrowsInitialWithDuplicates[domainMorphismList, 
        categoryMorphismEquivalences], categoryObjectEquivalences]; morphismAssociation = 
      Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
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
            DirectedEdge[#1, #1]]]] & ) /@ objects; imageQuiverObjectEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ quiverObjectEquivalences, 
               objects]] -> Catenate[Outer[tensorProductSymbol, Last /@ quiverObjectEquivalences, objects]]], 
           Thread[Catenate[Outer[tensorProductSymbol, objects, First /@ quiverObjectEquivalences]] -> 
             Catenate[Outer[tensorProductSymbol, objects, Last /@ quiverObjectEquivalences]]]] /. 
          Normal[objectMappings]] /. Rule -> Equal, #1 =!= True & ]; imageObjectEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ categoryObjectEquivalences, 
               objects]] -> Catenate[Outer[tensorProductSymbol, Last /@ categoryObjectEquivalences, objects]]], 
           Thread[Catenate[Outer[tensorProductSymbol, objects, First /@ categoryObjectEquivalences]] -> 
             Catenate[Outer[tensorProductSymbol, objects, Last /@ categoryObjectEquivalences]]]] /. 
          Normal[objectMappings]] /. Rule -> Equal, #1 =!= True & ]; imageArrowEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ arrowEquivalences, First /@ 
                Normal[arrows]]] -> Catenate[Outer[tensorProductSymbol, Last /@ arrowEquivalences, First /@ 
                Normal[arrows]]]], Thread[Catenate[Outer[tensorProductSymbol, First /@ Normal[arrows], First /@ 
                arrowEquivalences]] -> Catenate[Outer[tensorProductSymbol, First /@ Normal[arrows], Last /@ 
                arrowEquivalences]]]] /. Normal[arrowMappings]] /. Rule -> Equal, #1 =!= True & ]; 
     imageMorphismEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ categoryMorphismEquivalences, 
                First /@ Normal[morphismAssociation]]] -> Catenate[Outer[tensorProductSymbol, 
                Last /@ categoryMorphismEquivalences, First /@ Normal[morphismAssociation]]]], 
            Thread[Catenate[Outer[tensorProductSymbol, First /@ Normal[morphismAssociation], First /@ 
                 categoryMorphismEquivalences]] -> Catenate[Outer[tensorProductSymbol, First /@ 
                 Normal[morphismAssociation], Last /@ categoryMorphismEquivalences]]]] /. Normal[arrowMappings] /. 
          Normal[objectMappings]] /. Rule -> Equal, #1 =!= True & ]; imageMorphismList = 
      Select[reduceArrowsFinalWithDuplicates[reduceArrowsInitialWithDuplicates[arrowListWithDuplicates, 
         imageArrowEquivalences], imageQuiverObjectEquivalences], First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[imageCompositions = Select[Tuples[imageMorphismList, 2], Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ imageMorphismList, 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], imageMorphismList = 
           Append[imageMorphismList, compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ imageCompositions, 
      Length[reduceObjectsWithDuplicates[objectListWithDuplicates, imageQuiverObjectEquivalences]]]; 
     imageMorphismList = Select[imageMorphismList, Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[imageMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        imageMorphismList = Append[imageMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      reduceObjectsWithDuplicates[objectListWithDuplicates, imageQuiverObjectEquivalences]; 
     imageMorphismList = reduceArrowsFinalWithDuplicates[reduceArrowsFinalWithDuplicates[
        reduceArrowsFinalWithDuplicates[reduceArrowsInitialWithDuplicates[reduceArrowsInitialWithDuplicates[
           imageMorphismList, imageMorphismEquivalences], morphismEquivalences], imageObjectEquivalences], 
        monoidalEquations], objectEquivalences]; productMappings = DeleteDuplicates[
       Thread[First /@ domainMorphismList -> First /@ imageMorphismList] //. 
        {compositionSymbol[tensorProductSymbol[x_, y_], tensorProductSymbol[z_, w_]] :> 
          tensorProductSymbol[compositionSymbol[x, z], compositionSymbol[y, w]], 
         compositionSymbol[x_, identitySymbol[y_]] :> x, compositionSymbol[identitySymbol[x_], y_] :> y, 
         compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[compositionSymbol[x, y], z]}]; 
     productMappings = Select[productMappings, Counts[First /@ productMappings][First[#1]] == 1 || 
         First[#1] =!= Last[#1] & ]; Association[Thread[First /@ productMappings -> (Last /@ productMappings /. 
         Normal[arrowMappings])]]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"
AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "ObjectMappings" -> objectMappings_Association, "TensorProductSymbol" -> tensorProductSymbol_, 
     "UnitObject" -> unitObject_]]["ReducedMorphismMappingCount"] := 
  Module[{objectFunction, associatorEquations, leftUnitorEquations, rightUnitorEquations, monoidalEquations, 
     objectListWithDuplicates, productArrows, arrowListWithDuplicates, domainMorphismList, domainCompositions, 
     morphismAssociation, compositions, imageQuiverObjectEquivalences, imageObjectEquivalences, imageArrowEquivalences, 
     imageMorphismEquivalences, imageMorphismList, imageCompositions, productMappings}, 
    objectFunction = Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ Catenate[Outer[tensorProductSymbol, 
               reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], reduceObjects[
                reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences]]]]] -> 
          reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Values[Association[(#1 -> #1 & ) /@ Catenate[
                Outer[tensorProductSymbol, reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
                  categoryObjectEquivalences], reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
                  categoryObjectEquivalences]]]]], quiverObjectEquivalences], categoryObjectEquivalences]]], 
       Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[objectMappings], 
            quiverObjectEquivalences], categoryObjectEquivalences] -> reduceObjectsWithDuplicates[
           reduceObjectsWithDuplicates[Values[objectMappings], quiverObjectEquivalences], categoryObjectEquivalences]]]]; 
     associatorEquations = DeleteDuplicates[Select[reduceObjects[
         (tensorProductSymbol[#1[[1]], tensorProductSymbol[#1[[2]], #1[[3]]]] == tensorProductSymbol[
              tensorProductSymbol[#1[[1]], #1[[2]]], #1[[3]]] /. Normal[objectFunction] & ) /@ 
          Tuples[reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 3], 
         objectEquivalences], #1 =!= True & ]]; leftUnitorEquations = 
      DeleteDuplicates[Select[reduceObjects[(tensorProductSymbol[unitObject, #1] == #1 /. Normal[objectFunction] & ) /@ 
          reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 
         objectEquivalences], #1 =!= True & ]]; rightUnitorEquations = 
      DeleteDuplicates[Select[reduceObjects[(tensorProductSymbol[#1, unitObject] == #1 /. Normal[objectFunction] & ) /@ 
          reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 
         objectEquivalences], #1 =!= True & ]]; monoidalEquations = DeleteDuplicates[
       Join[associatorEquations, leftUnitorEquations, rightUnitorEquations]]; 
     objectListWithDuplicates = Catenate[Outer[tensorProductSymbol, objects, objects]] /. Normal[objectMappings]; 
     productArrows = Association[DeleteDuplicates[
        Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ Select[Normal[arrows], First[Last[#1]] =!= 
                 Last[Last[#1]] & ], First /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]] -> 
           Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ], (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ]]], Catenate[Outer[tensorProductSymbol, (Last[Last[#1]] & ) /@ 
                Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ], (Last[Last[#1]] & ) /@ 
                Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]]]]], 
         Thread[Catenate[Outer[tensorProductSymbol, First /@ Select[Normal[arrows], First[Last[#1]] =!= 
                 Last[Last[#1]] & ], identitySymbol /@ objects]] -> 
           Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ], objects]], Catenate[Outer[tensorProductSymbol, 
               (Last[Last[#1]] & ) /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ], objects]]]]], 
         Thread[Catenate[Outer[tensorProductSymbol, identitySymbol /@ objects, First /@ Select[Normal[arrows], 
               First[Last[#1]] =!= Last[Last[#1]] & ]]] -> Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, 
               objects, (First[Last[#1]] & ) /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]], 
             Catenate[Outer[tensorProductSymbol, objects, (Last[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ]]]]]]]]]; arrowListWithDuplicates = 
      Normal[productArrows] /. Normal[arrowMappings] /. Normal[objectMappings]; 
     domainMorphismList = Select[reduceArrowsFinalWithDuplicates[reduceArrowsInitialWithDuplicates[Normal[productArrows], 
         arrowEquivalences], quiverObjectEquivalences], First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[domainCompositions = Select[Tuples[domainMorphismList, 2], Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ domainMorphismList, 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], domainMorphismList = 
           Append[domainMorphismList, compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ domainCompositions, 
      Length[reduceObjects[Catenate[Outer[tensorProductSymbol, objects, objects]], quiverObjectEquivalences]]]; 
     domainMorphismList = Select[domainMorphismList, Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        domainMorphismList = Append[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      reduceObjects[Catenate[Outer[tensorProductSymbol, objects, objects]], quiverObjectEquivalences]; 
     domainMorphismList = reduceArrowsFinalWithDuplicates[reduceArrowsInitialWithDuplicates[domainMorphismList, 
        categoryMorphismEquivalences], categoryObjectEquivalences]; morphismAssociation = 
      Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
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
            DirectedEdge[#1, #1]]]] & ) /@ objects; imageQuiverObjectEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ quiverObjectEquivalences, 
               objects]] -> Catenate[Outer[tensorProductSymbol, Last /@ quiverObjectEquivalences, objects]]], 
           Thread[Catenate[Outer[tensorProductSymbol, objects, First /@ quiverObjectEquivalences]] -> 
             Catenate[Outer[tensorProductSymbol, objects, Last /@ quiverObjectEquivalences]]]] /. 
          Normal[objectMappings]] /. Rule -> Equal, #1 =!= True & ]; imageObjectEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ categoryObjectEquivalences, 
               objects]] -> Catenate[Outer[tensorProductSymbol, Last /@ categoryObjectEquivalences, objects]]], 
           Thread[Catenate[Outer[tensorProductSymbol, objects, First /@ categoryObjectEquivalences]] -> 
             Catenate[Outer[tensorProductSymbol, objects, Last /@ categoryObjectEquivalences]]]] /. 
          Normal[objectMappings]] /. Rule -> Equal, #1 =!= True & ]; imageArrowEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ arrowEquivalences, First /@ 
                Normal[arrows]]] -> Catenate[Outer[tensorProductSymbol, Last /@ arrowEquivalences, First /@ 
                Normal[arrows]]]], Thread[Catenate[Outer[tensorProductSymbol, First /@ Normal[arrows], First /@ 
                arrowEquivalences]] -> Catenate[Outer[tensorProductSymbol, First /@ Normal[arrows], Last /@ 
                arrowEquivalences]]]] /. Normal[arrowMappings]] /. Rule -> Equal, #1 =!= True & ]; 
     imageMorphismEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ categoryMorphismEquivalences, 
                First /@ Normal[morphismAssociation]]] -> Catenate[Outer[tensorProductSymbol, 
                Last /@ categoryMorphismEquivalences, First /@ Normal[morphismAssociation]]]], 
            Thread[Catenate[Outer[tensorProductSymbol, First /@ Normal[morphismAssociation], First /@ 
                 categoryMorphismEquivalences]] -> Catenate[Outer[tensorProductSymbol, First /@ 
                 Normal[morphismAssociation], Last /@ categoryMorphismEquivalences]]]] /. Normal[arrowMappings] /. 
          Normal[objectMappings]] /. Rule -> Equal, #1 =!= True & ]; imageMorphismList = 
      Select[reduceArrowsFinalWithDuplicates[reduceArrowsInitialWithDuplicates[arrowListWithDuplicates, 
         imageArrowEquivalences], imageQuiverObjectEquivalences], First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[imageCompositions = Select[Tuples[imageMorphismList, 2], Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ imageMorphismList, 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], imageMorphismList = 
           Append[imageMorphismList, compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ imageCompositions, 
      Length[reduceObjectsWithDuplicates[objectListWithDuplicates, imageQuiverObjectEquivalences]]]; 
     imageMorphismList = Select[imageMorphismList, Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[imageMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        imageMorphismList = Append[imageMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      reduceObjectsWithDuplicates[objectListWithDuplicates, imageQuiverObjectEquivalences]; 
     imageMorphismList = reduceArrowsFinalWithDuplicates[reduceArrowsFinalWithDuplicates[
        reduceArrowsFinalWithDuplicates[reduceArrowsInitialWithDuplicates[reduceArrowsInitialWithDuplicates[
           imageMorphismList, imageMorphismEquivalences], morphismEquivalences], imageObjectEquivalences], 
        monoidalEquations], objectEquivalences]; productMappings = DeleteDuplicates[
       Thread[First /@ domainMorphismList -> First /@ imageMorphismList] //. 
        {compositionSymbol[tensorProductSymbol[x_, y_], tensorProductSymbol[z_, w_]] :> 
          tensorProductSymbol[compositionSymbol[x, z], compositionSymbol[y, w]], 
         compositionSymbol[x_, identitySymbol[y_]] :> x, compositionSymbol[identitySymbol[x_], y_] :> y, 
         compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[compositionSymbol[x, y], z]}]; 
     productMappings = Select[productMappings, Counts[First /@ productMappings][First[#1]] == 1 || 
         First[#1] =!= Last[#1] & ]; 
     Length[Normal[Association[Thread[First /@ productMappings -> (Last /@ productMappings /. 
           Normal[arrowMappings])]]]]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"
AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "ObjectMappings" -> objectMappings_Association, "TensorProductSymbol" -> tensorProductSymbol_, 
     "UnitObject" -> unitObject_]]["ValidStrictMonoidalCategoryQ"] := 
  Module[{objectFunction, associatorEquations, leftUnitorEquations, rightUnitorEquations, monoidalEquations, 
     productArrows, morphismAssociation, compositions, reducedMorphismAssociation, reducedCompositions, imageObjects, 
     imageArrows, imageQuiverObjectEquivalences, imageObjectEquivalences, imageArrowEquivalences, 
     imageMorphismEquivalences, imageMorphismAssociation, imageCompositions}, 
    objectFunction = Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ Catenate[Outer[tensorProductSymbol, 
               reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], reduceObjects[
                reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences]]]]] -> 
          reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Values[Association[(#1 -> #1 & ) /@ Catenate[
                Outer[tensorProductSymbol, reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
                  categoryObjectEquivalences], reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
                  categoryObjectEquivalences]]]]], quiverObjectEquivalences], categoryObjectEquivalences]]], 
       Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[objectMappings], 
            quiverObjectEquivalences], categoryObjectEquivalences] -> reduceObjectsWithDuplicates[
           reduceObjectsWithDuplicates[Values[objectMappings], quiverObjectEquivalences], categoryObjectEquivalences]]]]; 
     associatorEquations = DeleteDuplicates[Select[reduceObjects[
         (tensorProductSymbol[#1[[1]], tensorProductSymbol[#1[[2]], #1[[3]]]] == tensorProductSymbol[
              tensorProductSymbol[#1[[1]], #1[[2]]], #1[[3]]] /. Normal[objectFunction] & ) /@ 
          Tuples[reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 3], 
         objectEquivalences], #1 =!= True & ]]; leftUnitorEquations = 
      DeleteDuplicates[Select[reduceObjects[(tensorProductSymbol[unitObject, #1] == #1 /. Normal[objectFunction] & ) /@ 
          reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 
         objectEquivalences], #1 =!= True & ]]; rightUnitorEquations = 
      DeleteDuplicates[Select[reduceObjects[(tensorProductSymbol[#1, unitObject] == #1 /. Normal[objectFunction] & ) /@ 
          reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 
         objectEquivalences], #1 =!= True & ]]; monoidalEquations = DeleteDuplicates[
       Join[associatorEquations, leftUnitorEquations, rightUnitorEquations]]; 
     productArrows = Association[DeleteDuplicates[
        Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ Select[Normal[arrows], First[Last[#1]] =!= 
                 Last[Last[#1]] & ], First /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]] -> 
           Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ], (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ]]], Catenate[Outer[tensorProductSymbol, (Last[Last[#1]] & ) /@ 
                Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ], (Last[Last[#1]] & ) /@ 
                Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]]]]], 
         Thread[Catenate[Outer[tensorProductSymbol, First /@ Select[Normal[arrows], First[Last[#1]] =!= 
                 Last[Last[#1]] & ], identitySymbol /@ objects]] -> 
           Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ], objects]], Catenate[Outer[tensorProductSymbol, 
               (Last[Last[#1]] & ) /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ], objects]]]]], 
         Thread[Catenate[Outer[tensorProductSymbol, identitySymbol /@ objects, First /@ Select[Normal[arrows], 
               First[Last[#1]] =!= Last[Last[#1]] & ]]] -> Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, 
               objects, (First[Last[#1]] & ) /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]], 
             Catenate[Outer[tensorProductSymbol, objects, (Last[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ]]]]]]]]]; morphismAssociation = 
      Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
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
     imageObjects = DeleteDuplicates[Catenate[Outer[tensorProductSymbol, objects, objects]] /. Normal[objectMappings]]; 
     imageArrows = Association[DeleteDuplicates[Normal[productArrows] /. Normal[arrowMappings] /. 
         Normal[objectMappings]]]; imageQuiverObjectEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ quiverObjectEquivalences, 
               objects]] -> Catenate[Outer[tensorProductSymbol, Last /@ quiverObjectEquivalences, objects]]], 
           Thread[Catenate[Outer[tensorProductSymbol, objects, First /@ quiverObjectEquivalences]] -> 
             Catenate[Outer[tensorProductSymbol, objects, Last /@ quiverObjectEquivalences]]]] /. 
          Normal[objectMappings]] /. Rule -> Equal, #1 =!= True & ]; imageObjectEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ categoryObjectEquivalences, 
               objects]] -> Catenate[Outer[tensorProductSymbol, Last /@ categoryObjectEquivalences, objects]]], 
           Thread[Catenate[Outer[tensorProductSymbol, objects, First /@ categoryObjectEquivalences]] -> 
             Catenate[Outer[tensorProductSymbol, objects, Last /@ categoryObjectEquivalences]]]] /. 
          Normal[objectMappings]] /. Rule -> Equal, #1 =!= True & ]; imageArrowEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ arrowEquivalences, First /@ 
                Normal[arrows]]] -> Catenate[Outer[tensorProductSymbol, Last /@ arrowEquivalences, First /@ 
                Normal[arrows]]]], Thread[Catenate[Outer[tensorProductSymbol, First /@ Normal[arrows], First /@ 
                arrowEquivalences]] -> Catenate[Outer[tensorProductSymbol, First /@ Normal[arrows], Last /@ 
                arrowEquivalences]]]] /. Normal[arrowMappings]] /. Rule -> Equal, #1 =!= True & ]; 
     imageMorphismEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ categoryMorphismEquivalences, 
                First /@ Normal[morphismAssociation]]] -> Catenate[Outer[tensorProductSymbol, 
                Last /@ categoryMorphismEquivalences, First /@ Normal[morphismAssociation]]]], 
            Thread[Catenate[Outer[tensorProductSymbol, First /@ Normal[morphismAssociation], First /@ 
                 categoryMorphismEquivalences]] -> Catenate[Outer[tensorProductSymbol, First /@ 
                 Normal[morphismAssociation], Last /@ categoryMorphismEquivalences]]]] /. Normal[arrowMappings] /. 
          Normal[objectMappings]] /. Rule -> Equal, #1 =!= True & ]; imageMorphismAssociation = 
      Association[Select[DeleteDuplicates[Normal[reduceArrowsFinal[reduceArrowsInitial[imageArrows, 
            imageArrowEquivalences], imageQuiverObjectEquivalences]]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[imageCompositions = Select[Tuples[Normal[imageMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[imageMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], 
             compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ imageCompositions, Length[reduceObjects[imageObjects, 
        imageQuiverObjectEquivalences]]]; imageMorphismAssociation = 
      Association[Select[Normal[imageMorphismAssociation], Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[imageMorphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[imageObjects, imageQuiverObjectEquivalences]; 
     imageMorphismAssociation = Association[DeleteDuplicates[Normal[imageMorphismAssociation] //. 
         {compositionSymbol[tensorProductSymbol[x_, y_], tensorProductSymbol[z_, w_]] :> 
           tensorProductSymbol[compositionSymbol[x, z], compositionSymbol[y, w]], 
          compositionSymbol[x_, identitySymbol[y_]] :> x, compositionSymbol[identitySymbol[x_], y_] :> y, 
          compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[compositionSymbol[x, y], z]}]]; 
     Sort[reduceObjects[reduceObjects[objects, quiverObjectEquivalences], objectEquivalences]] === 
       Sort[reduceObjects[reduceObjects[reduceObjects[reduceObjects[imageObjects, imageQuiverObjectEquivalences], 
           imageObjectEquivalences], monoidalEquations], objectEquivalences]] && 
      Sort[(First[#1] -> DirectedEdge @@ Last[#1] & ) /@ Normal[reduceArrowsFinal[reduceArrowsInitial[
            reducedMorphismAssociation, categoryMorphismEquivalences], categoryObjectEquivalences]]] === 
       Sort[(First[#1] -> DirectedEdge @@ Last[#1] & ) /@ Normal[reduceArrowsFinal[reduceArrowsFinal[
            reduceArrowsFinal[reduceArrowsInitial[reduceArrowsInitial[imageMorphismAssociation, 
               imageMorphismEquivalences], morphismEquivalences], imageObjectEquivalences], monoidalEquations], 
           objectEquivalences]]]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"
AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "ObjectMappings" -> objectMappings_Association, "TensorProductSymbol" -> tensorProductSymbol_, 
     "UnitObject" -> unitObject_]]["FullLabeledStringDiagrams"] := 
  Module[{objectListWithDuplicates, productArrows, arrowListWithDuplicates, domainMorphismList, domainCompositions, 
     imageMorphismList, imageCompositions, productMappings, morphismMappings, domainMorphismAssociation, stringDiagrams}, 
    objectListWithDuplicates = Catenate[Outer[tensorProductSymbol, objects, objects]] /. Normal[objectMappings]; 
     productArrows = Association[DeleteDuplicates[
        Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ Select[Normal[arrows], First[Last[#1]] =!= 
                 Last[Last[#1]] & ], First /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]] -> 
           Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ], (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ]]], Catenate[Outer[tensorProductSymbol, (Last[Last[#1]] & ) /@ 
                Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ], (Last[Last[#1]] & ) /@ 
                Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]]]]], 
         Thread[Catenate[Outer[tensorProductSymbol, First /@ Select[Normal[arrows], First[Last[#1]] =!= 
                 Last[Last[#1]] & ], identitySymbol /@ objects]] -> 
           Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ], objects]], Catenate[Outer[tensorProductSymbol, 
               (Last[Last[#1]] & ) /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ], objects]]]]], 
         Thread[Catenate[Outer[tensorProductSymbol, identitySymbol /@ objects, First /@ Select[Normal[arrows], 
               First[Last[#1]] =!= Last[Last[#1]] & ]]] -> Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, 
               objects, (First[Last[#1]] & ) /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]], 
             Catenate[Outer[tensorProductSymbol, objects, (Last[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ]]]]]]]]]; arrowListWithDuplicates = 
      Normal[productArrows] /. Normal[arrowMappings] /. Normal[objectMappings]; 
     domainMorphismList = Select[Normal[productArrows], First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[domainCompositions = Select[Tuples[domainMorphismList, 2], Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ domainMorphismList, 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], domainMorphismList = 
           Append[domainMorphismList, compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ domainCompositions, 
      Length[Catenate[Outer[tensorProductSymbol, objects, objects]]]]; domainMorphismList = 
      Select[domainMorphismList, Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        domainMorphismList = Append[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      Catenate[Outer[tensorProductSymbol, objects, objects]]; imageMorphismList = Select[arrowListWithDuplicates, 
       First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[imageCompositions = Select[Tuples[imageMorphismList, 2], Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ imageMorphismList, 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], imageMorphismList = 
           Append[imageMorphismList, compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ imageCompositions, 
      Length[objectListWithDuplicates]]; imageMorphismList = Select[imageMorphismList, 
       Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[imageMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        imageMorphismList = Append[imageMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      objectListWithDuplicates; productMappings = DeleteDuplicates[Thread[First /@ domainMorphismList -> 
         First /@ imageMorphismList]]; productMappings = Select[productMappings, 
       Counts[First /@ productMappings][First[#1]] == 1 || First[#1] =!= Last[#1] & ]; 
     morphismMappings = Association[Thread[First /@ productMappings -> (Last /@ productMappings /. 
          Normal[arrowMappings])]]; domainMorphismAssociation = Association[domainMorphismList]; stringDiagrams = {}; 
     (Module[{domainMorphism = #1, morphismList, wires}, 
        morphismList = Reverse[Flatten[{First[domainMorphism] /. compositionSymbol -> List}]]; wires = {}; 
         (Module[{compositionIndex = #1}, (Module[{morphismIndex = #1}, wires = Append[wires, 
                  {(First[domainMorphismAssociation[morphismList[[compositionIndex]]]] /. tensorProductSymbol -> List)[[
                     morphismIndex]], compositionIndex, morphismIndex} -> DirectedEdge[If[compositionIndex == 1, 
                     {Null, compositionIndex, morphismIndex}, {(morphismList[[compositionIndex - 1]] /. 
                        tensorProductSymbol -> List)[[morphismIndex]], compositionIndex - 1, morphismIndex}], 
                    {(morphismList[[compositionIndex]] /. tensorProductSymbol -> List)[[morphismIndex]], 
                     compositionIndex, morphismIndex}]]; wires = Append[wires, {(Last[domainMorphismAssociation[
                        morphismList[[compositionIndex]]]] /. tensorProductSymbol -> List)[[morphismIndex]], 
                    compositionIndex + 1, morphismIndex} -> DirectedEdge[{(morphismList[[compositionIndex]] /. 
                       tensorProductSymbol -> List)[[morphismIndex]], compositionIndex, morphismIndex}, 
                    If[compositionIndex == Length[morphismList], {Null, compositionIndex + 1, morphismIndex}, 
                     {(morphismList[[compositionIndex + 1]] /. tensorProductSymbol -> List)[[morphismIndex]], 
                      compositionIndex + 1, morphismIndex}]]]] & ) /@ Range[Length[morphismList[[compositionIndex]] /. 
                tensorProductSymbol -> List]]] & ) /@ Range[Length[morphismList]]; wires = DeleteDuplicates[wires]; 
         (Module[{compositionIndex = #1}, (Module[{morphismMapping = #1, mapExists}, If[First[morphismMapping] =!= 
                 Last[morphismMapping], mapExists = True; (Module[{morphismIndex = #1}, If[ !MemberQ[Catenate[
                        Last /@ wires /. DirectedEdge -> List], {(First[morphismMapping] /. tensorProductSymbol -> List)[[
                         morphismIndex]], compositionIndex, morphismIndex}], mapExists = False]] & ) /@ 
                  Range[Length[First[morphismMapping] /. tensorProductSymbol -> List]]; If[mapExists === True, 
                  (Module[{morphismIndex = #1}, wires = wires /. {(First[morphismMapping] /. tensorProductSymbol -> 
                            List)[[morphismIndex]], compositionIndex, morphismIndex} -> {Last[morphismMapping], 
                         compositionIndex}] & ) /@ Range[Length[First[morphismMapping] /. tensorProductSymbol -> 
                       List]]]]] & ) /@ Normal[morphismMappings]] & ) /@ Range[Length[morphismList]]; 
         stringDiagrams = Append[stringDiagrams, (First[domainMorphism] /. Normal[morphismMappings]) -> 
            EdgeTaggedGraph[(Labeled[DirectedEdge @@ Last[#1], Placed[First[First[#1]], 0.5]] & ) /@ wires, 
             VertexSize -> 0.5, VertexStyle -> Join[(#1 -> Directive[Transparent, EdgeForm[None]] & ) /@ 
                Select[Catenate[Last /@ wires /. DirectedEdge -> List], First[#1] === Null & ], (#1 -> Transparent & ) /@ 
                Select[Catenate[Last /@ wires /. DirectedEdge -> List], Head[First[#1]] === identitySymbol & ]], 
             VertexLabels -> (#1 -> If[First[#1] === Null, Placed["", Center], Placed[First[#1], Center]] & ) /@ Catenate[
                Last /@ wires /. DirectedEdge -> List], VertexLabelStyle -> Directive[Bold, 15], 
             EdgeLabelStyle -> Directive[Bold, 15], EdgeStyle -> Directive[Black, Thick], VertexShapeFunction -> 
              Join[{"Square"}, (#1 -> "Triangle" & ) /@ Select[Catenate[Last /@ wires /. DirectedEdge -> List], 
                 Head[First[#1]] === identitySymbol & ]], GraphLayout -> "LayeredDigraphEmbedding"]]] & ) /@ 
      Normal[domainMorphismAssociation]; stringDiagrams = DeleteDuplicates[
       Select[stringDiagrams, Head[First[#1]] =!= identitySymbol & ] //. 
         {compositionSymbol[tensorProductSymbol[x_, y_], tensorProductSymbol[z_, w_]] :> 
           tensorProductSymbol[compositionSymbol[x, z], compositionSymbol[y, w]], 
          compositionSymbol[x_, identitySymbol[y_]] :> x, compositionSymbol[identitySymbol[x_], y_] :> y, 
          compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[compositionSymbol[x, y], z]} /. 
        Normal[arrowMappings]]; stringDiagrams = 
      (First[First[#1]] -> If[Length[#1] == 1, Last[First[#1]], Last /@ #1] & ) /@ GatherBy[stringDiagrams, First]; 
     Association[stringDiagrams]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"
AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "ObjectMappings" -> objectMappings_Association, "TensorProductSymbol" -> tensorProductSymbol_, 
     "UnitObject" -> unitObject_]]["FullUnlabeledStringDiagrams"] := 
  Module[{objectListWithDuplicates, productArrows, arrowListWithDuplicates, domainMorphismList, domainCompositions, 
     imageMorphismList, imageCompositions, productMappings, morphismMappings, domainMorphismAssociation, stringDiagrams}, 
    objectListWithDuplicates = Catenate[Outer[tensorProductSymbol, objects, objects]] /. Normal[objectMappings]; 
     productArrows = Association[DeleteDuplicates[
        Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ Select[Normal[arrows], First[Last[#1]] =!= 
                 Last[Last[#1]] & ], First /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]] -> 
           Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ], (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ]]], Catenate[Outer[tensorProductSymbol, (Last[Last[#1]] & ) /@ 
                Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ], (Last[Last[#1]] & ) /@ 
                Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]]]]], 
         Thread[Catenate[Outer[tensorProductSymbol, First /@ Select[Normal[arrows], First[Last[#1]] =!= 
                 Last[Last[#1]] & ], identitySymbol /@ objects]] -> 
           Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ], objects]], Catenate[Outer[tensorProductSymbol, 
               (Last[Last[#1]] & ) /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ], objects]]]]], 
         Thread[Catenate[Outer[tensorProductSymbol, identitySymbol /@ objects, First /@ Select[Normal[arrows], 
               First[Last[#1]] =!= Last[Last[#1]] & ]]] -> Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, 
               objects, (First[Last[#1]] & ) /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]], 
             Catenate[Outer[tensorProductSymbol, objects, (Last[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ]]]]]]]]]; arrowListWithDuplicates = 
      Normal[productArrows] /. Normal[arrowMappings] /. Normal[objectMappings]; 
     domainMorphismList = Select[Normal[productArrows], First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[domainCompositions = Select[Tuples[domainMorphismList, 2], Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ domainMorphismList, 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], domainMorphismList = 
           Append[domainMorphismList, compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ domainCompositions, 
      Length[Catenate[Outer[tensorProductSymbol, objects, objects]]]]; domainMorphismList = 
      Select[domainMorphismList, Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        domainMorphismList = Append[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      Catenate[Outer[tensorProductSymbol, objects, objects]]; imageMorphismList = Select[arrowListWithDuplicates, 
       First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[imageCompositions = Select[Tuples[imageMorphismList, 2], Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ imageMorphismList, 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], imageMorphismList = 
           Append[imageMorphismList, compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ imageCompositions, 
      Length[objectListWithDuplicates]]; imageMorphismList = Select[imageMorphismList, 
       Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[imageMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        imageMorphismList = Append[imageMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      objectListWithDuplicates; productMappings = DeleteDuplicates[Thread[First /@ domainMorphismList -> 
         First /@ imageMorphismList]]; productMappings = Select[productMappings, 
       Counts[First /@ productMappings][First[#1]] == 1 || First[#1] =!= Last[#1] & ]; 
     morphismMappings = Association[Thread[First /@ productMappings -> (Last /@ productMappings /. 
          Normal[arrowMappings])]]; domainMorphismAssociation = Association[domainMorphismList]; stringDiagrams = {}; 
     (Module[{domainMorphism = #1, morphismList, wires}, 
        morphismList = Reverse[Flatten[{First[domainMorphism] /. compositionSymbol -> List}]]; wires = {}; 
         (Module[{compositionIndex = #1}, (Module[{morphismIndex = #1}, wires = Append[wires, 
                  {(First[domainMorphismAssociation[morphismList[[compositionIndex]]]] /. tensorProductSymbol -> List)[[
                     morphismIndex]], compositionIndex, morphismIndex} -> DirectedEdge[If[compositionIndex == 1, 
                     {Null, compositionIndex, morphismIndex}, {(morphismList[[compositionIndex - 1]] /. 
                        tensorProductSymbol -> List)[[morphismIndex]], compositionIndex - 1, morphismIndex}], 
                    {(morphismList[[compositionIndex]] /. tensorProductSymbol -> List)[[morphismIndex]], 
                     compositionIndex, morphismIndex}]]; wires = Append[wires, {(Last[domainMorphismAssociation[
                        morphismList[[compositionIndex]]]] /. tensorProductSymbol -> List)[[morphismIndex]], 
                    compositionIndex + 1, morphismIndex} -> DirectedEdge[{(morphismList[[compositionIndex]] /. 
                       tensorProductSymbol -> List)[[morphismIndex]], compositionIndex, morphismIndex}, 
                    If[compositionIndex == Length[morphismList], {Null, compositionIndex + 1, morphismIndex}, 
                     {(morphismList[[compositionIndex + 1]] /. tensorProductSymbol -> List)[[morphismIndex]], 
                      compositionIndex + 1, morphismIndex}]]]] & ) /@ Range[Length[morphismList[[compositionIndex]] /. 
                tensorProductSymbol -> List]]] & ) /@ Range[Length[morphismList]]; wires = DeleteDuplicates[wires]; 
         (Module[{compositionIndex = #1}, (Module[{morphismMapping = #1, mapExists}, If[First[morphismMapping] =!= 
                 Last[morphismMapping], mapExists = True; (Module[{morphismIndex = #1}, If[ !MemberQ[Catenate[
                        Last /@ wires /. DirectedEdge -> List], {(First[morphismMapping] /. tensorProductSymbol -> List)[[
                         morphismIndex]], compositionIndex, morphismIndex}], mapExists = False]] & ) /@ 
                  Range[Length[First[morphismMapping] /. tensorProductSymbol -> List]]; If[mapExists === True, 
                  (Module[{morphismIndex = #1}, wires = wires /. {(First[morphismMapping] /. tensorProductSymbol -> 
                            List)[[morphismIndex]], compositionIndex, morphismIndex} -> {Last[morphismMapping], 
                         compositionIndex}] & ) /@ Range[Length[First[morphismMapping] /. tensorProductSymbol -> 
                       List]]]]] & ) /@ Normal[morphismMappings]] & ) /@ Range[Length[morphismList]]; 
         stringDiagrams = Append[stringDiagrams, (First[domainMorphism] /. Normal[morphismMappings]) -> 
            EdgeTaggedGraph[(DirectedEdge @@ Last[#1] & ) /@ wires, VertexSize -> 0.5, VertexStyle -> 
              Join[(#1 -> Directive[Transparent, EdgeForm[None]] & ) /@ Select[Catenate[Last /@ wires /. 
                   DirectedEdge -> List], First[#1] === Null & ], (#1 -> Transparent & ) /@ 
                Select[Catenate[Last /@ wires /. DirectedEdge -> List], Head[First[#1]] === identitySymbol & ]], 
             EdgeStyle -> Directive[Black, Thick], VertexShapeFunction -> Join[{"Square"}, (#1 -> "Triangle" & ) /@ 
                Select[Catenate[Last /@ wires /. DirectedEdge -> List], Head[First[#1]] === identitySymbol & ]], 
             GraphLayout -> "LayeredDigraphEmbedding"]]] & ) /@ Normal[domainMorphismAssociation]; 
     stringDiagrams = DeleteDuplicates[Select[stringDiagrams, Head[First[#1]] =!= identitySymbol & ] //. 
         {compositionSymbol[tensorProductSymbol[x_, y_], tensorProductSymbol[z_, w_]] :> 
           tensorProductSymbol[compositionSymbol[x, z], compositionSymbol[y, w]], 
          compositionSymbol[x_, identitySymbol[y_]] :> x, compositionSymbol[identitySymbol[x_], y_] :> y, 
          compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[compositionSymbol[x, y], z]} /. 
        Normal[arrowMappings]]; stringDiagrams = 
      (First[First[#1]] -> If[Length[#1] == 1, Last[First[#1]], Last /@ #1] & ) /@ GatherBy[stringDiagrams, First]; 
     Association[stringDiagrams]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"
AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "ObjectMappings" -> objectMappings_Association, "TensorProductSymbol" -> tensorProductSymbol_, 
     "UnitObject" -> unitObject_]]["ReducedLabeledStringDiagrams"] := 
  Module[{objectFunction, associatorEquations, leftUnitorEquations, rightUnitorEquations, monoidalEquations, 
     objectListWithDuplicates, productArrows, arrowListWithDuplicates, domainMorphismList, domainCompositions, 
     morphismAssociation, compositions, imageQuiverObjectEquivalences, imageObjectEquivalences, imageArrowEquivalences, 
     imageMorphismEquivalences, imageMorphismList, imageCompositions, productMappings, morphismMappings, 
     domainMorphismAssociation, stringDiagrams}, 
    objectFunction = Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ Catenate[Outer[tensorProductSymbol, 
               reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], reduceObjects[
                reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences]]]]] -> 
          reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Values[Association[(#1 -> #1 & ) /@ Catenate[
                Outer[tensorProductSymbol, reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
                  categoryObjectEquivalences], reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
                  categoryObjectEquivalences]]]]], quiverObjectEquivalences], categoryObjectEquivalences]]], 
       Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[objectMappings], 
            quiverObjectEquivalences], categoryObjectEquivalences] -> reduceObjectsWithDuplicates[
           reduceObjectsWithDuplicates[Values[objectMappings], quiverObjectEquivalences], categoryObjectEquivalences]]]]; 
     associatorEquations = DeleteDuplicates[Select[reduceObjects[
         (tensorProductSymbol[#1[[1]], tensorProductSymbol[#1[[2]], #1[[3]]]] == tensorProductSymbol[
              tensorProductSymbol[#1[[1]], #1[[2]]], #1[[3]]] /. Normal[objectFunction] & ) /@ 
          Tuples[reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 3], 
         objectEquivalences], #1 =!= True & ]]; leftUnitorEquations = 
      DeleteDuplicates[Select[reduceObjects[(tensorProductSymbol[unitObject, #1] == #1 /. Normal[objectFunction] & ) /@ 
          reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 
         objectEquivalences], #1 =!= True & ]]; rightUnitorEquations = 
      DeleteDuplicates[Select[reduceObjects[(tensorProductSymbol[#1, unitObject] == #1 /. Normal[objectFunction] & ) /@ 
          reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 
         objectEquivalences], #1 =!= True & ]]; monoidalEquations = DeleteDuplicates[
       Join[associatorEquations, leftUnitorEquations, rightUnitorEquations]]; 
     objectListWithDuplicates = Catenate[Outer[tensorProductSymbol, objects, objects]] /. Normal[objectMappings]; 
     productArrows = Association[DeleteDuplicates[
        Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ Select[Normal[arrows], First[Last[#1]] =!= 
                 Last[Last[#1]] & ], First /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]] -> 
           Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ], (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ]]], Catenate[Outer[tensorProductSymbol, (Last[Last[#1]] & ) /@ 
                Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ], (Last[Last[#1]] & ) /@ 
                Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]]]]], 
         Thread[Catenate[Outer[tensorProductSymbol, First /@ Select[Normal[arrows], First[Last[#1]] =!= 
                 Last[Last[#1]] & ], identitySymbol /@ objects]] -> 
           Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ], objects]], Catenate[Outer[tensorProductSymbol, 
               (Last[Last[#1]] & ) /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ], objects]]]]], 
         Thread[Catenate[Outer[tensorProductSymbol, identitySymbol /@ objects, First /@ Select[Normal[arrows], 
               First[Last[#1]] =!= Last[Last[#1]] & ]]] -> Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, 
               objects, (First[Last[#1]] & ) /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]], 
             Catenate[Outer[tensorProductSymbol, objects, (Last[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ]]]]]]]]]; arrowListWithDuplicates = 
      Normal[productArrows] /. Normal[arrowMappings] /. Normal[objectMappings]; 
     domainMorphismList = Select[reduceArrowsFinalWithDuplicates[reduceArrowsInitialWithDuplicates[Normal[productArrows], 
         arrowEquivalences], quiverObjectEquivalences], First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[domainCompositions = Select[Tuples[domainMorphismList, 2], Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ domainMorphismList, 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], domainMorphismList = 
           Append[domainMorphismList, compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ domainCompositions, 
      Length[reduceObjects[Catenate[Outer[tensorProductSymbol, objects, objects]], quiverObjectEquivalences]]]; 
     domainMorphismList = Select[domainMorphismList, Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        domainMorphismList = Append[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      reduceObjects[Catenate[Outer[tensorProductSymbol, objects, objects]], quiverObjectEquivalences]; 
     domainMorphismList = reduceArrowsFinalWithDuplicates[reduceArrowsInitialWithDuplicates[domainMorphismList, 
        categoryMorphismEquivalences], categoryObjectEquivalences]; morphismAssociation = 
      Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
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
            DirectedEdge[#1, #1]]]] & ) /@ objects; imageQuiverObjectEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ quiverObjectEquivalences, 
               objects]] -> Catenate[Outer[tensorProductSymbol, Last /@ quiverObjectEquivalences, objects]]], 
           Thread[Catenate[Outer[tensorProductSymbol, objects, First /@ quiverObjectEquivalences]] -> 
             Catenate[Outer[tensorProductSymbol, objects, Last /@ quiverObjectEquivalences]]]] /. 
          Normal[objectMappings]] /. Rule -> Equal, #1 =!= True & ]; imageObjectEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ categoryObjectEquivalences, 
               objects]] -> Catenate[Outer[tensorProductSymbol, Last /@ categoryObjectEquivalences, objects]]], 
           Thread[Catenate[Outer[tensorProductSymbol, objects, First /@ categoryObjectEquivalences]] -> 
             Catenate[Outer[tensorProductSymbol, objects, Last /@ categoryObjectEquivalences]]]] /. 
          Normal[objectMappings]] /. Rule -> Equal, #1 =!= True & ]; imageArrowEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ arrowEquivalences, First /@ 
                Normal[arrows]]] -> Catenate[Outer[tensorProductSymbol, Last /@ arrowEquivalences, First /@ 
                Normal[arrows]]]], Thread[Catenate[Outer[tensorProductSymbol, First /@ Normal[arrows], First /@ 
                arrowEquivalences]] -> Catenate[Outer[tensorProductSymbol, First /@ Normal[arrows], Last /@ 
                arrowEquivalences]]]] /. Normal[arrowMappings]] /. Rule -> Equal, #1 =!= True & ]; 
     imageMorphismEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ categoryMorphismEquivalences, 
                First /@ Normal[morphismAssociation]]] -> Catenate[Outer[tensorProductSymbol, 
                Last /@ categoryMorphismEquivalences, First /@ Normal[morphismAssociation]]]], 
            Thread[Catenate[Outer[tensorProductSymbol, First /@ Normal[morphismAssociation], First /@ 
                 categoryMorphismEquivalences]] -> Catenate[Outer[tensorProductSymbol, First /@ 
                 Normal[morphismAssociation], Last /@ categoryMorphismEquivalences]]]] /. Normal[arrowMappings] /. 
          Normal[objectMappings]] /. Rule -> Equal, #1 =!= True & ]; imageMorphismList = 
      Select[reduceArrowsFinalWithDuplicates[reduceArrowsInitialWithDuplicates[arrowListWithDuplicates, 
         imageArrowEquivalences], imageQuiverObjectEquivalences], First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[imageCompositions = Select[Tuples[imageMorphismList, 2], Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ imageMorphismList, 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], imageMorphismList = 
           Append[imageMorphismList, compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ imageCompositions, 
      Length[reduceObjectsWithDuplicates[objectListWithDuplicates, imageQuiverObjectEquivalences]]]; 
     imageMorphismList = Select[imageMorphismList, Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[imageMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        imageMorphismList = Append[imageMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      reduceObjectsWithDuplicates[objectListWithDuplicates, imageQuiverObjectEquivalences]; 
     imageMorphismList = reduceArrowsFinalWithDuplicates[reduceArrowsFinalWithDuplicates[
        reduceArrowsFinalWithDuplicates[reduceArrowsInitialWithDuplicates[reduceArrowsInitialWithDuplicates[
           imageMorphismList, imageMorphismEquivalences], morphismEquivalences], imageObjectEquivalences], 
        monoidalEquations], objectEquivalences]; productMappings = DeleteDuplicates[
       Thread[First /@ domainMorphismList -> First /@ imageMorphismList]]; 
     productMappings = Select[productMappings, Counts[First /@ productMappings][First[#1]] == 1 || 
         First[#1] =!= Last[#1] & ]; morphismMappings = 
      Association[Thread[First /@ productMappings -> (Last /@ productMappings /. Normal[arrowMappings])]]; 
     domainMorphismAssociation = Association[domainMorphismList]; stringDiagrams = {}; 
     (Module[{domainMorphism = #1, morphismList, wires}, 
        morphismList = Reverse[Flatten[{First[domainMorphism] /. compositionSymbol -> List}]]; wires = {}; 
         (Module[{compositionIndex = #1}, (Module[{morphismIndex = #1}, wires = Append[wires, 
                  {(First[domainMorphismAssociation[morphismList[[compositionIndex]]]] /. tensorProductSymbol -> List)[[
                     morphismIndex]], compositionIndex, morphismIndex} -> DirectedEdge[If[compositionIndex == 1, 
                     {Null, compositionIndex, morphismIndex}, {(morphismList[[compositionIndex - 1]] /. 
                        tensorProductSymbol -> List)[[morphismIndex]], compositionIndex - 1, morphismIndex}], 
                    {(morphismList[[compositionIndex]] /. tensorProductSymbol -> List)[[morphismIndex]], 
                     compositionIndex, morphismIndex}]]; wires = Append[wires, {(Last[domainMorphismAssociation[
                        morphismList[[compositionIndex]]]] /. tensorProductSymbol -> List)[[morphismIndex]], 
                    compositionIndex + 1, morphismIndex} -> DirectedEdge[{(morphismList[[compositionIndex]] /. 
                       tensorProductSymbol -> List)[[morphismIndex]], compositionIndex, morphismIndex}, 
                    If[compositionIndex == Length[morphismList], {Null, compositionIndex + 1, morphismIndex}, 
                     {(morphismList[[compositionIndex + 1]] /. tensorProductSymbol -> List)[[morphismIndex]], 
                      compositionIndex + 1, morphismIndex}]]]] & ) /@ Range[Length[morphismList[[compositionIndex]] /. 
                tensorProductSymbol -> List]]] & ) /@ Range[Length[morphismList]]; wires = DeleteDuplicates[wires]; 
         (Module[{compositionIndex = #1}, (Module[{morphismMapping = #1, mapExists}, If[First[morphismMapping] =!= 
                 Last[morphismMapping], mapExists = True; (Module[{morphismIndex = #1}, If[ !MemberQ[Catenate[
                        Last /@ wires /. DirectedEdge -> List], {(First[morphismMapping] /. tensorProductSymbol -> List)[[
                         morphismIndex]], compositionIndex, morphismIndex}], mapExists = False]] & ) /@ 
                  Range[Length[First[morphismMapping] /. tensorProductSymbol -> List]]; If[mapExists === True, 
                  (Module[{morphismIndex = #1}, wires = wires /. {(First[morphismMapping] /. tensorProductSymbol -> 
                            List)[[morphismIndex]], compositionIndex, morphismIndex} -> {Last[morphismMapping], 
                         compositionIndex}] & ) /@ Range[Length[First[morphismMapping] /. tensorProductSymbol -> 
                       List]]]]] & ) /@ Normal[morphismMappings]] & ) /@ Range[Length[morphismList]]; 
         stringDiagrams = Append[stringDiagrams, (First[domainMorphism] /. Normal[morphismMappings]) -> 
            EdgeTaggedGraph[(Labeled[DirectedEdge @@ Last[#1], Placed[First[First[#1]], 0.5]] & ) /@ wires, 
             VertexSize -> 0.5, VertexStyle -> Join[(#1 -> Directive[Transparent, EdgeForm[None]] & ) /@ 
                Select[Catenate[Last /@ wires /. DirectedEdge -> List], First[#1] === Null & ], (#1 -> Transparent & ) /@ 
                Select[Catenate[Last /@ wires /. DirectedEdge -> List], Head[First[#1]] === identitySymbol & ]], 
             VertexLabels -> (#1 -> If[First[#1] === Null, Placed["", Center], Placed[First[#1], Center]] & ) /@ Catenate[
                Last /@ wires /. DirectedEdge -> List], VertexLabelStyle -> Directive[Bold, 15], 
             EdgeLabelStyle -> Directive[Bold, 15], EdgeStyle -> Directive[Black, Thick], VertexShapeFunction -> 
              Join[{"Square"}, (#1 -> "Triangle" & ) /@ Select[Catenate[Last /@ wires /. DirectedEdge -> List], 
                 Head[First[#1]] === identitySymbol & ]], GraphLayout -> "LayeredDigraphEmbedding"]]] & ) /@ 
      Normal[domainMorphismAssociation]; stringDiagrams = DeleteDuplicates[
       Select[stringDiagrams, Head[First[#1]] =!= identitySymbol & ] //. 
         {compositionSymbol[tensorProductSymbol[x_, y_], tensorProductSymbol[z_, w_]] :> 
           tensorProductSymbol[compositionSymbol[x, z], compositionSymbol[y, w]], 
          compositionSymbol[x_, identitySymbol[y_]] :> x, compositionSymbol[identitySymbol[x_], y_] :> y, 
          compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[compositionSymbol[x, y], z]} /. 
        Normal[arrowMappings]]; stringDiagrams = 
      (First[First[#1]] -> If[Length[#1] == 1, Last[First[#1]], Last /@ #1] & ) /@ GatherBy[stringDiagrams, First]; 
     Association[stringDiagrams]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"
AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "ObjectMappings" -> objectMappings_Association, "TensorProductSymbol" -> tensorProductSymbol_, 
     "UnitObject" -> unitObject_]]["ReducedUnlabeledStringDiagrams"] := 
  Module[{objectFunction, associatorEquations, leftUnitorEquations, rightUnitorEquations, monoidalEquations, 
     objectListWithDuplicates, productArrows, arrowListWithDuplicates, domainMorphismList, domainCompositions, 
     morphismAssociation, compositions, imageQuiverObjectEquivalences, imageObjectEquivalences, imageArrowEquivalences, 
     imageMorphismEquivalences, imageMorphismList, imageCompositions, productMappings, morphismMappings, 
     domainMorphismAssociation, stringDiagrams}, 
    objectFunction = Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ Catenate[Outer[tensorProductSymbol, 
               reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], reduceObjects[
                reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences]]]]] -> 
          reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Values[Association[(#1 -> #1 & ) /@ Catenate[
                Outer[tensorProductSymbol, reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
                  categoryObjectEquivalences], reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
                  categoryObjectEquivalences]]]]], quiverObjectEquivalences], categoryObjectEquivalences]]], 
       Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[objectMappings], 
            quiverObjectEquivalences], categoryObjectEquivalences] -> reduceObjectsWithDuplicates[
           reduceObjectsWithDuplicates[Values[objectMappings], quiverObjectEquivalences], categoryObjectEquivalences]]]]; 
     associatorEquations = DeleteDuplicates[Select[reduceObjects[
         (tensorProductSymbol[#1[[1]], tensorProductSymbol[#1[[2]], #1[[3]]]] == tensorProductSymbol[
              tensorProductSymbol[#1[[1]], #1[[2]]], #1[[3]]] /. Normal[objectFunction] & ) /@ 
          Tuples[reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 3], 
         objectEquivalences], #1 =!= True & ]]; leftUnitorEquations = 
      DeleteDuplicates[Select[reduceObjects[(tensorProductSymbol[unitObject, #1] == #1 /. Normal[objectFunction] & ) /@ 
          reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 
         objectEquivalences], #1 =!= True & ]]; rightUnitorEquations = 
      DeleteDuplicates[Select[reduceObjects[(tensorProductSymbol[#1, unitObject] == #1 /. Normal[objectFunction] & ) /@ 
          reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 
         objectEquivalences], #1 =!= True & ]]; monoidalEquations = DeleteDuplicates[
       Join[associatorEquations, leftUnitorEquations, rightUnitorEquations]]; 
     objectListWithDuplicates = Catenate[Outer[tensorProductSymbol, objects, objects]] /. Normal[objectMappings]; 
     productArrows = Association[DeleteDuplicates[
        Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ Select[Normal[arrows], First[Last[#1]] =!= 
                 Last[Last[#1]] & ], First /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]] -> 
           Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ], (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ]]], Catenate[Outer[tensorProductSymbol, (Last[Last[#1]] & ) /@ 
                Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ], (Last[Last[#1]] & ) /@ 
                Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]]]]], 
         Thread[Catenate[Outer[tensorProductSymbol, First /@ Select[Normal[arrows], First[Last[#1]] =!= 
                 Last[Last[#1]] & ], identitySymbol /@ objects]] -> 
           Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ], objects]], Catenate[Outer[tensorProductSymbol, 
               (Last[Last[#1]] & ) /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ], objects]]]]], 
         Thread[Catenate[Outer[tensorProductSymbol, identitySymbol /@ objects, First /@ Select[Normal[arrows], 
               First[Last[#1]] =!= Last[Last[#1]] & ]]] -> Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, 
               objects, (First[Last[#1]] & ) /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]], 
             Catenate[Outer[tensorProductSymbol, objects, (Last[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ]]]]]]]]]; arrowListWithDuplicates = 
      Normal[productArrows] /. Normal[arrowMappings] /. Normal[objectMappings]; 
     domainMorphismList = Select[reduceArrowsFinalWithDuplicates[reduceArrowsInitialWithDuplicates[Normal[productArrows], 
         arrowEquivalences], quiverObjectEquivalences], First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[domainCompositions = Select[Tuples[domainMorphismList, 2], Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ domainMorphismList, 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], domainMorphismList = 
           Append[domainMorphismList, compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ domainCompositions, 
      Length[reduceObjects[Catenate[Outer[tensorProductSymbol, objects, objects]], quiverObjectEquivalences]]]; 
     domainMorphismList = Select[domainMorphismList, Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        domainMorphismList = Append[domainMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      reduceObjects[Catenate[Outer[tensorProductSymbol, objects, objects]], quiverObjectEquivalences]; 
     domainMorphismList = reduceArrowsFinalWithDuplicates[reduceArrowsInitialWithDuplicates[domainMorphismList, 
        categoryMorphismEquivalences], categoryObjectEquivalences]; morphismAssociation = 
      Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
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
            DirectedEdge[#1, #1]]]] & ) /@ objects; imageQuiverObjectEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ quiverObjectEquivalences, 
               objects]] -> Catenate[Outer[tensorProductSymbol, Last /@ quiverObjectEquivalences, objects]]], 
           Thread[Catenate[Outer[tensorProductSymbol, objects, First /@ quiverObjectEquivalences]] -> 
             Catenate[Outer[tensorProductSymbol, objects, Last /@ quiverObjectEquivalences]]]] /. 
          Normal[objectMappings]] /. Rule -> Equal, #1 =!= True & ]; imageObjectEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ categoryObjectEquivalences, 
               objects]] -> Catenate[Outer[tensorProductSymbol, Last /@ categoryObjectEquivalences, objects]]], 
           Thread[Catenate[Outer[tensorProductSymbol, objects, First /@ categoryObjectEquivalences]] -> 
             Catenate[Outer[tensorProductSymbol, objects, Last /@ categoryObjectEquivalences]]]] /. 
          Normal[objectMappings]] /. Rule -> Equal, #1 =!= True & ]; imageArrowEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ arrowEquivalences, First /@ 
                Normal[arrows]]] -> Catenate[Outer[tensorProductSymbol, Last /@ arrowEquivalences, First /@ 
                Normal[arrows]]]], Thread[Catenate[Outer[tensorProductSymbol, First /@ Normal[arrows], First /@ 
                arrowEquivalences]] -> Catenate[Outer[tensorProductSymbol, First /@ Normal[arrows], Last /@ 
                arrowEquivalences]]]] /. Normal[arrowMappings]] /. Rule -> Equal, #1 =!= True & ]; 
     imageMorphismEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ categoryMorphismEquivalences, 
                First /@ Normal[morphismAssociation]]] -> Catenate[Outer[tensorProductSymbol, 
                Last /@ categoryMorphismEquivalences, First /@ Normal[morphismAssociation]]]], 
            Thread[Catenate[Outer[tensorProductSymbol, First /@ Normal[morphismAssociation], First /@ 
                 categoryMorphismEquivalences]] -> Catenate[Outer[tensorProductSymbol, First /@ 
                 Normal[morphismAssociation], Last /@ categoryMorphismEquivalences]]]] /. Normal[arrowMappings] /. 
          Normal[objectMappings]] /. Rule -> Equal, #1 =!= True & ]; imageMorphismList = 
      Select[reduceArrowsFinalWithDuplicates[reduceArrowsInitialWithDuplicates[arrowListWithDuplicates, 
         imageArrowEquivalences], imageQuiverObjectEquivalences], First[Last[#1]] =!= Last[Last[#1]] & ]; 
     Do[imageCompositions = Select[Tuples[imageMorphismList, 2], Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ imageMorphismList, 
            StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], imageMorphismList = 
           Append[imageMorphismList, compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
             DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]] & ) /@ imageCompositions, 
      Length[reduceObjectsWithDuplicates[objectListWithDuplicates, imageQuiverObjectEquivalences]]]; 
     imageMorphismList = Select[imageMorphismList, Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
         Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]; 
     (If[ !MemberQ[imageMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        imageMorphismList = Append[imageMorphismList, identitySymbol[#1] -> DirectedEdge[#1, #1]]] & ) /@ 
      reduceObjectsWithDuplicates[objectListWithDuplicates, imageQuiverObjectEquivalences]; 
     imageMorphismList = reduceArrowsFinalWithDuplicates[reduceArrowsFinalWithDuplicates[
        reduceArrowsFinalWithDuplicates[reduceArrowsInitialWithDuplicates[reduceArrowsInitialWithDuplicates[
           imageMorphismList, imageMorphismEquivalences], morphismEquivalences], imageObjectEquivalences], 
        monoidalEquations], objectEquivalences]; productMappings = DeleteDuplicates[
       Thread[First /@ domainMorphismList -> First /@ imageMorphismList]]; 
     productMappings = Select[productMappings, Counts[First /@ productMappings][First[#1]] == 1 || 
         First[#1] =!= Last[#1] & ]; morphismMappings = 
      Association[Thread[First /@ productMappings -> (Last /@ productMappings /. Normal[arrowMappings])]]; 
     domainMorphismAssociation = Association[domainMorphismList]; stringDiagrams = {}; 
     (Module[{domainMorphism = #1, morphismList, wires}, 
        morphismList = Reverse[Flatten[{First[domainMorphism] /. compositionSymbol -> List}]]; wires = {}; 
         (Module[{compositionIndex = #1}, (Module[{morphismIndex = #1}, wires = Append[wires, 
                  {(First[domainMorphismAssociation[morphismList[[compositionIndex]]]] /. tensorProductSymbol -> List)[[
                     morphismIndex]], compositionIndex, morphismIndex} -> DirectedEdge[If[compositionIndex == 1, 
                     {Null, compositionIndex, morphismIndex}, {(morphismList[[compositionIndex - 1]] /. 
                        tensorProductSymbol -> List)[[morphismIndex]], compositionIndex - 1, morphismIndex}], 
                    {(morphismList[[compositionIndex]] /. tensorProductSymbol -> List)[[morphismIndex]], 
                     compositionIndex, morphismIndex}]]; wires = Append[wires, {(Last[domainMorphismAssociation[
                        morphismList[[compositionIndex]]]] /. tensorProductSymbol -> List)[[morphismIndex]], 
                    compositionIndex + 1, morphismIndex} -> DirectedEdge[{(morphismList[[compositionIndex]] /. 
                       tensorProductSymbol -> List)[[morphismIndex]], compositionIndex, morphismIndex}, 
                    If[compositionIndex == Length[morphismList], {Null, compositionIndex + 1, morphismIndex}, 
                     {(morphismList[[compositionIndex + 1]] /. tensorProductSymbol -> List)[[morphismIndex]], 
                      compositionIndex + 1, morphismIndex}]]]] & ) /@ Range[Length[morphismList[[compositionIndex]] /. 
                tensorProductSymbol -> List]]] & ) /@ Range[Length[morphismList]]; wires = DeleteDuplicates[wires]; 
         (Module[{compositionIndex = #1}, (Module[{morphismMapping = #1, mapExists}, If[First[morphismMapping] =!= 
                 Last[morphismMapping], mapExists = True; (Module[{morphismIndex = #1}, If[ !MemberQ[Catenate[
                        Last /@ wires /. DirectedEdge -> List], {(First[morphismMapping] /. tensorProductSymbol -> List)[[
                         morphismIndex]], compositionIndex, morphismIndex}], mapExists = False]] & ) /@ 
                  Range[Length[First[morphismMapping] /. tensorProductSymbol -> List]]; If[mapExists === True, 
                  (Module[{morphismIndex = #1}, wires = wires /. {(First[morphismMapping] /. tensorProductSymbol -> 
                            List)[[morphismIndex]], compositionIndex, morphismIndex} -> {Last[morphismMapping], 
                         compositionIndex}] & ) /@ Range[Length[First[morphismMapping] /. tensorProductSymbol -> 
                       List]]]]] & ) /@ Normal[morphismMappings]] & ) /@ Range[Length[morphismList]]; 
         stringDiagrams = Append[stringDiagrams, (First[domainMorphism] /. Normal[morphismMappings]) -> 
            EdgeTaggedGraph[(DirectedEdge @@ Last[#1] & ) /@ wires, VertexSize -> 0.5, VertexStyle -> 
              Join[(#1 -> Directive[Transparent, EdgeForm[None]] & ) /@ Select[Catenate[Last /@ wires /. 
                   DirectedEdge -> List], First[#1] === Null & ], (#1 -> Transparent & ) /@ 
                Select[Catenate[Last /@ wires /. DirectedEdge -> List], Head[First[#1]] === identitySymbol & ]], 
             EdgeStyle -> Directive[Black, Thick], VertexShapeFunction -> Join[{"Square"}, (#1 -> "Triangle" & ) /@ 
                Select[Catenate[Last /@ wires /. DirectedEdge -> List], Head[First[#1]] === identitySymbol & ]], 
             GraphLayout -> "LayeredDigraphEmbedding"]]] & ) /@ Normal[domainMorphismAssociation]; 
     stringDiagrams = DeleteDuplicates[Select[stringDiagrams, Head[First[#1]] =!= identitySymbol & ] //. 
         {compositionSymbol[tensorProductSymbol[x_, y_], tensorProductSymbol[z_, w_]] :> 
           tensorProductSymbol[compositionSymbol[x, z], compositionSymbol[y, w]], 
          compositionSymbol[x_, identitySymbol[y_]] :> x, compositionSymbol[identitySymbol[x_], y_] :> y, 
          compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[compositionSymbol[x, y], z]} /. 
        Normal[arrowMappings]]; stringDiagrams = 
      (First[First[#1]] -> If[Length[#1] == 1, Last[First[#1]], Last /@ #1] & ) /@ GatherBy[stringDiagrams, First]; 
     Association[stringDiagrams]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"
AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "ObjectMappings" -> objectMappings_Association, "TensorProductSymbol" -> tensorProductSymbol_, 
     "UnitObject" -> unitObject_]]["AssociatorEquations"] := 
  DeleteDuplicates[Select[(tensorProductSymbol[#1[[1]], tensorProductSymbol[#1[[2]], #1[[3]]]] == 
         tensorProductSymbol[tensorProductSymbol[#1[[1]], #1[[2]]], #1[[3]]] /. Normal[objectMappings] & ) /@ 
      Tuples[objects, 3], #1 =!= True & ]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"
AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "ObjectMappings" -> objectMappings_Association, "TensorProductSymbol" -> tensorProductSymbol_, 
     "UnitObject" -> unitObject_]]["ReducedAssociatorEquations"] := 
  Module[{objectFunction}, 
    objectFunction = Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ Catenate[Outer[tensorProductSymbol, 
               reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], reduceObjects[
                reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences]]]]] -> 
          reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Values[Association[(#1 -> #1 & ) /@ Catenate[
                Outer[tensorProductSymbol, reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
                  categoryObjectEquivalences], reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
                  categoryObjectEquivalences]]]]], quiverObjectEquivalences], categoryObjectEquivalences]]], 
       Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[objectMappings], 
            quiverObjectEquivalences], categoryObjectEquivalences] -> reduceObjectsWithDuplicates[
           reduceObjectsWithDuplicates[Values[objectMappings], quiverObjectEquivalences], categoryObjectEquivalences]]]]; 
     DeleteDuplicates[Select[reduceObjects[(tensorProductSymbol[#1[[1]], tensorProductSymbol[#1[[2]], #1[[3]]]] == 
            tensorProductSymbol[tensorProductSymbol[#1[[1]], #1[[2]]], #1[[3]]] /. Normal[objectFunction] & ) /@ 
         Tuples[reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 3], 
        objectEquivalences], #1 =!= True & ]]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"
AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "ObjectMappings" -> objectMappings_Association, "TensorProductSymbol" -> tensorProductSymbol_, 
     "UnitObject" -> unitObject_]]["LeftUnitorEquations"] := 
  DeleteDuplicates[Select[(tensorProductSymbol[unitObject, #1] == #1 /. Normal[objectMappings] & ) /@ objects, 
     #1 =!= True & ]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === 
     "AbstractCategory"
AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "ObjectMappings" -> objectMappings_Association, "TensorProductSymbol" -> tensorProductSymbol_, 
     "UnitObject" -> unitObject_]]["ReducedLeftUnitorEquations"] := 
  Module[{objectFunction}, 
    objectFunction = Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ Catenate[Outer[tensorProductSymbol, 
               reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], reduceObjects[
                reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences]]]]] -> 
          reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Values[Association[(#1 -> #1 & ) /@ Catenate[
                Outer[tensorProductSymbol, reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
                  categoryObjectEquivalences], reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
                  categoryObjectEquivalences]]]]], quiverObjectEquivalences], categoryObjectEquivalences]]], 
       Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[objectMappings], 
            quiverObjectEquivalences], categoryObjectEquivalences] -> reduceObjectsWithDuplicates[
           reduceObjectsWithDuplicates[Values[objectMappings], quiverObjectEquivalences], categoryObjectEquivalences]]]]; 
     DeleteDuplicates[Select[reduceObjects[(tensorProductSymbol[unitObject, #1] == #1 /. Normal[objectFunction] & ) /@ 
         reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 
        objectEquivalences], #1 =!= True & ]]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"
AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "ObjectMappings" -> objectMappings_Association, "TensorProductSymbol" -> tensorProductSymbol_, 
     "UnitObject" -> unitObject_]]["RightUnitorEquations"] := 
  DeleteDuplicates[Select[(tensorProductSymbol[#1, unitObject] == #1 /. Normal[objectMappings] & ) /@ objects, 
     #1 =!= True & ]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === 
     "AbstractCategory"
AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "ObjectMappings" -> objectMappings_Association, "TensorProductSymbol" -> tensorProductSymbol_, 
     "UnitObject" -> unitObject_]]["ReducedRightUnitorEquations"] := 
  Module[{objectFunction}, 
    objectFunction = Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ Catenate[Outer[tensorProductSymbol, 
               reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], reduceObjects[
                reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences]]]]] -> 
          reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Values[Association[(#1 -> #1 & ) /@ Catenate[
                Outer[tensorProductSymbol, reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
                  categoryObjectEquivalences], reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
                  categoryObjectEquivalences]]]]], quiverObjectEquivalences], categoryObjectEquivalences]]], 
       Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[objectMappings], 
            quiverObjectEquivalences], categoryObjectEquivalences] -> reduceObjectsWithDuplicates[
           reduceObjectsWithDuplicates[Values[objectMappings], quiverObjectEquivalences], categoryObjectEquivalences]]]]; 
     DeleteDuplicates[Select[reduceObjects[(tensorProductSymbol[#1, unitObject] == #1 /. Normal[objectFunction] & ) /@ 
         reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 
        objectEquivalences], #1 =!= True & ]]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"
AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "ObjectMappings" -> objectMappings_Association, "TensorProductSymbol" -> tensorProductSymbol_, 
     "UnitObject" -> unitObject_]]["CommutativeDiagramQ"] := 
  Module[{objectFunction, associatorEquations, leftUnitorEquations, rightUnitorEquations, monoidalEquations, 
     productArrows, morphismAssociation, compositions, imageObjects, imageArrows, imageQuiverObjectEquivalences, 
     imageObjectEquivalences, imageArrowEquivalences, imageMorphismEquivalences, imageMorphismAssociation, 
     imageCompositions}, 
    objectFunction = Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ Catenate[Outer[tensorProductSymbol, 
               reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], reduceObjects[
                reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences]]]]] -> 
          reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Values[Association[(#1 -> #1 & ) /@ Catenate[
                Outer[tensorProductSymbol, reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
                  categoryObjectEquivalences], reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
                  categoryObjectEquivalences]]]]], quiverObjectEquivalences], categoryObjectEquivalences]]], 
       Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[objectMappings], 
            quiverObjectEquivalences], categoryObjectEquivalences] -> reduceObjectsWithDuplicates[
           reduceObjectsWithDuplicates[Values[objectMappings], quiverObjectEquivalences], categoryObjectEquivalences]]]]; 
     associatorEquations = DeleteDuplicates[Select[reduceObjects[
         (tensorProductSymbol[#1[[1]], tensorProductSymbol[#1[[2]], #1[[3]]]] == tensorProductSymbol[
              tensorProductSymbol[#1[[1]], #1[[2]]], #1[[3]]] /. Normal[objectFunction] & ) /@ 
          Tuples[reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 3], 
         objectEquivalences], #1 =!= True & ]]; leftUnitorEquations = 
      DeleteDuplicates[Select[reduceObjects[(tensorProductSymbol[unitObject, #1] == #1 /. Normal[objectFunction] & ) /@ 
          reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 
         objectEquivalences], #1 =!= True & ]]; rightUnitorEquations = 
      DeleteDuplicates[Select[reduceObjects[(tensorProductSymbol[#1, unitObject] == #1 /. Normal[objectFunction] & ) /@ 
          reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 
         objectEquivalences], #1 =!= True & ]]; monoidalEquations = DeleteDuplicates[
       Join[associatorEquations, leftUnitorEquations, rightUnitorEquations]]; 
     productArrows = Association[DeleteDuplicates[
        Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ Select[Normal[arrows], First[Last[#1]] =!= 
                 Last[Last[#1]] & ], First /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]] -> 
           Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ], (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ]]], Catenate[Outer[tensorProductSymbol, (Last[Last[#1]] & ) /@ 
                Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ], (Last[Last[#1]] & ) /@ 
                Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]]]]], 
         Thread[Catenate[Outer[tensorProductSymbol, First /@ Select[Normal[arrows], First[Last[#1]] =!= 
                 Last[Last[#1]] & ], identitySymbol /@ objects]] -> 
           Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ], objects]], Catenate[Outer[tensorProductSymbol, 
               (Last[Last[#1]] & ) /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ], objects]]]]], 
         Thread[Catenate[Outer[tensorProductSymbol, identitySymbol /@ objects, First /@ Select[Normal[arrows], 
               First[Last[#1]] =!= Last[Last[#1]] & ]]] -> Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, 
               objects, (First[Last[#1]] & ) /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]], 
             Catenate[Outer[tensorProductSymbol, objects, (Last[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ]]]]]]]]]; morphismAssociation = 
      Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
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
            DirectedEdge[#1, #1]]]] & ) /@ objects; imageObjects = DeleteDuplicates[
       Catenate[Outer[tensorProductSymbol, objects, objects]] /. Normal[objectMappings]]; 
     imageArrows = Association[DeleteDuplicates[Normal[productArrows] /. Normal[arrowMappings] /. 
         Normal[objectMappings]]]; imageQuiverObjectEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ quiverObjectEquivalences, 
               objects]] -> Catenate[Outer[tensorProductSymbol, Last /@ quiverObjectEquivalences, objects]]], 
           Thread[Catenate[Outer[tensorProductSymbol, objects, First /@ quiverObjectEquivalences]] -> 
             Catenate[Outer[tensorProductSymbol, objects, Last /@ quiverObjectEquivalences]]]] /. 
          Normal[objectMappings]] /. Rule -> Equal, #1 =!= True & ]; imageObjectEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ categoryObjectEquivalences, 
               objects]] -> Catenate[Outer[tensorProductSymbol, Last /@ categoryObjectEquivalences, objects]]], 
           Thread[Catenate[Outer[tensorProductSymbol, objects, First /@ categoryObjectEquivalences]] -> 
             Catenate[Outer[tensorProductSymbol, objects, Last /@ categoryObjectEquivalences]]]] /. 
          Normal[objectMappings]] /. Rule -> Equal, #1 =!= True & ]; imageArrowEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ arrowEquivalences, First /@ 
                Normal[arrows]]] -> Catenate[Outer[tensorProductSymbol, Last /@ arrowEquivalences, First /@ 
                Normal[arrows]]]], Thread[Catenate[Outer[tensorProductSymbol, First /@ Normal[arrows], First /@ 
                arrowEquivalences]] -> Catenate[Outer[tensorProductSymbol, First /@ Normal[arrows], Last /@ 
                arrowEquivalences]]]] /. Normal[arrowMappings]] /. Rule -> Equal, #1 =!= True & ]; 
     imageMorphismEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ categoryMorphismEquivalences, 
                First /@ Normal[morphismAssociation]]] -> Catenate[Outer[tensorProductSymbol, 
                Last /@ categoryMorphismEquivalences, First /@ Normal[morphismAssociation]]]], 
            Thread[Catenate[Outer[tensorProductSymbol, First /@ Normal[morphismAssociation], First /@ 
                 categoryMorphismEquivalences]] -> Catenate[Outer[tensorProductSymbol, First /@ 
                 Normal[morphismAssociation], Last /@ categoryMorphismEquivalences]]]] /. Normal[arrowMappings] /. 
          Normal[objectMappings]] /. Rule -> Equal, #1 =!= True & ]; imageMorphismAssociation = 
      Association[Select[DeleteDuplicates[Normal[reduceArrowsFinal[reduceArrowsInitial[imageArrows, 
            imageArrowEquivalences], imageQuiverObjectEquivalences]]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[imageCompositions = Select[Tuples[Normal[imageMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[imageMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], 
             compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ imageCompositions, Length[reduceObjects[imageObjects, 
        imageQuiverObjectEquivalences]]]; imageMorphismAssociation = 
      Association[Select[Normal[imageMorphismAssociation], Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[imageMorphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[imageObjects, imageQuiverObjectEquivalences]; 
     imageMorphismAssociation = Association[DeleteDuplicates[Normal[imageMorphismAssociation] //. 
         {compositionSymbol[tensorProductSymbol[x_, y_], tensorProductSymbol[z_, w_]] :> 
           tensorProductSymbol[compositionSymbol[x, z], compositionSymbol[y, w]], 
          compositionSymbol[x_, identitySymbol[y_]] :> x, compositionSymbol[identitySymbol[x_], y_] :> y, 
          compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[compositionSymbol[x, y], z]}]]; 
     AllTrue[Normal[CountsBy[Normal[reduceArrowsFinal[reduceArrowsFinal[reduceArrowsFinal[reduceArrowsInitial[
             reduceArrowsInitial[imageMorphismAssociation, imageMorphismEquivalences], morphismEquivalences], 
            imageObjectEquivalences], monoidalEquations], objectEquivalences]], DirectedEdge @@ Last[#1] & ]], 
      Last[#1] == 1 & ]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"
AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "ObjectMappings" -> objectMappings_Association, "TensorProductSymbol" -> tensorProductSymbol_, 
     "UnitObject" -> unitObject_]]["CommutativityEquations"] := 
  Module[{productArrows, imageMorphismAssociation, imageCompositions}, 
    productArrows = Association[DeleteDuplicates[
        Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ Select[Normal[arrows], First[Last[#1]] =!= 
                 Last[Last[#1]] & ], First /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]] -> 
           Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ], (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ]]], Catenate[Outer[tensorProductSymbol, (Last[Last[#1]] & ) /@ 
                Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ], (Last[Last[#1]] & ) /@ 
                Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]]]]], 
         Thread[Catenate[Outer[tensorProductSymbol, First /@ Select[Normal[arrows], First[Last[#1]] =!= 
                 Last[Last[#1]] & ], identitySymbol /@ objects]] -> 
           Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ], objects]], Catenate[Outer[tensorProductSymbol, 
               (Last[Last[#1]] & ) /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ], objects]]]]], 
         Thread[Catenate[Outer[tensorProductSymbol, identitySymbol /@ objects, First /@ Select[Normal[arrows], 
               First[Last[#1]] =!= Last[Last[#1]] & ]]] -> Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, 
               objects, (First[Last[#1]] & ) /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]], 
             Catenate[Outer[tensorProductSymbol, objects, (Last[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ]]]]]]]]]; imageMorphismAssociation = 
      Association[Select[Normal[Association[DeleteDuplicates[Normal[productArrows] /. Normal[arrowMappings] /. 
            Normal[objectMappings]]]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[imageCompositions = Select[Tuples[Normal[imageMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[imageMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], 
             compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ imageCompositions, 
      Length[DeleteDuplicates[Catenate[Outer[tensorProductSymbol, objects, objects]] /. Normal[objectMappings]]]]; 
     imageMorphismAssociation = Association[Select[Normal[imageMorphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[imageMorphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ DeleteDuplicates[Catenate[Outer[tensorProductSymbol, objects, objects]] /. 
        Normal[objectMappings]]; imageMorphismAssociation = 
      Association[DeleteDuplicates[Normal[imageMorphismAssociation] //. 
         {compositionSymbol[tensorProductSymbol[x_, y_], tensorProductSymbol[z_, w_]] :> 
           tensorProductSymbol[compositionSymbol[x, z], compositionSymbol[y, w]], 
          compositionSymbol[x_, identitySymbol[y_]] :> x, compositionSymbol[identitySymbol[x_], y_] :> y, 
          compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[compositionSymbol[x, y], z]}]]; 
     Flatten[(EdgeList[TransitiveReductionGraph[Graph[Apply[UndirectedEdge, Tuples[First /@ #1, 2], {1}]]]] /. 
         UndirectedEdge -> Equal & ) /@ Select[GatherBy[(First[#1] -> DirectedEdge @@ Last[#1] & ) /@ 
          Normal[imageMorphismAssociation], Last], Length[#1] > 1 & ]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "ObjectMappings" -> objectMappings_Association, "TensorProductSymbol" -> tensorProductSymbol_, 
     "UnitObject" -> unitObject_]]["ReducedCommutativityEquations"] := 
  Module[{objectFunction, associatorEquations, leftUnitorEquations, rightUnitorEquations, monoidalEquations, 
     productArrows, morphismAssociation, compositions, imageObjects, imageArrows, imageQuiverObjectEquivalences, 
     imageObjectEquivalences, imageArrowEquivalences, imageMorphismEquivalences, imageMorphismAssociation, 
     imageCompositions}, 
    objectFunction = Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ Catenate[Outer[tensorProductSymbol, 
               reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], reduceObjects[
                reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences]]]]] -> 
          reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Values[Association[(#1 -> #1 & ) /@ Catenate[
                Outer[tensorProductSymbol, reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
                  categoryObjectEquivalences], reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
                  categoryObjectEquivalences]]]]], quiverObjectEquivalences], categoryObjectEquivalences]]], 
       Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[objectMappings], 
            quiverObjectEquivalences], categoryObjectEquivalences] -> reduceObjectsWithDuplicates[
           reduceObjectsWithDuplicates[Values[objectMappings], quiverObjectEquivalences], categoryObjectEquivalences]]]]; 
     associatorEquations = DeleteDuplicates[Select[reduceObjects[
         (tensorProductSymbol[#1[[1]], tensorProductSymbol[#1[[2]], #1[[3]]]] == tensorProductSymbol[
              tensorProductSymbol[#1[[1]], #1[[2]]], #1[[3]]] /. Normal[objectFunction] & ) /@ 
          Tuples[reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 3], 
         objectEquivalences], #1 =!= True & ]]; leftUnitorEquations = 
      DeleteDuplicates[Select[reduceObjects[(tensorProductSymbol[unitObject, #1] == #1 /. Normal[objectFunction] & ) /@ 
          reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 
         objectEquivalences], #1 =!= True & ]]; rightUnitorEquations = 
      DeleteDuplicates[Select[reduceObjects[(tensorProductSymbol[#1, unitObject] == #1 /. Normal[objectFunction] & ) /@ 
          reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 
         objectEquivalences], #1 =!= True & ]]; monoidalEquations = DeleteDuplicates[
       Join[associatorEquations, leftUnitorEquations, rightUnitorEquations]]; 
     productArrows = Association[DeleteDuplicates[
        Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ Select[Normal[arrows], First[Last[#1]] =!= 
                 Last[Last[#1]] & ], First /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]] -> 
           Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ], (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ]]], Catenate[Outer[tensorProductSymbol, (Last[Last[#1]] & ) /@ 
                Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ], (Last[Last[#1]] & ) /@ 
                Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]]]]], 
         Thread[Catenate[Outer[tensorProductSymbol, First /@ Select[Normal[arrows], First[Last[#1]] =!= 
                 Last[Last[#1]] & ], identitySymbol /@ objects]] -> 
           Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ], objects]], Catenate[Outer[tensorProductSymbol, 
               (Last[Last[#1]] & ) /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ], objects]]]]], 
         Thread[Catenate[Outer[tensorProductSymbol, identitySymbol /@ objects, First /@ Select[Normal[arrows], 
               First[Last[#1]] =!= Last[Last[#1]] & ]]] -> Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, 
               objects, (First[Last[#1]] & ) /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]], 
             Catenate[Outer[tensorProductSymbol, objects, (Last[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ]]]]]]]]]; morphismAssociation = 
      Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
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
            DirectedEdge[#1, #1]]]] & ) /@ objects; imageObjects = DeleteDuplicates[
       Catenate[Outer[tensorProductSymbol, objects, objects]] /. Normal[objectMappings]]; 
     imageArrows = Association[DeleteDuplicates[Normal[productArrows] /. Normal[arrowMappings] /. 
         Normal[objectMappings]]]; imageQuiverObjectEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ quiverObjectEquivalences, 
               objects]] -> Catenate[Outer[tensorProductSymbol, Last /@ quiverObjectEquivalences, objects]]], 
           Thread[Catenate[Outer[tensorProductSymbol, objects, First /@ quiverObjectEquivalences]] -> 
             Catenate[Outer[tensorProductSymbol, objects, Last /@ quiverObjectEquivalences]]]] /. 
          Normal[objectMappings]] /. Rule -> Equal, #1 =!= True & ]; imageObjectEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ categoryObjectEquivalences, 
               objects]] -> Catenate[Outer[tensorProductSymbol, Last /@ categoryObjectEquivalences, objects]]], 
           Thread[Catenate[Outer[tensorProductSymbol, objects, First /@ categoryObjectEquivalences]] -> 
             Catenate[Outer[tensorProductSymbol, objects, Last /@ categoryObjectEquivalences]]]] /. 
          Normal[objectMappings]] /. Rule -> Equal, #1 =!= True & ]; imageArrowEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ arrowEquivalences, First /@ 
                Normal[arrows]]] -> Catenate[Outer[tensorProductSymbol, Last /@ arrowEquivalences, First /@ 
                Normal[arrows]]]], Thread[Catenate[Outer[tensorProductSymbol, First /@ Normal[arrows], First /@ 
                arrowEquivalences]] -> Catenate[Outer[tensorProductSymbol, First /@ Normal[arrows], Last /@ 
                arrowEquivalences]]]] /. Normal[arrowMappings]] /. Rule -> Equal, #1 =!= True & ]; 
     imageMorphismEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ categoryMorphismEquivalences, 
                First /@ Normal[morphismAssociation]]] -> Catenate[Outer[tensorProductSymbol, 
                Last /@ categoryMorphismEquivalences, First /@ Normal[morphismAssociation]]]], 
            Thread[Catenate[Outer[tensorProductSymbol, First /@ Normal[morphismAssociation], First /@ 
                 categoryMorphismEquivalences]] -> Catenate[Outer[tensorProductSymbol, First /@ 
                 Normal[morphismAssociation], Last /@ categoryMorphismEquivalences]]]] /. Normal[arrowMappings] /. 
          Normal[objectMappings]] /. Rule -> Equal, #1 =!= True & ]; imageMorphismAssociation = 
      Association[Select[DeleteDuplicates[Normal[reduceArrowsFinal[reduceArrowsInitial[imageArrows, 
            imageArrowEquivalences], imageQuiverObjectEquivalences]]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[imageCompositions = Select[Tuples[Normal[imageMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[imageMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], 
             compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ imageCompositions, Length[reduceObjects[imageObjects, 
        imageQuiverObjectEquivalences]]]; imageMorphismAssociation = 
      Association[Select[Normal[imageMorphismAssociation], Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[imageMorphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[imageObjects, imageQuiverObjectEquivalences]; 
     imageMorphismAssociation = Association[DeleteDuplicates[Normal[imageMorphismAssociation] //. 
         {compositionSymbol[tensorProductSymbol[x_, y_], tensorProductSymbol[z_, w_]] :> 
           tensorProductSymbol[compositionSymbol[x, z], compositionSymbol[y, w]], 
          compositionSymbol[x_, identitySymbol[y_]] :> x, compositionSymbol[identitySymbol[x_], y_] :> y, 
          compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[compositionSymbol[x, y], z]}]]; 
     Flatten[(EdgeList[TransitiveReductionGraph[Graph[Apply[UndirectedEdge, Tuples[First /@ #1, 2], {1}]]]] /. 
         UndirectedEdge -> Equal & ) /@ Select[GatherBy[(First[#1] -> DirectedEdge @@ Last[#1] & ) /@ 
          Normal[reduceArrowsFinal[reduceArrowsFinal[reduceArrowsFinal[reduceArrowsInitial[reduceArrowsInitial[
                imageMorphismAssociation, imageMorphismEquivalences], morphismEquivalences], imageObjectEquivalences], 
             monoidalEquations], objectEquivalences]], Last], Length[#1] > 1 & ]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "ObjectMappings" -> objectMappings_Association, "TensorProductSymbol" -> tensorProductSymbol_, 
     "UnitObject" -> unitObject_]]["StrictSymmetricMonoidalCategoryQ"] := 
  Module[{objectFunction, associatorEquations, leftUnitorEquations, rightUnitorEquations, monoidalEquations, 
     imageQuiverObjectEquivalences, imageObjectEquivalences, objectEquivalenceGraph, reducedSymmetryEquations}, 
    objectFunction = Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ Catenate[Outer[tensorProductSymbol, 
               reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], reduceObjects[
                reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences]]]]] -> 
          reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Values[Association[(#1 -> #1 & ) /@ Catenate[
                Outer[tensorProductSymbol, reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
                  categoryObjectEquivalences], reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
                  categoryObjectEquivalences]]]]], quiverObjectEquivalences], categoryObjectEquivalences]]], 
       Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[objectMappings], 
            quiverObjectEquivalences], categoryObjectEquivalences] -> reduceObjectsWithDuplicates[
           reduceObjectsWithDuplicates[Values[objectMappings], quiverObjectEquivalences], categoryObjectEquivalences]]]]; 
     associatorEquations = DeleteDuplicates[Select[reduceObjects[
         (tensorProductSymbol[#1[[1]], tensorProductSymbol[#1[[2]], #1[[3]]]] == tensorProductSymbol[
              tensorProductSymbol[#1[[1]], #1[[2]]], #1[[3]]] /. Normal[objectFunction] & ) /@ 
          Tuples[reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 3], 
         objectEquivalences], #1 =!= True & ]]; leftUnitorEquations = 
      DeleteDuplicates[Select[reduceObjects[(tensorProductSymbol[unitObject, #1] == #1 /. Normal[objectFunction] & ) /@ 
          reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 
         objectEquivalences], #1 =!= True & ]]; rightUnitorEquations = 
      DeleteDuplicates[Select[reduceObjects[(tensorProductSymbol[#1, unitObject] == #1 /. Normal[objectFunction] & ) /@ 
          reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 
         objectEquivalences], #1 =!= True & ]]; monoidalEquations = DeleteDuplicates[
       Join[associatorEquations, leftUnitorEquations, rightUnitorEquations]]; imageQuiverObjectEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ quiverObjectEquivalences, 
               objects]] -> Catenate[Outer[tensorProductSymbol, Last /@ quiverObjectEquivalences, objects]]], 
           Thread[Catenate[Outer[tensorProductSymbol, objects, First /@ quiverObjectEquivalences]] -> 
             Catenate[Outer[tensorProductSymbol, objects, Last /@ quiverObjectEquivalences]]]] /. 
          Normal[objectMappings]] /. Rule -> Equal, #1 =!= True & ]; imageObjectEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ categoryObjectEquivalences, 
              objects]], Catenate[Outer[tensorProductSymbol, Last /@ categoryObjectEquivalences, objects]]], 
           Thread[Catenate[Outer[tensorProductSymbol, objects, First /@ categoryObjectEquivalences]] -> 
             Catenate[Outer[tensorProductSymbol, objects, Last /@ categoryObjectEquivalences]]]] /. 
          Normal[objectMappings]] /. Rule -> Equal, #1 =!= True & ]; objectEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, DeleteDuplicates[
             Join[imageQuiverObjectEquivalences, imageObjectEquivalences, monoidalEquations, objectEquivalences]], 
            {1}]]]], (UndirectedEdge[#1, #1] & ) /@ DeleteDuplicates[
          Catenate[Outer[tensorProductSymbol, objects, objects]] /. Normal[objectMappings]]]]; 
     reducedSymmetryEquations = {}; 
     (Module[{tuple = #1}, If[MemberQ[VertexList[objectEquivalenceGraph], tensorProductSymbol[First[tuple], 
             Last[tuple]] /. Normal[objectMappings]] && MemberQ[VertexList[objectEquivalenceGraph], 
           tensorProductSymbol[Last[tuple], First[tuple]] /. Normal[objectMappings]], 
         If[Length[FindShortestPath[objectEquivalenceGraph, tensorProductSymbol[First[tuple], Last[tuple]] /. 
              Normal[objectMappings], tensorProductSymbol[Last[tuple], First[tuple]] /. Normal[objectMappings]]] == 0, 
          reducedSymmetryEquations = Append[reducedSymmetryEquations, tensorProductSymbol[First[tuple], Last[tuple]] == 
              tensorProductSymbol[Last[tuple], First[tuple]] /. Normal[objectMappings]]], 
         reducedSymmetryEquations = Append[reducedSymmetryEquations, tensorProductSymbol[First[tuple], Last[tuple]] == 
             tensorProductSymbol[Last[tuple], First[tuple]] /. Normal[objectMappings]]]] & ) /@ Tuples[objects, 2]; 
     Length[DeleteDuplicates[Sort /@ Select[reduceObjects[reduceObjects[reduceObjects[reduceObjects[
              reducedSymmetryEquations, imageQuiverObjectEquivalences], imageObjectEquivalences], monoidalEquations], 
           objectEquivalences], #1 =!= True & ]]] == 0] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"
AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "ObjectMappings" -> objectMappings_Association, "TensorProductSymbol" -> tensorProductSymbol_, 
     "UnitObject" -> unitObject_]]["SymmetryEquations"] := 
  DeleteDuplicates[Sort /@ Select[(tensorProductSymbol[First[#1], Last[#1]] == tensorProductSymbol[Last[#1], 
           First[#1]] /. Normal[objectMappings] & ) /@ Tuples[objects, 2], #1 =!= True & ]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "ObjectMappings" -> objectMappings_Association, "TensorProductSymbol" -> tensorProductSymbol_, 
     "UnitObject" -> unitObject_]]["ReducedSymmetryEquations"] := 
  Module[{objectFunction, associatorEquations, leftUnitorEquations, rightUnitorEquations, monoidalEquations, 
     imageQuiverObjectEquivalences, imageObjectEquivalences, objectEquivalenceGraph, reducedSymmetryEquations}, 
    objectFunction = Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ Catenate[Outer[tensorProductSymbol, 
               reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], reduceObjects[
                reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences]]]]] -> 
          reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Values[Association[(#1 -> #1 & ) /@ Catenate[
                Outer[tensorProductSymbol, reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
                  categoryObjectEquivalences], reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
                  categoryObjectEquivalences]]]]], quiverObjectEquivalences], categoryObjectEquivalences]]], 
       Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[objectMappings], 
            quiverObjectEquivalences], categoryObjectEquivalences] -> reduceObjectsWithDuplicates[
           reduceObjectsWithDuplicates[Values[objectMappings], quiverObjectEquivalences], categoryObjectEquivalences]]]]; 
     associatorEquations = DeleteDuplicates[Select[reduceObjects[
         (tensorProductSymbol[#1[[1]], tensorProductSymbol[#1[[2]], #1[[3]]]] == tensorProductSymbol[
              tensorProductSymbol[#1[[1]], #1[[2]]], #1[[3]]] /. Normal[objectFunction] & ) /@ 
          Tuples[reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 3], 
         objectEquivalences], #1 =!= True & ]]; leftUnitorEquations = 
      DeleteDuplicates[Select[reduceObjects[(tensorProductSymbol[unitObject, #1] == #1 /. Normal[objectFunction] & ) /@ 
          reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 
         objectEquivalences], #1 =!= True & ]]; rightUnitorEquations = 
      DeleteDuplicates[Select[reduceObjects[(tensorProductSymbol[#1, unitObject] == #1 /. Normal[objectFunction] & ) /@ 
          reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 
         objectEquivalences], #1 =!= True & ]]; monoidalEquations = DeleteDuplicates[
       Join[associatorEquations, leftUnitorEquations, rightUnitorEquations]]; imageQuiverObjectEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ quiverObjectEquivalences, 
               objects]] -> Catenate[Outer[tensorProductSymbol, Last /@ quiverObjectEquivalences, objects]]], 
           Thread[Catenate[Outer[tensorProductSymbol, objects, First /@ quiverObjectEquivalences]] -> 
             Catenate[Outer[tensorProductSymbol, objects, Last /@ quiverObjectEquivalences]]]] /. 
          Normal[objectMappings]] /. Rule -> Equal, #1 =!= True & ]; imageObjectEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ categoryObjectEquivalences, 
              objects]], Catenate[Outer[tensorProductSymbol, Last /@ categoryObjectEquivalences, objects]]], 
           Thread[Catenate[Outer[tensorProductSymbol, objects, First /@ categoryObjectEquivalences]] -> 
             Catenate[Outer[tensorProductSymbol, objects, Last /@ categoryObjectEquivalences]]]] /. 
          Normal[objectMappings]] /. Rule -> Equal, #1 =!= True & ]; objectEquivalenceGraph = 
      Graph[Join[EdgeList[TransitiveClosureGraph[Graph[Apply[UndirectedEdge, DeleteDuplicates[
             Join[imageQuiverObjectEquivalences, imageObjectEquivalences, monoidalEquations, objectEquivalences]], 
            {1}]]]], (UndirectedEdge[#1, #1] & ) /@ DeleteDuplicates[
          Catenate[Outer[tensorProductSymbol, objects, objects]] /. Normal[objectMappings]]]]; 
     reducedSymmetryEquations = {}; 
     (Module[{tuple = #1}, If[MemberQ[VertexList[objectEquivalenceGraph], tensorProductSymbol[First[tuple], 
             Last[tuple]] /. Normal[objectMappings]] && MemberQ[VertexList[objectEquivalenceGraph], 
           tensorProductSymbol[Last[tuple], First[tuple]] /. Normal[objectMappings]], 
         If[Length[FindShortestPath[objectEquivalenceGraph, tensorProductSymbol[First[tuple], Last[tuple]] /. 
              Normal[objectMappings], tensorProductSymbol[Last[tuple], First[tuple]] /. Normal[objectMappings]]] == 0, 
          reducedSymmetryEquations = Append[reducedSymmetryEquations, tensorProductSymbol[First[tuple], Last[tuple]] == 
              tensorProductSymbol[Last[tuple], First[tuple]] /. Normal[objectMappings]]], 
         reducedSymmetryEquations = Append[reducedSymmetryEquations, tensorProductSymbol[First[tuple], Last[tuple]] == 
             tensorProductSymbol[Last[tuple], First[tuple]] /. Normal[objectMappings]]]] & ) /@ Tuples[objects, 2]; 
     DeleteDuplicates[Sort /@ Select[reduceObjects[reduceObjects[reduceObjects[reduceObjects[reducedSymmetryEquations, 
            imageQuiverObjectEquivalences], imageObjectEquivalences], monoidalEquations], objectEquivalences], 
        #1 =!= True & ]]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory"
AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "ObjectMappings" -> objectMappings_Association, "TensorProductSymbol" -> tensorProductSymbol_, 
     "UnitObject" -> unitObject_]]["FullLabeledGraph"] := 
  Module[{productArrows, domainMorphismAssociation, domainCompositions, imageMorphismAssociation, imageCompositions}, 
    productArrows = Association[DeleteDuplicates[
        Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ Select[Normal[arrows], First[Last[#1]] =!= 
                 Last[Last[#1]] & ], First /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]] -> 
           Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ], (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ]]], Catenate[Outer[tensorProductSymbol, (Last[Last[#1]] & ) /@ 
                Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ], (Last[Last[#1]] & ) /@ 
                Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]]]]], 
         Thread[Catenate[Outer[tensorProductSymbol, First /@ Select[Normal[arrows], First[Last[#1]] =!= 
                 Last[Last[#1]] & ], identitySymbol /@ objects]] -> 
           Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ], objects]], Catenate[Outer[tensorProductSymbol, 
               (Last[Last[#1]] & ) /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ], objects]]]]], 
         Thread[Catenate[Outer[tensorProductSymbol, identitySymbol /@ objects, First /@ Select[Normal[arrows], 
               First[Last[#1]] =!= Last[Last[#1]] & ]]] -> Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, 
               objects, (First[Last[#1]] & ) /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]], 
             Catenate[Outer[tensorProductSymbol, objects, (Last[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ]]]]]]]]]; domainMorphismAssociation = 
      Association[Select[Normal[productArrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[domainCompositions = Select[Tuples[Normal[domainMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[domainMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          domainMorphismAssociation = Association[Append[Normal[domainMorphismAssociation], 
             compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ domainCompositions, 
      Length[Catenate[Outer[tensorProductSymbol, objects, objects]]]]; domainMorphismAssociation = 
      Association[Select[Normal[domainMorphismAssociation], Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[domainMorphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        domainMorphismAssociation = Association[Append[Normal[domainMorphismAssociation], 
           identitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ Catenate[Outer[tensorProductSymbol, objects, objects]]; 
     domainMorphismAssociation = Association[DeleteDuplicates[Normal[domainMorphismAssociation] //. 
         {compositionSymbol[tensorProductSymbol[x_, y_], tensorProductSymbol[z_, w_]] :> 
           tensorProductSymbol[compositionSymbol[x, z], compositionSymbol[y, w]], 
          compositionSymbol[x_, identitySymbol[y_]] :> x, compositionSymbol[identitySymbol[x_], y_] :> y, 
          compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[compositionSymbol[x, y], z]}]]; 
     imageMorphismAssociation = Association[Select[Normal[Association[DeleteDuplicates[
           Normal[productArrows] /. Normal[arrowMappings] /. Normal[objectMappings]]]], 
        First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[imageCompositions = Select[Tuples[Normal[imageMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[imageMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], 
             compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ imageCompositions, 
      Length[DeleteDuplicates[Catenate[Outer[tensorProductSymbol, objects, objects]] /. Normal[objectMappings]]]]; 
     imageMorphismAssociation = Association[Select[Normal[imageMorphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[imageMorphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ DeleteDuplicates[Catenate[Outer[tensorProductSymbol, objects, objects]] /. 
        Normal[objectMappings]]; imageMorphismAssociation = 
      Association[DeleteDuplicates[Normal[imageMorphismAssociation] //. 
         {compositionSymbol[tensorProductSymbol[x_, y_], tensorProductSymbol[z_, w_]] :> 
           tensorProductSymbol[compositionSymbol[x, z], compositionSymbol[y, w]], 
          compositionSymbol[x_, identitySymbol[y_]] :> x, compositionSymbol[identitySymbol[x_], y_] :> y, 
          compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[compositionSymbol[x, y], z]}]]; 
     EdgeTaggedGraph[Catenate[Outer[tensorProductSymbol, objects, objects]], 
       (Labeled[DirectedEdge @@ Last[#1], Placed[First[#1], 0.5]] & ) /@ Normal[domainMorphismAssociation], 
       VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], VertexLabels -> Placed["Name", Center], 
       VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
       EdgeStyle -> Directive[Black, Thick], GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}] -> 
      EdgeTaggedGraph[DeleteDuplicates[Catenate[Outer[tensorProductSymbol, objects, objects]] /. Normal[objectMappings]], 
       (Labeled[DirectedEdge @@ Last[#1], Placed[First[#1], 0.5]] & ) /@ Normal[imageMorphismAssociation], 
       VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], VertexLabels -> Placed["Name", Center], 
       VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
       EdgeStyle -> Directive[Black, Thick], GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "ObjectMappings" -> objectMappings_Association, "TensorProductSymbol" -> tensorProductSymbol_, 
     "UnitObject" -> unitObject_]]["FullUnlabeledGraph"] := 
  Module[{productArrows, domainMorphismAssociation, domainCompositions, imageMorphismAssociation, imageCompositions}, 
    productArrows = Association[DeleteDuplicates[
        Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ Select[Normal[arrows], First[Last[#1]] =!= 
                 Last[Last[#1]] & ], First /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]] -> 
           Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ], (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ]]], Catenate[Outer[tensorProductSymbol, (Last[Last[#1]] & ) /@ 
                Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ], (Last[Last[#1]] & ) /@ 
                Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]]]]], 
         Thread[Catenate[Outer[tensorProductSymbol, First /@ Select[Normal[arrows], First[Last[#1]] =!= 
                 Last[Last[#1]] & ], identitySymbol /@ objects]] -> 
           Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ], objects]], Catenate[Outer[tensorProductSymbol, 
               (Last[Last[#1]] & ) /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ], objects]]]]], 
         Thread[Catenate[Outer[tensorProductSymbol, identitySymbol /@ objects, First /@ Select[Normal[arrows], 
               First[Last[#1]] =!= Last[Last[#1]] & ]]] -> Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, 
               objects, (First[Last[#1]] & ) /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]], 
             Catenate[Outer[tensorProductSymbol, objects, (Last[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ]]]]]]]]]; domainMorphismAssociation = 
      Association[Select[Normal[productArrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[domainCompositions = Select[Tuples[Normal[domainMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[domainMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          domainMorphismAssociation = Association[Append[Normal[domainMorphismAssociation], 
             compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ domainCompositions, 
      Length[Catenate[Outer[tensorProductSymbol, objects, objects]]]]; domainMorphismAssociation = 
      Association[Select[Normal[domainMorphismAssociation], Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[domainMorphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        domainMorphismAssociation = Association[Append[Normal[domainMorphismAssociation], 
           identitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ Catenate[Outer[tensorProductSymbol, objects, objects]]; 
     domainMorphismAssociation = Association[DeleteDuplicates[Normal[domainMorphismAssociation] //. 
         {compositionSymbol[tensorProductSymbol[x_, y_], tensorProductSymbol[z_, w_]] :> 
           tensorProductSymbol[compositionSymbol[x, z], compositionSymbol[y, w]], 
          compositionSymbol[x_, identitySymbol[y_]] :> x, compositionSymbol[identitySymbol[x_], y_] :> y, 
          compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[compositionSymbol[x, y], z]}]]; 
     imageMorphismAssociation = Association[Select[Normal[Association[DeleteDuplicates[
           Normal[productArrows] /. Normal[arrowMappings] /. Normal[objectMappings]]]], 
        First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[imageCompositions = Select[Tuples[Normal[imageMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[imageMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], 
             compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ imageCompositions, 
      Length[DeleteDuplicates[Catenate[Outer[tensorProductSymbol, objects, objects]] /. Normal[objectMappings]]]]; 
     imageMorphismAssociation = Association[Select[Normal[imageMorphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[imageMorphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ DeleteDuplicates[Catenate[Outer[tensorProductSymbol, objects, objects]] /. 
        Normal[objectMappings]]; imageMorphismAssociation = 
      Association[DeleteDuplicates[Normal[imageMorphismAssociation] //. 
         {compositionSymbol[tensorProductSymbol[x_, y_], tensorProductSymbol[z_, w_]] :> 
           tensorProductSymbol[compositionSymbol[x, z], compositionSymbol[y, w]], 
          compositionSymbol[x_, identitySymbol[y_]] :> x, compositionSymbol[identitySymbol[x_], y_] :> y, 
          compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[compositionSymbol[x, y], z]}]]; 
     EdgeTaggedGraph[Catenate[Outer[tensorProductSymbol, objects, objects]], (DirectedEdge @@ Last[#1] & ) /@ 
        Normal[domainMorphismAssociation], VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], 
       VertexLabels -> Placed["Name", Center], VertexLabelStyle -> Directive[Bold, 20], 
       EdgeLabelStyle -> Directive[Bold, 20], EdgeStyle -> Directive[Black, Thick], 
       GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}] -> 
      EdgeTaggedGraph[DeleteDuplicates[Catenate[Outer[tensorProductSymbol, objects, objects]] /. Normal[objectMappings]], 
       (DirectedEdge @@ Last[#1] & ) /@ Normal[imageMorphismAssociation], VertexSize -> 0.3, 
       VertexStyle -> Directive[Transparent, EdgeForm[None]], VertexLabels -> Placed["Name", Center], 
       VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
       EdgeStyle -> Directive[Black, Thick], GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "ObjectMappings" -> objectMappings_Association, "TensorProductSymbol" -> tensorProductSymbol_, 
     "UnitObject" -> unitObject_]]["ReducedLabeledGraph"] := 
  Module[{objectFunction, associatorEquations, leftUnitorEquations, rightUnitorEquations, monoidalEquations, 
     productArrows, domainMorphismAssociation, domainCompositions, morphismAssociation, compositions, imageObjects, 
     imageArrows, imageQuiverObjectEquivalences, imageObjectEquivalences, imageArrowEquivalences, 
     imageMorphismEquivalences, imageMorphismAssociation, imageCompositions}, 
    objectFunction = Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ Catenate[Outer[tensorProductSymbol, 
               reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], reduceObjects[
                reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences]]]]] -> 
          reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Values[Association[(#1 -> #1 & ) /@ Catenate[
                Outer[tensorProductSymbol, reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
                  categoryObjectEquivalences], reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
                  categoryObjectEquivalences]]]]], quiverObjectEquivalences], categoryObjectEquivalences]]], 
       Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[objectMappings], 
            quiverObjectEquivalences], categoryObjectEquivalences] -> reduceObjectsWithDuplicates[
           reduceObjectsWithDuplicates[Values[objectMappings], quiverObjectEquivalences], categoryObjectEquivalences]]]]; 
     associatorEquations = DeleteDuplicates[Select[reduceObjects[
         (tensorProductSymbol[#1[[1]], tensorProductSymbol[#1[[2]], #1[[3]]]] == tensorProductSymbol[
              tensorProductSymbol[#1[[1]], #1[[2]]], #1[[3]]] /. Normal[objectFunction] & ) /@ 
          Tuples[reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 3], 
         objectEquivalences], #1 =!= True & ]]; leftUnitorEquations = 
      DeleteDuplicates[Select[reduceObjects[(tensorProductSymbol[unitObject, #1] == #1 /. Normal[objectFunction] & ) /@ 
          reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 
         objectEquivalences], #1 =!= True & ]]; rightUnitorEquations = 
      DeleteDuplicates[Select[reduceObjects[(tensorProductSymbol[#1, unitObject] == #1 /. Normal[objectFunction] & ) /@ 
          reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 
         objectEquivalences], #1 =!= True & ]]; monoidalEquations = DeleteDuplicates[
       Join[associatorEquations, leftUnitorEquations, rightUnitorEquations]]; 
     productArrows = Association[DeleteDuplicates[
        Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ Select[Normal[arrows], First[Last[#1]] =!= 
                 Last[Last[#1]] & ], First /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]] -> 
           Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ], (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ]]], Catenate[Outer[tensorProductSymbol, (Last[Last[#1]] & ) /@ 
                Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ], (Last[Last[#1]] & ) /@ 
                Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]]]]], 
         Thread[Catenate[Outer[tensorProductSymbol, First /@ Select[Normal[arrows], First[Last[#1]] =!= 
                 Last[Last[#1]] & ], identitySymbol /@ objects]] -> 
           Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ], objects]], Catenate[Outer[tensorProductSymbol, 
               (Last[Last[#1]] & ) /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ], objects]]]]], 
         Thread[Catenate[Outer[tensorProductSymbol, identitySymbol /@ objects, First /@ Select[Normal[arrows], 
               First[Last[#1]] =!= Last[Last[#1]] & ]]] -> Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, 
               objects, (First[Last[#1]] & ) /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]], 
             Catenate[Outer[tensorProductSymbol, objects, (Last[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ]]]]]]]]]; domainMorphismAssociation = 
      Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[productArrows, arrowEquivalences], 
          quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[domainCompositions = Select[Tuples[Normal[domainMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[domainMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          domainMorphismAssociation = Association[Append[Normal[domainMorphismAssociation], 
             compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ domainCompositions, 
      Length[reduceObjects[Catenate[Outer[tensorProductSymbol, objects, objects]], quiverObjectEquivalences]]]; 
     domainMorphismAssociation = Association[Select[Normal[domainMorphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[domainMorphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        domainMorphismAssociation = Association[Append[Normal[domainMorphismAssociation], 
           identitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ 
      reduceObjects[Catenate[Outer[tensorProductSymbol, objects, objects]], quiverObjectEquivalences]; 
     domainMorphismAssociation = Association[DeleteDuplicates[Normal[domainMorphismAssociation] //. 
         {compositionSymbol[tensorProductSymbol[x_, y_], tensorProductSymbol[z_, w_]] :> 
           tensorProductSymbol[compositionSymbol[x, z], compositionSymbol[y, w]], 
          compositionSymbol[x_, identitySymbol[y_]] :> x, compositionSymbol[identitySymbol[x_], y_] :> y, 
          compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[compositionSymbol[x, y], z]}]]; 
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
            DirectedEdge[#1, #1]]]] & ) /@ objects; imageObjects = DeleteDuplicates[
       Catenate[Outer[tensorProductSymbol, objects, objects]] /. Normal[objectMappings]]; 
     imageArrows = Association[DeleteDuplicates[Normal[productArrows] /. Normal[arrowMappings] /. 
         Normal[objectMappings]]]; imageQuiverObjectEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ quiverObjectEquivalences, 
               objects]] -> Catenate[Outer[tensorProductSymbol, Last /@ quiverObjectEquivalences, objects]]], 
           Thread[Catenate[Outer[tensorProductSymbol, objects, First /@ quiverObjectEquivalences]] -> 
             Catenate[Outer[tensorProductSymbol, objects, Last /@ quiverObjectEquivalences]]]] /. 
          Normal[objectMappings]] /. Rule -> Equal, #1 =!= True & ]; imageObjectEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ categoryObjectEquivalences, 
               objects]] -> Catenate[Outer[tensorProductSymbol, Last /@ categoryObjectEquivalences, objects]]], 
           Thread[Catenate[Outer[tensorProductSymbol, objects, First /@ categoryObjectEquivalences]] -> 
             Catenate[Outer[tensorProductSymbol, objects, Last /@ categoryObjectEquivalences]]]] /. 
          Normal[objectMappings]] /. Rule -> Equal, #1 =!= True & ]; imageArrowEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ arrowEquivalences, First /@ 
                Normal[arrows]]] -> Catenate[Outer[tensorProductSymbol, Last /@ arrowEquivalences, First /@ 
                Normal[arrows]]]], Thread[Catenate[Outer[tensorProductSymbol, First /@ Normal[arrows], First /@ 
                arrowEquivalences]] -> Catenate[Outer[tensorProductSymbol, First /@ Normal[arrows], Last /@ 
                arrowEquivalences]]]] /. Normal[arrowMappings]] /. Rule -> Equal, #1 =!= True & ]; 
     imageMorphismEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ categoryMorphismEquivalences, 
                First /@ Normal[morphismAssociation]]] -> Catenate[Outer[tensorProductSymbol, 
                Last /@ categoryMorphismEquivalences, First /@ Normal[morphismAssociation]]]], 
            Thread[Catenate[Outer[tensorProductSymbol, First /@ Normal[morphismAssociation], First /@ 
                 categoryMorphismEquivalences]] -> Catenate[Outer[tensorProductSymbol, First /@ 
                 Normal[morphismAssociation], Last /@ categoryMorphismEquivalences]]]] /. Normal[arrowMappings] /. 
          Normal[objectMappings]] /. Rule -> Equal, #1 =!= True & ]; imageMorphismAssociation = 
      Association[Select[DeleteDuplicates[Normal[reduceArrowsFinal[reduceArrowsInitial[imageArrows, 
            imageArrowEquivalences], imageQuiverObjectEquivalences]]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[imageCompositions = Select[Tuples[Normal[imageMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[imageMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], 
             compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ imageCompositions, Length[reduceObjects[imageObjects, 
        imageQuiverObjectEquivalences]]]; imageMorphismAssociation = 
      Association[Select[Normal[imageMorphismAssociation], Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[imageMorphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[imageObjects, imageQuiverObjectEquivalences]; 
     imageMorphismAssociation = Association[DeleteDuplicates[Normal[imageMorphismAssociation] //. 
         {compositionSymbol[tensorProductSymbol[x_, y_], tensorProductSymbol[z_, w_]] :> 
           tensorProductSymbol[compositionSymbol[x, z], compositionSymbol[y, w]], 
          compositionSymbol[x_, identitySymbol[y_]] :> x, compositionSymbol[identitySymbol[x_], y_] :> y, 
          compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[compositionSymbol[x, y], z]}]]; 
     EdgeTaggedGraph[reduceObjects[reduceObjects[Catenate[Outer[tensorProductSymbol, objects, objects]], 
         quiverObjectEquivalences], categoryObjectEquivalences], 
       (Labeled[DirectedEdge @@ Last[#1], Placed[First[#1], 0.5]] & ) /@ 
        Normal[reduceArrowsFinal[reduceArrowsInitial[domainMorphismAssociation, categoryMorphismEquivalences], 
          categoryObjectEquivalences]], VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], 
       VertexLabels -> Placed["Name", Center], VertexLabelStyle -> Directive[Bold, 20], 
       EdgeLabelStyle -> Directive[Bold, 20], EdgeStyle -> Directive[Black, Thick], 
       GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}] -> 
      EdgeTaggedGraph[reduceObjects[reduceObjects[reduceObjects[reduceObjects[imageObjects, 
           imageQuiverObjectEquivalences], imageObjectEquivalences], monoidalEquations], objectEquivalences], 
       (Labeled[DirectedEdge @@ Last[#1], Placed[First[#1], 0.5]] & ) /@ 
        Normal[reduceArrowsFinal[reduceArrowsFinal[reduceArrowsFinal[reduceArrowsInitial[reduceArrowsInitial[
              imageMorphismAssociation, imageMorphismEquivalences], morphismEquivalences], imageObjectEquivalences], 
           monoidalEquations], objectEquivalences]], VertexSize -> 0.3, 
       VertexStyle -> Directive[Transparent, EdgeForm[None]], VertexLabels -> Placed["Name", Center], 
       VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
       EdgeStyle -> Directive[Black, Thick], GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "ObjectMappings" -> objectMappings_Association, "TensorProductSymbol" -> tensorProductSymbol_, 
     "UnitObject" -> unitObject_]]["ReducedUnlabeledGraph"] := 
  Module[{objectFunction, associatorEquations, leftUnitorEquations, rightUnitorEquations, monoidalEquations, 
     productArrows, domainMorphismAssociation, domainCompositions, morphismAssociation, compositions, imageObjects, 
     imageArrows, imageQuiverObjectEquivalences, imageObjectEquivalences, imageArrowEquivalences, 
     imageMorphismEquivalences, imageMorphismAssociation, imageCompositions}, 
    objectFunction = Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ Catenate[Outer[tensorProductSymbol, 
               reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], reduceObjects[
                reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences]]]]] -> 
          reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Values[Association[(#1 -> #1 & ) /@ Catenate[
                Outer[tensorProductSymbol, reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
                  categoryObjectEquivalences], reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
                  categoryObjectEquivalences]]]]], quiverObjectEquivalences], categoryObjectEquivalences]]], 
       Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[objectMappings], 
            quiverObjectEquivalences], categoryObjectEquivalences] -> reduceObjectsWithDuplicates[
           reduceObjectsWithDuplicates[Values[objectMappings], quiverObjectEquivalences], categoryObjectEquivalences]]]]; 
     associatorEquations = DeleteDuplicates[Select[reduceObjects[
         (tensorProductSymbol[#1[[1]], tensorProductSymbol[#1[[2]], #1[[3]]]] == tensorProductSymbol[
              tensorProductSymbol[#1[[1]], #1[[2]]], #1[[3]]] /. Normal[objectFunction] & ) /@ 
          Tuples[reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 3], 
         objectEquivalences], #1 =!= True & ]]; leftUnitorEquations = 
      DeleteDuplicates[Select[reduceObjects[(tensorProductSymbol[unitObject, #1] == #1 /. Normal[objectFunction] & ) /@ 
          reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 
         objectEquivalences], #1 =!= True & ]]; rightUnitorEquations = 
      DeleteDuplicates[Select[reduceObjects[(tensorProductSymbol[#1, unitObject] == #1 /. Normal[objectFunction] & ) /@ 
          reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 
         objectEquivalences], #1 =!= True & ]]; monoidalEquations = DeleteDuplicates[
       Join[associatorEquations, leftUnitorEquations, rightUnitorEquations]]; 
     productArrows = Association[DeleteDuplicates[
        Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ Select[Normal[arrows], First[Last[#1]] =!= 
                 Last[Last[#1]] & ], First /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]] -> 
           Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ], (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ]]], Catenate[Outer[tensorProductSymbol, (Last[Last[#1]] & ) /@ 
                Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ], (Last[Last[#1]] & ) /@ 
                Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]]]]], 
         Thread[Catenate[Outer[tensorProductSymbol, First /@ Select[Normal[arrows], First[Last[#1]] =!= 
                 Last[Last[#1]] & ], identitySymbol /@ objects]] -> 
           Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ], objects]], Catenate[Outer[tensorProductSymbol, 
               (Last[Last[#1]] & ) /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ], objects]]]]], 
         Thread[Catenate[Outer[tensorProductSymbol, identitySymbol /@ objects, First /@ Select[Normal[arrows], 
               First[Last[#1]] =!= Last[Last[#1]] & ]]] -> Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, 
               objects, (First[Last[#1]] & ) /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]], 
             Catenate[Outer[tensorProductSymbol, objects, (Last[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ]]]]]]]]]; domainMorphismAssociation = 
      Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[productArrows, arrowEquivalences], 
          quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[domainCompositions = Select[Tuples[Normal[domainMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[domainMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          domainMorphismAssociation = Association[Append[Normal[domainMorphismAssociation], 
             compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ domainCompositions, 
      Length[reduceObjects[Catenate[Outer[tensorProductSymbol, objects, objects]], quiverObjectEquivalences]]]; 
     domainMorphismAssociation = Association[Select[Normal[domainMorphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[domainMorphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        domainMorphismAssociation = Association[Append[Normal[domainMorphismAssociation], 
           identitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ 
      reduceObjects[Catenate[Outer[tensorProductSymbol, objects, objects]], quiverObjectEquivalences]; 
     domainMorphismAssociation = Association[DeleteDuplicates[Normal[domainMorphismAssociation] //. 
         {compositionSymbol[tensorProductSymbol[x_, y_], tensorProductSymbol[z_, w_]] :> 
           tensorProductSymbol[compositionSymbol[x, z], compositionSymbol[y, w]], 
          compositionSymbol[x_, identitySymbol[y_]] :> x, compositionSymbol[identitySymbol[x_], y_] :> y, 
          compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[compositionSymbol[x, y], z]}]]; 
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
            DirectedEdge[#1, #1]]]] & ) /@ objects; imageObjects = DeleteDuplicates[
       Catenate[Outer[tensorProductSymbol, objects, objects]] /. Normal[objectMappings]]; 
     imageArrows = Association[DeleteDuplicates[Normal[productArrows] /. Normal[arrowMappings] /. 
         Normal[objectMappings]]]; imageQuiverObjectEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ quiverObjectEquivalences, 
               objects]] -> Catenate[Outer[tensorProductSymbol, Last /@ quiverObjectEquivalences, objects]]], 
           Thread[Catenate[Outer[tensorProductSymbol, objects, First /@ quiverObjectEquivalences]] -> 
             Catenate[Outer[tensorProductSymbol, objects, Last /@ quiverObjectEquivalences]]]] /. 
          Normal[objectMappings]] /. Rule -> Equal, #1 =!= True & ]; imageObjectEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ categoryObjectEquivalences, 
               objects]] -> Catenate[Outer[tensorProductSymbol, Last /@ categoryObjectEquivalences, objects]]], 
           Thread[Catenate[Outer[tensorProductSymbol, objects, First /@ categoryObjectEquivalences]] -> 
             Catenate[Outer[tensorProductSymbol, objects, Last /@ categoryObjectEquivalences]]]] /. 
          Normal[objectMappings]] /. Rule -> Equal, #1 =!= True & ]; imageArrowEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ arrowEquivalences, First /@ 
                Normal[arrows]]] -> Catenate[Outer[tensorProductSymbol, Last /@ arrowEquivalences, First /@ 
                Normal[arrows]]]], Thread[Catenate[Outer[tensorProductSymbol, First /@ Normal[arrows], First /@ 
                arrowEquivalences]] -> Catenate[Outer[tensorProductSymbol, First /@ Normal[arrows], Last /@ 
                arrowEquivalences]]]] /. Normal[arrowMappings]] /. Rule -> Equal, #1 =!= True & ]; 
     imageMorphismEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ categoryMorphismEquivalences, 
                First /@ Normal[morphismAssociation]]] -> Catenate[Outer[tensorProductSymbol, 
                Last /@ categoryMorphismEquivalences, First /@ Normal[morphismAssociation]]]], 
            Thread[Catenate[Outer[tensorProductSymbol, First /@ Normal[morphismAssociation], First /@ 
                 categoryMorphismEquivalences]] -> Catenate[Outer[tensorProductSymbol, First /@ 
                 Normal[morphismAssociation], Last /@ categoryMorphismEquivalences]]]] /. Normal[arrowMappings] /. 
          Normal[objectMappings]] /. Rule -> Equal, #1 =!= True & ]; imageMorphismAssociation = 
      Association[Select[DeleteDuplicates[Normal[reduceArrowsFinal[reduceArrowsInitial[imageArrows, 
            imageArrowEquivalences], imageQuiverObjectEquivalences]]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[imageCompositions = Select[Tuples[Normal[imageMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[imageMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], 
             compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ imageCompositions, Length[reduceObjects[imageObjects, 
        imageQuiverObjectEquivalences]]]; imageMorphismAssociation = 
      Association[Select[Normal[imageMorphismAssociation], Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[imageMorphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[imageObjects, imageQuiverObjectEquivalences]; 
     imageMorphismAssociation = Association[DeleteDuplicates[Normal[imageMorphismAssociation] //. 
         {compositionSymbol[tensorProductSymbol[x_, y_], tensorProductSymbol[z_, w_]] :> 
           tensorProductSymbol[compositionSymbol[x, z], compositionSymbol[y, w]], 
          compositionSymbol[x_, identitySymbol[y_]] :> x, compositionSymbol[identitySymbol[x_], y_] :> y, 
          compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[compositionSymbol[x, y], z]}]]; 
     EdgeTaggedGraph[reduceObjects[reduceObjects[Catenate[Outer[tensorProductSymbol, objects, objects]], 
         quiverObjectEquivalences], categoryObjectEquivalences], (DirectedEdge @@ Last[#1] & ) /@ 
        Normal[reduceArrowsFinal[reduceArrowsInitial[domainMorphismAssociation, categoryMorphismEquivalences], 
          categoryObjectEquivalences]], VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], 
       VertexLabels -> Placed["Name", Center], VertexLabelStyle -> Directive[Bold, 20], 
       EdgeLabelStyle -> Directive[Bold, 20], EdgeStyle -> Directive[Black, Thick], 
       GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}] -> 
      EdgeTaggedGraph[reduceObjects[reduceObjects[reduceObjects[reduceObjects[imageObjects, 
           imageQuiverObjectEquivalences], imageObjectEquivalences], monoidalEquations], objectEquivalences], 
       (DirectedEdge @@ Last[#1] & ) /@ Normal[reduceArrowsFinal[reduceArrowsFinal[reduceArrowsFinal[
            reduceArrowsInitial[reduceArrowsInitial[imageMorphismAssociation, imageMorphismEquivalences], 
             morphismEquivalences], imageObjectEquivalences], monoidalEquations], objectEquivalences]], 
       VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], VertexLabels -> Placed["Name", Center], 
       VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
       EdgeStyle -> Directive[Black, Thick], GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "ObjectMappings" -> objectMappings_Association, "TensorProductSymbol" -> tensorProductSymbol_, 
     "UnitObject" -> unitObject_]]["SimpleLabeledGraph"] := 
  Module[{productArrows, domainMorphismAssociation, domainCompositions, imageMorphismAssociation, imageCompositions}, 
    productArrows = Association[DeleteDuplicates[
        Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ Select[Normal[arrows], First[Last[#1]] =!= 
                 Last[Last[#1]] & ], First /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]] -> 
           Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ], (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ]]], Catenate[Outer[tensorProductSymbol, (Last[Last[#1]] & ) /@ 
                Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ], (Last[Last[#1]] & ) /@ 
                Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]]]]], 
         Thread[Catenate[Outer[tensorProductSymbol, First /@ Select[Normal[arrows], First[Last[#1]] =!= 
                 Last[Last[#1]] & ], identitySymbol /@ objects]] -> 
           Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ], objects]], Catenate[Outer[tensorProductSymbol, 
               (Last[Last[#1]] & ) /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ], objects]]]]], 
         Thread[Catenate[Outer[tensorProductSymbol, identitySymbol /@ objects, First /@ Select[Normal[arrows], 
               First[Last[#1]] =!= Last[Last[#1]] & ]]] -> Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, 
               objects, (First[Last[#1]] & ) /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]], 
             Catenate[Outer[tensorProductSymbol, objects, (Last[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ]]]]]]]]]; domainMorphismAssociation = 
      Association[Select[Normal[productArrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[domainCompositions = Select[Tuples[Normal[domainMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[domainMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          domainMorphismAssociation = Association[Append[Normal[domainMorphismAssociation], 
             compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ domainCompositions, 
      Length[Catenate[Outer[tensorProductSymbol, objects, objects]]]]; domainMorphismAssociation = 
      Association[Select[Normal[domainMorphismAssociation], Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     domainMorphismAssociation = Association[DeleteDuplicates[Normal[domainMorphismAssociation] //. 
         {compositionSymbol[tensorProductSymbol[x_, y_], tensorProductSymbol[z_, w_]] :> 
           tensorProductSymbol[compositionSymbol[x, z], compositionSymbol[y, w]], 
          compositionSymbol[x_, identitySymbol[y_]] :> x, compositionSymbol[identitySymbol[x_], y_] :> y, 
          compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[compositionSymbol[x, y], z]}]]; 
     imageMorphismAssociation = Association[Select[Normal[Association[DeleteDuplicates[
           Normal[productArrows] /. Normal[arrowMappings] /. Normal[objectMappings]]]], 
        First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[imageCompositions = Select[Tuples[Normal[imageMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[imageMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], 
             compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ imageCompositions, 
      Length[DeleteDuplicates[Catenate[Outer[tensorProductSymbol, objects, objects]] /. Normal[objectMappings]]]]; 
     imageMorphismAssociation = Association[Select[Normal[imageMorphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     imageMorphismAssociation = Association[DeleteDuplicates[Normal[imageMorphismAssociation] //. 
         {compositionSymbol[tensorProductSymbol[x_, y_], tensorProductSymbol[z_, w_]] :> 
           tensorProductSymbol[compositionSymbol[x, z], compositionSymbol[y, w]], 
          compositionSymbol[x_, identitySymbol[y_]] :> x, compositionSymbol[identitySymbol[x_], y_] :> y, 
          compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[compositionSymbol[x, y], z]}]]; 
     EdgeTaggedGraph[Catenate[Outer[tensorProductSymbol, objects, objects]], 
       (Labeled[DirectedEdge @@ Last[#1], Placed[First[#1], 0.5]] & ) /@ 
        Select[DeleteDuplicatesBy[Normal[domainMorphismAssociation], DirectedEdge @@ Last[#1] & ], 
         First[Last[#1]] =!= Last[Last[#1]] & ], VertexSize -> 0.3, VertexStyle -> Directive[Transparent, 
         EdgeForm[None]], VertexLabels -> Placed["Name", Center], VertexLabelStyle -> Directive[Bold, 20], 
       EdgeLabelStyle -> Directive[Bold, 20], EdgeStyle -> Directive[Black, Thick], 
       GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}] -> 
      EdgeTaggedGraph[DeleteDuplicates[Catenate[Outer[tensorProductSymbol, objects, objects]] /. Normal[objectMappings]], 
       (Labeled[DirectedEdge @@ Last[#1], Placed[First[#1], 0.5]] & ) /@ 
        Select[DeleteDuplicatesBy[Normal[imageMorphismAssociation], DirectedEdge @@ Last[#1] & ], 
         First[Last[#1]] =!= Last[Last[#1]] & ], VertexSize -> 0.3, VertexStyle -> Directive[Transparent, 
         EdgeForm[None]], VertexLabels -> Placed["Name", Center], VertexLabelStyle -> Directive[Bold, 20], 
       EdgeLabelStyle -> Directive[Bold, 20], EdgeStyle -> Directive[Black, Thick], 
       GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "ObjectMappings" -> objectMappings_Association, "TensorProductSymbol" -> tensorProductSymbol_, 
     "UnitObject" -> unitObject_]]["SimpleUnlabeledGraph"] := 
  Module[{productArrows, domainMorphismAssociation, domainCompositions, imageMorphismAssociation, imageCompositions}, 
    productArrows = Association[DeleteDuplicates[
        Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ Select[Normal[arrows], First[Last[#1]] =!= 
                 Last[Last[#1]] & ], First /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]] -> 
           Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ], (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ]]], Catenate[Outer[tensorProductSymbol, (Last[Last[#1]] & ) /@ 
                Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ], (Last[Last[#1]] & ) /@ 
                Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]]]]], 
         Thread[Catenate[Outer[tensorProductSymbol, First /@ Select[Normal[arrows], First[Last[#1]] =!= 
                 Last[Last[#1]] & ], identitySymbol /@ objects]] -> 
           Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ], objects]], Catenate[Outer[tensorProductSymbol, 
               (Last[Last[#1]] & ) /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ], objects]]]]], 
         Thread[Catenate[Outer[tensorProductSymbol, identitySymbol /@ objects, First /@ Select[Normal[arrows], 
               First[Last[#1]] =!= Last[Last[#1]] & ]]] -> Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, 
               objects, (First[Last[#1]] & ) /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]], 
             Catenate[Outer[tensorProductSymbol, objects, (Last[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ]]]]]]]]]; domainMorphismAssociation = 
      Association[Select[Normal[productArrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[domainCompositions = Select[Tuples[Normal[domainMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[domainMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          domainMorphismAssociation = Association[Append[Normal[domainMorphismAssociation], 
             compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ domainCompositions, 
      Length[Catenate[Outer[tensorProductSymbol, objects, objects]]]]; domainMorphismAssociation = 
      Association[Select[Normal[domainMorphismAssociation], Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     domainMorphismAssociation = Association[DeleteDuplicates[Normal[domainMorphismAssociation] //. 
         {compositionSymbol[tensorProductSymbol[x_, y_], tensorProductSymbol[z_, w_]] :> 
           tensorProductSymbol[compositionSymbol[x, z], compositionSymbol[y, w]], 
          compositionSymbol[x_, identitySymbol[y_]] :> x, compositionSymbol[identitySymbol[x_], y_] :> y, 
          compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[compositionSymbol[x, y], z]}]]; 
     imageMorphismAssociation = Association[Select[Normal[Association[DeleteDuplicates[
           Normal[productArrows] /. Normal[arrowMappings] /. Normal[objectMappings]]]], 
        First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[imageCompositions = Select[Tuples[Normal[imageMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[imageMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], 
             compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ imageCompositions, 
      Length[DeleteDuplicates[Catenate[Outer[tensorProductSymbol, objects, objects]] /. Normal[objectMappings]]]]; 
     imageMorphismAssociation = Association[Select[Normal[imageMorphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     imageMorphismAssociation = Association[DeleteDuplicates[Normal[imageMorphismAssociation] //. 
         {compositionSymbol[tensorProductSymbol[x_, y_], compositionSymbol[z_, w_]] :> tensorProductSymbol[
            compositionSymbol[x, z], compositionSymbol[y, w]], compositionSymbol[x_, identitySymbol[y_]] :> x, 
          compositionSymbol[identitySymbol[x_], y_] :> y, compositionSymbol[x_, compositionSymbol[y_, z_]] :> 
           compositionSymbol[compositionSymbol[x, y], z]}]]; 
     EdgeTaggedGraph[Catenate[Outer[tensorProductSymbol, objects, objects]], (DirectedEdge @@ Last[#1] & ) /@ 
        Select[DeleteDuplicatesBy[Normal[domainMorphismAssociation], DirectedEdge @@ Last[#1] & ], 
         First[Last[#1]] =!= Last[Last[#1]] & ], VertexSize -> 0.3, VertexStyle -> Directive[Transparent, 
         EdgeForm[None]], VertexLabels -> Placed["Name", Center], VertexLabelStyle -> Directive[Bold, 20], 
       EdgeLabelStyle -> Directive[Bold, 20], EdgeStyle -> Directive[Black, Thick], 
       GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}] -> 
      EdgeTaggedGraph[DeleteDuplicates[Catenate[Outer[tensorProductSymbol, objects, objects]] /. Normal[objectMappings]], 
       (DirectedEdge @@ Last[#1] & ) /@ Select[DeleteDuplicatesBy[Normal[imageMorphismAssociation], 
          DirectedEdge @@ Last[#1] & ], First[Last[#1]] =!= Last[Last[#1]] & ], VertexSize -> 0.3, 
       VertexStyle -> Directive[Transparent, EdgeForm[None]], VertexLabels -> Placed["Name", Center], 
       VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
       EdgeStyle -> Directive[Black, Thick], GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "ObjectMappings" -> objectMappings_Association, "TensorProductSymbol" -> tensorProductSymbol_, 
     "UnitObject" -> unitObject_]]["ReducedSimpleLabeledGraph"] := 
  Module[{objectFunction, associatorEquations, leftUnitorEquations, rightUnitorEquations, monoidalEquations, 
     productArrows, domainMorphismAssociation, domainCompositions, morphismAssociation, compositions, imageObjects, 
     imageArrows, imageQuiverObjectEquivalences, imageObjectEquivalences, imageArrowEquivalences, 
     imageMorphismEquivalences, imageMorphismAssociation, imageCompositions}, 
    objectFunction = Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ Catenate[Outer[tensorProductSymbol, 
               reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], reduceObjects[
                reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences]]]]] -> 
          reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Values[Association[(#1 -> #1 & ) /@ Catenate[
                Outer[tensorProductSymbol, reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
                  categoryObjectEquivalences], reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
                  categoryObjectEquivalences]]]]], quiverObjectEquivalences], categoryObjectEquivalences]]], 
       Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[objectMappings], 
            quiverObjectEquivalences], categoryObjectEquivalences] -> reduceObjectsWithDuplicates[
           reduceObjectsWithDuplicates[Values[objectMappings], quiverObjectEquivalences], categoryObjectEquivalences]]]]; 
     associatorEquations = DeleteDuplicates[Select[reduceObjects[
         (tensorProductSymbol[#1[[1]], tensorProductSymbol[#1[[2]], #1[[3]]]] == tensorProductSymbol[
              tensorProductSymbol[#1[[1]], #1[[2]]], #1[[3]]] /. Normal[objectFunction] & ) /@ 
          Tuples[reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 3], 
         objectEquivalences], #1 =!= True & ]]; leftUnitorEquations = 
      DeleteDuplicates[Select[reduceObjects[(tensorProductSymbol[unitObject, #1] == #1 /. Normal[objectFunction] & ) /@ 
          reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 
         objectEquivalences], #1 =!= True & ]]; rightUnitorEquations = 
      DeleteDuplicates[Select[reduceObjects[(tensorProductSymbol[#1, unitObject] == #1 /. Normal[objectFunction] & ) /@ 
          reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 
         objectEquivalences], #1 =!= True & ]]; monoidalEquations = DeleteDuplicates[
       Join[associatorEquations, leftUnitorEquations, rightUnitorEquations]]; 
     productArrows = Association[DeleteDuplicates[
        Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ Select[Normal[arrows], First[Last[#1]] =!= 
                 Last[Last[#1]] & ], First /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]] -> 
           Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ], (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ]]], Catenate[Outer[tensorProductSymbol, (Last[Last[#1]] & ) /@ 
                Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ], (Last[Last[#1]] & ) /@ 
                Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]]]]], 
         Thread[Catenate[Outer[tensorProductSymbol, First /@ Select[Normal[arrows], First[Last[#1]] =!= 
                 Last[Last[#1]] & ], identitySymbol /@ objects]] -> 
           Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ], objects]], Catenate[Outer[tensorProductSymbol, 
               (Last[Last[#1]] & ) /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ], objects]]]]], 
         Thread[Catenate[Outer[tensorProductSymbol, identitySymbol /@ objects, First /@ Select[Normal[arrows], 
               First[Last[#1]] =!= Last[Last[#1]] & ]]] -> Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, 
               objects, (First[Last[#1]] & ) /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]], 
             Catenate[Outer[tensorProductSymbol, objects, (Last[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ]]]]]]]]]; domainMorphismAssociation = 
      Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[productArrows, arrowEquivalences], 
          quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[domainCompositions = Select[Tuples[Normal[domainMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[domainMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          domainMorphismAssociation = Association[Append[Normal[domainMorphismAssociation], 
             compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ domainCompositions, 
      Length[reduceObjects[Catenate[Outer[tensorProductSymbol, objects, objects]], quiverObjectEquivalences]]]; 
     domainMorphismAssociation = Association[Select[Normal[domainMorphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     domainMorphismAssociation = Association[DeleteDuplicates[Normal[domainMorphismAssociation] //. 
         {compositionSymbol[tensorProductSymbol[x_, y_], tensorProductSymbol[z_, w_]] :> 
           tensorProductSymbol[compositionSymbol[x, z], compositionSymbol[y, w]], 
          compositionSymbol[x_, identitySymbol[y_]] :> x, compositionSymbol[identitySymbol[x_], y_] :> y, 
          compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[compositionSymbol[x, y], z]}]]; 
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
            DirectedEdge[#1, #1]]]] & ) /@ objects; imageObjects = DeleteDuplicates[
       Catenate[Outer[tensorProductSymbol, objects, objects]] /. Normal[objectMappings]]; 
     imageArrows = Association[DeleteDuplicates[Normal[productArrows] /. Normal[arrowMappings] /. 
         Normal[objectMappings]]]; imageQuiverObjectEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ quiverObjectEquivalences, 
               objects]] -> Catenate[Outer[tensorProductSymbol, Last /@ quiverObjectEquivalences, objects]]], 
           Thread[Catenate[Outer[tensorProductSymbol, objects, First /@ quiverObjectEquivalences]] -> 
             Catenate[Outer[tensorProductSymbol, objects, Last /@ quiverObjectEquivalences]]]] /. 
          Normal[objectMappings]] /. Rule -> Equal, #1 =!= True & ]; imageObjectEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ categoryObjectEquivalences, 
               objects]] -> Catenate[Outer[tensorProductSymbol, Last /@ categoryObjectEquivalences, objects]]], 
           Thread[Catenate[Outer[tensorProductSymbol, objects, First /@ categoryObjectEquivalences]] -> 
             Catenate[Outer[tensorProductSymbol, objects, Last /@ categoryObjectEquivalences]]]] /. 
          Normal[objectMappings]] /. Rule -> Equal, #1 =!= True & ]; imageArrowEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ arrowEquivalences, First /@ 
                Normal[arrows]]] -> Catenate[Outer[tensorProductSymbol, Last /@ arrowEquivalences, First /@ 
                Normal[arrows]]]], Thread[Catenate[Outer[tensorProductSymbol, First /@ Normal[arrows], First /@ 
                arrowEquivalences]] -> Catenate[Outer[tensorProductSymbol, First /@ Normal[arrows], Last /@ 
                arrowEquivalences]]]] /. Normal[arrowMappings]] /. Rule -> Equal, #1 =!= True & ]; 
     imageMorphismEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ categoryMorphismEquivalences, 
                First /@ Normal[morphismAssociation]]] -> Catenate[Outer[tensorProductSymbol, 
                Last /@ categoryMorphismEquivalences, First /@ Normal[morphismAssociation]]]], 
            Thread[Catenate[Outer[tensorProductSymbol, First /@ Normal[morphismAssociation], First /@ 
                 categoryMorphismEquivalences]] -> Catenate[Outer[tensorProductSymbol, First /@ 
                 Normal[morphismAssociation], Last /@ categoryMorphismEquivalences]]]] /. Normal[arrowMappings] /. 
          Normal[objectMappings]] /. Rule -> Equal, #1 =!= True & ]; imageMorphismAssociation = 
      Association[Select[DeleteDuplicates[Normal[reduceArrowsFinal[reduceArrowsInitial[imageArrows, 
            imageArrowEquivalences], imageQuiverObjectEquivalences]]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[imageCompositions = Select[Tuples[Normal[imageMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[imageMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], 
             compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ imageCompositions, Length[reduceObjects[imageObjects, 
        imageQuiverObjectEquivalences]]]; imageMorphismAssociation = 
      Association[Select[Normal[imageMorphismAssociation], Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     imageMorphismAssociation = Association[DeleteDuplicates[Normal[imageMorphismAssociation] //. 
         {compositionSymbol[tensorProductSymbol[x_, y_], tensorProductSymbol[z_, w_]] :> 
           tensorProductSymbol[compositionSymbol[x, z], compositionSymbol[y, w]], 
          compositionSymbol[x_, identitySymbol[y_]] :> x, compositionSymbol[identitySymbol[x_], y_] :> y, 
          compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[compositionSymbol[x, y], z]}]]; 
     EdgeTaggedGraph[reduceObjects[reduceObjects[Catenate[Outer[tensorProductSymbol, objects, objects]], 
         quiverObjectEquivalences], categoryObjectEquivalences], 
       (Labeled[DirectedEdge @@ Last[#1], Placed[First[#1], 0.5]] & ) /@ 
        Normal[reduceArrowsFinal[reduceArrowsInitial[Association[Select[DeleteDuplicatesBy[
              Normal[domainMorphismAssociation], DirectedEdge @@ Last[#1] & ], First[Last[#1]] =!= Last[Last[#1]] & ]], 
           categoryMorphismEquivalences], categoryObjectEquivalences]], VertexSize -> 0.3, 
       VertexStyle -> Directive[Transparent, EdgeForm[None]], VertexLabels -> Placed["Name", Center], 
       VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
       EdgeStyle -> Directive[Black, Thick], GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}] -> 
      EdgeTaggedGraph[reduceObjects[reduceObjects[reduceObjects[reduceObjects[imageObjects, 
           imageQuiverObjectEquivalences], imageObjectEquivalences], monoidalEquations], objectEquivalences], 
       (Labeled[DirectedEdge @@ Last[#1], Placed[First[#1], 0.5]] & ) /@ 
        Normal[reduceArrowsFinal[reduceArrowsFinal[reduceArrowsInitial[reduceArrowsInitial[reduceArrowsInitial[
              Association[Select[DeleteDuplicatesBy[Normal[imageMorphismAssociation], DirectedEdge @@ Last[#1] & ], 
                First[Last[#1]] =!= Last[Last[#1]] & ]], imageMorphismEquivalences], morphismEquivalences], 
            imageObjectEquivalences], monoidalEquations], objectEquivalences]], VertexSize -> 0.3, 
       VertexStyle -> Directive[Transparent, EdgeForm[None]], VertexLabels -> Placed["Name", Center], 
       VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
       EdgeStyle -> Directive[Black, Thick], GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "ObjectMappings" -> objectMappings_Association, "TensorProductSymbol" -> tensorProductSymbol_, 
     "UnitObject" -> unitObject_]]["ReducedSimpleUnlabeledGraph"] := 
  Module[{objectFunction, associatorEquations, leftUnitorEquations, rightUnitorEquations, monoidalEquations, 
     productArrows, domainMorphismAssociation, domainCompositions, morphismAssociation, compositions, imageObjects, 
     imageArrows, imageQuiverObjectEquivalences, imageObjectEquivalences, imageArrowEquivalences, 
     imageMorphismEquivalences, imageMorphismAssociation, imageCompositions}, 
    objectFunction = Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ Catenate[Outer[tensorProductSymbol, 
               reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], reduceObjects[
                reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences]]]]] -> 
          reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Values[Association[(#1 -> #1 & ) /@ Catenate[
                Outer[tensorProductSymbol, reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
                  categoryObjectEquivalences], reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
                  categoryObjectEquivalences]]]]], quiverObjectEquivalences], categoryObjectEquivalences]]], 
       Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[objectMappings], 
            quiverObjectEquivalences], categoryObjectEquivalences] -> reduceObjectsWithDuplicates[
           reduceObjectsWithDuplicates[Values[objectMappings], quiverObjectEquivalences], categoryObjectEquivalences]]]]; 
     associatorEquations = DeleteDuplicates[Select[reduceObjects[
         (tensorProductSymbol[#1[[1]], tensorProductSymbol[#1[[2]], #1[[3]]]] == tensorProductSymbol[
              tensorProductSymbol[#1[[1]], #1[[2]]], #1[[3]]] /. Normal[objectFunction] & ) /@ 
          Tuples[reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 3], 
         objectEquivalences], #1 =!= True & ]]; leftUnitorEquations = 
      DeleteDuplicates[Select[reduceObjects[(tensorProductSymbol[unitObject, #1] == #1 /. Normal[objectFunction] & ) /@ 
          reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 
         objectEquivalences], #1 =!= True & ]]; rightUnitorEquations = 
      DeleteDuplicates[Select[reduceObjects[(tensorProductSymbol[#1, unitObject] == #1 /. Normal[objectFunction] & ) /@ 
          reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 
         objectEquivalences], #1 =!= True & ]]; monoidalEquations = DeleteDuplicates[
       Join[associatorEquations, leftUnitorEquations, rightUnitorEquations]]; 
     productArrows = Association[DeleteDuplicates[
        Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ Select[Normal[arrows], First[Last[#1]] =!= 
                 Last[Last[#1]] & ], First /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]] -> 
           Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ], (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ]]], Catenate[Outer[tensorProductSymbol, (Last[Last[#1]] & ) /@ 
                Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ], (Last[Last[#1]] & ) /@ 
                Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]]]]], 
         Thread[Catenate[Outer[tensorProductSymbol, First /@ Select[Normal[arrows], First[Last[#1]] =!= 
                 Last[Last[#1]] & ], identitySymbol /@ objects]] -> 
           Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ], objects]], Catenate[Outer[tensorProductSymbol, 
               (Last[Last[#1]] & ) /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ], objects]]]]], 
         Thread[Catenate[Outer[tensorProductSymbol, identitySymbol /@ objects, First /@ Select[Normal[arrows], 
               First[Last[#1]] =!= Last[Last[#1]] & ]]] -> Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, 
               objects, (First[Last[#1]] & ) /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]], 
             Catenate[Outer[tensorProductSymbol, objects, (Last[Last[#1]] & ) /@ Select[Normal[arrows], 
                 First[Last[#1]] =!= Last[Last[#1]] & ]]]]]]]]]; domainMorphismAssociation = 
      Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[productArrows, arrowEquivalences], 
          quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[domainCompositions = Select[Tuples[Normal[domainMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[domainMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          domainMorphismAssociation = Association[Append[Normal[domainMorphismAssociation], 
             compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ domainCompositions, 
      Length[reduceObjects[Catenate[Outer[tensorProductSymbol, objects, objects]], quiverObjectEquivalences]]]; 
     domainMorphismAssociation = Association[Select[Normal[domainMorphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     domainMorphismAssociation = Association[DeleteDuplicates[Normal[domainMorphismAssociation] //. 
         {compositionSymbol[tensorProductSymbol[x_, y_], tensorProductSymbol[z_, w_]] :> 
           tensorProductSymbol[compositionSymbol[x, z], compositionSymbol[y, w]], 
          compositionSymbol[x_, identitySymbol[y_]] :> x, compositionSymbol[identitySymbol[x_], y_] :> y, 
          compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[compositionSymbol[x, y], z]}]]; 
     morphismAssociation = Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[compositions = Select[Tuples[Normal[morphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ Normal[morphismAssociation], 
           StringDelete[ToString[compositionSymbol[First[Last[#1]], First[First[#1]]]], {"(", ")", " "}] -> 
            DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], morphismAssociation = 
           Association[Append[Normal[morphismAssociation], compositionSymbol[First[Last[#1]], First[First[#1]]] -> 
              DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]]]] & ) /@ compositions, Length[objects]]; 
     morphismAssociation = Association[Select[Normal[morphismAssociation], 
        Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     (If[ !MemberQ[Normal[morphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
        morphismAssociation = Association[Append[Normal[morphismAssociation], identitySymbol[#1] -> 
            DirectedEdge[#1, #1]]]] & ) /@ objects; imageObjects = DeleteDuplicates[
       Catenate[Outer[tensorProductSymbol, objects, objects]] /. Normal[objectMappings]]; 
     imageArrows = Association[DeleteDuplicates[Normal[productArrows] /. Normal[arrowMappings] /. 
         Normal[objectMappings]]]; imageQuiverObjectEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ quiverObjectEquivalences, 
               objects]] -> Catenate[Outer[tensorProductSymbol, Last /@ quiverObjectEquivalences, objects]]], 
           Thread[Catenate[Outer[tensorProductSymbol, objects, First /@ quiverObjectEquivalences]] -> 
             Catenate[Outer[tensorProductSymbol, objects, Last /@ quiverObjectEquivalences]]]] /. 
          Normal[objectMappings]] /. Rule -> Equal, #1 =!= True & ]; imageObjectEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ categoryObjectEquivalences, 
               objects]] -> Catenate[Outer[tensorProductSymbol, Last /@ categoryObjectEquivalences, objects]]], 
           Thread[Catenate[Outer[tensorProductSymbol, objects, First /@ categoryObjectEquivalences]] -> 
             Catenate[Outer[tensorProductSymbol, objects, Last /@ categoryObjectEquivalences]]]] /. 
          Normal[objectMappings]] /. Rule -> Equal, #1 =!= True & ]; imageArrowEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ arrowEquivalences, First /@ 
                Normal[arrows]]] -> Catenate[Outer[tensorProductSymbol, Last /@ arrowEquivalences, First /@ 
                Normal[arrows]]]], Thread[Catenate[Outer[tensorProductSymbol, First /@ Normal[arrows], First /@ 
                arrowEquivalences]] -> Catenate[Outer[tensorProductSymbol, First /@ Normal[arrows], Last /@ 
                arrowEquivalences]]]] /. Normal[arrowMappings]] /. Rule -> Equal, #1 =!= True & ]; 
     imageMorphismEquivalences = 
      Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ categoryMorphismEquivalences, 
                First /@ Normal[morphismAssociation]]] -> Catenate[Outer[tensorProductSymbol, 
                Last /@ categoryMorphismEquivalences, First /@ Normal[morphismAssociation]]]], 
            Thread[Catenate[Outer[tensorProductSymbol, First /@ Normal[morphismAssociation], First /@ 
                 categoryMorphismEquivalences]] -> Catenate[Outer[tensorProductSymbol, First /@ 
                 Normal[morphismAssociation], Last /@ categoryMorphismEquivalences]]]] /. Normal[arrowMappings] /. 
          Normal[objectMappings]] /. Rule -> Equal, #1 =!= True & ]; imageMorphismAssociation = 
      Association[Select[DeleteDuplicates[Normal[reduceArrowsFinal[reduceArrowsInitial[imageArrows, 
            imageArrowEquivalences], imageQuiverObjectEquivalences]]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
     Do[imageCompositions = Select[Tuples[Normal[imageMorphismAssociation], 2], 
         Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
       (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
             Normal[imageMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
          imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], 
             compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], Last[
                Last[Last[#1]]]]]]] & ) /@ imageCompositions, Length[reduceObjects[imageObjects, 
        imageQuiverObjectEquivalences]]]; imageMorphismAssociation = 
      Association[Select[Normal[imageMorphismAssociation], Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
          Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
     imageMorphismAssociation = Association[DeleteDuplicates[Normal[imageMorphismAssociation] //. 
         {compositionSymbol[tensorProductSymbol[x_, y_], tensorProductSymbol[z_, w_]] :> 
           tensorProductSymbol[compositionSymbol[x, z], compositionSymbol[y, w]], 
          compositionSymbol[x_, identitySymbol[y_]] :> x, compositionSymbol[identitySymbol[x_], y_] :> y, 
          compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[compositionSymbol[x, y], z]}]]; 
     EdgeTaggedGraph[reduceObjects[reduceObjects[Catenate[Outer[tensorProductSymbol, objects, objects]], 
         quiverObjectEquivalences], categoryObjectEquivalences], (DirectedEdge @@ Last[#1] & ) /@ 
        Normal[reduceArrowsFinal[reduceArrowsInitial[Association[Select[DeleteDuplicatesBy[
              Normal[domainMorphismAssociation], DirectedEdge @@ Last[#1] & ], First[Last[#1]] =!= Last[Last[#1]] & ]], 
           categoryMorphismEquivalences], categoryObjectEquivalences]], VertexSize -> 0.3, 
       VertexStyle -> Directive[Transparent, EdgeForm[None]], VertexLabels -> Placed["Name", Center], 
       VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
       EdgeStyle -> Directive[Black, Thick], GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}] -> 
      EdgeTaggedGraph[reduceObjects[reduceObjects[reduceObjects[reduceObjects[imageObjects, 
           imageQuiverObjectEquivalences], imageObjectEquivalences], monoidalEquations], objectEquivalences], 
       (DirectedEdge @@ Last[#1] & ) /@ Normal[reduceArrowsFinal[reduceArrowsFinal[reduceArrowsInitial[
            reduceArrowsInitial[reduceArrowsInitial[Association[Select[DeleteDuplicatesBy[Normal[
                  imageMorphismAssociation], DirectedEdge @@ Last[#1] & ], First[Last[#1]] =!= Last[Last[#1]] & ]], 
              imageMorphismEquivalences], morphismEquivalences], imageObjectEquivalences], monoidalEquations], 
          objectEquivalences]], VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], 
       VertexLabels -> Placed["Name", Center], VertexLabelStyle -> Directive[Bold, 20], 
       EdgeLabelStyle -> Directive[Bold, 20], EdgeStyle -> Directive[Black, Thick], 
       GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "ObjectMappings" -> objectMappings_Association, "TensorProductSymbol" -> tensorProductSymbol_, 
     "UnitObject" -> unitObject_]]["AssociationForm"] := 
  Association["Category" -> ResourceFunction["AbstractCategory"][Association["CompositionSymbol" -> compositionSymbol, 
       "IdentitySymbol" -> identitySymbol, "MorphismEquivalences" -> categoryMorphismEquivalences, 
       "ObjectEquivalences" -> categoryObjectEquivalences, "Quiver" -> ResourceFunction["AbstractQuiver"][
         Association["ArrowEquivalences" -> arrowEquivalences, "Arrows" -> arrows, "ObjectEquivalences" -> 
           quiverObjectEquivalences, "Objects" -> objects]]]], "ObjectMappings" -> objectMappings, 
    "ArrowMappings" -> arrowMappings, "TensorProductSymbol" -> tensorProductSymbol, "UnitObject" -> unitObject, 
    "ObjectEquivalences" -> objectEquivalences, "MorphismEquivalences" -> morphismEquivalences] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "ObjectMappings" -> objectMappings_Association, "TensorProductSymbol" -> tensorProductSymbol_, 
     "UnitObject" -> unitObject_]]["Properties"] := {"ObjectCount", "MorphismCount", "ObjectEquivalences", 
    "ObjectEquivalenceCount", "MorphismEquivalences", "MorphismEquivalenceCount", "ReducedObjectCount", 
    "ReducedMorphismCount", "TensorProductSymbol", "UnitObject", "Category", "DualStrictMonoidalCategory", 
    "ObjectMappings", "ObjectMappingCount", "ReducedObjectMappings", "ReducedObjectMappingCount", "ArrowMappings", 
    "ArrowMappingCount", "MorphismMappings", "MorphismMappingCount", "ReducedMorphismMappings", 
    "ReducedMorphismMappingCount", "ValidStrictMonoidalCategoryQ", "FullLabeledStringDiagrams", 
    "FullUnlabeledStringDiagrams", "ReducedLabeledStringDiagrams", "ReducedUnlabeledStringDiagrams", 
    "AssociatorEquations", "ReducedAssociatorEquations", "LeftUnitorEquations", "ReducedLeftUnitorEquations", 
    "RightUnitorEquations", "ReducedRightUnitorEquations", "CommutativeDiagramQ", "CommutativityEquations", 
    "ReducedCommutativityEquations", "StrictSymmetricMonoidalCategoryQ", "SymmetryEquations", "ReducedSymmetryEquations", 
    "FullLabeledGraph", "FullUnlabeledGraph", "ReducedLabeledGraph", "ReducedUnlabeledGraph", "SimpleLabeledGraph", 
    "SimpleUnlabeledGraph", "ReducedSimpleLabeledGraph", "ReducedSimpleUnlabeledGraph", "AssociationForm", 
    "Properties"} /; SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === 
     "AbstractCategory"
AbstractStrictMonoidalCategory /: 
  MakeBoxes[abstractStrictMonoidalCategory:AbstractStrictMonoidalCategory[
      Association["ArrowMappings" -> arrowMappings_Association, "Category" -> (abstractCategory_)[
         Association["CompositionSymbol" -> compositionSymbol_, "IdentitySymbol" -> identitySymbol_, 
          "MorphismEquivalences" -> categoryMorphismEquivalences_List, "ObjectEquivalences" -> 
           categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> 
              arrowEquivalences_List, "Arrows" -> arrows_Association, "ObjectEquivalences" -> 
              quiverObjectEquivalences_List, "Objects" -> objects_List]]]], "MorphismEquivalences" -> 
        morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
       "ObjectMappings" -> objectMappings_Association, "TensorProductSymbol" -> tensorProductSymbol_, 
       "UnitObject" -> unitObject_]], format_] := 
   Module[{productArrows, domainMorphismAssociation, domainCompositions, imageMorphismAssociation, imageCompositions, 
      icon, objectCount, morphismCount, objectFunction, associatorEquations, leftUnitorEquations, rightUnitorEquations, 
      monoidalEquations, reducedDomainMorphismAssociation, reducedDomainCompositions, morphismAssociation, compositions, 
      imageObjects, imageArrows, imageQuiverObjectEquivalences, imageObjectEquivalences, imageArrowEquivalences, 
      imageMorphismEquivalences, reducedImageMorphismAssociation, reducedImageCompositions, reducedObjectCount, 
      reducedMorphismCount}, productArrows = Association[DeleteDuplicates[
         Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ Select[Normal[arrows], First[Last[#1]] =!= 
                  Last[Last[#1]] & ], First /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]] -> 
            Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                  First[Last[#1]] =!= Last[Last[#1]] & ], (First[Last[#1]] & ) /@ Select[Normal[arrows], 
                  First[Last[#1]] =!= Last[Last[#1]] & ]]], Catenate[Outer[tensorProductSymbol, (Last[Last[#1]] & ) /@ 
                 Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ], (Last[Last[#1]] & ) /@ 
                 Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]]]]], 
          Thread[Catenate[Outer[tensorProductSymbol, First /@ Select[Normal[arrows], First[Last[#1]] =!= 
                  Last[Last[#1]] & ], identitySymbol /@ objects]] -> Thread[DirectedEdge[Catenate[Outer[
                tensorProductSymbol, (First[Last[#1]] & ) /@ Select[Normal[arrows], First[Last[#1]] =!= 
                    Last[Last[#1]] & ], objects]], Catenate[Outer[tensorProductSymbol, (Last[Last[#1]] & ) /@ 
                 Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ], objects]]]]], 
          Thread[Catenate[Outer[tensorProductSymbol, identitySymbol /@ objects, First /@ Select[Normal[arrows], 
                First[Last[#1]] =!= Last[Last[#1]] & ]]] -> Thread[DirectedEdge[Catenate[Outer[tensorProductSymbol, 
                objects, (First[Last[#1]] & ) /@ Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]], 
              Catenate[Outer[tensorProductSymbol, objects, (Last[Last[#1]] & ) /@ Select[Normal[arrows], 
                  First[Last[#1]] =!= Last[Last[#1]] & ]]]]]]]]]; domainMorphismAssociation = 
       Association[Select[Normal[productArrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
      Do[domainCompositions = Select[Tuples[Normal[domainMorphismAssociation], 2], 
          Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
        (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
              Normal[domainMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                 First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
           domainMorphismAssociation = Association[Append[Normal[domainMorphismAssociation], compositionSymbol[
                First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], 
                Last[Last[Last[#1]]]]]]] & ) /@ domainCompositions, 
       Length[Catenate[Outer[tensorProductSymbol, objects, objects]]]]; domainMorphismAssociation = 
       Association[Select[Normal[domainMorphismAssociation], Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == 
           Length[DeleteDuplicates[Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
      (If[ !MemberQ[Normal[domainMorphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
         domainMorphismAssociation = Association[Append[Normal[domainMorphismAssociation], identitySymbol[#1] -> 
             DirectedEdge[#1, #1]]]] & ) /@ Catenate[Outer[tensorProductSymbol, objects, objects]]; 
      domainMorphismAssociation = Association[DeleteDuplicates[Normal[domainMorphismAssociation] //. 
          {compositionSymbol[tensorProductSymbol[x_, y_], tensorProductSymbol[z_, w_]] :> tensorProductSymbol[
             compositionSymbol[x, z], compositionSymbol[y, w]], compositionSymbol[x_, identitySymbol[y_]] :> x, 
           compositionSymbol[identitySymbol[x_], y_] :> y, compositionSymbol[x_, compositionSymbol[y_, z_]] :> 
            compositionSymbol[compositionSymbol[x, y], z]}]]; imageMorphismAssociation = 
       Association[Select[Normal[Association[DeleteDuplicates[Normal[productArrows] /. Normal[arrowMappings] /. 
             Normal[objectMappings]]]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
      Do[imageCompositions = Select[Tuples[Normal[imageMorphismAssociation], 2], 
          Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
        (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
              Normal[imageMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                 First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
           imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], compositionSymbol[
                First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], 
                Last[Last[Last[#1]]]]]]] & ) /@ imageCompositions, 
       Length[DeleteDuplicates[Catenate[Outer[tensorProductSymbol, objects, objects]] /. Normal[objectMappings]]]]; 
      imageMorphismAssociation = Association[Select[Normal[imageMorphismAssociation], 
         Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == Length[DeleteDuplicates[
             Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
      (If[ !MemberQ[Normal[imageMorphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
         imageMorphismAssociation = Association[Append[Normal[imageMorphismAssociation], identitySymbol[#1] -> 
             DirectedEdge[#1, #1]]]] & ) /@ DeleteDuplicates[Catenate[Outer[tensorProductSymbol, objects, objects]] /. 
         Normal[objectMappings]]; imageMorphismAssociation = Association[DeleteDuplicates[
         Normal[imageMorphismAssociation] //. {compositionSymbol[tensorProductSymbol[x_, y_], 
             tensorProductSymbol[z_, w_]] :> tensorProductSymbol[compositionSymbol[x, z], compositionSymbol[y, w]], 
           compositionSymbol[x_, identitySymbol[y_]] :> x, compositionSymbol[identitySymbol[x_], y_] :> y, 
           compositionSymbol[x_, compositionSymbol[y_, z_]] :> compositionSymbol[compositionSymbol[x, y], z]}]]; 
      icon = GraphPlot[EdgeTaggedGraph[Catenate[Outer[tensorProductSymbol, objects, objects]], 
          (DirectedEdge @@ Last[#1] & ) /@ Normal[domainMorphismAssociation], VertexSize -> 0.3, 
          VertexStyle -> Directive[Transparent, EdgeForm[None]], EdgeShapeFunction -> 
           GraphElementData["ShortFilledArrow", "ArrowSize" -> 0.05], EdgeStyle -> Black, 
          GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]] -> 
        GraphPlot[EdgeTaggedGraph[DeleteDuplicates[Catenate[Outer[tensorProductSymbol, objects, objects]] /. 
            Normal[objectMappings]], (DirectedEdge @@ Last[#1] & ) /@ Normal[imageMorphismAssociation], 
          VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], EdgeShapeFunction -> 
           GraphElementData["ShortFilledArrow", "ArrowSize" -> 0.05], EdgeStyle -> Black, 
          GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]]; 
      objectCount = Length[Catenate[Outer[tensorProductSymbol, objects, objects]]] -> 
        Length[DeleteDuplicates[Catenate[Outer[tensorProductSymbol, objects, objects]] /. Normal[objectMappings]]]; 
      morphismCount = Length[Normal[domainMorphismAssociation]] -> Length[Normal[imageMorphismAssociation]]; 
      objectFunction = Join[Association[Thread[Keys[Association[(#1 -> #1 & ) /@ Catenate[Outer[tensorProductSymbol, 
                reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 
                reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences]]]]] -> 
           reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Values[Association[(#1 -> #1 & ) /@ 
                Catenate[Outer[tensorProductSymbol, reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
                   categoryObjectEquivalences], reduceObjects[reduceObjects[objects, quiverObjectEquivalences], 
                   categoryObjectEquivalences]]]]], quiverObjectEquivalences], categoryObjectEquivalences]]], 
        Association[Thread[reduceObjectsWithDuplicates[reduceObjectsWithDuplicates[Keys[objectMappings], 
             quiverObjectEquivalences], categoryObjectEquivalences] -> reduceObjectsWithDuplicates[
            reduceObjectsWithDuplicates[Values[objectMappings], quiverObjectEquivalences], 
            categoryObjectEquivalences]]]]; associatorEquations = DeleteDuplicates[
        Select[reduceObjects[(tensorProductSymbol[#1[[1]], tensorProductSymbol[#1[[2]], #1[[3]]]] == 
              tensorProductSymbol[tensorProductSymbol[#1[[1]], #1[[2]]], #1[[3]]] /. Normal[objectFunction] & ) /@ 
           Tuples[reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 3], 
          objectEquivalences], #1 =!= True & ]]; leftUnitorEquations = DeleteDuplicates[
        Select[reduceObjects[(tensorProductSymbol[unitObject, #1] == #1 /. Normal[objectFunction] & ) /@ 
           reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 
          objectEquivalences], #1 =!= True & ]]; rightUnitorEquations = DeleteDuplicates[
        Select[reduceObjects[(tensorProductSymbol[#1, unitObject] == #1 /. Normal[objectFunction] & ) /@ 
           reduceObjects[reduceObjects[objects, quiverObjectEquivalences], categoryObjectEquivalences], 
          objectEquivalences], #1 =!= True & ]]; monoidalEquations = DeleteDuplicates[
        Join[associatorEquations, leftUnitorEquations, rightUnitorEquations]]; reducedDomainMorphismAssociation = 
       Association[Select[Normal[reduceArrowsFinal[reduceArrowsInitial[productArrows, arrowEquivalences], 
           quiverObjectEquivalences]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
      Do[reducedDomainCompositions = Select[Tuples[Normal[reducedDomainMorphismAssociation], 2], 
          Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
        (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
              Normal[reducedDomainMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                 First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
           reducedDomainMorphismAssociation = Association[Append[Normal[reducedDomainMorphismAssociation], 
              compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], 
                Last[Last[Last[#1]]]]]]] & ) /@ reducedDomainCompositions, 
       Length[reduceObjects[Catenate[Outer[tensorProductSymbol, objects, objects]], quiverObjectEquivalences]]]; 
      reducedDomainMorphismAssociation = Association[Select[Normal[reducedDomainMorphismAssociation], 
         Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == Length[DeleteDuplicates[
             Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
      (If[ !MemberQ[Normal[reducedDomainMorphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
         reducedDomainMorphismAssociation = Association[Append[Normal[reducedDomainMorphismAssociation], 
            identitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[
        Catenate[Outer[tensorProductSymbol, objects, objects]], quiverObjectEquivalences]; 
      reducedDomainMorphismAssociation = Association[DeleteDuplicates[Normal[reducedDomainMorphismAssociation] //. 
          {compositionSymbol[tensorProductSymbol[x_, y_], tensorProductSymbol[z_, w_]] :> tensorProductSymbol[
             compositionSymbol[x, z], compositionSymbol[y, w]], compositionSymbol[x_, identitySymbol[y_]] :> x, 
           compositionSymbol[identitySymbol[x_], y_] :> y, compositionSymbol[x_, compositionSymbol[y_, z_]] :> 
            compositionSymbol[compositionSymbol[x, y], z]}]]; morphismAssociation = 
       Association[Select[Normal[arrows], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
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
             DirectedEdge[#1, #1]]]] & ) /@ objects; imageObjects = DeleteDuplicates[
        Catenate[Outer[tensorProductSymbol, objects, objects]] /. Normal[objectMappings]]; 
      imageArrows = Association[DeleteDuplicates[Normal[productArrows] /. Normal[arrowMappings] /. 
          Normal[objectMappings]]]; imageQuiverObjectEquivalences = 
       Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ quiverObjectEquivalences, 
                objects]] -> Catenate[Outer[tensorProductSymbol, Last /@ quiverObjectEquivalences, objects]]], 
            Thread[Catenate[Outer[tensorProductSymbol, objects, First /@ quiverObjectEquivalences]] -> 
              Catenate[Outer[tensorProductSymbol, objects, Last /@ quiverObjectEquivalences]]]] /. 
           Normal[objectMappings]] /. Rule -> Equal, #1 =!= True & ]; imageObjectEquivalences = 
       Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ categoryObjectEquivalences, 
                objects]] -> Catenate[Outer[tensorProductSymbol, Last /@ categoryObjectEquivalences, objects]]], 
            Thread[Catenate[Outer[tensorProductSymbol, objects, First /@ categoryObjectEquivalences]] -> 
              Catenate[Outer[tensorProductSymbol, objects, Last /@ categoryObjectEquivalences]]]] /. 
           Normal[objectMappings]] /. Rule -> Equal, #1 =!= True & ]; imageArrowEquivalences = 
       Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ arrowEquivalences, 
                First /@ Normal[arrows]]] -> Catenate[Outer[tensorProductSymbol, Last /@ arrowEquivalences, 
                First /@ Normal[arrows]]]], Thread[Catenate[Outer[tensorProductSymbol, First /@ Normal[arrows], 
                First /@ arrowEquivalences]] -> Catenate[Outer[tensorProductSymbol, First /@ Normal[arrows], 
                Last /@ arrowEquivalences]]]] /. Normal[arrowMappings]] /. Rule -> Equal, #1 =!= True & ]; 
      imageMorphismEquivalences = 
       Select[DeleteDuplicates[Join[Thread[Catenate[Outer[tensorProductSymbol, First /@ categoryObjectEquivalences, 
                 First /@ Normal[morphismAssociation]]] -> Catenate[Outer[tensorProductSymbol, 
                 Last /@ categoryMorphismEquivalences, First /@ Normal[morphismAssociation]]]], 
             Thread[Catenate[Outer[tensorProductSymbol, First /@ Normal[morphismAssociation], First /@ 
                  categoryMorphismEquivalences]] -> Catenate[Outer[tensorProductSymbol, First /@ 
                  Normal[morphismAssociation], Last /@ categoryMorphismEquivalences]]]] /. Normal[arrowMappings] /. 
           Normal[objectMappings]] /. Rule -> Equal, #1 =!= True & ]; reducedImageMorphismAssociation = 
       Association[Select[DeleteDuplicates[Normal[reduceArrowsFinal[reduceArrowsInitial[imageArrows, 
             imageArrowEquivalences], imageQuiverObjectEquivalences]]], First[Last[#1]] =!= Last[Last[#1]] & ]]; 
      Do[reducedImageCompositions = Select[Tuples[Normal[reducedImageMorphismAssociation], 2], 
          Last[Last[First[#1]]] === First[Last[Last[#1]]] & ]; 
        (If[ !MemberQ[(StringDelete[ToString[First[#1]], {"(", ")", " "}] -> Last[#1] & ) /@ 
              Normal[reducedImageMorphismAssociation], StringDelete[ToString[compositionSymbol[First[Last[#1]], 
                 First[First[#1]]]], {"(", ")", " "}] -> DirectedEdge[First[Last[First[#1]]], Last[Last[Last[#1]]]]], 
           reducedImageMorphismAssociation = Association[Append[Normal[reducedImageMorphismAssociation], 
              compositionSymbol[First[Last[#1]], First[First[#1]]] -> DirectedEdge[First[Last[First[#1]]], 
                Last[Last[Last[#1]]]]]]] & ) /@ imageCompositions, 
       Length[reduceObjects[imageObjects, imageQuiverObjectEquivalences]]]; reducedImageMorphismAssociation = 
       Association[Select[Normal[reducedImageMorphismAssociation], 
         Length[Flatten[{First[#1] /. compositionSymbol -> List}]] == Length[DeleteDuplicates[
             Flatten[{First[#1] /. compositionSymbol -> List}]]] & ]]; 
      (If[ !MemberQ[Normal[reducedImageMorphismAssociation], identitySymbol[#1] -> DirectedEdge[#1, #1]], 
         reducedImageMorphismAssociation = Association[Append[Normal[reducedImageMorphismAssociation], 
            identitySymbol[#1] -> DirectedEdge[#1, #1]]]] & ) /@ reduceObjects[imageObjects, 
        imageQuiverObjectEquivalences]; reducedImageMorphismAssociation = 
       Association[DeleteDuplicates[Normal[reducedImageMorphismAssociation] //. 
          {compositionSymbol[tensorProductSymbol[x_, y_], tensorProductSymbol[z_, w_]] :> tensorProductSymbol[
             compositionSymbol[x, z], compositionSymbol[y, w]], compositionSymbol[x_, identitySymbol[y_]] :> x, 
           compositionSymbol[identitySymbol[x_], y_] :> y, compositionSymbol[x_, compositionSymbol[y_, z_]] :> 
            compositionSymbol[compositionSymbol[x, y], z]}]]; reducedObjectCount = 
       Length[reduceObjects[reduceObjects[Catenate[Outer[tensorProductSymbol, objects, objects]], 
           quiverObjectEquivalences], categoryObjectEquivalences]] -> 
        Length[reduceObjects[reduceObjects[reduceObjects[reduceObjects[imageObjects, imageQuiverObjectEquivalences], 
            imageObjectEquivalences], monoidalEquations], objectEquivalences]]; 
      reducedMorphismCount = Length[Normal[reduceArrowsFinal[reduceArrowsInitial[reducedDomainMorphismAssociation, 
            categoryMorphismEquivalences], categoryObjectEquivalences]]] -> 
        Length[Normal[reduceArrowsFinal[reduceArrowsFinal[reduceArrowsFinal[reduceArrowsInitial[
              reduceArrowsInitial[reducedImageMorphismAssociation, imageMorphismEquivalences], morphismEquivalences], 
             imageObjectEquivalences], monoidalEquations], objectEquivalences]]]; 
      BoxForm`ArrangeSummaryBox["AbstractStrictMonoidalCategory", abstractStrictMonoidalCategory, icon, 
       {{BoxForm`SummaryItem[{"Tensor Product: ", tensorProductSymbol}], BoxForm`SummaryItem[
          {"Unit Object: ", unitObject}]}, {BoxForm`SummaryItem[{"Objects: ", objectCount}], 
         BoxForm`SummaryItem[{"Morphisms: ", morphismCount}]}}, 
       {{BoxForm`SummaryItem[{"Reduced Objects: ", reducedObjectCount}], BoxForm`SummaryItem[
          {"Reduced Morphisms: ", reducedMorphismCount}]}}, format, "Interpretable" -> Automatic]] /; 
    SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractStrictMonoidalCategory[(abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
     "ObjectEquivalences" -> categoryObjectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]]] := AbstractStrictMonoidalCategory[Association["ArrowMappings" -> Association[], 
     "Category" -> ResourceFunction["AbstractCategory"][Association["CompositionSymbol" -> compositionSymbol, 
        "IdentitySymbol" -> identitySymbol, "MorphismEquivalences" -> categoryMorphismEquivalences, 
        "ObjectEquivalences" -> categoryObjectEquivalences, "Quiver" -> ResourceFunction["AbstractQuiver"][
          Association["ArrowEquivalences" -> arrowEquivalences, "Arrows" -> arrows, "ObjectEquivalences" -> 
            quiverObjectEquivalences, "Objects" -> objects]]]], "MorphismEquivalences" -> {}, "ObjectEquivalences" -> {}, 
     "ObjectMappings" -> Association[], "TensorProductSymbol" -> CircleTimes, "UnitObject" -> First[objects]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory" && 
    Length[objects] > 0
AbstractStrictMonoidalCategory[(abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
     "ObjectEquivalences" -> categoryObjectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]], objectMappings_Association] := 
  AbstractStrictMonoidalCategory[Association["ArrowMappings" -> Association[], 
     "Category" -> ResourceFunction["AbstractCategory"][Association["CompositionSymbol" -> compositionSymbol, 
        "IdentitySymbol" -> identitySymbol, "MorphismEquivalences" -> categoryMorphismEquivalences, 
        "ObjectEquivalences" -> categoryObjectEquivalences, "Quiver" -> ResourceFunction["AbstractQuiver"][
          Association["ArrowEquivalences" -> arrowEquivalences, "Arrows" -> arrows, "ObjectEquivalences" -> 
            quiverObjectEquivalences, "Objects" -> objects]]]], "MorphismEquivalences" -> {}, "ObjectEquivalences" -> {}, 
     "ObjectMappings" -> objectMappings, "TensorProductSymbol" -> CircleTimes, "UnitObject" -> First[objects]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory" && 
    Length[objects] > 0
AbstractStrictMonoidalCategory[(abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
     "ObjectEquivalences" -> categoryObjectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]], objectMappings_Association, arrowMappings_Association] := 
  AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings, 
     "Category" -> ResourceFunction["AbstractCategory"][Association["CompositionSymbol" -> compositionSymbol, 
        "IdentitySymbol" -> identitySymbol, "MorphismEquivalences" -> categoryMorphismEquivalences, 
        "ObjectEquivalences" -> categoryObjectEquivalences, "Quiver" -> ResourceFunction["AbstractQuiver"][
          Association["ArrowEquivalences" -> arrowEquivalences, "Arrows" -> arrows, "ObjectEquivalences" -> 
            quiverObjectEquivalences, "Objects" -> objects]]]], "MorphismEquivalences" -> {}, "ObjectEquivalences" -> {}, 
     "ObjectMappings" -> objectMappings, "TensorProductSymbol" -> CircleTimes, "UnitObject" -> First[objects]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory" && 
    Length[objects] > 0
AbstractStrictMonoidalCategory[(abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
     "ObjectEquivalences" -> categoryObjectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]], objectMappings_Association, arrowMappings_Association, objectEquivalences_List] := 
  AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings, 
     "Category" -> ResourceFunction["AbstractCategory"][Association["CompositionSymbol" -> compositionSymbol, 
        "IdentitySymbol" -> identitySymbol, "MorphismEquivalences" -> categoryMorphismEquivalences, 
        "ObjectEquivalences" -> categoryObjectEquivalences, "Quiver" -> ResourceFunction["AbstractQuiver"][
          Association["ArrowEquivalences" -> arrowEquivalences, "Arrows" -> arrows, "ObjectEquivalences" -> 
            quiverObjectEquivalences, "Objects" -> objects]]]], "MorphismEquivalences" -> {}, 
     "ObjectEquivalences" -> objectEquivalences, "ObjectMappings" -> objectMappings, 
     "TensorProductSymbol" -> CircleTimes, "UnitObject" -> First[objects]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory" && 
    Length[objects] > 0
AbstractStrictMonoidalCategory[(abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
     "ObjectEquivalences" -> categoryObjectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]], objectMappings_Association, arrowMappings_Association, objectEquivalences_List, 
   morphismEquivalences_List] := AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings, 
     "Category" -> ResourceFunction["AbstractCategory"][Association["CompositionSymbol" -> compositionSymbol, 
        "IdentitySymbol" -> identitySymbol, "MorphismEquivalences" -> categoryMorphismEquivalences, 
        "ObjectEquivalences" -> categoryObjectEquivalences, "Quiver" -> ResourceFunction["AbstractQuiver"][
          Association["ArrowEquivalences" -> arrowEquivalences, "Arrows" -> arrows, "ObjectEquivalences" -> 
            quiverObjectEquivalences, "Objects" -> objects]]]], "MorphismEquivalences" -> morphismEquivalences, 
     "ObjectEquivalences" -> objectEquivalences, "ObjectMappings" -> objectMappings, 
     "TensorProductSymbol" -> CircleTimes, "UnitObject" -> First[objects]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory" && 
    Length[objects] > 0
AbstractStrictMonoidalCategory[(abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
     "ObjectEquivalences" -> categoryObjectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]], objectMappings_Association, arrowMappings_Association, tensorProductSymbol_] := 
  AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings, 
     "Category" -> ResourceFunction["AbstractCategory"][Association["CompositionSymbol" -> compositionSymbol, 
        "IdentitySymbol" -> identitySymbol, "MorphismEquivalences" -> categoryMorphismEquivalences, 
        "ObjectEquivalences" -> categoryObjectEquivalences, "Quiver" -> ResourceFunction["AbstractQuiver"][
          Association["ArrowEquivalences" -> arrowEquivalences, "Arrows" -> arrows, "ObjectEquivalences" -> 
            quiverObjectEquivalences, "Objects" -> objects]]]], "MorphismEquivalences" -> {}, "ObjectEquivalences" -> {}, 
     "ObjectMappings" -> objectMappings, "TensorProductSymbol" -> tensorProductSymbol, 
     "UnitObject" -> First[objects]]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
    SymbolName[abstractCategory] === "AbstractCategory" && Length[objects] > 0 &&  !ListQ[tensorProductSymbol]
AbstractStrictMonoidalCategory[(abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
     "ObjectEquivalences" -> categoryObjectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]], objectMappings_Association, arrowMappings_Association, tensorProductSymbol_, 
   objectEquivalences_List] := AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings, 
     "Category" -> ResourceFunction["AbstractCategory"][Association["CompositionSymbol" -> compositionSymbol, 
        "IdentitySymbol" -> identitySymbol, "MorphismEquivalences" -> categoryMorphismEquivalences, 
        "ObjectEquivalences" -> categoryObjectEquivalences, "Quiver" -> ResourceFunction["AbstractQuiver"][
          Association["ArrowEquivalences" -> arrowEquivalences, "Arrows" -> arrows, "ObjectEquivalences" -> 
            quiverObjectEquivalences, "Objects" -> objects]]]], "MorphismEquivalences" -> {}, 
     "ObjectEquivalences" -> objectEquivalences, "ObjectMappings" -> objectMappings, 
     "TensorProductSymbol" -> tensorProductSymbol, "UnitObject" -> First[objects]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory" && 
    Length[objects] > 0 &&  !ListQ[tensorProductSymbol]
AbstractStrictMonoidalCategory[(abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
     "ObjectEquivalences" -> categoryObjectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]], objectMappings_Association, arrowMappings_Association, tensorProductSymbol_, 
   objectEquivalences_List, morphismEquivalences_List] := 
  AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings, 
     "Category" -> ResourceFunction["AbstractCategory"][Association["CompositionSymbol" -> compositionSymbol, 
        "IdentitySymbol" -> identitySymbol, "MorphismEquivalences" -> categoryMorphismEquivalences, 
        "ObjectEquivalences" -> categoryObjectEquivalences, "Quiver" -> ResourceFunction["AbstractQuiver"][
          Association["ArrowEquivalences" -> arrowEquivalences, "Arrows" -> arrows, "ObjectEquivalences" -> 
            quiverObjectEquivalences, "Objects" -> objects]]]], "MorphismEquivalences" -> morphismEquivalences, 
     "ObjectEquivalences" -> objectEquivalences, "ObjectMappings" -> objectMappings, 
     "TensorProductSymbol" -> tensorProductSymbol, "UnitObject" -> First[objects]]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory" && 
    Length[objects] > 0 &&  !ListQ[tensorProductSymbol]
AbstractStrictMonoidalCategory[(abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
     "ObjectEquivalences" -> categoryObjectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]], objectMappings_Association, arrowMappings_Association, tensorProductSymbol_, 
   unitObject_] := AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings, 
     "Category" -> ResourceFunction["AbstractCategory"][Association["CompositionSymbol" -> compositionSymbol, 
        "IdentitySymbol" -> identitySymbol, "MorphismEquivalences" -> categoryMorphismEquivalences, 
        "ObjectEquivalences" -> categoryObjectEquivalences, "Quiver" -> ResourceFunction["AbstractQuiver"][
          Association["ArrowEquivalences" -> arrowEquivalences, "Arrows" -> arrows, "ObjectEquivalences" -> 
            quiverObjectEquivalences, "Objects" -> objects]]]], "MorphismEquivalences" -> {}, "ObjectEquivalences" -> {}, 
     "ObjectMappings" -> objectMappings, "TensorProductSymbol" -> tensorProductSymbol, "UnitObject" -> unitObject]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory" && 
    Length[objects] > 0 &&  !ListQ[tensorProductSymbol] &&  !ListQ[unitObject]
AbstractStrictMonoidalCategory[(abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
     "ObjectEquivalences" -> categoryObjectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]], objectMappings_Association, arrowMappings_Association, tensorProductSymbol_, 
   unitObject_, objectEquivalences_List] := 
  AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings, 
     "Category" -> ResourceFunction["AbstractCategory"][Association["CompositionSymbol" -> compositionSymbol, 
        "IdentitySymbol" -> identitySymbol, "MorphismEquivalences" -> categoryMorphismEquivalences, 
        "ObjectEquivalences" -> categoryObjectEquivalences, "Quiver" -> ResourceFunction["AbstractQuiver"][
          Association["ArrowEquivalences" -> arrowEquivalences, "Arrows" -> arrows, "ObjectEquivalences" -> 
            quiverObjectEquivalences, "Objects" -> objects]]]], "MorphismEquivalences" -> {}, 
     "ObjectEquivalences" -> objectEquivalences, "ObjectMappings" -> objectMappings, 
     "TensorProductSymbol" -> tensorProductSymbol, "UnitObject" -> unitObject]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory" && 
    Length[objects] > 0 &&  !ListQ[tensorProductSymbol] &&  !ListQ[unitObject]
AbstractStrictMonoidalCategory[(abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
     "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
     "ObjectEquivalences" -> categoryObjectEquivalences_List, 
     "Quiver" -> (abstractQuiver_)[Association["ArrowEquivalences" -> arrowEquivalences_List, 
        "Arrows" -> arrows_Association, "ObjectEquivalences" -> quiverObjectEquivalences_List, 
        "Objects" -> objects_List]]]], objectMappings_Association, arrowMappings_Association, tensorProductSymbol_, 
   unitObject_, objectEquivalences_List, morphismEquivalences_List] := 
  AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings, 
     "Category" -> ResourceFunction["AbstractCategory"][Association["CompositionSymbol" -> compositionSymbol, 
        "IdentitySymbol" -> identitySymbol, "MorphismEquivalences" -> categoryMorphismEquivalences, 
        "ObjectEquivalences" -> categoryObjectEquivalences, "Quiver" -> ResourceFunction["AbstractQuiver"][
          Association["ArrowEquivalences" -> arrowEquivalences, "Arrows" -> arrows, "ObjectEquivalences" -> 
            quiverObjectEquivalences, "Objects" -> objects]]]], "MorphismEquivalences" -> morphismEquivalences, 
     "ObjectEquivalences" -> objectEquivalences, "ObjectMappings" -> objectMappings, 
     "TensorProductSymbol" -> tensorProductSymbol, "UnitObject" -> unitObject]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory" && 
    Length[objects] > 0 &&  !ListQ[tensorProductSymbol] &&  !ListQ[unitObject]
AbstractStrictMonoidalCategory[strictMonoidalCategory_Association] := 
  AbstractStrictMonoidalCategory[KeySort[strictMonoidalCategory]] /; KeyExistsQ[strictMonoidalCategory, "Category"] && 
    KeyExistsQ[strictMonoidalCategory, "ObjectMappings"] && KeyExistsQ[strictMonoidalCategory, "ArrowMappings"] && 
    KeyExistsQ[strictMonoidalCategory, "TensorProductSymbol"] && KeyExistsQ[strictMonoidalCategory, "UnitObject"] && 
    KeyExistsQ[strictMonoidalCategory, "ObjectEquivalences"] && KeyExistsQ[strictMonoidalCategory, 
     "MorphismEquivalences"] && Keys[KeySort[strictMonoidalCategory]] =!= Keys[strictMonoidalCategory]
AbstractStrictMonoidalCategory[AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "ObjectMappings" -> objectMappings_Association, "TensorProductSymbol" -> tensorProductSymbol_, 
     "UnitObject" -> unitObject_]], newObjectEquivalences_List] := 
  AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings, 
     "Category" -> ResourceFunction["AbstractCategory"][Association["CompositionSymbol" -> compositionSymbol, 
        "IdentitySymbol" -> identitySymbol, "MorphismEquivalences" -> categoryMorphismEquivalences, 
        "ObjectEquivalences" -> categoryObjectEquivalences, "Quiver" -> ResourceFunction["AbstractQuiver"][
          Association["ArrowEquivalences" -> arrowEquivalences, "Arrows" -> arrows, "ObjectEquivalences" -> 
            quiverObjectEquivalences, "Objects" -> objects]]]], "MorphismEquivalences" -> morphismEquivalences, 
     "ObjectEquivalences" -> newObjectEquivalences, "ObjectMappings" -> objectMappings, 
     "TensorProductSymbol" -> tensorProductSymbol, "UnitObject" -> unitObject]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractStrictMonoidalCategory[AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "ObjectMappings" -> objectMappings_Association, "TensorProductSymbol" -> tensorProductSymbol_, 
     "UnitObject" -> unitObject_]], newObjectEquivalences_List, newMorphismEquivalences_List] := 
  AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings, 
     "Category" -> ResourceFunction["AbstractCategory"][Association["CompositionSymbol" -> compositionSymbol, 
        "IdentitySymbol" -> identitySymbol, "MorphismEquivalences" -> categoryMorphismEquivalences, 
        "ObjectEquivalences" -> categoryObjectEquivalences, "Quiver" -> ResourceFunction["AbstractQuiver"][
          Association["ArrowEquivalences" -> arrowEquivalences, "Arrows" -> arrows, "ObjectEquivalences" -> 
            quiverObjectEquivalences, "Objects" -> objects]]]], "MorphismEquivalences" -> newMorphismEquivalences, 
     "ObjectEquivalences" -> newObjectEquivalences, "ObjectMappings" -> objectMappings, 
     "TensorProductSymbol" -> tensorProductSymbol, "UnitObject" -> unitObject]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory"
AbstractStrictMonoidalCategory[AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "ObjectMappings" -> objectMappings_Association, "TensorProductSymbol" -> tensorProductSymbol_, 
     "UnitObject" -> unitObject_]], newTensorProductSymbol_] := 
  AbstractStrictMonoidalCategory[Association["ArrowMappings" -> Association[Normal[arrowMappings] /. 
        tensorProductSymbol -> newTensorProductSymbol], "Category" -> ResourceFunction["AbstractCategory"][
       Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
        "MorphismEquivalences" -> categoryMorphismEquivalences, "ObjectEquivalences" -> categoryObjectEquivalences, 
        "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> arrowEquivalences, 
           "Arrows" -> arrows, "ObjectEquivalences" -> quiverObjectEquivalences, "Objects" -> objects]]]], 
     "MorphismEquivalences" -> morphismEquivalences, "ObjectEquivalences" -> objectEquivalences, 
     "ObjectMappings" -> Association[Normal[objectMappings] /. tensorProductSymbol -> newTensorProductSymbol], 
     "TensorProductSymbol" -> newTensorProductSymbol, "UnitObject" -> unitObject]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory" && 
     !ListQ[newTensorProductSymbol]
AbstractStrictMonoidalCategory[AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "ObjectMappings" -> objectMappings_Association, "TensorProductSymbol" -> tensorProductSymbol_, 
     "UnitObject" -> unitObject_]], newTensorProductSymbol_, newObjectEquivalences_List] := 
  AbstractStrictMonoidalCategory[Association["ArrowMappings" -> Association[Normal[arrowMappings] /. 
        tensorProductSymbol -> newTensorProductSymbol], "Category" -> ResourceFunction["AbstractCategory"][
       Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
        "MorphismEquivalences" -> categoryMorphismEquivalences, "ObjectEquivalences" -> categoryObjectEquivalences, 
        "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> arrowEquivalences, 
           "Arrows" -> arrows, "ObjectEquivalences" -> quiverObjectEquivalences, "Objects" -> objects]]]], 
     "MorphismEquivalences" -> morphismEquivalences, "ObjectEquivalences" -> newObjectEquivalences, 
     "ObjectMappings" -> Association[Normal[objectMappings] /. tensorProductSymbol -> newTensorProductSymbol], 
     "TensorProductSymbol" -> newTensorProductSymbol, "UnitObject" -> unitObject]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory" && 
     !ListQ[newTensorProductSymbol]
AbstractStrictMonoidalCategory[AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "ObjectMappings" -> objectMappings_Association, "TensorProductSymbol" -> tensorProductSymbol_, 
     "UnitObject" -> unitObject_]], newTensorProductSymbol_, newObjectEquivalences_List, newMorphismEquivalences_List] := 
  AbstractStrictMonoidalCategory[Association["ArrowMappings" -> Association[Normal[arrowMappings] /. 
        tensorProductSymbol -> newTensorProductSymbol], "Category" -> ResourceFunction["AbstractCategory"][
       Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
        "MorphismEquivalences" -> categoryMorphismEquivalences, "ObjectEquivalences" -> categoryObjectEquivalences, 
        "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> arrowEquivalences, 
           "Arrows" -> arrows, "ObjectEquivalences" -> quiverObjectEquivalences, "Objects" -> objects]]]], 
     "MorphismEquivalences" -> newMorphismEquivalences, "ObjectEquivalences" -> newObjectEquivalences, 
     "ObjectMappings" -> Association[Normal[objectMappings] /. tensorProductSymbol -> newTensorProductSymbol], 
     "TensorProductSymbol" -> newTensorProductSymbol, "UnitObject" -> unitObject]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory" && 
     !ListQ[newTensorProductSymbol]
AbstractStrictMonoidalCategory[AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "ObjectMappings" -> objectMappings_Association, "TensorProductSymbol" -> tensorProductSymbol_, 
     "UnitObject" -> unitObject_]], newTensorProductSymbol_, newUnitObject_] := 
  AbstractStrictMonoidalCategory[Association["ArrowMappings" -> Association[Normal[arrowMappings] /. 
        tensorProductSymbol -> newTensorProductSymbol], "Category" -> ResourceFunction["AbstractCategory"][
       Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
        "MorphismEquivalences" -> categoryMorphismEquivalences, "ObjectEquivalences" -> categoryObjectEquivalences, 
        "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> arrowEquivalences, 
           "Arrows" -> arrows, "ObjectEquivalences" -> quiverObjectEquivalences, "Objects" -> objects]]]], 
     "MorphismEquivalences" -> morphismEquivalences, "ObjectEquivalences" -> objectEquivalences, 
     "ObjectMappings" -> Association[Normal[objectMappings] /. tensorProductSymbol -> newTensorProductSymbol], 
     "TensorProductSymbol" -> newTensorProductSymbol, "UnitObject" -> newUnitObject]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory" && 
     !ListQ[newTensorProductSymbol] &&  !ListQ[newUnitObject]
AbstractStrictMonoidalCategory[AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "ObjectMappings" -> objectMappings_Association, "TensorProductSymbol" -> tensorProductSymbol_, 
     "UnitObject" -> unitObject_]], newTensorProductSymbol_, newUnitObject_, newObjectEquivalences_List] := 
  AbstractStrictMonoidalCategory[Association["ArrowMappings" -> Association[Normal[arrowMappings] /. 
        tensorProductSymbol -> newTensorProductSymbol], "Category" -> ResourceFunction["AbstractCategory"][
       Association["CompositionSymbol" -> compositionSymbol, "IdentitySymbol" -> identitySymbol, 
        "MorphismEquivalences" -> categoryMorphismEquivalences, "ObjectEquivalences" -> categoryObjectEquivalences, 
        "Quiver" -> ResourceFunction["AbstractQuiver"][Association["ArrowEquivalences" -> arrowEquivalences, 
           "Arrows" -> arrows, "ObjectEquivalences" -> quiverObjectEquivalences, "Objects" -> objects]]]], 
     "MorphismEquivalences" -> morphismEquivalences, "ObjectEquivalences" -> newObjectEquivalences, 
     "ObjectMappings" -> Association[Normal[objectMappings] /. tensorProductSymbol -> newTensorProductSymbol], 
     "TensorProductSymbol" -> newTensorProductSymbol, "UnitObject" -> newUnitObject]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory" && 
     !ListQ[newTensorProductSymbol] &&  !ListQ[newUnitObject]
AbstractStrictMonoidalCategory[AbstractStrictMonoidalCategory[Association["ArrowMappings" -> arrowMappings_Association, 
     "Category" -> (abstractCategory_)[Association["CompositionSymbol" -> compositionSymbol_, 
        "IdentitySymbol" -> identitySymbol_, "MorphismEquivalences" -> categoryMorphismEquivalences_List, 
        "ObjectEquivalences" -> categoryObjectEquivalences_List, "Quiver" -> (abstractQuiver_)[
          Association["ArrowEquivalences" -> arrowEquivalences_List, "Arrows" -> arrows_Association, 
           "ObjectEquivalences" -> quiverObjectEquivalences_List, "Objects" -> objects_List]]]], 
     "MorphismEquivalences" -> morphismEquivalences_List, "ObjectEquivalences" -> objectEquivalences_List, 
     "ObjectMappings" -> objectMappings_Association, "TensorProductSymbol" -> tensorProductSymbol_, 
     "UnitObject" -> unitObject_]], newTensorProductSymbol_, newUnitObject_, newObjectEquivalences_List, 
   newMorphismEquivalences_List] := AbstractStrictMonoidalCategory[
    Association["ArrowMappings" -> Association[Normal[arrowMappings] /. tensorProductSymbol -> newTensorProductSymbol], 
     "Category" -> ResourceFunction["AbstractCategory"][Association["CompositionSymbol" -> compositionSymbol, 
        "IdentitySymbol" -> identitySymbol, "MorphismEquivalences" -> categoryMorphismEquivalences, 
        "ObjectEquivalences" -> categoryObjectEquivalences, "Quiver" -> ResourceFunction["AbstractQuiver"][
          Association["ArrowEquivalences" -> arrowEquivalences, "Arrows" -> arrows, "ObjectEquivalences" -> 
            quiverObjectEquivalences, "Objects" -> objects]]]], "MorphismEquivalences" -> newMorphismEquivalences, 
     "ObjectEquivalences" -> newObjectEquivalences, "ObjectMappings" -> 
      Association[Normal[objectMappings] /. tensorProductSymbol -> newTensorProductSymbol], 
     "TensorProductSymbol" -> newTensorProductSymbol, "UnitObject" -> newUnitObject]] /; 
   SymbolName[abstractQuiver] === "AbstractQuiver" && SymbolName[abstractCategory] === "AbstractCategory" && 
     !ListQ[newTensorProductSymbol] &&  !ListQ[newUnitObject]

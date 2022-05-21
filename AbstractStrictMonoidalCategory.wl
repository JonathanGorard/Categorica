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
          Normal[reduceArrowsFinal[reduceArrowsFinal[reduceArrowsInitial[reduceArrowsInitial[imageMorphismAssociation, 
               imageMorphismEquivalences], morphismEquivalences], imageObjectEquivalences], monoidalEquations]], Last], 
        Length[#1] > 1 & ]]] /; SymbolName[abstractQuiver] === "AbstractQuiver" && 
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
        Normal[reduceArrowsFinal[reduceArrowsFinal[reduceArrowsInitial[reduceArrowsInitial[imageMorphismAssociation, 
             imageMorphismEquivalences], morphismEquivalences], imageObjectEquivalences], monoidalEquations]], 
       VertexSize -> 0.3, VertexStyle -> Directive[Transparent, EdgeForm[None]], VertexLabels -> Placed["Name", Center], 
       VertexLabelStyle -> Directive[Bold, 20], EdgeLabelStyle -> Directive[Bold, 20], 
       EdgeStyle -> Directive[Black, Thick], GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Left}]] /; 
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

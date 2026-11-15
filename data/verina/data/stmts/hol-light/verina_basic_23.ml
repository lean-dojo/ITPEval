(*
  Statement-only formalization of VERINA corpus artifact verina_basic_23,
  catalog title "differenceMinMax": an executable scan of a nonempty integer
  array returns its maximum minus its minimum, with the exact accumulator-fold
  correctness contract. This file contains no proof.
*)

let differenceMinMax_precond = new_definition
  `differenceMinMax_precond (a:int list) <=>
     ~(a = [])`;;

let differenceMinMax_loop =
  new_recursive_definition list_RECURSION
    `(!minVal:int. !maxVal:int.
        differenceMinMax_loop
          ([]:int list) minVal maxVal =
        maxVal - minVal) /\
     (!x:int. !xs:int list. !minVal:int. !maxVal:int.
        differenceMinMax_loop
          (CONS x xs) minVal maxVal =
        let newMin =
          if x < minVal then x else minVal in
        let newMax =
          if x > maxVal then x else maxVal in
        differenceMinMax_loop xs newMin newMax)`;;

let differenceMinMax = new_definition
  `differenceMinMax (a:int list) =
     if a = [] then
       (&0:int)
     else
       differenceMinMax_loop (TL a) (HD a) (HD a)`;;

let differenceMinMax_foldMin =
  new_recursive_definition list_RECURSION
    `(!acc:int.
        differenceMinMax_foldMin ([]:int list) acc = acc) /\
     (!x:int. !xs:int list. !acc:int.
        differenceMinMax_foldMin (CONS x xs) acc =
        differenceMinMax_foldMin
          xs (if x < acc then x else acc))`;;

let differenceMinMax_foldMax =
  new_recursive_definition list_RECURSION
    `(!acc:int.
        differenceMinMax_foldMax ([]:int list) acc = acc) /\
     (!x:int. !xs:int list. !acc:int.
        differenceMinMax_foldMax (CONS x xs) acc =
        differenceMinMax_foldMax
          xs (if x > acc then x else acc))`;;

let differenceMinMax_postcond = new_definition
  `differenceMinMax_postcond
      (a:int list) (result:int) <=>
     let initial = if a = [] then (&0:int) else HD a in
     result + differenceMinMax_foldMin a initial =
     differenceMinMax_foldMax a initial`;;

let differenceMinMax_spec_satisfied =
  `!a:int list.
     differenceMinMax_precond a
     ==> differenceMinMax_postcond
           a (differenceMinMax a)`;;

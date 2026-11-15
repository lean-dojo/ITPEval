(*
  Statement-only formalization of VERINA corpus artifact verina_basic_20,
  catalog title "uniqueProduct": a deterministic integer-array scan multiplies
  each distinct value on its first occurrence, with its total precondition and
  duplicate-erased fold correctness contract. This file contains no proof.
*)

let uniqueProduct_precond = new_definition
  `uniqueProduct_precond (arr:int list) <=> T`;;

let uniqueProduct_loop =
  new_recursive_definition list_RECURSION
    `(!seen:int list. !acc:int.
        uniqueProduct_loop ([]:int list) seen acc = acc) /\
     (!x:int. !xs:int list. !seen:int list. !acc:int.
        uniqueProduct_loop (CONS x xs) seen acc =
        if MEM x seen then
          uniqueProduct_loop xs seen acc
        else
          uniqueProduct_loop
            xs (CONS x seen) (acc * x))`;;

let uniqueProduct = new_definition
  `uniqueProduct (arr:int list) =
     uniqueProduct_loop arr [] (&1:int)`;;

let uniqueProduct_eraseDupsLoop =
  new_recursive_definition list_RECURSION
    `(!seenReversed:int list.
        uniqueProduct_eraseDupsLoop
          ([]:int list) seenReversed =
        REVERSE seenReversed) /\
     (!x:int. !xs:int list. !seenReversed:int list.
        uniqueProduct_eraseDupsLoop
          (CONS x xs) seenReversed =
        if MEM x seenReversed then
          uniqueProduct_eraseDupsLoop xs seenReversed
        else
          uniqueProduct_eraseDupsLoop
            xs (CONS x seenReversed))`;;

let uniqueProduct_eraseDups = new_definition
  `uniqueProduct_eraseDups (arr:int list) =
     uniqueProduct_eraseDupsLoop arr []`;;

let uniqueProduct_foldlProduct =
  new_recursive_definition list_RECURSION
    `(!acc:int.
        uniqueProduct_foldlProduct ([]:int list) acc = acc) /\
     (!x:int. !xs:int list. !acc:int.
        uniqueProduct_foldlProduct (CONS x xs) acc =
        uniqueProduct_foldlProduct xs (acc * x))`;;

let uniqueProduct_postcond = new_definition
  `uniqueProduct_postcond
      (arr:int list) (result:int) <=>
     let expected =
       uniqueProduct_foldlProduct
         (uniqueProduct_eraseDups arr) (&1:int) in
     result - expected = (&0:int) /\
     expected - result = (&0:int)`;;

let uniqueProduct_spec_satisfied =
  `!arr:int list.
     uniqueProduct_precond arr
     ==> uniqueProduct_postcond arr (uniqueProduct arr)`;;

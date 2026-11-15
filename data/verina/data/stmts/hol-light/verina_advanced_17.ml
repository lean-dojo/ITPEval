(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_17,
  catalog title "insertionSort": executable insertion sort on integer lists,
  with its total precondition and nondecreasing permutation postcondition.
  This file contains no proof.
*)

let insertionSort_precond = new_definition
  `insertionSort_precond (l:int list) <=> T`;;

let insertElement =
  new_recursive_definition list_RECURSION
    `(insertElement (x:int) [] = CONS x []) /\
     (!y:int. !ys:int list. !x:int.
        insertElement x (CONS y ys) =
        if x <= y
        then CONS x (CONS y ys)
        else CONS y (insertElement x ys))`;;

let sortList =
  new_recursive_definition list_RECURSION
    `(sortList ([]:int list) = []) /\
     (!x:int. !xs:int list.
        sortList (CONS x xs) = insertElement x (sortList xs))`;;

let insertionSort = new_definition
  `insertionSort (l:int list) = sortList l`;;

let insertionSort_count = new_definition
  `insertionSort_count (z:int) (xs:int list) =
     LENGTH (FILTER (\x:int. x = z) xs)`;;

let insertionSort_isPerm = new_definition
  `insertionSort_isPerm (xs:int list) (ys:int list) <=>
     !z:int. insertionSort_count z xs = insertionSort_count z ys`;;

let insertionSort_postcond = new_definition
  `insertionSort_postcond (l:int list) (result:int list) <=>
     PAIRWISE (\x y:int. x <= y) result /\
     insertionSort_isPerm l result`;;

let insertionSort_spec_satisfied =
  `!l:int list.
     insertionSort_precond l
     ==> insertionSort_postcond l (insertionSort l)`;;

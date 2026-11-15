(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_16,
  catalog title "insertionSort": executable insertion sort on integer lists,
  with its total precondition and sorted-permutation postcondition. This file
  contains no proof.
*)

let insertionSort_precond = new_definition
  `insertionSort_precond (xs:int list) <=> T`;;

let insertionSort_insert =
  new_recursive_definition list_RECURSION
    `(insertionSort_insert (x:int) [] = CONS x []) /\
     (!y:int. !ys:int list. !x:int.
        insertionSort_insert x (CONS y ys) =
        if x <= y
        then CONS x (CONS y ys)
        else CONS y (insertionSort_insert x ys))`;;

let insertionSort =
  new_recursive_definition list_RECURSION
    `(insertionSort ([]:int list) = []) /\
     (!x:int. !xs:int list.
        insertionSort (CONS x xs) =
        insertionSort_insert x (insertionSort xs))`;;

let insertionSort_count = new_definition
  `insertionSort_count (z:int) (xs:int list) =
     LENGTH (FILTER (\x:int. x = z) xs)`;;

let insertionSort_isPerm = new_definition
  `insertionSort_isPerm (xs:int list) (ys:int list) <=>
     !z:int. insertionSort_count z xs = insertionSort_count z ys`;;

let insertionSort_postcond = new_definition
  `insertionSort_postcond (xs:int list) (result:int list) <=>
     PAIRWISE (\x y:int. x <= y) result /\
     insertionSort_isPerm xs result`;;

let insertionSort_spec_satisfied =
  `!xs:int list.
     insertionSort_precond xs
     ==> insertionSort_postcond xs (insertionSort xs)`;;

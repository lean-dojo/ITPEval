(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_48,
  catalog title "mergeSort": executable insertion sort on integer lists, with
  its total precondition and sorted-permutation postcondition. This file
  contains no proof.
*)

let mergeSort_precond = new_definition
  `mergeSort_precond (list:int list) <=> T`;;

let mergeSort_insert =
  new_recursive_definition list_RECURSION
    `(mergeSort_insert (x:int) ([]:int list) = CONS x []) /\
     (!y:int. !ys:int list. !x:int.
        mergeSort_insert x (CONS y ys) =
        if x <= y
        then CONS x (CONS y ys)
        else CONS y (mergeSort_insert x ys))`;;

let mergeSort_sort =
  new_recursive_definition list_RECURSION
    `(mergeSort_sort ([]:int list) = []) /\
     (!x:int. !xs:int list.
        mergeSort_sort (CONS x xs) =
        mergeSort_insert x (mergeSort_sort xs))`;;

let mergeSort = new_definition
  `mergeSort (list:int list) = mergeSort_sort list`;;

let mergeSort_count = new_definition
  `mergeSort_count (z:int) (xs:int list) =
     LENGTH (FILTER (\x:int. x = z) xs)`;;

let mergeSort_isPerm = new_definition
  `mergeSort_isPerm (xs:int list) (ys:int list) <=>
     !z:int. mergeSort_count z xs = mergeSort_count z ys`;;

let mergeSort_postcond = new_definition
  `mergeSort_postcond (list:int list) (result:int list) <=>
     PAIRWISE (\x y:int. x <= y) result /\
     mergeSort_isPerm list result`;;

let mergeSort_spec_satisfied =
  `!list:int list.
     mergeSort_precond list
     ==> mergeSort_postcond list (mergeSort list)`;;

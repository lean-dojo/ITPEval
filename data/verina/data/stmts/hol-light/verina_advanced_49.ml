(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_49,
  catalog title "mergeSortedLists": an executable left-biased merge combines
  two ascendingly sorted integer lists, with a sorted-permutation correctness
  contract. This file contains no proof.
*)

let mergeSortedLists_precond = new_definition
  `mergeSortedLists_precond
      (arr1:int list) (arr2:int list) <=>
     PAIRWISE (\x y:int. x <= y) arr1 /\
     PAIRWISE (\x y:int. x <= y) arr2`;;

let mergeSortedLists_mergeFuel =
  new_recursive_definition num_RECURSION
    `(!xs:int list. !ys:int list.
        mergeSortedLists_mergeFuel 0 xs ys =
        if xs = [] then ys
        else if ys = [] then xs
        else []) /\
     (!n:num. !xs:int list. !ys:int list.
        mergeSortedLists_mergeFuel (SUC n) xs ys =
        if xs = [] then ys
        else if ys = [] then xs
        else if HD xs <= HD ys then
          CONS (HD xs)
            (mergeSortedLists_mergeFuel n (TL xs) ys)
        else
          CONS (HD ys)
            (mergeSortedLists_mergeFuel n xs (TL ys)))`;;

let mergeSortedLists_merge = new_definition
  `mergeSortedLists_merge
      (xs:int list) (ys:int list) =
     mergeSortedLists_mergeFuel
       (LENGTH xs + LENGTH ys) xs ys`;;

let mergeSortedLists = new_definition
  `mergeSortedLists
     (arr1:int list) (arr2:int list) =
     mergeSortedLists_merge arr1 arr2`;;

let mergeSortedLists_count = new_definition
  `mergeSortedLists_count
      (z:int) (xs:int list) =
     LENGTH (FILTER (\x:int. x = z) xs)`;;

let mergeSortedLists_isPerm = new_definition
  `mergeSortedLists_isPerm
      (xs:int list) (ys:int list) <=>
     !z:int.
       mergeSortedLists_count z xs =
       mergeSortedLists_count z ys`;;

let mergeSortedLists_postcond = new_definition
  `mergeSortedLists_postcond
      (arr1:int list) (arr2:int list)
      (result:int list) <=>
     PAIRWISE (\x y:int. x <= y) result /\
     mergeSortedLists_isPerm
       (APPEND arr1 arr2) result`;;

let mergeSortedLists_spec_satisfied =
  `!arr1:int list. !arr2:int list.
     mergeSortedLists_precond arr1 arr2
     ==> mergeSortedLists_postcond
           arr1 arr2
           (mergeSortedLists arr1 arr2)`;;

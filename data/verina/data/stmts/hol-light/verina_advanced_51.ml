(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_51,
  catalog title "mergeSorted": an executable left-biased merge combines two
  non-decreasing integer lists, with a sorted-permutation correctness
  contract. This file contains no proof.
*)

let mergeSorted_precond = new_definition
  `mergeSorted_precond
      (a:int list) (b:int list) <=>
     PAIRWISE (\x y:int. x <= y) a /\
     PAIRWISE (\x y:int. x <= y) b`;;

let mergeSortedAuxFuel =
  new_recursive_definition num_RECURSION
    `(!xs:int list. !ys:int list.
        mergeSortedAuxFuel 0 xs ys =
        if xs = [] then ys
        else if ys = [] then xs
        else []) /\
     (!n:num. !xs:int list. !ys:int list.
        mergeSortedAuxFuel (SUC n) xs ys =
        if xs = [] then ys
        else if ys = [] then xs
        else if HD xs <= HD ys then
          CONS (HD xs)
            (mergeSortedAuxFuel n (TL xs) ys)
        else
          CONS (HD ys)
            (mergeSortedAuxFuel n xs (TL ys)))`;;

let mergeSortedAux = new_definition
  `mergeSortedAux
      (xs:int list) (ys:int list) =
     mergeSortedAuxFuel
       (LENGTH xs + LENGTH ys) xs ys`;;

let mergeSorted = new_definition
  `mergeSorted
      (a:int list) (b:int list) =
     mergeSortedAux a b`;;

let mergeSorted_count = new_definition
  `mergeSorted_count
      (z:int) (xs:int list) =
     LENGTH (FILTER (\x:int. x = z) xs)`;;

let mergeSorted_isPerm = new_definition
  `mergeSorted_isPerm
      (xs:int list) (ys:int list) <=>
     !z:int.
       mergeSorted_count z xs =
       mergeSorted_count z ys`;;

let mergeSorted_postcond = new_definition
  `mergeSorted_postcond
      (a:int list) (b:int list)
      (result:int list) <=>
     PAIRWISE (\x y:int. x <= y) result /\
     mergeSorted_isPerm result (APPEND a b)`;;

let mergeSorted_spec_satisfied =
  `!a:int list. !b:int list.
     mergeSorted_precond a b
     ==> mergeSorted_postcond
           a b (mergeSorted a b)`;;

(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_73,
  catalog title "smallestMissing": an executable scan of a strictly increasing
  natural-number list returns its least missing natural number, together with
  the corresponding precondition and correctness contract. This file contains
  no proof.
*)

let smallestMissing_precond = new_definition
  `smallestMissing_precond (l:num list) <=>
     PAIRWISE (\x y:num. x < y) l`;;

let smallestMissing_search =
  new_recursive_definition list_RECURSION
    `(!n:num.
        smallestMissing_search ([]:num list) n = n) /\
     (!x:num. !xs:num list. !n:num.
        smallestMissing_search (CONS x xs) n =
        if x = n then
          smallestMissing_search xs (n + 1)
        else if x > n then
          n
        else
          smallestMissing_search xs n)`;;

let smallestMissing = new_definition
  `smallestMissing (l:num list) =
     let sortedList = l in
     let result = smallestMissing_search sortedList 0 in
     result`;;

let smallestMissing_postcond = new_definition
  `smallestMissing_postcond
      (l:num list) (result:num) <=>
     ~(MEM result l) /\
     (!candidate:num.
        candidate < result ==> MEM candidate l)`;;

let smallestMissing_spec_satisfied =
  `!l:num list.
     smallestMissing_precond l
     ==> smallestMissing_postcond
           l (smallestMissing l)`;;

(*
  Statement-only formalization of VERINA corpus artifact verina_basic_22,
  catalog title "dissimilarElements": a deterministic integer-array program
  returns the sorted duplicate-free symmetric difference of two arrays,
  together with its full membership and ordering contract. This file contains
  no proof.
*)

let dissimilarElements_inArray = new_definition
  `dissimilarElements_inArray (a:int list) (x:int) <=> MEM x a`;;

let dissimilarElements_precond = new_definition
  `dissimilarElements_precond
      (a:int list) (b:int list) <=> T`;;

let dissimilarElements_setInsert = new_definition
  `dissimilarElements_setInsert
      (x:int) (set:int list) =
     if dissimilarElements_inArray set x then set
     else CONS x set`;;

let dissimilarElements_foldDissimilar =
  new_recursive_definition list_RECURSION
    `(!other:int list. !set:int list.
        dissimilarElements_foldDissimilar
          ([]:int list) other set =
        set) /\
     (!x:int. !xs:int list. !other:int list. !set:int list.
        dissimilarElements_foldDissimilar
          (CONS x xs) other set =
        dissimilarElements_foldDissimilar
          xs other
          (if dissimilarElements_inArray other x then set
           else dissimilarElements_setInsert x set))`;;

let dissimilarElements_insertSorted =
  new_recursive_definition list_RECURSION
    `(dissimilarElements_insertSorted
        (x:int) ([]:int list) =
      CONS x []) /\
     (!y:int. !ys:int list. !x:int.
        dissimilarElements_insertSorted x (CONS y ys) =
        if x <= y then CONS x (CONS y ys)
        else
          CONS y
            (dissimilarElements_insertSorted x ys))`;;

let dissimilarElements_sort =
  new_recursive_definition list_RECURSION
    `(dissimilarElements_sort ([]:int list) = []) /\
     (!x:int. !xs:int list.
        dissimilarElements_sort (CONS x xs) =
        dissimilarElements_insertSorted
          x (dissimilarElements_sort xs))`;;

let dissimilarElements = new_definition
  `dissimilarElements (a:int list) (b:int list) =
     let fromA =
       dissimilarElements_foldDissimilar a b [] in
     let fromB =
       dissimilarElements_foldDissimilar b a fromA in
     dissimilarElements_sort fromB`;;

let dissimilarElements_allMembershipsDiffer =
  new_recursive_definition list_RECURSION
    `(!a:int list. !b:int list.
        dissimilarElements_allMembershipsDiffer
          ([]:int list) a b <=>
        T) /\
     (!x:int. !xs:int list. !a:int list. !b:int list.
        dissimilarElements_allMembershipsDiffer
          (CONS x xs) a b <=>
        ~(dissimilarElements_inArray a x <=>
          dissimilarElements_inArray b x) /\
        dissimilarElements_allMembershipsDiffer xs a b)`;;

let dissimilarElements_directionalCoverage =
  new_recursive_definition list_RECURSION
    `(!other:int list. !result:int list.
        dissimilarElements_directionalCoverage
          ([]:int list) other result <=>
        T) /\
     (!x:int. !xs:int list. !other:int list. !result:int list.
        dissimilarElements_directionalCoverage
          (CONS x xs) other result <=>
        (if dissimilarElements_inArray other x
         then ~dissimilarElements_inArray result x
         else dissimilarElements_inArray result x) /\
        dissimilarElements_directionalCoverage
          xs other result)`;;

let dissimilarElements_noDuplicates =
  new_recursive_definition list_RECURSION
    `(dissimilarElements_noDuplicates ([]:int list) <=> T) /\
     (!x:int. !xs:int list.
        dissimilarElements_noDuplicates (CONS x xs) <=>
        ~dissimilarElements_inArray xs x /\
        dissimilarElements_noDuplicates xs)`;;

let dissimilarElements_postcond = new_definition
  `dissimilarElements_postcond
      (a:int list) (b:int list) (result:int list) <=>
     dissimilarElements_allMembershipsDiffer result a b /\
     PAIRWISE (\x y:int. x <= y) result /\
     dissimilarElements_noDuplicates result /\
     dissimilarElements_directionalCoverage a b result /\
     dissimilarElements_directionalCoverage b a result`;;

let dissimilarElements_spec_satisfied =
  `!a:int list. !b:int list.
     dissimilarElements_precond a b
     ==> dissimilarElements_postcond
           a b (dissimilarElements a b)`;;

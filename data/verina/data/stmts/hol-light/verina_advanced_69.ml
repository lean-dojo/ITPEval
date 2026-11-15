(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_69,
  catalog title "searchInsert": an executable scan returns the first index
  where a target can occur in a strictly increasing integer list, together
  with its insertion-position correctness contract. This file contains no
  proof.
*)

let searchInsert_precond = new_definition
  `searchInsert_precond (xs:int list) (target:int) <=>
     PAIRWISE (\x y:int. x < y) xs`;;

let searchInsert_helper =
  new_recursive_definition list_RECURSION
    `(!target:int. !idx:num.
        searchInsert_helper target ([]:int list) idx = idx) /\
     (!y:int. !ys:int list. !target:int. !idx:num.
        searchInsert_helper target (CONS y ys) idx =
        if target <= y then idx
        else searchInsert_helper target ys (idx + 1))`;;

let searchInsert = new_definition
  `searchInsert (xs:int list) (target:int) =
     if xs = [] then 0
     else searchInsert_helper target xs 0`;;

let searchInsert_range =
  new_recursive_definition num_RECURSION
    `(searchInsert_range 0 = []) /\
     (!n:num.
        searchInsert_range (SUC n) =
        APPEND (searchInsert_range n) (CONS n []))`;;

let searchInsert_postcond = new_definition
  `searchInsert_postcond
      (xs:int list) (target:int) (result:num) <=>
     result <= LENGTH xs /\
     ALL
       (\i:num. EL i xs < target)
       (searchInsert_range result) /\
     (result < LENGTH xs ==> target <= EL result xs)`;;

let searchInsert_spec_satisfied =
  `!xs:int list. !target:int.
     searchInsert_precond xs target
     ==> searchInsert_postcond
           xs target (searchInsert xs target)`;;

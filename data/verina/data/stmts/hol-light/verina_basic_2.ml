(*
  Statement-only formalization of VERINA corpus artifact verina_basic_2,
  catalog title "findSmallest": an executable scan returns the least natural
  number in a finite array, or no value exactly when the array is empty,
  together with its total correctness contract. This file contains no proof.
*)

let findSmallest_precond = new_definition
  `findSmallest_precond (s:num list) <=> T`;;

let findSmallest_min =
  new_recursive_definition list_RECURSION
    `(!current:num. findSmallest_min current [] = current) /\
     (!x:num. !xs:num list. !current:num.
        findSmallest_min current (CONS x xs) =
        findSmallest_min (MIN current x) xs)`;;

let findSmallest = new_definition
  `findSmallest (s:num list) =
     if s = [] then (NONE:num option)
     else SOME (findSmallest_min (HD s) (TL s))`;;

let findSmallest_postcond = new_definition
  `findSmallest_postcond
      (s:num list) (result:num option) <=>
     (result = NONE /\ s = []) \/
     (?r:num.
        result = SOME r /\
        MEM r s /\
        (!x:num. MEM x s ==> r <= x))`;;

let findSmallest_spec_satisfied =
  `!s:num list.
     findSmallest_precond s
     ==> findSmallest_postcond s (findSmallest s)`;;

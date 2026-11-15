(*
  Statement-only formalization of VERINA corpus artifact verina_basic_19,
  catalog title "isSorted": an executable Boolean check determines whether an
  integer array is nondecreasing, with its total precondition and exact
  adjacent-pair correctness contract. This file contains no proof.
*)

let isSorted_precond = new_definition
  `isSorted_precond (a:int list) <=> T`;;

let isSorted =
  new_recursive_definition list_RECURSION
    `(isSorted ([]:int list) = T) /\
     (!x:int. !xs:int list.
        isSorted (CONS x xs) =
        if xs = [] then T
        else x <= HD xs /\ isSorted xs)`;;

let isSorted_postcond = new_definition
  `isSorted_postcond (a:int list) (result:bool) <=>
     ((!i:num.
         i < LENGTH a - 1
         ==> EL i a <= EL (i + 1) a) <=>
      result)`;;

let isSorted_spec_satisfied =
  `!a:int list.
     isSorted_precond a
     ==> isSorted_postcond a (isSorted a)`;;

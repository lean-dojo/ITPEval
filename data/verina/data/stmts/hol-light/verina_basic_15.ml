(*
  Statement-only formalization of VERINA corpus artifact verina_basic_15,
  catalog title "containsConsecutiveNumbers": an executable adjacent-pair scan
  returns true exactly when an integer is immediately followed by its
  successor, together with its total precondition and Boolean correctness
  contract. This file contains no proof.
*)

let containsConsecutiveNumbers_precond = new_definition
  `containsConsecutiveNumbers_precond (a:int list) <=> T`;;

let containsConsecutiveNumbers =
  new_recursive_definition list_RECURSION
    `(containsConsecutiveNumbers ([]:int list) = F) /\
     (!x:int. !xs:int list.
        containsConsecutiveNumbers (CONS x xs) =
        if xs = [] then F
        else x + &1 = HD xs \/ containsConsecutiveNumbers xs)`;;

let containsConsecutiveNumbers_postcond = new_definition
  `containsConsecutiveNumbers_postcond
      (a:int list) (result:bool) <=>
     ((?i:num.
         i < LENGTH a - 1 /\
         EL i a + &1 = EL (i + 1) a) <=> result)`;;

let containsConsecutiveNumbers_spec_satisfied =
  `!a:int list.
     containsConsecutiveNumbers_precond a
     ==> containsConsecutiveNumbers_postcond
           a (containsConsecutiveNumbers a)`;;

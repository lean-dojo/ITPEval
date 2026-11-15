(*
  Statement-only formalization of VERINA corpus artifact verina_basic_69
  (verina__hol-light__verina_basic_69), catalog title "LinearSearch": an
  executable left-to-right scan of an integer array known to contain a target
  returns its first occurrence index, together with the exact precondition and
  first-occurrence correctness contract. This file contains no proof.
*)

let LinearSearch_precond = new_definition
  `LinearSearch_precond (a:int list) (e:int) <=>
     ?i:num. i < LENGTH a /\ EL i a = e`;;

let linearSearchAuxFuel =
  new_recursive_definition num_RECURSION
    `(!a:int list. !e:int. !n:num.
        linearSearchAuxFuel 0 a e n = 0) /\
     (!fuel:num. !a:int list. !e:int. !n:num.
        linearSearchAuxFuel (SUC fuel) a e n =
        if n < LENGTH a then
          if EL n a = e then n
          else linearSearchAuxFuel fuel a e (n + 1)
        else
          0)`;;

let linearSearchAux = new_definition
  `linearSearchAux (a:int list) (e:int) (n:num) =
     linearSearchAuxFuel (SUC (LENGTH a - n)) a e n`;;

let LinearSearch = new_definition
  `LinearSearch (a:int list) (e:int) =
     linearSearchAux a e 0`;;

let LinearSearch_postcond = new_definition
  `LinearSearch_postcond
      (a:int list) (e:int) (result:num) <=>
     result < LENGTH a /\
     EL result a = e /\
     (!k:num. k < result ==> ~(EL k a = e))`;;

let LinearSearch_spec_satisfied =
  `!a:int list. !e:int.
     LinearSearch_precond a e
     ==> LinearSearch_postcond a e (LinearSearch a e)`;;

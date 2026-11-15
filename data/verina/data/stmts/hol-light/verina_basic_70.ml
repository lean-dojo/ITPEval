(*
  Statement-only formalization of VERINA corpus artifact verina_basic_70
  (verina__hol-light__verina_basic_70), catalog title "LinearSearch3": an
  executable left-to-right scan of an integer array known to contain an
  element satisfying an arbitrary Boolean predicate returns the first such
  index, together with its exact precondition and correctness contract. This
  file contains no proof.
*)

let LinearSearch3_precond = new_definition
  `LinearSearch3_precond (a:int list) (P:int->bool) <=>
     ?i:num. i < LENGTH a /\ P (EL i a)`;;

let LinearSearch3_loopFuel =
  new_recursive_definition num_RECURSION
    `(!a:int list. !P:int->bool. !n:num.
        LinearSearch3_loopFuel 0 a P n = 0) /\
     (!fuel:num. !a:int list. !P:int->bool. !n:num.
        LinearSearch3_loopFuel (SUC fuel) a P n =
        if n < LENGTH a then
          if P (EL n a) then n
          else LinearSearch3_loopFuel fuel a P (n + 1)
        else
          0)`;;

let LinearSearch3_loop = new_definition
  `LinearSearch3_loop
      (a:int list) (P:int->bool) (n:num) =
     LinearSearch3_loopFuel (SUC (LENGTH a - n)) a P n`;;

let LinearSearch3 = new_definition
  `LinearSearch3 (a:int list) (P:int->bool) =
     LinearSearch3_loop a P 0`;;

let LinearSearch3_postcond = new_definition
  `LinearSearch3_postcond
      (a:int list) (P:int->bool) (result:num) <=>
     result < LENGTH a /\
     P (EL result a) /\
     (!k:num. k < result ==> ~(P (EL k a)))`;;

let LinearSearch3_spec_satisfied =
  `!a:int list. !P:int->bool.
     LinearSearch3_precond a P
     ==> LinearSearch3_postcond
           a P (LinearSearch3 a P)`;;

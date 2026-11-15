(*
  Statement-only formalization of VERINA corpus artifact verina_basic_47
  (verina__hol-light__verina_basic_47), catalog title "arraySum": an
  executable recursive sum of a nonempty integer array, together with the
  defaulted-index recursive sum helper and the complete result correctness
  contract. This file contains no proof.
*)

let arraySum_precond = new_definition
  `arraySum_precond (a:int list) <=>
     LENGTH a > 0`;;

let arraySum =
  new_recursive_definition list_RECURSION
    `(arraySum ([]:int list) = (&0:int)) /\
     (!x:int. !xs:int list.
        arraySum (CONS x xs) =
        x + arraySum xs)`;;

let arraySum_sumTo =
  new_recursive_definition num_RECURSION
    `(!a:int list.
        arraySum_sumTo a 0 = (&0:int)) /\
     (!a:int list. !n:num.
        arraySum_sumTo a (SUC n) =
        arraySum_sumTo a n +
          (if n < LENGTH a then EL n a else (&0:int)))`;;

let arraySum_postcond = new_definition
  `arraySum_postcond (a:int list) (result:int) <=>
     result - arraySum_sumTo a (LENGTH a) = (&0:int) /\
     result >= arraySum_sumTo a (LENGTH a)`;;

let arraySum_spec_satisfied =
  `!a:int list.
     arraySum_precond a
     ==> arraySum_postcond a (arraySum a)`;;

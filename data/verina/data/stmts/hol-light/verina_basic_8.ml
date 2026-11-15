(*
  Statement-only formalization of VERINA corpus artifact verina_basic_8
  (verina__hol-light__verina_basic_8), catalog title "myMin": an executable
  integer comparison returns the minimum of two inputs, together with its
  total precondition and lower-bound-and-input-membership correctness
  contract. This file contains no proof.
*)

let myMin_precond = new_definition
  `myMin_precond (a:int) (b:int) <=> T`;;

let myMin = new_definition
  `myMin (a:int) (b:int) =
     if a <= b then a else b`;;

let myMin_postcond = new_definition
  `myMin_postcond (a:int) (b:int) (result:int) <=>
     (result <= a /\ result <= b) /\
     (result = a \/ result = b)`;;

let myMin_spec_satisfied =
  `!a:int. !b:int.
     myMin_precond a b
     ==> myMin_postcond a b (myMin a b)`;;

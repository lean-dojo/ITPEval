(*
  Statement-only formalization of VERINA corpus artifact verina_basic_76
  (verina__hol-light__verina_basic_76), catalog title "myMin": an executable
  integer conditional returns the smaller of two integers, together with its
  total precondition and branchwise correctness contract. This file contains
  no proof.
*)

let myMin_precond = new_definition
  `myMin_precond (x:int) (y:int) <=> T`;;

let myMin = new_definition
  `myMin (x:int) (y:int) =
     if x < y then x else y`;;

let myMin_postcond = new_definition
  `myMin_postcond (x:int) (y:int) (result:int) <=>
     (x <= y ==> result = x) /\
     (x > y ==> result = y)`;;

let myMin_spec_satisfied =
  `!x y:int.
     myMin_precond x y
     ==> myMin_postcond x y (myMin x y)`;;

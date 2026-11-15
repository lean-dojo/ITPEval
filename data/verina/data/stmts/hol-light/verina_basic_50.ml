(*
  Statement-only formalization of VERINA corpus artifact verina_basic_50
  (verina__hol-light__verina_basic_50), catalog title "Abs": an executable
  integer conditional computes the absolute value, together with its total
  precondition and branchwise correctness contract. This file contains no
  proof.
*)

let abs_precond_definition = new_definition
  `Abs_precond (x:int) <=> T`;;

let abs_definition = new_definition
  `Abs (x:int) =
     if x < &0 then --x else x`;;

let abs_postcond_definition = new_definition
  `Abs_postcond (x:int) (result:int) <=>
     (x >= &0 ==> x = result) /\
     (x < &0 ==> x + result = &0)`;;

let abs_spec_satisfied_statement =
  `!x:int.
     Abs_precond x
     ==> Abs_postcond x (Abs x)`;;

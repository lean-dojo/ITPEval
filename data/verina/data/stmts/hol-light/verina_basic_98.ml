(*
  Statement-only formalization of VERINA corpus artifact verina_basic_98
  (verina__hol-light__verina_basic_98), catalog title "Triple": an executable
  integer function multiplies its input by three, together with its total
  precondition and integer-division correctness contract. This file contains
  no proof.
*)

let triple_precond = new_definition
  `Triple_precond (x:int) <=> T`;;

let triple = new_definition
  `Triple (x:int) = x * &3`;;

let triple_postcond = new_definition
  `Triple_postcond (x:int) (result:int) <=>
     result div &3 = x /\
     result div &3 * &3 = result`;;

let triple_spec_satisfied =
  `!x:int.
     Triple_precond x
     ==> Triple_postcond x (Triple x)`;;

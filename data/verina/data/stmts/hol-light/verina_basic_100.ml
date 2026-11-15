(*
  Statement-only formalization of VERINA corpus artifact verina_basic_100,
  catalog title "Triple": an executable integer function returns zero at zero
  and otherwise computes x + 2 * x, together with its total precondition and
  integer-division correctness contract. This file contains no proof.
*)

let triple_precond = new_definition
  `Triple_precond (x:int) <=> T`;;

let triple = new_definition
  `Triple (x:int) =
     if x = &0 then &0
     else
       let y = &2 * x in
       x + y`;;

let triple_postcond = new_definition
  `Triple_postcond (x:int) (result:int) <=>
     result div &3 = x /\
     result div &3 * &3 = result`;;

let triple_spec_satisfied =
  `!x:int.
     Triple_precond x
     ==> Triple_postcond x (Triple x)`;;

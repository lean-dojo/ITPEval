(*
  Statement-only formalization of VERINA corpus artifact verina_basic_101,
  catalog title "Triple": an executable integer function doubles its input
  and adds the original input, together with its total precondition and
  integer-division correctness contract. This file contains no proof.
*)

let triple_precond = new_definition
  `Triple_precond (x:int) <=> T`;;

let triple = new_definition
  `Triple (x:int) =
     let y = x * &2 in
     y + x`;;

let triple_postcond = new_definition
  `Triple_postcond (x:int) (result:int) <=>
     result div &3 = x /\
     result div &3 * &3 = result`;;

let triple_spec_satisfied =
  `!x:int.
     Triple_precond x
     ==> Triple_postcond x (Triple x)`;;

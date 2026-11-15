(*
  Statement-only formalization of VERINA corpus artifact verina_basic_26,
  catalog title "isEven": an executable integer parity test returns true
  exactly when the input is divisible by two, together with its total
  correctness contract. This file contains no proof.
*)

let isEven_precond = new_definition
  `isEven_precond (n:int) <=> T`;;

let isEven = new_definition
  `isEven (n:int) =
     (n rem (&2:int) = (&0:int))`;;

let isEven_postcond = new_definition
  `isEven_postcond (n:int) (result:bool) <=>
     (result ==> n rem (&2:int) = (&0:int)) /\
     (~result ==> ~(n rem (&2:int) = (&0:int)))`;;

let isEven_spec_satisfied =
  `!n:int.
     isEven_precond n
     ==> isEven_postcond n (isEven n)`;;

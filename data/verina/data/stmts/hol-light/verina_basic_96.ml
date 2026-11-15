(*
  Statement-only formalization of VERINA corpus artifact verina_basic_96
  (verina__hol-light__verina_basic_96), catalog title "SwapSimultaneous": an
  executable simultaneous assignment returns two integer inputs in reversed
  order, together with its total precondition and exact pair-valued
  correctness contract. This file contains no proof.
*)

let SwapSimultaneous_precond = new_definition
  `SwapSimultaneous_precond (X:int) (Y:int) <=> T`;;

let SwapSimultaneous = new_definition
  `SwapSimultaneous (X:int) (Y:int) = (Y,X)`;;

let SwapSimultaneous_postcond = new_definition
  `SwapSimultaneous_postcond
      (X:int) (Y:int) (result:int#int) <=>
     FST result = Y /\
     SND result = X /\
     (~(X = Y)
      ==> ~(FST result = X) /\ ~(SND result = Y))`;;

let SwapSimultaneous_spec_satisfied =
  `!X:int. !Y:int.
     SwapSimultaneous_precond X Y
     ==> SwapSimultaneous_postcond
           X Y (SwapSimultaneous X Y)`;;

(*
  Statement-only formalization of VERINA corpus artifact verina_basic_92
  (verina__hol-light__verina_basic_92), catalog title "SwapArithmetic": an
  executable integer program swaps two inputs using subtraction and addition,
  together with its total precondition and full pair-valued correctness
  contract. This file contains no proof.
*)

let SwapArithmetic_precond_def = new_definition
  `SwapArithmetic_precond (x_input:int) (y_input:int) <=> T`;;

let SwapArithmetic_def = new_definition
  `SwapArithmetic (x_input:int) (y_input:int) =
     let x1 = x_input in
     let y1 = y_input in
     let x2 = y1 - x1 in
     let y2 = y1 - x2 in
     let x3 = y2 + x2 in
     (x3,y2)`;;

let SwapArithmetic_postcond_def = new_definition
  `SwapArithmetic_postcond
      (x_input:int) (y_input:int) (result:int#int) <=>
     FST result = y_input /\
     SND result = x_input /\
     (~(x_input = y_input)
      ==> ~(FST result = x_input) /\
          ~(SND result = y_input))`;;

let SwapArithmetic_spec_satisfied_statement =
  `!x_input:int. !y_input:int.
     SwapArithmetic_precond x_input y_input
     ==> SwapArithmetic_postcond
           x_input y_input (SwapArithmetic x_input y_input)`;;

(*
  Statement-only formalization of VERINA corpus artifact verina_basic_91
  (verina__hol-light__verina_basic_91), catalog title "Swap": an executable
  integer program swaps two inputs through a temporary value, together with
  its total precondition and full pair-valued correctness contract. This file
  contains no proof.
*)

let swap_precond_def = new_definition
  `Swap_precond (x_input:int) (y_input:int) <=> T`;;

let swap_def = new_definition
  `Swap (x_input:int) (y_input:int) =
     let x = x_input in
     let y = y_input in
     let tmp = x in
     let x = y in
     let y = tmp in
     (x,y)`;;

let swap_postcond_def = new_definition
  `Swap_postcond
      (x_input:int) (y_input:int) (result:int#int) <=>
     FST result = y_input /\
     SND result = x_input /\
     (~(x_input = y_input)
      ==> ~(FST result = x_input) /\
          ~(SND result = y_input))`;;

let swap_spec_satisfied_statement =
  `!x_input:int. !y_input:int.
     Swap_precond x_input y_input
     ==> Swap_postcond
           x_input y_input (Swap x_input y_input)`;;

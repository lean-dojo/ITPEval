(*
  Statement-only formalization of VERINA corpus artifact verina_basic_78
  (verina__hol-light__verina_basic_78), catalog title "MultipleReturns": an
  executable integer computation returns the sum and difference of two
  integers, together with its total precondition and pair-valued correctness
  contract. This file contains no proof.
*)

let MultipleReturns_precond = new_definition
  `MultipleReturns_precond (x:int) (y:int) <=> T`;;

let MultipleReturns = new_definition
  `MultipleReturns (x:int) (y:int) =
     let more = x + y in
     let less = x - y in
     (more,less)`;;

let MultipleReturns_postcond = new_definition
  `MultipleReturns_postcond
      (x:int) (y:int) (result:int#int) <=>
     FST result = x + y /\
     SND result + y = x`;;

let MultipleReturns_spec_satisfied =
  `!x:int. !y:int.
     MultipleReturns_precond x y
     ==> MultipleReturns_postcond
           x y (MultipleReturns x y)`;;

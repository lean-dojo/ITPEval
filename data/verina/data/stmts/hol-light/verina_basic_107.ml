(*
  Statement-only formalization of VERINA corpus artifact verina_basic_107,
  catalog title "ComputeAvg": Euclidean integer division computes the average
  of two integers and satisfies its exact quotient-remainder correctness
  contract. This file contains no proof.
*)

let ComputeAvg_precond = new_definition
  `ComputeAvg_precond (a:int) (b:int) <=> T`;;

let ComputeAvg = new_definition
  `ComputeAvg (a:int) (b:int) =
     (a + b) div (&2:int)`;;

let ComputeAvg_postcond = new_definition
  `ComputeAvg_postcond (a:int) (b:int) (result:int) <=>
     (&2:int) * result =
     a + b - ((a + b) rem (&2:int))`;;

let ComputeAvg_spec_satisfied =
  `!a b:int.
     ComputeAvg_precond a b
     ==> ComputeAvg_postcond a b (ComputeAvg a b)`;;

(*
  Statement-only formalization of VERINA corpus artifact verina_basic_5,
  catalog title "multiply": executable integer multiplication returns the
  product of its two inputs, together with its total precondition and
  subtraction-based correctness contract. This file contains no proof.
*)

let multiply_precond = new_definition
  `multiply_precond (a:int) (b:int) <=> T`;;

let multiply = new_definition
  `multiply (a:int) (b:int) = a * b`;;

let multiply_postcond = new_definition
  `multiply_postcond (a:int) (b:int) (result:int) <=>
     result - a * b = (&0:int) /\
     a * b - result = (&0:int)`;;

let multiply_spec_satisfied =
  `!a:int. !b:int.
     multiply_precond a b
     ==> multiply_postcond a b (multiply a b)`;;

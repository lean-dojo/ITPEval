(*
  Statement-only formalization of VERINA corpus artifact verina_basic_59
  (verina__hol-light__verina_basic_59), catalog title "DoubleQuadruple": an
  executable integer computation returns twice its input and then twice that
  first result, together with its total precondition and pair-valued
  correctness contract. This file contains no proof.
*)

let DoubleQuadruple_precond = new_definition
  `DoubleQuadruple_precond (x:int) <=> T`;;

let DoubleQuadruple = new_definition
  `DoubleQuadruple (x:int) =
     let a = (&2:int) * x in
     let b = (&2:int) * a in
     (a,b)`;;

let DoubleQuadruple_postcond = new_definition
  `DoubleQuadruple_postcond
      (x:int) (result:int#int) <=>
     FST result = (&2:int) * x /\
     SND result = (&2:int) * FST result`;;

let DoubleQuadruple_spec_satisfied =
  `!x:int.
     DoubleQuadruple_precond x
     ==> DoubleQuadruple_postcond
           x (DoubleQuadruple x)`;;

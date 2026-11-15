(*
  Statement-only formalization of VERINA corpus artifact verina_basic_81
  (verina__hol-light__verina_basic_81), catalog title "DivisionFunction": an
  executable natural-number division function returns an integer remainder
  and quotient, with a zero-divisor branch and the quotient-remainder
  correctness contract. This file contains no proof.
*)

let DivisionFunction_precond = new_definition
  `DivisionFunction_precond (x:num) (y:num) <=> T`;;

let divMod = new_definition
  `divMod (x:num) (y:num) =
     ((&(x MOD y):int),(&(x DIV y):int))`;;

let DivisionFunction = new_definition
  `DivisionFunction (x:num) (y:num) =
     if y = 0 then ((&x:int),(&0:int))
     else divMod x y`;;

let DivisionFunction_postcond = new_definition
  `DivisionFunction_postcond
      (x:num) (y:num) (result:int#int) <=>
     let r = FST result in
     let q = SND result in
     (y = 0 ==> r = (&x:int) /\ q = (&0:int)) /\
     (~(y = 0)
      ==> q * (&y:int) + r = (&x:int) /\
          ((&0:int) <= r /\ r < (&y:int)) /\
          (&0:int) <= q)`;;

let DivisionFunction_spec_satisfied =
  `!x:num. !y:num.
     DivisionFunction_precond x y
     ==> DivisionFunction_postcond
           x y (DivisionFunction x y)`;;

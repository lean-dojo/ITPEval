(*
  Statement-only formalization of VERINA corpus artifact verina_basic_1,
  catalog title "hasOppositeSign": an executable integer-product test detects
  exactly when two integers have opposite nonzero signs, together with its
  precondition and Boolean correctness contract. This file contains no proof.
*)

let hasOppositeSign_precond = new_definition
  `hasOppositeSign_precond (a:int) (b:int) <=> T`;;

let hasOppositeSign = new_definition
  `hasOppositeSign (a:int) (b:int) = (a * b < &0)`;;

let hasOppositeSign_postcond = new_definition
  `hasOppositeSign_postcond
      (a:int) (b:int) (result:bool) <=>
     (((a < &0 /\ b > &0) \/ (a > &0 /\ b < &0)) ==> result) /\
     (~((a < &0 /\ b > &0) \/ (a > &0 /\ b < &0)) ==> ~result)`;;

let hasOppositeSign_spec_satisfied =
  `!a:int. !b:int.
     hasOppositeSign_precond a b
     ==> hasOppositeSign_postcond
           a b (hasOppositeSign a b)`;;

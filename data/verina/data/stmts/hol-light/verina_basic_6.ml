(*
  Statement-only formalization of VERINA corpus artifact verina_basic_6
  (verina__hol-light__verina_basic_6), catalog title "minOfThree": an
  executable integer comparison returns the minimum of three inputs, together
  with its total precondition and lower-bound-and-input-membership correctness
  contract. This file contains no proof.
*)

let minOfThree_precond = new_definition
  `minOfThree_precond (a:int) (b:int) (c:int) <=> T`;;

let minOfThree = new_definition
  `minOfThree (a:int) (b:int) (c:int) =
     if a <= b /\ a <= c then a
     else if b <= a /\ b <= c then b
     else c`;;

let minOfThree_postcond = new_definition
  `minOfThree_postcond
      (a:int) (b:int) (c:int) (result:int) <=>
     (result <= a /\ result <= b /\ result <= c) /\
     (result = a \/ result = b \/ result = c)`;;

let minOfThree_spec_satisfied =
  `!a:int. !b:int. !c:int.
     minOfThree_precond a b c
     ==> minOfThree_postcond a b c (minOfThree a b c)`;;

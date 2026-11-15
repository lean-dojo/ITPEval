(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_41,
  catalog title "maxOfThree": an executable conditional selects the maximum
  of three integers, with a total precondition and a postcondition stating
  that the result bounds every input and equals one of them. This file
  contains no proof.
*)

let maxOfThree_precond = new_definition
  `maxOfThree_precond (a:int) (b:int) (c:int) <=> T`;;

let maxOfThree = new_definition
  `maxOfThree (a:int) (b:int) (c:int) =
     if a >= b /\ a >= c then a
     else if b >= a /\ b >= c then b
     else c`;;

let maxOfThree_postcond = new_definition
  `maxOfThree_postcond
      (a:int) (b:int) (c:int) (result:int) <=>
     (result >= a /\ result >= b /\ result >= c) /\
     (result = a \/ result = b \/ result = c)`;;

let maxOfThree_spec_satisfied =
  `!a:int. !b:int. !c:int.
     maxOfThree_precond a b c
     ==> maxOfThree_postcond a b c
           (maxOfThree a b c)`;;

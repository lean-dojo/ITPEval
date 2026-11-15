(*
  Statement-only formalization of VERINA corpus artifact verina_basic_37
  (verina__hol-light__verina_basic_37), catalog title
  "findFirstOccurrence": an executable left-to-right scan of a nondecreasing
  integer array returns the first target index, stops once an element exceeds
  the target, or returns -1 when absent, together with its full
  first-occurrence correctness contract. This file contains no proof.
*)

let findFirstOccurrence_precond = new_definition
  `findFirstOccurrence_precond
      (arr:int list) (target:int) <=>
     PAIRWISE (\x y:int. x <= y) arr`;;

let findFirstOccurrence_loop =
  new_recursive_definition list_RECURSION
    `(!target:int. !i:num.
        findFirstOccurrence_loop
          ([]:int list) target i = (-- &1:int)) /\
     (!a:int. !rest:int list. !target:int. !i:num.
        findFirstOccurrence_loop
          (CONS a rest) target i =
        if a = target then
          &i
        else if a > target then
          (-- &1:int)
        else
          findFirstOccurrence_loop rest target (SUC i))`;;

let findFirstOccurrence = new_definition
  `findFirstOccurrence (arr:int list) (target:int) =
     findFirstOccurrence_loop arr target 0`;;

let findFirstOccurrence_toNat = new_definition
  `findFirstOccurrence_toNat (z:int) =
     if z < &0 then 0 else num_of_int z`;;

let findFirstOccurrence_postcond = new_definition
  `findFirstOccurrence_postcond
      (arr:int list) (target:int) (result:int) <=>
     (result = -- &1 \/ result >= &0) /\
     (result >= &0
      ==> findFirstOccurrence_toNat result < LENGTH arr /\
          EL (findFirstOccurrence_toNat result) arr = target /\
          (!i:num.
             i < findFirstOccurrence_toNat result
             ==> ~(EL i arr = target))) /\
     (result = -- &1
      ==> (!i:num.
             i < LENGTH arr
             ==> ~(EL i arr = target)))`;;

let findFirstOccurrence_spec_satisfied =
  `!arr:int list. !target:int.
     findFirstOccurrence_precond arr target
     ==> findFirstOccurrence_postcond
           arr target (findFirstOccurrence arr target)`;;

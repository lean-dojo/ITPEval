(*
  Statement-only formalization of VERINA corpus artifact verina_basic_4
  (verina__hol-light__verina_basic_4), catalog title "kthElement": a
  deterministic integer-array lookup returns the element at a valid one-based
  natural index, with its exact array-membership and selected-index
  postcondition. This file contains no proof.
*)

let kthElement_precond = new_definition
  `kthElement_precond (arr:int list) (k:num) <=>
     1 <= k /\ k <= LENGTH arr`;;

let kthElement_getDefault = new_definition
  `kthElement_getDefault (arr:int list) (index:num) =
     if index < LENGTH arr then EL index arr else (&0:int)`;;

let kthElement = new_definition
  `kthElement (arr:int list) (k:num) =
     kthElement_getDefault arr (k - 1)`;;

let kthElement_postcond = new_definition
  `kthElement_postcond
      (arr:int list) (k:num) (result:int) <=>
     ?x:int.
       MEM x arr /\
       x = result /\
       x = kthElement_getDefault arr (k - 1)`;;

let kthElement_spec_satisfied =
  `!arr:int list. !k:num.
     kthElement_precond arr k
     ==> kthElement_postcond arr k (kthElement arr k)`;;

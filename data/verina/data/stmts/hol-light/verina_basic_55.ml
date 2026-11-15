(*
  Statement-only formalization of VERINA corpus artifact verina_basic_55
  (verina__hol-light__verina_basic_55), catalog title "Compare": an executable
  integer-equality comparison returns true exactly when its two inputs are
  equal, together with its total precondition and Boolean correctness contract.
  This file contains no proof.
*)

let compare_precond_definition = new_definition
  `Compare_precond (a:int) (b:int) <=> T`;;

let compare_definition = new_definition
  `Compare (a:int) (b:int) =
     if a = b then T else F`;;

let compare_postcond_definition = new_definition
  `Compare_postcond (a:int) (b:int) (result:bool) <=>
     (a = b ==> result = T) /\
     (~(a = b) ==> result = F)`;;

let compare_spec_satisfied =
  `!a:int. !b:int.
     Compare_precond a b
     ==> Compare_postcond a b (Compare a b)`;;

(*
  Statement-only formalization of Logipedia corpus artifact logic.eq_ind,
  catalog title "logic.eq_ind": equality induction transports an arbitrary
  predicate from an element to any equal element over an arbitrary type. This
  file contains no proof.
*)

let logipedia_logic_eq = new_definition
  `logipedia_logic_eq (x:A) (y:A) <=> x = y`;;

let statement =
  `!x:A.
   !P:A->bool.
     P x
     ==> !y:A. logipedia_logic_eq x y ==> P y`;;

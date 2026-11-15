(*
  Statement-only formalization of Logipedia corpus artifact logic.eq_rect_r,
  catalog title "logic.eq_rect_r": reverse-oriented equality elimination
  transports an arbitrary predicate from an element to an equal element over
  an arbitrary type. This file contains no proof.
*)

let logipedia_logic_eq = new_definition
  `logipedia_logic_eq (x:A) (y:A) <=> x = y`;;

let statement =
  `!a:A.
   !x:A.
     logipedia_logic_eq x a
     ==> !P:A->bool. P a ==> P x`;;

(*
  Statement-only formalization of Logipedia corpus artifact logic.eq_ind_r,
  catalog title "logic.eq_ind_r": reverse-oriented equality induction
  transports an arbitrary predicate from an element to any element equal to
  it over an arbitrary type. This file contains no proof.
*)

let logipedia_logic_eq = new_definition
  `logipedia_logic_eq (x:A) (y:A) <=> x = y`;;

let statement =
  `!a:A.
   !P:A->bool.
     P a
     ==> !x:A. logipedia_logic_eq x a ==> P x`;;

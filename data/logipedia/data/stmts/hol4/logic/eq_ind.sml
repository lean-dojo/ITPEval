(*
  Statement-only formalization of the Logipedia corpus artifact logic.eq_ind
  (catalog title "logic.eq_ind"): a predicate holding at an element of an
  arbitrary type also holds at every equal element. This file contains no
  proof.
*)

open HolKernel Parse boolLib;

val logic_eq_ind =
  ``!(x : 'a) (P : 'a -> bool).
      P x ==>
      !y : 'a. x = y ==> P y``;

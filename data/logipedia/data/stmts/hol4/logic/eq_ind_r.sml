(*
  Statement-only formalization of the Logipedia corpus artifact logic.eq_ind_r
  (catalog title "logic.eq_ind_r"): a predicate holding at an element of an
  arbitrary type also holds at every element equal to it in the reverse
  orientation. This file contains no proof.
*)

open HolKernel Parse boolLib;

val logic_eq_ind_r =
  ``!(a : 'a) (P : 'a -> bool).
      P a ==>
      !x : 'a. x = a ==> P x``;

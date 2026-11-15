(*
  Statement-only formalization of the Logipedia corpus artifact logic.rewrite_r
  (catalog title "logic.rewrite_r"): a predicate holding at an element of an
  arbitrary type also holds at every element equal to it in the reverse
  orientation. This file contains no proof.
*)

open HolKernel Parse boolLib;

val logic_rewrite_r =
  ``!(x : 'a) (P : 'a -> bool).
      P x ==>
      !y : 'a. y = x ==> P y``;

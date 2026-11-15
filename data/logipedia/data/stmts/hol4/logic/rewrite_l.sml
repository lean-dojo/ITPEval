(*
  Statement-only formalization of the Logipedia corpus artifact logic.rewrite_l
  (catalog title "logic.rewrite_l"): a predicate holding at an element of an
  arbitrary type also holds at every equal element. This file contains no
  proof.
*)

open HolKernel Parse boolLib;

val logic_rewrite_l =
  ``!(x : 'a) (P : 'a -> bool).
      P x ==>
      !y : 'a. x = y ==> P y``;

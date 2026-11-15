(*
  Statement-only formalization of the Logipedia corpus artifact logic.trans_eq
  (catalog title "logic.trans_eq"): equality is transitive for all three
  elements of an arbitrary type. This file contains no proof.
*)

open HolKernel Parse boolLib;

val logic_trans_eq =
  ``!(x : 'a) (y : 'a) (z : 'a).
      x = y ==> y = z ==> x = z``;

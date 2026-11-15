(*
  Statement-only formalization of the Logipedia corpus artifact logic.eq_f
  (catalog title "logic.eq_f"): equality of two elements of an arbitrary type
  is preserved by every function into an arbitrary codomain. This file
  contains no proof.
*)

open HolKernel Parse boolLib;

val logic_eq_f =
  ``!(f : 'a -> 'b) (x : 'a) (y : 'a).
      x = y ==> f x = f y``;

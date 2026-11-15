(*
  Statement-only formalization of the Logipedia corpus artifact logic.eq_rect_r
  (catalog title "logic.eq_rect_r"): equality from x to a transports every
  predicate holding at a back to x. This file contains no proof.
*)

open HolKernel Parse boolLib;

val logic_eq_rect_r =
  ``!(a : 'a) (x : 'a).
      x = a ==>
      !P : 'a -> bool. P a ==> P x``;

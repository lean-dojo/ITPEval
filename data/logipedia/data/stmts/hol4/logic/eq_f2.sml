(*
  Statement-only formalization of the Logipedia corpus artifact logic.eq_f2
  (catalog title "logic.eq_f2"): equality of both inputs to a curried binary
  function implies equality of the corresponding outputs. This file contains
  no proof.
*)

open HolKernel Parse boolLib;

val logic_eq_f2 =
  ``!(f : 'a -> 'b -> 'c) (x1 : 'a) (x2 : 'a)
      (y1 : 'b) (y2 : 'b).
      x1 = x2 ==>
      y1 = y2 ==>
      f x1 y1 = f x2 y2``;

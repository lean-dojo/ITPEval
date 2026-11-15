(*
  Statement-only formalization of Logipedia corpus artifact logic.eq_f2
  (catalog title "logic.eq_f2"): equality of both inputs to a curried binary
  function entails equality of its outputs. This file contains no proof.
*)

Theorem logic_eq_f2 :
  forall (A B C : Type) (f : A -> B -> C)
         (x1 x2 : A) (y1 y2 : B),
    x1 = x2 ->
    y1 = y2 ->
    f x1 y1 = f x2 y2.
Admitted.

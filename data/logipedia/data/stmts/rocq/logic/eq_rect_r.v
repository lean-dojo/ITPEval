(*
  Statement-only formalization of Logipedia corpus artifact logic.eq_rect_r
  (catalog title "logic.eq_rect_r"): right-oriented equality transports an
  arbitrary predicate from a distinguished element to an equal element.
  This file contains no proof.
*)

Theorem logic_eq_rect_r :
  forall (A : Type) (a x : A),
    x = a ->
    forall P : A -> Prop,
      P a ->
      P x.
Admitted.

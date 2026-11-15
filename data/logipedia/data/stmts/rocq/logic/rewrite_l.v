(*
  Statement-only formalization of Logipedia corpus artifact logic.rewrite_l
  (catalog title "logic.rewrite_l"): equality transports an arbitrary
  predicate from an element to every equal element. This file contains no
  proof.
*)

Theorem logic_rewrite_l :
  forall (A : Type) (x : A) (P : A -> Prop),
    P x ->
    forall y : A,
      x = y ->
      P y.
Admitted.

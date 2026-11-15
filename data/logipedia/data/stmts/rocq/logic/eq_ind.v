(*
  Statement-only formalization of Logipedia corpus artifact logic.eq_ind
  (catalog title "logic.eq_ind"): equality transports an arbitrary predicate
  from an element to every equal element. This file contains no proof.
*)

Theorem logic_eq_ind :
  forall (A : Type) (x : A) (P : A -> Prop),
    P x ->
    forall y : A,
      x = y ->
      P y.
Admitted.

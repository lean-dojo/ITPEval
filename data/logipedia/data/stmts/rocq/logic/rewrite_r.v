(*
  Statement-only formalization of Logipedia corpus artifact logic.rewrite_r
  (catalog title "logic.rewrite_r"): right-oriented equality transports an
  arbitrary predicate from an element to any element equal to it. This file
  contains no proof.
*)

Theorem logic_rewrite_r :
  forall (A : Type) (x : A) (P : A -> Prop),
    P x ->
    forall y : A,
      y = x ->
      P y.
Admitted.

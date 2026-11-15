(*
  Statement-only formalization of Logipedia corpus artifact logic.eq_ind_r
  (catalog title "logic.eq_ind_r"): right-oriented equality transports an
  arbitrary predicate from a distinguished element to any element equal to it.
  This file contains no proof.
*)

Theorem logic_eq_ind_r :
  forall (A : Type) (a : A) (P : A -> Prop),
    P a ->
    forall x : A,
      x = a ->
      P x.
Admitted.

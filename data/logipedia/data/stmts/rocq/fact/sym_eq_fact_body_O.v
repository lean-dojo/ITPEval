(*
  Statement-only formalization of Logipedia corpus artifact
  fact.sym_eq_fact_body_O (catalog title "fact.sym_eq_fact_body_O"): one is
  Leibniz-equal to the factorial body at zero. This file contains no proof.
*)

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter fact_body : nat -> nat.

Theorem fact_sym_eq_fact_body_O :
  logipedia_leibniz nat (S O) (fact_body O).
Admitted.

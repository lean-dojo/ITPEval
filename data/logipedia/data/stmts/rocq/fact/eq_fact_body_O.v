(*
  Statement-only formalization of Logipedia corpus artifact
  fact.eq_fact_body_O (catalog title "fact.eq_fact_body_O"): the factorial
  body at zero is Leibniz-equal to one. This file contains no proof.
*)

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter fact_body : nat -> nat.

Theorem fact_eq_fact_body_O :
  logipedia_leibniz nat (fact_body O) (S O).
Admitted.

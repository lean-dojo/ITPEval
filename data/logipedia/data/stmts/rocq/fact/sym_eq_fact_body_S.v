(*
  Statement-only formalization of Logipedia corpus artifact
  fact.sym_eq_fact_body_S (catalog title "fact.sym_eq_fact_body_S"): for every
  natural input, the factorial value times its successor is Leibniz-equal to
  the factorial body at that successor. This file contains no proof.
*)

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter fact fact_body : nat -> nat.

Theorem fact_sym_eq_fact_body_S :
  forall n : nat,
    logipedia_leibniz
      nat
      (Nat.mul (fact n) (S n))
      (fact_body (S n)).
Admitted.

(*
  Statement-only formalization of Logipedia corpus artifact
  fact.eq_fact_body_S (catalog title "fact.eq_fact_body_S"): for every natural
  input, the factorial body at its successor is Leibniz-equal to the factorial
  value times that successor. This file contains no proof.
*)

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter fact fact_body : nat -> nat.

Theorem fact_eq_fact_body_S :
  forall n : nat,
    logipedia_leibniz
      nat
      (fact_body (S n))
      (Nat.mul (fact n) (S n)).
Admitted.

(*
  Statement-only formalization of Logipedia corpus artifact
  fact.axiom_fact_body_S (catalog title "fact.axiom_fact_body_S"): for every
  natural input, the source equality relates the factorial body at its
  successor to the factorial value times that successor. This file contains
  no proof.
*)

Parameter connectives_equal : forall A : Type, A -> A -> Prop.
Parameter fact fact_body : nat -> nat.

Theorem fact_axiom_fact_body_S :
  forall n : nat,
    connectives_equal
      nat
      (fact_body (S n))
      (Nat.mul (fact n) (S n)).
Admitted.

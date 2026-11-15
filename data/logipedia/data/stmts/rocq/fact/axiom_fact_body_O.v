(*
  Statement-only formalization of Logipedia corpus artifact
  fact.axiom_fact_body_O (catalog title "fact.axiom_fact_body_O"): the source
  equality relates the factorial body at zero to one. This file contains no
  proof.
*)

Parameter connectives_equal : forall A : Type, A -> A -> Prop.
Parameter fact_body : nat -> nat.

Theorem fact_axiom_fact_body_O :
  connectives_equal nat (fact_body O) (S O).
Admitted.

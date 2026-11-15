(*
  Statement-only formalization of Logipedia corpus artifact fact.axiom_fact
  (catalog title "fact.axiom_fact"): for every natural input, the source
  equality relates the factorial value to the filtered factorial body.
  This file contains no proof.
*)

Parameter connectives_equal : forall A : Type, A -> A -> Prop.
Parameter filter_nat_type :
  forall return_type : Type,
    (nat -> return_type) -> nat -> return_type.
Parameter fact fact_body : nat -> nat.

Theorem fact_axiom_fact :
  forall n : nat,
    connectives_equal
      nat
      (fact n)
      (filter_nat_type nat fact_body n).
Admitted.

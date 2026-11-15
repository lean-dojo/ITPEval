(*
  Statement-only formalization of Logipedia corpus artifact nat.axiom_minus
  (catalog title "nat.axiom_minus"): for every natural input, the source
  polymorphic equality relates the partially applied natural subtraction
  function to the corresponding naturally filtered subtraction body.
  This file contains no proof.
*)

Parameter connectives_equal : forall A : Type, A -> A -> Prop.
Parameter filter_nat_type :
  forall return_type : Type,
    (nat -> return_type) -> nat -> return_type.
Parameter minus minus_body : nat -> nat -> nat.

Theorem logipedia_nat_axiom_minus :
  forall n : nat,
    connectives_equal
      (nat -> nat)
      (minus n)
      (filter_nat_type (nat -> nat) minus_body n).
Admitted.

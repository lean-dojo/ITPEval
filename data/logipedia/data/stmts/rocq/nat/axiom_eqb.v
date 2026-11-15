(*
  Statement-only formalization of Logipedia corpus artifact nat.axiom_eqb
  (catalog title "nat.axiom_eqb"): for every natural input, the source
  polymorphic equality relates the Boolean-valued equality-test function to
  the corresponding naturally filtered equality-test body. This file contains
  no proof.
*)

Parameter connectives_equal : forall A : Type, A -> A -> Prop.
Parameter filter_nat_type :
  forall return_type : Type,
    (nat -> return_type) -> nat -> return_type.
Parameter eqb eqb_body : nat -> nat -> bool.

Theorem logipedia_nat_axiom_eqb :
  forall n : nat,
    connectives_equal
      (nat -> bool)
      (eqb n)
      (filter_nat_type (nat -> bool) eqb_body n).
Admitted.

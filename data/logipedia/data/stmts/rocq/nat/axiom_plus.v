(*
  Statement-only formalization of Logipedia corpus artifact nat.axiom_plus
  (catalog title "nat.axiom_plus"): for every natural input, the source
  polymorphic equality relates the partially applied natural addition
  function to the corresponding naturally filtered addition body.
  This file contains no proof.
*)

Parameter connectives_equal : forall A : Type, A -> A -> Prop.
Parameter filter_nat_type :
  forall return_type : Type,
    (nat -> return_type) -> nat -> return_type.
Parameter plus plus_body : nat -> nat -> nat.

Theorem logipedia_nat_axiom_plus :
  forall n : nat,
    connectives_equal
      (nat -> nat)
      (plus n)
      (filter_nat_type (nat -> nat) plus_body n).
Admitted.

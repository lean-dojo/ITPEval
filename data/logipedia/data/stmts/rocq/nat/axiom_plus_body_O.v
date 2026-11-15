(*
  Statement-only formalization of Logipedia corpus artifact
  nat.axiom_plus_body_O (catalog title "nat.axiom_plus_body_O"): the source
  polymorphic equality relates the natural-addition body at zero to the
  identity function on natural numbers. This file contains no proof.
*)

Parameter connectives_equal : forall A : Type, A -> A -> Prop.
Parameter plus_body : nat -> nat -> nat.

Theorem logipedia_nat_axiom_plus_body_O :
  connectives_equal
    (nat -> nat)
    (plus_body O)
    (fun m : nat => m).
Admitted.

(*
  Statement-only formalization of Logipedia corpus artifact
  nat.axiom_leb_body_O (catalog title "nat.axiom_leb_body_O"): the source
  polymorphic equality relates the Boolean less-than-or-equal test body at
  natural zero to the constant-true function on natural numbers. This file
  contains no proof.
*)

Parameter connectives_equal : forall A : Type, A -> A -> Prop.
Parameter leb_body : nat -> nat -> bool.

Theorem logipedia_nat_axiom_leb_body_O :
  connectives_equal
    (nat -> bool)
    (leb_body O)
    (fun _ : nat => true).
Admitted.

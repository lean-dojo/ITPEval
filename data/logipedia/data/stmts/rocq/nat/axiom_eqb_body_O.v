(*
  Statement-only formalization of Logipedia corpus artifact
  nat.axiom_eqb_body_O (catalog title "nat.axiom_eqb_body_O"): the source
  polymorphic equality relates the Boolean equality-test body at natural zero
  to the natural-number matcher with true at zero and false at successors.
  This file contains no proof.
*)

Parameter connectives_equal : forall A : Type, A -> A -> Prop.
Parameter eqb_body : nat -> nat -> bool.
Parameter match_nat_type :
  forall return_type : Type,
    return_type -> (nat -> return_type) -> nat -> return_type.

Theorem logipedia_nat_axiom_eqb_body_O :
  connectives_equal
    (nat -> bool)
    (eqb_body O)
    (fun m : nat =>
       match_nat_type bool true (fun _ : nat => false) m).
Admitted.

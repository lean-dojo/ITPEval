(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.axiom_gcd_aux_body_O (catalog title "gcd.axiom_gcd_aux_body_O"): the
  source equality relates the auxiliary gcd body at zero to the binary
  natural-number function that returns its first argument. This file contains
  no proof.
*)

Parameter connectives_equal : forall A : Type, A -> A -> Prop.
Parameter gcd_aux_body : nat -> nat -> nat -> nat.

Theorem gcd_axiom_gcd_aux_body_O :
  connectives_equal
    (nat -> nat -> nat)
    (gcd_aux_body O)
    (fun m : nat => fun n : nat => m).
Admitted.

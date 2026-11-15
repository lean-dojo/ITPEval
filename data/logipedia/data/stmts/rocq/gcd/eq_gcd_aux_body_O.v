(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.eq_gcd_aux_body_O (catalog title "gcd.eq_gcd_aux_body_O"): the auxiliary
  gcd body at zero is Leibniz-equal to the binary natural-number function that
  returns its first argument. This file contains no proof.
*)

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter gcd_aux_body : nat -> nat -> nat -> nat.

Theorem gcd_eq_gcd_aux_body_O :
  logipedia_leibniz
    (nat -> nat -> nat)
    (gcd_aux_body O)
    (fun m : nat => fun n : nat => m).
Admitted.

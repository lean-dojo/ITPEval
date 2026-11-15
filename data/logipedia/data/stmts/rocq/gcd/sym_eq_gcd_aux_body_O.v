(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.sym_eq_gcd_aux_body_O (catalog title "gcd.sym_eq_gcd_aux_body_O"): the
  binary natural-number function that returns its first argument is
  Leibniz-equal to the auxiliary gcd body at zero. This file contains no proof.
*)

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter gcd_aux_body : nat -> nat -> nat -> nat.

Theorem gcd_sym_eq_gcd_aux_body_O :
  logipedia_leibniz
    (nat -> nat -> nat)
    (fun m : nat => fun n : nat => m)
    (gcd_aux_body O).
Admitted.

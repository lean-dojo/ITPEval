(*
  Statement-only formalization of Logipedia corpus artifact
  nat.eq_minus_body_O (catalog title "nat.eq_minus_body_O"): Leibniz equality
  relates the natural-subtraction body at zero to the constant-zero function
  on natural numbers. This file contains no proof.
*)

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter minus_body : nat -> nat -> nat.

Theorem logipedia_nat_eq_minus_body_O :
  logipedia_leibniz
    (nat -> nat)
    (minus_body O)
    (fun _ : nat => O).
Admitted.

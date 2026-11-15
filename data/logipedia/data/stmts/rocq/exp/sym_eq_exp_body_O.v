(*
  Statement-only formalization of Logipedia corpus artifact
  exp.sym_eq_exp_body_O (catalog title "exp.sym_eq_exp_body_O"): for every
  natural input, one is Leibniz-equal to the exponentiation body at zero.
  This file contains no proof.
*)

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter exp_body : nat -> nat -> nat.

Theorem exp_sym_eq_exp_body_O :
  forall n : nat,
    logipedia_leibniz nat (S O) (exp_body n O).
Admitted.

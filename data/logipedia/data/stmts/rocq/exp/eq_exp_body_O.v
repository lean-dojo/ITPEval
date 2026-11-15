(*
  Statement-only formalization of Logipedia corpus artifact
  exp.eq_exp_body_O (catalog title "exp.eq_exp_body_O"): for every natural
  input, the exponentiation body at zero is Leibniz-equal to one. This file
  contains no proof.
*)

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter exp_body : nat -> nat -> nat.

Theorem exp_eq_exp_body_O :
  forall n : nat,
    logipedia_leibniz nat (exp_body n O) (S O).
Admitted.

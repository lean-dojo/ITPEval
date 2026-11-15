(*
  Statement-only formalization of Logipedia corpus artifact
  exp.eq_exp_body_S (catalog title "exp.eq_exp_body_S"): for all natural
  inputs, the exponentiation body at a successor exponent is Leibniz-equal
  to the product of the exponential value and its base. This file contains
  no proof.
*)

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter exp exp_body : nat -> nat -> nat.

Theorem exp_eq_exp_body_S :
  forall n m : nat,
    logipedia_leibniz
      nat
      (exp_body n (S m))
      (Nat.mul (exp n m) n).
Admitted.

(*
  Statement-only formalization of Logipedia corpus artifact
  exp.sym_eq_exp_body_S (catalog title "exp.sym_eq_exp_body_S"): for all
  natural inputs, the product of the exponential value and its base is
  Leibniz-equal to the exponentiation body at the successor exponent.
  This file contains no proof.
*)

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter exp exp_body : nat -> nat -> nat.

Theorem exp_sym_eq_exp_body_S :
  forall n m : nat,
    logipedia_leibniz
      nat
      (Nat.mul (exp n m) n)
      (exp_body n (S m)).
Admitted.

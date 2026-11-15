(*
  Statement-only formalization of Logipedia corpus artifact
  exp.axiom_exp_body_S (catalog title "exp.axiom_exp_body_S"): for all
  natural inputs, the source equality relates the exponentiation body at a
  successor exponent to the product of the exponential value and its base.
  This file contains no proof.
*)

Parameter connectives_equal : forall A : Type, A -> A -> Prop.
Parameter exp exp_body : nat -> nat -> nat.

Theorem exp_axiom_exp_body_S :
  forall n m : nat,
    connectives_equal
      nat
      (exp_body n (S m))
      (Nat.mul (exp n m) n).
Admitted.

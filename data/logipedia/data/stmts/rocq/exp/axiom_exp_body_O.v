(*
  Statement-only formalization of Logipedia corpus artifact
  exp.axiom_exp_body_O (catalog title "exp.axiom_exp_body_O"): for every
  natural input, the source equality relates the exponentiation body at zero
  to one. This file contains no proof.
*)

Parameter connectives_equal : forall A : Type, A -> A -> Prop.
Parameter exp_body : nat -> nat -> nat.

Theorem exp_axiom_exp_body_O :
  forall n : nat,
    connectives_equal nat (exp_body n O) (S O).
Admitted.

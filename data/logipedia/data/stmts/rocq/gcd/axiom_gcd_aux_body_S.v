(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.axiom_gcd_aux_body_S (catalog title "gcd.axiom_gcd_aux_body_S"): for
  every natural index, the source equality relates the auxiliary gcd body at
  its successor to the binary function that returns the second input when it
  divides the first, and otherwise recurses on the remainder. This file
  contains no proof.
*)

Parameter connectives_equal : forall A : Type, A -> A -> Prop.
Parameter gcd_aux gcd_aux_body : nat -> nat -> nat -> nat.
Parameter modulo : nat -> nat -> nat.
Parameter dividesb : nat -> nat -> bool.

Theorem gcd_axiom_gcd_aux_body_S :
  forall p : nat,
    connectives_equal
      (nat -> nat -> nat)
      (gcd_aux_body (S p))
      (fun m n : nat =>
         if dividesb n m
         then n
         else gcd_aux p n (modulo m n)).
Admitted.

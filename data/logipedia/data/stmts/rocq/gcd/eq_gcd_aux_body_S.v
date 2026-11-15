(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.eq_gcd_aux_body_S (catalog title "gcd.eq_gcd_aux_body_S"): for every
  natural index, the successor-indexed auxiliary gcd body is Leibniz-equal to
  the binary function that returns the second input when it divides the first,
  and otherwise recurses on the remainder. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Definition gcd_source_modulo (m n : nat) : nat :=
  match n with
  | O => m
  | S n' => Nat.modulo m (S n')
  end.

Definition gcd_source_dividesb (n m : nat) : bool :=
  Nat.eqb (gcd_source_modulo m n) O.

Parameter gcd_aux gcd_aux_body : nat -> nat -> nat -> nat.

Theorem gcd_eq_gcd_aux_body_S :
  forall p : nat,
    logipedia_leibniz
      (nat -> nat -> nat)
      (gcd_aux_body (S p))
      (fun m n : nat =>
         if gcd_source_dividesb n m
         then n
         else gcd_aux p n (gcd_source_modulo m n)).
Admitted.

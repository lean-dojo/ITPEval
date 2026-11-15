(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.sym_eq_gcd_aux_body_S (catalog title "gcd.sym_eq_gcd_aux_body_S"): for
  every natural index, the concrete successor-indexed auxiliary gcd body is
  Leibniz-equal, in the symmetric direction, to its conditional recursive
  equation. This file contains no proof.
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

Fixpoint gcd_aux (p m n : nat) : nat :=
  match p with
  | O => m
  | S q =>
      if gcd_source_dividesb n m
      then n
      else gcd_aux q n (gcd_source_modulo m n)
  end.

Definition gcd_aux_body (p : nat) : nat -> nat -> nat :=
  match p with
  | O => fun m _ => m
  | S q =>
      fun m n =>
        if gcd_source_dividesb n m
        then n
        else gcd_aux q n (gcd_source_modulo m n)
  end.

Theorem gcd_sym_eq_gcd_aux_body_S :
  forall p : nat,
    logipedia_leibniz
      (nat -> nat -> nat)
      (fun m n : nat =>
         if gcd_source_dividesb n m
         then n
         else gcd_aux p n (gcd_source_modulo m n))
      (gcd_aux_body (S p)).
Admitted.

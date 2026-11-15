(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1186808
  (thousand-theorems__rocq__Q1186808), "Lucas's theorem": for a prime p,
  a binomial coefficient is congruent modulo p to the product of the
  binomial coefficients of the corresponding base-p digits. This file
  contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat ZArith.ZArith.
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition q1186808_prime (p : nat) : Prop :=
  (1 < p)%nat /\
  forall d : nat, Nat.divide d p -> d = 1 \/ d = p.

Theorem lucas_theorem :
  forall n k p a : nat,
    q1186808_prime p ->
    (n < Nat.pow p a)%nat ->
    (k < Nat.pow p a)%nat ->
    Z.divide
      (Z.of_nat p)
      (Z.of_nat
         (\prod_(0 <= i < a)
            binomial
              (Nat.modulo (Nat.div n (Nat.pow p i)) p)
              (Nat.modulo (Nat.div k (Nat.pow p i)) p)) -
       Z.of_nat (binomial n k))%Z.
Admitted.

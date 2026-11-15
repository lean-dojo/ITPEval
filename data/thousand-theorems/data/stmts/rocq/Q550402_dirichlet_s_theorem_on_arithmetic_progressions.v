(*
  Statement-only formalization of Thousand Theorems corpus artifact Q550402
  (thousand-theorems__rocq__Q550402), "Dirichlet's theorem on arithmetic
  progressions": for a nonzero modulus and a unit residue class, infinitely
  many prime natural numbers lie in that residue class. This file contains
  no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Definition q550402_prime (p : nat) : Prop :=
  (1 < p)%nat /\
  forall d : nat, Nat.divide d p -> d = 1 \/ d = p.

Record q550402_zmod (q : nat) : Type := {
  q550402_zmod_val : nat;
  q550402_zmod_val_lt : (q550402_zmod_val < q)%nat
}.

Definition q550402_zmod_eq (q a b : nat) : Prop :=
  Nat.modulo a q = Nat.modulo b q.

Definition q550402_is_unit
    (q : nat) (a : q550402_zmod q) : Prop :=
  Nat.gcd (q550402_zmod_val q a) q = 1.

Theorem infinite_setOf_prime_and_eq_mod :
  forall q : nat,
    q <> 0 ->
    forall a : q550402_zmod q,
      q550402_is_unit q a ->
      forall n : nat,
        exists p : nat,
          (n < p)%nat /\
          q550402_prime p /\
          q550402_zmod_eq q p (q550402_zmod_val q a).
Admitted.

(*
  Statement-only formalization of Thousand Theorems corpus artifact Q188295
  (thousand-theorems__rocq__Q188295), "Fermat's little theorem": for a prime
  p, every nonzero residue modulo p raised to the power p - 1 equals one in
  the residue field. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Definition q188295_prime (p : nat) : Prop :=
  (1 < p)%nat /\
  forall d : nat, Nat.divide d p -> d = 1 \/ d = p.

Record q188295_zmod (p : nat) : Type := {
  q188295_zmod_val : nat;
  q188295_zmod_val_lt : (q188295_zmod_val < p)%nat
}.

Definition q188295_zmod_eq (p a b : nat) : Prop :=
  Nat.modulo a p = Nat.modulo b p.

Theorem pow_card_sub_one_eq_one :
  forall p : nat,
    q188295_prime p ->
    forall a : q188295_zmod p,
      ~ q188295_zmod_eq p (q188295_zmod_val p a) 0 ->
      q188295_zmod_eq p
        (Nat.pow (q188295_zmod_val p a) (p - 1))
        1.
Admitted.

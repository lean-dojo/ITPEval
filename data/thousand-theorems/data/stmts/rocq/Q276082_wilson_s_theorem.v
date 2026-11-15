(*
  Statement-only formalization of Thousand Theorems corpus artifact Q276082
  (thousand-theorems__rocq__Q276082), "Wilson's theorem": for a prime natural
  number p, the factorial of p - 1 is congruent to -1 modulo p. This file
  contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat Arith.Factorial.

Definition q276082_prime (p : nat) : Prop :=
  (1 < p)%nat /\
  forall d : nat, Nat.divide d p -> d = 1 \/ d = p.

Definition q276082_zmod_eq (p a b : nat) : Prop :=
  Nat.modulo a p = Nat.modulo b p.

Theorem wilsons_lemma :
  forall p : nat,
    q276082_prime p ->
    q276082_zmod_eq p (fact (p - 1)) (p - 1).
Admitted.

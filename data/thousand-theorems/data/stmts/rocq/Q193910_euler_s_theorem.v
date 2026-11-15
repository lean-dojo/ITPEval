(*
  Statement-only formalization of Thousand Theorems corpus artifact Q193910
  (thousand-theorems__rocq__Q193910), "Euler's theorem": natural numbers
  coprime to a modulus have their Euler-totient power congruent to one modulo
  that modulus. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat Lists.List.

Definition q193910_euler_totient (n : nat) : nat :=
  List.length
    (List.filter
       (fun k : nat => Nat.eqb (Nat.gcd k n) 1)
       (List.seq 0 n)).

Definition q193910_mod_eq (n a b : nat) : Prop :=
  Nat.modulo a n = Nat.modulo b n.

Theorem nat_mod_eq_pow_totient :
  forall x n : nat,
    Nat.gcd x n = 1 ->
    q193910_mod_eq n (Nat.pow x (q193910_euler_totient n)) 1.
Admitted.

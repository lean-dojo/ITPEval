(* Statement-only formalization of PutnamBench corpus artifact putnam_2024_a4
   (putnambench__rocq__putnam_2024_a4): classification of the primes for which
   powers of an integer can be rearranged with a fixed nonzero modular
   difference. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat ZArith ZArith.Znumtheory.

Definition putnam_2024_a4_in_interval
    (upper n : nat) : Prop :=
  (n <= upper)%nat.

Definition putnam_2024_a4_bij_on_interval
    (e : nat -> nat) (upper : nat) : Prop :=
  (forall n : nat,
      putnam_2024_a4_in_interval upper n ->
      putnam_2024_a4_in_interval upper (e n)) /\
  (forall x y : nat,
      putnam_2024_a4_in_interval upper x ->
      putnam_2024_a4_in_interval upper y ->
      e x = e y ->
      x = y) /\
  (forall y : nat,
      putnam_2024_a4_in_interval upper y ->
      exists x : nat,
        putnam_2024_a4_in_interval upper x /\
        e x = y).

Definition putnam_2024_a4_qualifies (p : nat) : Prop :=
  Znumtheory.prime (Z.of_nat p) /\
  (5 < p)%nat /\
  exists a r : Z,
    (1 <= r)%Z /\
    (r <= Z.of_nat (p - 1))%Z /\
    exists e : nat -> nat,
      putnam_2024_a4_bij_on_interval e (p - 5) /\
      forall n : nat,
        (1 <= n)%nat /\ (n <= p - 5)%nat ->
        Z.divide
          (Z.of_nat p)
          (Z.pow a (Z.of_nat (e n)) -
           Z.pow a (Z.of_nat (e ((n - 1)%nat))) - r).

Definition putnam_2024_a4_solution (p : nat) : Prop :=
  p = 7%nat.

Theorem putnam_2024_a4 :
  forall p : nat,
    putnam_2024_a4_qualifies p <->
    putnam_2024_a4_solution p.
Admitted.

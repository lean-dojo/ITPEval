(*
  Statement-only formalization of Hundred Theorems item 005, "The Prime Number Theorem":
  the ratio of the number of primes at most n to n / ln n tends to 1.
  This file contains no proof.
*)

From Stdlib Require Import Reals List PeanoNat.

Open Scope R_scope.

Definition primeb (p : nat) : bool :=
  andb (Nat.leb 2 p)
    (forallb
       (fun d => negb (Nat.eqb (Nat.modulo p d) 0))
       (seq 2 (p - 2))).

Definition prime_count (n : nat) : nat :=
  length (filter primeb (seq 0 (S n))).

Definition tends_to (u : nat -> R) (l : R) : Prop :=
  forall eps : R,
    0 < eps ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        Rabs (u n - l) < eps.

Theorem prime_number_theorem :
  tends_to
    (fun n =>
       INR (prime_count n) / (INR n / ln (INR n)))
    1.
Admitted.

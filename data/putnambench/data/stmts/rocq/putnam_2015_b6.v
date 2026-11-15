(* Statement-only formalization of PutnamBench corpus artifact putnam_2015_b6:
   the alternating series formed from counts of odd divisors of k below
   sqrt(2k) sums to pi squared over 16. This file contains no proof. *)

From Stdlib Require Import Reals List ClassicalDescription SeqSeries.

Open Scope R_scope.

Definition putnam_2015_b6_qualifies (j k : nat) : bool :=
  if excluded_middle_informative
       (Nat.Odd j /\
        Nat.divide j k /\
        INR j < sqrt (2 * INR k))
  then true
  else false.

Definition putnam_2015_b6_divisor_count (k : nat) : nat :=
  length
    (filter
      (fun j : nat => putnam_2015_b6_qualifies j k)
      (seq 1 k)).

Definition putnam_2015_b6_solution : R :=
  PI ^ 2 / 16.

Theorem putnam_2015_b6
    (A : nat -> nat)
    (hA : forall k : nat,
      (0 < k)%nat ->
      A k = putnam_2015_b6_divisor_count k) :
  infinite_sum
    (fun n : nat =>
      (-1) ^ n * INR (A (S n)) / INR (S n))
    putnam_2015_b6_solution.
Admitted.

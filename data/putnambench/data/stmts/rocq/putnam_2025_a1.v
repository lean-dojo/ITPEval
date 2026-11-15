(* Statement-only formalization of PutnamBench corpus artifact putnam_2025_a1:
   eventual coprimality in a recurrence of reduced positive rational
   numerators and denominators. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat QArith.

Open Scope Q_scope.

Definition putnam_2025_a1_nat_to_Q (x : nat) : Q :=
  inject_Z (Z.of_nat x).

Theorem putnam_2025_a1
    (m n : nat -> nat)
    (hm : forall k : nat, (0 < m k)%nat)
    (hn : forall k : nat, (0 < n k)%nat)
    (h_distinct : m 0%nat <> n 0%nat)
    (h_coprime :
      forall k : nat,
        (0 < k)%nat ->
        Nat.gcd (m k) (n k) = 1%nat)
    (h_recurrence :
      forall k : nat,
        Qeq
          (putnam_2025_a1_nat_to_Q (m (S k)) /
           putnam_2025_a1_nat_to_Q (n (S k)))
          ((2 * putnam_2025_a1_nat_to_Q (m k) + 1) /
           (2 * putnam_2025_a1_nat_to_Q (n k) + 1))) :
  exists bound : nat,
    forall k : nat,
      (bound < k)%nat ->
      Nat.gcd ((2 * m k + 1)%nat) ((2 * n k + 1)%nat) = 1%nat.
Admitted.

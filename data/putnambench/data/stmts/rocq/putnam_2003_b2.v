(* Statement-only formalization of PutnamBench corpus artifact putnam_2003_b2:
   the strict upper bound for the final term obtained by repeatedly averaging
   neighboring entries of the rational harmonic sequence; this file contains no proof. *)

From Stdlib Require Import QArith Arith.PeanoNat.

Open Scope Q_scope.

Theorem putnam_2003_b2
    (n : nat)
    (hn : (0 < n)%nat)
    (seq : nat -> nat -> Q)
    (hinit :
      forall j : nat,
        (1 <= j <= n)%nat ->
        seq 0%nat j = 1 / inject_Z (Z.of_nat j))
    (havg :
      forall k : nat,
        (1 <= k <= n - 1)%nat ->
        forall j : nat,
          (1 <= j <= n - k)%nat ->
          seq k j =
            (seq (k - 1)%nat j + seq (k - 1)%nat (j + 1)%nat) / 2) :
  seq (n - 1)%nat 1%nat < 2 / inject_Z (Z.of_nat n).
Admitted.

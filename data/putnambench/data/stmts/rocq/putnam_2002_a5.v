(* Statement-only formalization of PutnamBench artifact putnam_2002_a5:
   the recursively defined rational sequence enumerates every positive
   rational as a ratio of consecutive terms; this file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat QArith.

Open Scope Q_scope.

Theorem putnam_2002_a5
    (a : nat -> Q)
    (ha :
      a 0%nat == 1 /\
      forall n : nat,
        a (2 * n + 1)%nat == a n /\
        a (2 * n + 2)%nat == a n + a (n + 1)%nat) :
  forall q : Q,
    0 < q ->
    exists n : nat,
      (1 <= n)%nat /\
      q == a (n - 1)%nat / a n.
Admitted.

(* Statement-only formalization of PutnamBench corpus artifact putnam_2006_a3:
   a recursively defined integer sequence has 2005 consecutive terms divisible
   by 2006. This file contains no proof. *)

From Stdlib Require Import ZArith.

Open Scope Z_scope.

Theorem putnam_2006_a3
    (x : Z -> Z)
    (hxlo :
      forall k : Z,
        1 <= k <= 2006 ->
        x k = k)
    (hxhi :
      forall k : Z,
        2006 <= k ->
        x (k + 1) = x k + x (k - 2005)) :
  exists i : nat,
    (0 < i)%nat /\
    forall j : nat,
      (j < 2005)%nat ->
      Z.divide 2006 (x (Z.of_nat (i + j))).
Admitted.

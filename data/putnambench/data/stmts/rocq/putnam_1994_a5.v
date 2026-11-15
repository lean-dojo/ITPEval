(* Statement-only formalization of PutnamBench corpus artifact putnam_1994_a5:
   positive real sequences tending to zero and gaps in the set of sums over
   1994 strictly increasing indices. This file contains no proof. *)

From Stdlib Require Import Reals Ensembles SeqSeries.

Open Scope R_scope.

Definition putnam_1994_a5_sum
    (r : nat -> R) (i : nat -> nat) : R :=
  sum_f_R0 (fun j : nat => r (i j)) 1993.

Definition putnam_1994_a5_representable
    (r : nat -> R) : Ensemble R :=
  fun x : R =>
    exists i : nat -> nat,
      (forall j k : nat,
        (j < 1994)%nat ->
        (k < 1994)%nat ->
        (j < k)%nat ->
        (i j < i k)%nat) /\
      x = putnam_1994_a5_sum r i.

Theorem putnam_1994_a5
    (r : nat -> R)
    (S : Ensemble R)
    (rpos : forall n : nat, 0 < r n)
    (rlim : Un_cv r 0)
    (hS : Same_set R S (putnam_1994_a5_representable r)) :
  forall a b : R,
    a < b ->
    exists c d : R,
      a <= c /\
      c < d /\
      d <= b /\
      forall x : R, c < x /\ x < d -> ~ S x.
Admitted.

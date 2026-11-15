(* Statement-only formalization of PutnamBench artifact putnam_1964_a3:
   the gap lengths created by an injective dense sequence in the open unit
   interval satisfy the stated infinite-series identity. This file contains no proof. *)

From Stdlib Require Import Reals.

Open Scope R_scope.

Definition putnam_1964_a3_is_supremum
    (S : R -> Prop) (s : R) : Prop :=
  (forall y : R, S y -> y <= s) /\
  (forall u : R, (forall y : R, S y -> y <= u) -> s <= u).

Definition putnam_1964_a3_is_infimum
    (S : R -> Prop) (s : R) : Prop :=
  (forall y : R, S y -> s <= y) /\
  (forall l : R, (forall y : R, S y -> l <= y) -> l <= s).

Definition putnam_1964_a3_left_candidates
    (x : nat -> R) (n : nat) : R -> Prop :=
  fun p : R =>
    p = 0 \/
    (p < x n /\ exists i : nat, (i < n)%nat /\ p = x i).

Definition putnam_1964_a3_right_candidates
    (x : nat -> R) (n : nat) : R -> Prop :=
  fun p : R =>
    p = 1 \/
    (x n < p /\ exists i : nat, (i < n)%nat /\ p = x i).

Fixpoint putnam_1964_a3_partial_sum
    (f : nat -> R) (n : nat) : R :=
  match n with
  | O => 0
  | S k => putnam_1964_a3_partial_sum f k + f k
  end.

Definition putnam_1964_a3_series_has_sum
    (f : nat -> R) (s : R) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        Rabs (putnam_1964_a3_partial_sum f n - s) < epsilon.

Theorem putnam_1964_a3
    (x a b : nat -> R)
    (hxin : forall n : nat, 0 < x n < 1)
    (hxdense :
      forall y epsilon : R,
        0 < y < 1 ->
        0 < epsilon ->
        exists n : nat, Rabs (x n - y) < epsilon)
    (hxinj : forall m n : nat, x m = x n -> m = n)
    (ha :
      forall n : nat,
        putnam_1964_a3_is_supremum
          (putnam_1964_a3_left_candidates x n)
          (x n - a n))
    (hb :
      forall n : nat,
        putnam_1964_a3_is_infimum
          (putnam_1964_a3_right_candidates x n)
          (x n + b n)) :
  putnam_1964_a3_series_has_sum
    (fun n : nat => a n * b n * (a n + b n))
    (1 / 3).
Admitted.

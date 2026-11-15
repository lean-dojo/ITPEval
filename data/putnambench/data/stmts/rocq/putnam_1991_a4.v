(* Statement-only formalization of PutnamBench corpus artifact putnam_1991_a4:
   existence of a sequence of closed discs in the real plane whose centers
   have no finite limit point, whose total area is finite, and which meets
   every line. This file contains no proof. *)

From Stdlib Require Import Reals Arith.PeanoNat.

Open Scope R_scope.

Definition putnam_1991_a4_point : Type := (R * R)%type.

Definition putnam_1991_a4_point_zero : putnam_1991_a4_point :=
  (0, 0).

Definition putnam_1991_a4_point_add
    (p q : putnam_1991_a4_point) : putnam_1991_a4_point :=
  (fst p + fst q, snd p + snd q).

Definition putnam_1991_a4_point_scale
    (a : R) (p : putnam_1991_a4_point) : putnam_1991_a4_point :=
  (a * fst p, a * snd p).

Definition putnam_1991_a4_point_distance
    (p q : putnam_1991_a4_point) : R :=
  sqrt ((fst p - fst q) ^ 2 + (snd p - snd q) ^ 2).

Definition putnam_1991_a4_strictly_increasing
    (f : nat -> nat) : Prop :=
  forall i j : nat, (i < j)%nat -> (f i < f j)%nat.

Definition putnam_1991_a4_has_finite_limit_point
    (c : nat -> putnam_1991_a4_point) : Prop :=
  exists p : putnam_1991_a4_point,
    forall epsilon : R,
      0 < epsilon ->
      exists f : nat -> nat,
        putnam_1991_a4_strictly_increasing f /\
        forall i : nat,
          putnam_1991_a4_point_distance (c (f i)) p < epsilon.

Fixpoint putnam_1991_a4_partial_sum
    (u : nat -> R) (n : nat) : R :=
  match n with
  | O => 0
  | S k => putnam_1991_a4_partial_sum u k + u k
  end.

Definition putnam_1991_a4_series_converges
    (u : nat -> R) : Prop :=
  exists total : R,
    forall epsilon : R,
      0 < epsilon ->
      exists N : nat,
        forall n : nat,
          (N <= n)%nat ->
          Rabs (putnam_1991_a4_partial_sum u n - total) < epsilon.

Definition putnam_1991_a4_line_point
    (base direction : putnam_1991_a4_point)
    (t : R) : putnam_1991_a4_point :=
  putnam_1991_a4_point_add
    base
    (putnam_1991_a4_point_scale t direction).

Definition putnam_1991_a4_solution : Prop := True.

Theorem putnam_1991_a4 :
  (exists (c : nat -> putnam_1991_a4_point) (r : nat -> R),
      (forall i : nat, 0 <= r i) /\
      ~ putnam_1991_a4_has_finite_limit_point c /\
      putnam_1991_a4_series_converges
        (fun i : nat => PI * (r i) ^ 2) /\
      (forall base direction : putnam_1991_a4_point,
        direction <> putnam_1991_a4_point_zero ->
        exists (i : nat) (t : R),
          putnam_1991_a4_point_distance
            (putnam_1991_a4_line_point base direction t)
            (c i) <= r i)) <->
  putnam_1991_a4_solution.
Admitted.

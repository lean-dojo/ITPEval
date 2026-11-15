(* Statement-only formalization of PutnamBench corpus artifact putnam_2023_b4:
   the least time for a continuous piecewise twice differentiable real
   function with prescribed accelerations to reach 2023. This file contains
   no proof. *)

From Stdlib Require Import Reals.

Open Scope R_scope.

Definition putnam_2023_b4_solution : R := 29.

Definition putnam_2023_b4_regular_point
    (n : nat) (ts : nat -> R) (t : R) : Prop :=
  t > ts 0%nat /\
  forall i : nat, (1 <= i <= n)%nat -> t <> ts i.

Definition putnam_2023_b4_continuous_from
    (f : R -> R) (a : R) : Prop :=
  forall x : R,
    a <= x ->
    forall epsilon : R,
      epsilon > 0 ->
      exists delta : R,
        delta > 0 /\
        forall y : R,
          a <= y ->
          Rabs (y - x) < delta ->
          Rabs (f y - f x) < epsilon.

Definition putnam_2023_b4_has_derivative_at
    (f : R -> R) (x derivative : R) : Prop :=
  forall epsilon : R,
    epsilon > 0 ->
    exists delta : R,
      delta > 0 /\
      forall h : R,
        0 < Rabs h < delta ->
        Rabs ((f (x + h) - f x) / h - derivative) < epsilon.

Definition putnam_2023_b4_right_limit_zero
    (g : R -> R) (a : R) : Prop :=
  forall epsilon : R,
    epsilon > 0 ->
    exists delta : R,
      delta > 0 /\
      forall t : R,
        a < t < a + delta ->
        Rabs (g t) < epsilon.

Definition putnam_2023_b4_admissible
    (n : nat) (ts : nat -> R) (f : R -> R) : Prop :=
  (forall k : nat,
      (k < n)%nat ->
      ts (S k) >= ts k + 1) /\
  putnam_2023_b4_continuous_from f (ts 0%nat) /\
  exists first_derivative second_derivative : R -> R,
    (forall t : R,
        putnam_2023_b4_regular_point n ts t ->
        putnam_2023_b4_has_derivative_at f t (first_derivative t) /\
        putnam_2023_b4_has_derivative_at
          first_derivative t (second_derivative t)) /\
    f (ts 0%nat) = / 2 /\
    (forall k : nat,
        (k <= n)%nat ->
        putnam_2023_b4_right_limit_zero first_derivative (ts k)) /\
    (forall k : nat,
        (k < n)%nat ->
        forall t : R,
          ts k < t < ts (S k) ->
          second_derivative t = INR (S k)) /\
    (forall t : R,
        t > ts n ->
        second_derivative t = INR (S n)).

Definition putnam_2023_b4_feasible_time (T : R) : Prop :=
  0 <= T /\
  exists (n : nat) (ts : nat -> R) (f : R -> R),
    putnam_2023_b4_admissible n ts f /\
    f (ts 0%nat + T) = 2023.

Definition putnam_2023_b4_is_least_time (T : R) : Prop :=
  putnam_2023_b4_feasible_time T /\
  forall U : R,
    putnam_2023_b4_feasible_time U ->
    T <= U.

Theorem putnam_2023_b4 :
  putnam_2023_b4_is_least_time putnam_2023_b4_solution.
Admitted.

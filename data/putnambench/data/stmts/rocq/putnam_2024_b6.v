(* Statement-only formalization of PutnamBench corpus artifact putnam_2024_b6
   (putnambench__rocq__putnam_2024_b6): the critical exponent for the
   left-limit asymptotics of a real power series near 1. This file contains
   no proof. *)

From Stdlib Require Import Reals Rpower Arith.PeanoNat.

Open Scope R_scope.

Fixpoint putnam_2024_b6_partial_sum
    (u : nat -> R) (count : nat) : R :=
  match count with
  | O => 0
  | S k => putnam_2024_b6_partial_sum u k + u k
  end.

Definition putnam_2024_b6_series_sum
    (u : nat -> R) (sum : R) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists cutoff : nat,
      forall count : nat,
        (cutoff <= count)%nat ->
        Rabs (putnam_2024_b6_partial_sum u count - sum) < epsilon.

Definition putnam_2024_b6_term
    (a x : R) (n : nat) : R :=
  Rpower (INR (S n)) a *
  exp (2 * INR (S n)) *
  x ^ Nat.pow (S n) 2.

Definition putnam_2024_b6_left_limit
    (g : R -> R) (limit : R) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists delta : R,
      0 < delta /\
      forall x : R,
        0 < 1 - x < delta ->
        Rabs (g x - limit) < epsilon.

Definition putnam_2024_b6_left_limit_at_top
    (g : R -> R) : Prop :=
  forall bound : R,
    exists delta : R,
      0 < delta /\
      forall x : R,
        0 < 1 - x < delta ->
        bound <= g x.

Definition putnam_2024_b6_solution : R :=
  -1 / 2.

Theorem putnam_2024_b6 :
  forall (F : R -> R -> R) (c : R),
    (forall (a x : R),
      0 <= x < 1 ->
      putnam_2024_b6_series_sum
        (putnam_2024_b6_term a x) (F a x)) ->
    ((forall a : R,
        a < c ->
        putnam_2024_b6_left_limit
          (fun x : R =>
            F a x * exp (-1 / (1 - x)))
          0) /\
     (forall a : R,
        a > c ->
        putnam_2024_b6_left_limit_at_top
          (fun x : R =>
            F a x * exp (-1 / (1 - x)))))
    <->
    c = putnam_2024_b6_solution.
Admitted.

(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1137206
  (thousand-theorems__rocq__Q1137206), "Taylor's theorem": the Lagrange and
  Cauchy forms of the remainder for the Taylor polynomial of a real function
  on a closed interval. This file contains no proof.
*)

From Stdlib Require Import
  Reals
  ClassicalDescription
  ClassicalEpsilon
  Arith.Factorial
  Arith.PeanoNat.

Open Scope R_scope.

Definition q1137206_set : Type := R -> Prop.

Definition q1137206_closed_interval
    (a b : R) : q1137206_set :=
  fun y : R => a <= y /\ y <= b.

Definition q1137206_open_interval
    (a b : R) : q1137206_set :=
  fun y : R => a < y /\ y < b.

Definition q1137206_continuous_within_at
    (f : R -> R) (s : q1137206_set) (x : R) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists delta : R,
      0 < delta /\
      forall y : R,
        s y ->
        Rabs (y - x) < delta ->
        Rabs (f y - f x) < epsilon.

Definition q1137206_continuous_on
    (f : R -> R) (s : q1137206_set) : Prop :=
  forall x : R,
    s x ->
    q1137206_continuous_within_at f s x.

Definition q1137206_has_deriv_within_at
    (f : R -> R) (derivative : R)
    (s : q1137206_set) (x : R) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists delta : R,
      0 < delta /\
      forall y : R,
        s y ->
        Rabs (y - x) < delta ->
        Rabs
          (f y - f x - derivative * (y - x))
        <= epsilon * Rabs (y - x).

Definition q1137206_differentiable_within_at
    (f : R -> R) (s : q1137206_set) (x : R) : Prop :=
  exists derivative : R,
    q1137206_has_deriv_within_at f derivative s x.

Definition q1137206_differentiable_on
    (f : R -> R) (s : q1137206_set) : Prop :=
  forall x : R,
    s x ->
    q1137206_differentiable_within_at f s x.

Definition q1137206_deriv_within
    (f : R -> R) (s : q1137206_set) (x : R) : R :=
  match excluded_middle_informative
          (exists derivative : R,
            q1137206_has_deriv_within_at f derivative s x) with
  | left _ =>
      epsilon (inhabits 0)
        (fun derivative : R =>
          q1137206_has_deriv_within_at f derivative s x)
  | right _ => 0
  end.

Fixpoint q1137206_iterated_deriv_within
    (n : nat) (f : R -> R) (s : q1137206_set) : R -> R :=
  match n with
  | O => f
  | S k =>
      fun x : R =>
        q1137206_deriv_within
          (q1137206_iterated_deriv_within k f s) s x
  end.

Definition q1137206_cont_diff_on
    (n : nat) (f : R -> R) (s : q1137206_set) : Prop :=
  forall k : nat,
    (k <= n)%nat ->
    q1137206_continuous_on
      (q1137206_iterated_deriv_within k f s) s /\
    ((k < n)%nat ->
      q1137206_differentiable_on
        (q1137206_iterated_deriv_within k f s) s).

Definition q1137206_taylor_term
    (f : R -> R) (s : q1137206_set)
    (x0 x : R) (k : nat) : R :=
  q1137206_iterated_deriv_within k f s x0 *
  (x - x0) ^ k / INR (fact k).

Fixpoint q1137206_taylor_within_eval
    (f : R -> R) (n : nat) (s : q1137206_set)
    (x0 x : R) : R :=
  match n with
  | O => q1137206_taylor_term f s x0 x O
  | S k =>
      q1137206_taylor_within_eval f k s x0 x +
      q1137206_taylor_term f s x0 x (S k)
  end.

Theorem taylor_mean_remainder_lagrange :
  forall (f : R -> R) (x x0 : R) (n : nat),
    x0 < x ->
    q1137206_cont_diff_on n f
      (q1137206_closed_interval x0 x) ->
    q1137206_differentiable_on
      (q1137206_iterated_deriv_within n f
        (q1137206_closed_interval x0 x))
      (q1137206_open_interval x0 x) ->
    exists x' : R,
      q1137206_open_interval x0 x x' /\
      f x -
        q1137206_taylor_within_eval f n
          (q1137206_closed_interval x0 x) x0 x =
      q1137206_iterated_deriv_within (S n) f
        (q1137206_closed_interval x0 x) x' *
      (x - x0) ^ (S n) / INR (fact (S n)).
Admitted.

Theorem taylor_mean_remainder_cauchy :
  forall (f : R -> R) (x x0 : R) (n : nat),
    x0 < x ->
    q1137206_cont_diff_on n f
      (q1137206_closed_interval x0 x) ->
    q1137206_differentiable_on
      (q1137206_iterated_deriv_within n f
        (q1137206_closed_interval x0 x))
      (q1137206_open_interval x0 x) ->
    exists x' : R,
      q1137206_open_interval x0 x x' /\
      f x -
        q1137206_taylor_within_eval f n
          (q1137206_closed_interval x0 x) x0 x =
      q1137206_iterated_deriv_within (S n) f
        (q1137206_closed_interval x0 x) x' *
      (x - x') ^ n / INR (fact n) * (x - x0).
Admitted.

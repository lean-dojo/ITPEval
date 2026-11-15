(*
  Statement-only formalization of Thousand Theorems corpus artifact Q2734084
  (thousand-theorems__rocq__Q2734084), "Bohr–Mollerup theorem": a positive
  log-convex real function on the positive reals, normalized at one and
  satisfying the Gamma recurrence, equals the Gamma function there. This file
  contains no proof.
*)

From Stdlib Require Import
  Reals
  ClassicalEpsilon
  Arith.Factorial.

Open Scope R_scope.

Definition q2734084_set : Type := R -> Prop.

Definition q2734084_positive_reals : q2734084_set :=
  fun x : R => 0 < x.

Definition q2734084_convex_set
    (s : q2734084_set) : Prop :=
  forall x y a b : R,
    s x ->
    s y ->
    0 <= a ->
    0 <= b ->
    a + b = 1 ->
    s (a * x + b * y).

Definition q2734084_log_convex_on_positive
    (f : R -> R) : Prop :=
  q2734084_convex_set q2734084_positive_reals /\
  forall x y a b : R,
    q2734084_positive_reals x ->
    q2734084_positive_reals y ->
    0 <= a ->
    0 <= b ->
    a + b = 1 ->
    ln (f (a * x + b * y)) <=
      a * ln (f x) + b * ln (f y).

Fixpoint q2734084_rising_product
    (x : R) (n : nat) : R :=
  match n with
  | O => x
  | S k =>
      q2734084_rising_product x k * (x + INR (S k))
  end.

Definition q2734084_euler_gamma_sequence
    (x : R) (n : nat) : R :=
  let m := S n in
  INR (fact m) *
    exp (x * ln (INR m)) /
    q2734084_rising_product x m.

Definition q2734084_sequence_converges
    (u : nat -> R) (limit : R) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        Rabs (u n - limit) < epsilon.

Definition q2734084_Gamma (x : R) : R :=
  epsilon (inhabits 0)
    (fun limit : R =>
      q2734084_sequence_converges
        (q2734084_euler_gamma_sequence x) limit).

Theorem eq_Gamma_of_log_convex :
  forall f : R -> R,
    q2734084_log_convex_on_positive f ->
    (forall y : R,
      0 < y ->
      f (y + 1) = y * f y) ->
    (forall y : R,
      0 < y ->
      0 < f y) ->
    f 1 = 1 ->
    forall x : R,
      0 < x ->
      f x = q2734084_Gamma x.
Admitted.

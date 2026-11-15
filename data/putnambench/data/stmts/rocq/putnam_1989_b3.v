(* Statement-only formalization of PutnamBench artifact putnam_1989_b3:
   moments of a rapidly decaying solution of a dilation differential equation,
   their closed form, and convergence of their factorial normalization; this
   file contains no proof. *)

From Stdlib Require Import Reals ClassicalEpsilon Arith.Factorial.

Open Scope R_scope.

Definition putnam_1989_b3_nonnegative_derivative
    (f : R -> R) (x d : R) : Prop :=
  forall epsilon : R,
    epsilon > 0 ->
    exists delta : R,
      delta > 0 /\
      forall y : R,
        0 <= y ->
        y <> x ->
        Rabs (y - x) < delta ->
        Rabs ((f y - f x) / (y - x) - d) < epsilon.

Definition putnam_1989_b3_derivative
    (f : R -> R) (x : R) : R :=
  epsilon (inhabits (0 : R))
    (fun d : R => putnam_1989_b3_nonnegative_derivative f x d).

Fixpoint putnam_1989_b3_product (n : nat) : R :=
  match n with
  | O => 1
  | S k =>
      putnam_1989_b3_product k *
      (1 - / (2 ^ (S k)))
  end.

Definition putnam_1989_b3_solution
    (n : nat) (c : R) : R :=
  c * INR (fact n) /
  (3 ^ n * putnam_1989_b3_product n).

Definition putnam_1989_b3_tends_to_at_pos_infty
    (g : R -> R) (limit : R) : Prop :=
  forall epsilon : R,
    epsilon > 0 ->
    exists M : R,
      forall b : R,
        b >= M ->
        Rabs (g b - limit) < epsilon.

Definition putnam_1989_b3_moment
    (f : R -> R) (n : nat) (value : R) : Prop :=
  exists partial_integral : R -> R,
    (forall b : R,
      0 <= b ->
      exists integrable :
        Riemann_integrable
          (fun x : R => x ^ n * f x) 0 b,
        partial_integral b = RiemannInt integrable) /\
    putnam_1989_b3_tends_to_at_pos_infty
      partial_integral value.

Definition putnam_1989_b3_sequence_converges_to
    (u : nat -> R) (limit : R) : Prop :=
  forall epsilon : R,
    epsilon > 0 ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        Rabs (u n - limit) < epsilon.

Definition putnam_1989_b3_normalized_moment
    (mu : nat -> R) (n : nat) : R :=
  mu n * 3 ^ n / INR (fact n).

Theorem putnam_1989_b3
    (f : R -> R)
    (hfdiff :
      forall x : R,
        0 <= x ->
        putnam_1989_b3_nonnegative_derivative
          f x (putnam_1989_b3_derivative f x))
    (hfderiv :
      forall x : R,
        x > 0 ->
        putnam_1989_b3_derivative f x =
        -3 * f x + 6 * f (2 * x))
    (hdecay :
      forall x : R,
        x >= 0 ->
        Rabs (f x) <= exp (- sqrt x))
    (mu : nat -> R)
    (mu_def :
      forall n : nat,
        putnam_1989_b3_moment f n (mu n)) :
  (forall n : nat,
    mu n = putnam_1989_b3_solution n (mu 0%nat)) /\
  (exists limit : R,
    putnam_1989_b3_sequence_converges_to
      (putnam_1989_b3_normalized_moment mu) limit) /\
  (putnam_1989_b3_sequence_converges_to
      (putnam_1989_b3_normalized_moment mu) 0 ->
    mu 0%nat = 0).
Admitted.

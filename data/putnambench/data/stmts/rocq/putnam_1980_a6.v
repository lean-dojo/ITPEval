(* Statement-only formalization of PutnamBench artifact putnam_1980_a6:
   the greatest uniform lower bound of the integral of |f' - f| over
   continuously differentiable real functions on [0,1] with prescribed
   endpoint values; this file contains no proof. *)

From Stdlib Require Import Reals ClassicalEpsilon.

Open Scope R_scope.

Definition putnam_1980_a6_unit_interval (x : R) : Prop :=
  0 <= x <= 1.

Definition putnam_1980_a6_derivable_within
    (f : R -> R) (x d : R) : Prop :=
  forall epsilon : R,
    epsilon > 0 ->
    exists delta : R,
      delta > 0 /\
      forall y : R,
        putnam_1980_a6_unit_interval y ->
        y <> x ->
        Rabs (y - x) < delta ->
        Rabs ((f y - f x) / (y - x) - d) < epsilon.

Definition putnam_1980_a6_derivative
    (f : R -> R) (x : R) : R :=
  epsilon (inhabits (0 : R))
    (fun d : R => putnam_1980_a6_derivable_within f x d).

Definition putnam_1980_a6_continuous_on_unit
    (g : R -> R) : Prop :=
  forall x : R,
    putnam_1980_a6_unit_interval x ->
    forall epsilon : R,
      epsilon > 0 ->
      exists delta : R,
        delta > 0 /\
        forall y : R,
          putnam_1980_a6_unit_interval y ->
          Rabs (y - x) < delta ->
          Rabs (g y - g x) < epsilon.

Definition putnam_1980_a6_continuously_differentiable_on_unit
    (f : R -> R) : Prop :=
  (forall x : R,
      putnam_1980_a6_unit_interval x ->
      putnam_1980_a6_derivable_within
        f x (putnam_1980_a6_derivative f x)) /\
  putnam_1980_a6_continuous_on_unit
    (putnam_1980_a6_derivative f).

Definition putnam_1980_a6_solution : R :=
  1 / exp 1.

Definition putnam_1980_a6_integral_has_value
    (g : R -> R) (value : R) : Prop :=
  exists integrable : Riemann_integrable g 0 1,
    value = RiemannInt integrable.

Definition putnam_1980_a6_is_lower_bound
    (C : (R -> R) -> Prop) (u : R) : Prop :=
  forall f : R -> R,
    C f ->
    forall value : R,
      putnam_1980_a6_integral_has_value
        (fun x : R =>
          Rabs (putnam_1980_a6_derivative f x - f x))
        value ->
      u <= value.

Theorem putnam_1980_a6
    (C : (R -> R) -> Prop)
    (hC :
      forall f : R -> R,
        C f <->
        putnam_1980_a6_continuously_differentiable_on_unit f /\
        f 0 = 0 /\
        f 1 = 1) :
  putnam_1980_a6_is_lower_bound C putnam_1980_a6_solution /\
  forall u : R,
    putnam_1980_a6_is_lower_bound C u ->
    u <= putnam_1980_a6_solution.
Admitted.

(* Statement-only formalization of PutnamBench artifact putnam_1980_b5:
   multiplicative closure of nonnegative strictly increasing convex continuous
   real functions on [0,1] satisfying a parameterized finite-difference
   inequality; this file contains no proof. *)

From Stdlib Require Import Reals.

Open Scope R_scope.

Definition putnam_1980_b5_unit_interval (x : R) : Prop :=
  0 <= x <= 1.

Definition putnam_1980_b5_strictly_increasing_on_unit
    (f : R -> R) : Prop :=
  forall x y : R,
    putnam_1980_b5_unit_interval x ->
    putnam_1980_b5_unit_interval y ->
    x < y ->
    f x < f y.

Definition putnam_1980_b5_convex_on_unit
    (f : R -> R) : Prop :=
  forall u v s : R,
    putnam_1980_b5_unit_interval u ->
    putnam_1980_b5_unit_interval v ->
    putnam_1980_b5_unit_interval s ->
    f (s * u + (1 - s) * v) <=
      s * f u + (1 - s) * f v.

Definition putnam_1980_b5_continuous_on_unit
    (f : R -> R) : Prop :=
  forall x : R,
    putnam_1980_b5_unit_interval x ->
    forall epsilon : R,
      epsilon > 0 ->
      exists delta : R,
        delta > 0 /\
        forall y : R,
          putnam_1980_b5_unit_interval y ->
          Rabs (y - x) < delta ->
          Rabs (f y - f x) < epsilon.

Definition putnam_1980_b5_difference_condition
    (t : R) (f : R -> R) : Prop :=
  f 1 - 2 * f (2 / 3) + f (1 / 3) >=
    t * (f (2 / 3) - 2 * f (1 / 3) + f 0).

Definition putnam_1980_b5_class
    (t : R) (f : R -> R) : Prop :=
  (forall x : R,
      putnam_1980_b5_unit_interval x ->
      f x >= 0) /\
  putnam_1980_b5_strictly_increasing_on_unit f /\
  putnam_1980_b5_convex_on_unit f /\
  putnam_1980_b5_continuous_on_unit f /\
  putnam_1980_b5_difference_condition t f.

Definition putnam_1980_b5_solution (t : R) : Prop :=
  t <= 1.

Theorem putnam_1980_b5 :
  forall t : R,
    t >= 0 ->
    ((forall f g : R -> R,
        putnam_1980_b5_class t f ->
        putnam_1980_b5_class t g ->
        putnam_1980_b5_class t (fun x : R => f x * g x)) <->
      putnam_1980_b5_solution t).
Admitted.

(* Statement-only formalization of PutnamBench corpus artifact putnam_2019_b4:
   the greatest lower bound of a mixed finite difference for twice continuously
   differentiable functions satisfying two partial differential equations on
   the quadrant x >= 1, y >= 1. This file contains no proof. *)

From Stdlib Require Import Reals ClassicalEpsilon.

Open Scope R_scope.

Definition putnam_2019_b4_point : Type := (R * R)%type.

Definition putnam_2019_b4_in_quadrant
    (p : putnam_2019_b4_point) : Prop :=
  1 <= fst p /\ 1 <= snd p.

Definition putnam_2019_b4_derivable_on_ray
    (g : R -> R) (x d : R) : Prop :=
  forall eps : R,
    eps > 0 ->
    exists delta : R,
      delta > 0 /\
      forall y : R,
        1 <= y ->
        y <> x ->
        Rabs (y - x) < delta ->
        Rabs ((g y - g x) / (y - x) - d) < eps.

Definition putnam_2019_b4_real_derivative
    (g : R -> R) (x : R) : R :=
  epsilon (inhabits (0 : R))
    (fun d : R => putnam_2019_b4_derivable_on_ray g x d).

Definition putnam_2019_b4_partial_x
    (f : putnam_2019_b4_point -> R)
    (p : putnam_2019_b4_point) : R :=
  putnam_2019_b4_real_derivative
    (fun x : R => f (x, snd p))
    (fst p).

Definition putnam_2019_b4_partial_y
    (f : putnam_2019_b4_point -> R)
    (p : putnam_2019_b4_point) : R :=
  putnam_2019_b4_real_derivative
    (fun y : R => f (fst p, y))
    (snd p).

Definition putnam_2019_b4_partial_xx
    (f : putnam_2019_b4_point -> R)
    (p : putnam_2019_b4_point) : R :=
  putnam_2019_b4_real_derivative
    (fun x : R => putnam_2019_b4_partial_x f (x, snd p))
    (fst p).

Definition putnam_2019_b4_partial_xy
    (f : putnam_2019_b4_point -> R)
    (p : putnam_2019_b4_point) : R :=
  putnam_2019_b4_real_derivative
    (fun y : R => putnam_2019_b4_partial_x f (fst p, y))
    (snd p).

Definition putnam_2019_b4_partial_yx
    (f : putnam_2019_b4_point -> R)
    (p : putnam_2019_b4_point) : R :=
  putnam_2019_b4_real_derivative
    (fun x : R => putnam_2019_b4_partial_y f (x, snd p))
    (fst p).

Definition putnam_2019_b4_partial_yy
    (f : putnam_2019_b4_point -> R)
    (p : putnam_2019_b4_point) : R :=
  putnam_2019_b4_real_derivative
    (fun y : R => putnam_2019_b4_partial_y f (fst p, y))
    (snd p).

Definition putnam_2019_b4_continuous_on_quadrant
    (g : putnam_2019_b4_point -> R) : Prop :=
  forall p : putnam_2019_b4_point,
    putnam_2019_b4_in_quadrant p ->
    forall eps : R,
      eps > 0 ->
      exists delta : R,
        delta > 0 /\
        forall q : putnam_2019_b4_point,
          putnam_2019_b4_in_quadrant q ->
          Rabs (fst q - fst p) < delta ->
          Rabs (snd q - snd p) < delta ->
          Rabs (g q - g p) < eps.

Definition putnam_2019_b4_contdiff_two
    (f : putnam_2019_b4_point -> R) : Prop :=
  (forall p : putnam_2019_b4_point,
    putnam_2019_b4_in_quadrant p ->
    putnam_2019_b4_derivable_on_ray
      (fun x : R => f (x, snd p))
      (fst p)
      (putnam_2019_b4_partial_x f p) /\
    putnam_2019_b4_derivable_on_ray
      (fun y : R => f (fst p, y))
      (snd p)
      (putnam_2019_b4_partial_y f p) /\
    putnam_2019_b4_derivable_on_ray
      (fun x : R => putnam_2019_b4_partial_x f (x, snd p))
      (fst p)
      (putnam_2019_b4_partial_xx f p) /\
    putnam_2019_b4_derivable_on_ray
      (fun y : R => putnam_2019_b4_partial_x f (fst p, y))
      (snd p)
      (putnam_2019_b4_partial_xy f p) /\
    putnam_2019_b4_derivable_on_ray
      (fun x : R => putnam_2019_b4_partial_y f (x, snd p))
      (fst p)
      (putnam_2019_b4_partial_yx f p) /\
    putnam_2019_b4_derivable_on_ray
      (fun y : R => putnam_2019_b4_partial_y f (fst p, y))
      (snd p)
      (putnam_2019_b4_partial_yy f p)) /\
  putnam_2019_b4_continuous_on_quadrant f /\
  putnam_2019_b4_continuous_on_quadrant
    (putnam_2019_b4_partial_x f) /\
  putnam_2019_b4_continuous_on_quadrant
    (putnam_2019_b4_partial_y f) /\
  putnam_2019_b4_continuous_on_quadrant
    (putnam_2019_b4_partial_xx f) /\
  putnam_2019_b4_continuous_on_quadrant
    (putnam_2019_b4_partial_xy f) /\
  putnam_2019_b4_continuous_on_quadrant
    (putnam_2019_b4_partial_yx f) /\
  putnam_2019_b4_continuous_on_quadrant
    (putnam_2019_b4_partial_yy f).

Definition putnam_2019_b4_increment
    (f : putnam_2019_b4_point -> R) (s : R) : R :=
  f (s + 1, s + 1) -
  f (s + 1, s) -
  f (s, s + 1) +
  f (s, s).

Definition putnam_2019_b4_is_lower_bound
    (f : putnam_2019_b4_point -> R) (m : R) : Prop :=
  forall s : R,
    1 <= s ->
    m <= putnam_2019_b4_increment f s.

Definition putnam_2019_b4_is_greatest_lower_bound
    (f : putnam_2019_b4_point -> R) (m : R) : Prop :=
  putnam_2019_b4_is_lower_bound f m /\
  forall candidate : R,
    putnam_2019_b4_is_lower_bound f candidate ->
    candidate <= m.

Definition putnam_2019_b4_solution : R :=
  2 * ln 2 - 1 / 2.

Theorem putnam_2019_b4
    (f : putnam_2019_b4_point -> R)
    (fdiff : putnam_2019_b4_contdiff_two f)
    (feq1 :
      forall x y : R,
        1 <= x ->
        1 <= y ->
        x * putnam_2019_b4_partial_x f (x, y) +
        y * putnam_2019_b4_partial_y f (x, y) =
        x * y * ln (x * y))
    (feq2 :
      forall x y : R,
        1 <= x ->
        1 <= y ->
        x ^ 2 * putnam_2019_b4_partial_xx f (x, y) +
        y ^ 2 * putnam_2019_b4_partial_yy f (x, y) =
        x * y) :
  putnam_2019_b4_is_greatest_lower_bound
    f putnam_2019_b4_solution.
Admitted.

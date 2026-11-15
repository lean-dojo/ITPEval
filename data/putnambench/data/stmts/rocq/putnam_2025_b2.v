(* Statement-only formalization of PutnamBench corpus artifact putnam_2025_b2
   (putnambench__rocq__putnam_2025_b2): comparison of the normalized first
   moments determining the centroid abscissas of a planar region and its
   solid of revolution; this file contains no proof. *)

From Stdlib Require Import Reals ClassicalEpsilon RiemannInt.

Open Scope R_scope.

Definition putnam_2025_b2_unit_interval (x : R) : Prop :=
  0 <= x <= 1.

Definition putnam_2025_b2_continuous_on_unit
    (f : R -> R) : Prop :=
  forall x : R,
    putnam_2025_b2_unit_interval x ->
    forall epsilon : R,
      epsilon > 0 ->
      exists delta : R,
        delta > 0 /\
        forall y : R,
          putnam_2025_b2_unit_interval y ->
          Rabs (y - x) < delta ->
          Rabs (f y - f x) < epsilon.

Definition putnam_2025_b2_strictly_increasing_on_unit
    (f : R -> R) : Prop :=
  forall x y : R,
    putnam_2025_b2_unit_interval x ->
    putnam_2025_b2_unit_interval y ->
    x < y ->
    f x < f y.

Definition putnam_2025_b2_unit_integral
    (g : R -> R) : R :=
  epsilon (inhabits (0 : R))
    (fun value : R =>
      exists integrable : Riemann_integrable g 0 1,
        value = RiemannInt integrable).

Theorem putnam_2025_b2
    (f : R -> R)
    (hf_cont : putnam_2025_b2_continuous_on_unit f)
    (hf_mono : putnam_2025_b2_strictly_increasing_on_unit f)
    (hf_nonneg :
      forall x : R,
        putnam_2025_b2_unit_interval x ->
        0 <= f x) :
  putnam_2025_b2_unit_integral (fun x : R => x * f x) /
    putnam_2025_b2_unit_integral f <
  putnam_2025_b2_unit_integral (fun x : R => x * (f x) ^ 2) /
    putnam_2025_b2_unit_integral (fun x : R => (f x) ^ 2).
Admitted.

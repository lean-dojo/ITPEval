/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Manuel Candales
-/
module

public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Tactic.IntervalCases

/-!
# Triangles

This file proves basic geometrical results about distances and angles
in (possibly degenerate) triangles in real inner product spaces and
Euclidean affine spaces. More specialized results, and results
developed for simplices in general rather than just for triangles, are
in separate files. Definitions and results that make sense in more
general affine spaces rather than just in the Euclidean case go under
`LinearAlgebra.AffineSpace`.

## Implementation notes

Results in this file are generally given in a form with only those
non-degeneracy conditions needed for the particular result, rather
than requiring affine independence of the points of a triangle
unnecessarily.

## References

* https://en.wikipedia.org/wiki/Law_of_cosines
* https://en.wikipedia.org/wiki/Pons_asinorum
* https://en.wikipedia.org/wiki/Sum_of_angles_of_a_triangle
* https://en.wikipedia.org/wiki/Law_of_sines

-/

public section

noncomputable section

open scoped CharZero Real RealInnerProductSpace

namespace InnerProductGeometry

/-!
### Geometrical results on triangles in real inner product spaces

This section develops some results on (possibly degenerate) triangles
in real inner product spaces, where those definitions and results can
most conveniently be developed in terms of vectors and then used to
deduce corresponding results for Euclidean affine spaces.
-/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **Law of cosines** (cosine rule), vector angle form. -/
theorem norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_norm_mul_norm_mul_cos_angle (x y : V) :
    ‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ - 2 * ‖x‖ * ‖y‖ * Real.cos (angle x y) := by sorry
theorem sin_angle_mul_norm_eq_sin_angle_mul_norm (x y : V) :
    Real.sin (angle x y) * ‖x‖ = Real.sin (angle y (x - y)) * ‖x - y‖ := by sorry
theorem sin_angle_div_norm_eq_sin_angle_div_norm (x y : V) (hx : x ≠ 0) (hxy : x - y ≠ 0) :
    Real.sin (angle x y) / ‖x - y‖ = Real.sin (angle y (x - y)) / ‖x‖ := by sorry
theorem angle_sub_eq_angle_sub_rev_of_norm_eq {x y : V} (h : ‖x‖ = ‖y‖) :
    angle x (x - y) = angle y (y - x) := by sorry
theorem norm_eq_of_angle_sub_eq_angle_sub_rev_of_angle_ne_pi {x y : V}
    (h : angle x (x - y) = angle y (y - x)) (hpi : angle x y ≠ π) : ‖x‖ = ‖y‖ := by sorry
theorem angle_eq_angle_add_add_angle_add (x : V) {y : V} (hy : y ≠ 0) :
    angle x y = angle x (x + y) + angle y (x + y) := by sorry
theorem angle_add_angle_sub_add_angle_sub_eq_pi (x : V) {y : V} (hy : y ≠ 0) :
    angle x y + angle x (x - y) + angle y (y - x) = π := by sorry
end InnerProductGeometry

namespace Orientation

open Module InnerProductGeometry

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 2)]
variable (o : Orientation ℝ V (Fin 2))

/-- **Converse of pons asinorum**, oriented vector angle form (given equality of angles mod `π`). -/
theorem norm_eq_of_two_zsmul_oangle_sub_eq {x y : V}
    (h : (2 : ℤ) • o.oangle x (x - y) = (2 : ℤ) • o.oangle (y - x) y) (h0 : o.oangle x y ≠ 0)
    (hpi : o.oangle x y ≠ π) : ‖x‖ = ‖y‖ := by sorry
end Orientation

namespace EuclideanGeometry

/-!
### Geometrical results on triangles in Euclidean affine spaces

This section develops some geometrical definitions and results on
(possibly degenerate) triangles in Euclidean affine spaces.
-/

open InnerProductGeometry
open scoped EuclideanGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- **Law of cosines** (cosine rule), angle-at-point form. -/
theorem dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle (p₁ p₂ p₃ : P) :
    dist p₁ p₃ * dist p₁ p₃ = dist p₁ p₂ * dist p₁ p₂ + dist p₃ p₂ * dist p₃ p₂ -
      2 * dist p₁ p₂ * dist p₃ p₂ * Real.cos (∠ p₁ p₂ p₃) := by sorry
theorem sin_angle_mul_dist_eq_sin_angle_mul_dist (p₁ p₂ p₃ : P) :
    Real.sin (∠ p₁ p₂ p₃) * dist p₂ p₃ = Real.sin (∠ p₃ p₁ p₂) * dist p₃ p₁ := by sorry
theorem sin_angle_div_dist_eq_sin_angle_div_dist {p₁ p₂ p₃ : P} (h23 : p₂ ≠ p₃) (h31 : p₃ ≠ p₁) :
    Real.sin (∠ p₁ p₂ p₃) / dist p₃ p₁ = Real.sin (∠ p₃ p₁ p₂) / dist p₂ p₃ := by sorry
theorem dist_eq_dist_mul_sin_angle_div_sin_angle {p₁ p₂ p₃ : P}
    (h : ¬Collinear ℝ ({p₁, p₂, p₃} : Set P)) :
    dist p₁ p₂ = dist p₃ p₁ * Real.sin (∠ p₂ p₃ p₁) / Real.sin (∠ p₁ p₂ p₃) := by sorry
theorem angle_eq_angle_of_dist_eq {p₁ p₂ p₃ : P} (h : dist p₁ p₂ = dist p₁ p₃) :
    ∠ p₁ p₂ p₃ = ∠ p₁ p₃ p₂ := by sorry
theorem dist_eq_of_angle_eq_angle_of_angle_ne_pi {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = ∠ p₁ p₃ p₂)
    (hpi : ∠ p₂ p₁ p₃ ≠ π) : dist p₁ p₂ = dist p₁ p₃ := by sorry
theorem dist_eq_of_two_zsmul_oangle_eq [Module.Oriented ℝ V (Fin 2)]
    [Fact (Module.finrank ℝ V = 2)] {p₁ p₂ p₃ : P} (h : (2 : ℤ) • ∡ p₁ p₂ p₃ = (2 : ℤ) • ∡ p₂ p₃ p₁)
    (h0 : ∡ p₃ p₁ p₂ ≠ 0) (hpi : ∡ p₃ p₁ p₂ ≠ π) : dist p₁ p₂ = dist p₁ p₃ := by sorry
theorem angle_add_angle_add_angle_eq_pi {p₁ p₂ : P} (p₃ : P) (h : p₂ ≠ p₁) :
    ∠ p₁ p₂ p₃ + ∠ p₂ p₃ p₁ + ∠ p₃ p₁ p₂ = π := by sorry
theorem exterior_angle_eq_angle_add_angle {p₁ p₂ p₃ : P} (p : P) (h : Sbtw ℝ p p₁ p₂) :
    ∠ p₃ p₁ p = ∠ p₁ p₃ p₂ + ∠ p₃ p₂ p₁ := by sorry
theorem oangle_add_oangle_add_oangle_eq_pi [Module.Oriented ℝ V (Fin 2)]
    [Fact (Module.finrank ℝ V = 2)] {p₁ p₂ p₃ : P} (h21 : p₂ ≠ p₁) (h32 : p₃ ≠ p₂)
    (h13 : p₁ ≠ p₃) : ∡ p₁ p₂ p₃ + ∡ p₂ p₃ p₁ + ∡ p₃ p₁ p₂ = π := by sorry
lemma angle_add_of_ne_of_ne {a b c p : P} (hb : a ≠ b) (hc : a ≠ c) (hp : Wbtw ℝ b p c) :
    ∠ b a p + ∠ p a c = ∠ b a c := by sorry
theorem dist_sq_mul_dist_add_dist_sq_mul_dist (a b c p : P) (h : ∠ b p c = π) :
    dist a b ^ 2 * dist c p + dist a c ^ 2 * dist b p =
    dist b c * (dist a p ^ 2 + dist b p * dist c p) := by sorry
theorem dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq (a b c : P) :
    dist a b ^ 2 + dist a c ^ 2 = 2 * (dist a (midpoint ℝ b c) ^ 2 + (dist b c / 2) ^ 2) := by sorry
theorem dist_mul_of_eq_angle_of_dist_mul (a b c a' b' c' : P) (r : ℝ) (h : ∠ a' b' c' = ∠ a b c)
    (hab : dist a' b' = r * dist a b) (hcb : dist c' b' = r * dist c b) :
    dist a' c' = r * dist a c := by sorry
theorem dist_lt_of_angle_lt {a b c : P} (h : ¬Collinear ℝ ({a, b, c} : Set P)) :
    ∠ a c b < ∠ a b c → dist a b < dist a c := by sorry
theorem angle_lt_iff_dist_lt {a b c : P} (h : ¬Collinear ℝ ({a, b, c} : Set P)) :
    ∠ a c b < ∠ a b c ↔ dist a b < dist a c := by sorry
theorem angle_le_iff_dist_le {a b c : P} (h : ¬Collinear ℝ ({a, b, c} : Set P)) :
    ∠ a c b ≤ ∠ a b c ↔ dist a b ≤ dist a c := by sorry
lemma pi_div_three_le_angle_of_le_of_le {p₁ p₂ p₃ : P} (h₂₃₁ : ∠ p₂ p₃ p₁ ≤ ∠ p₁ p₂ p₃)
    (h₃₁₂ : ∠ p₃ p₁ p₂ ≤ ∠ p₁ p₂ p₃) : π / 3 ≤ ∠ p₁ p₂ p₃ := by sorry
lemma pi_div_three_lt_angle_of_le_of_le_of_ne {p₁ p₂ p₃ : P} (h₂₃₁ : ∠ p₂ p₃ p₁ ≤ ∠ p₁ p₂ p₃)
    (h₃₁₂ : ∠ p₃ p₁ p₂ ≤ ∠ p₁ p₂ p₃)
    (hne : ∠ p₁ p₂ p₃ ≠ ∠ p₂ p₃ p₁ ∨ ∠ p₁ p₂ p₃ ≠ ∠ p₃ p₁ p₂ ∨ ∠ p₂ p₃ p₁ ≠ ∠ p₃ p₁ p₂) :
    π / 3 < ∠ p₁ p₂ p₃ := by sorry
lemma angle_le_pi_div_three_of_le_of_le {p₁ p₂ p₃ : P} (h₂₃₁ : ∠ p₁ p₂ p₃ ≤ ∠ p₂ p₃ p₁)
    (h₃₁₂ : ∠ p₁ p₂ p₃ ≤ ∠ p₃ p₁ p₂) (hnd : p₁ ≠ p₂ ∨ p₁ ≠ p₃ ∨ p₂ ≠ p₃) :
    ∠ p₁ p₂ p₃ ≤ π / 3 := by sorry
lemma angle_lt_pi_div_three_of_le_of_le_of_ne {p₁ p₂ p₃ : P} (h₂₃₁ : ∠ p₁ p₂ p₃ ≤ ∠ p₂ p₃ p₁)
    (h₃₁₂ : ∠ p₁ p₂ p₃ ≤ ∠ p₃ p₁ p₂)
    (hne : ∠ p₁ p₂ p₃ ≠ ∠ p₂ p₃ p₁ ∨ ∠ p₁ p₂ p₃ ≠ ∠ p₃ p₁ p₂ ∨ ∠ p₂ p₃ p₁ ≠ ∠ p₃ p₁ p₂) :
    ∠ p₁ p₂ p₃ < π / 3 := by sorry
end EuclideanGeometry

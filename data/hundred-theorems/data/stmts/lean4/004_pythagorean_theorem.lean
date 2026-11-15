/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine

/-!
# Right-angled triangles

This file proves basic geometric results about distances and angles in (possibly degenerate)
right-angled triangles in real inner product spaces and Euclidean affine spaces.

## Implementation notes

Results in this file are generally given in a form with only those non-degeneracy conditions
needed for the particular result, rather than requiring affine independence of the points of a
triangle unnecessarily.

## References

* https://en.wikipedia.org/wiki/Pythagorean_theorem

-/

public section


noncomputable section

open scoped EuclideanGeometry

open scoped Real

open scoped RealInnerProductSpace

namespace InnerProductGeometry

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Pythagorean theorem, if-and-only-if vector angle form. -/
theorem norm_add_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two (x y : V) :
    ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ ↔ angle x y = π / 2 := by sorry
theorem norm_add_sq_eq_norm_sq_add_norm_sq' (x y : V) (h : angle x y = π / 2) :
    ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ :=
  (norm_add_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two x y).2 h

/-- Pythagorean theorem, subtracting vectors, if-and-only-if vector angle form. -/
theorem norm_sub_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two (x y : V) :
    ‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ ↔ angle x y = π / 2 := by sorry
theorem norm_sub_sq_eq_norm_sq_add_norm_sq' (x y : V) (h : angle x y = π / 2) :
    ‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ :=
  (norm_sub_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two x y).2 h

/-- An angle in a right-angled triangle expressed using `arccos`. -/
theorem angle_add_eq_arccos_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
    angle x (x + y) = Real.arccos (‖x‖ / ‖x + y‖) := by sorry
theorem angle_add_eq_arcsin_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x ≠ 0 ∨ y ≠ 0) :
    angle x (x + y) = Real.arcsin (‖y‖ / ‖x + y‖) := by sorry
theorem angle_add_eq_arctan_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x ≠ 0) :
    angle x (x + y) = Real.arctan (‖y‖ / ‖x‖) := by sorry
theorem angle_add_pos_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x = 0 ∨ y ≠ 0) :
    0 < angle x (x + y) := by sorry
theorem angle_add_le_pi_div_two_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
    angle x (x + y) ≤ π / 2 := by sorry
theorem angle_add_lt_pi_div_two_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x ≠ 0) :
    angle x (x + y) < π / 2 := by sorry
theorem cos_angle_add_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
    Real.cos (angle x (x + y)) = ‖x‖ / ‖x + y‖ := by sorry
theorem sin_angle_add_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x ≠ 0 ∨ y ≠ 0) :
    Real.sin (angle x (x + y)) = ‖y‖ / ‖x + y‖ := by sorry
theorem tan_angle_add_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
    Real.tan (angle x (x + y)) = ‖y‖ / ‖x‖ := by sorry
theorem cos_angle_add_mul_norm_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
    Real.cos (angle x (x + y)) * ‖x + y‖ = ‖x‖ := by sorry
theorem sin_angle_add_mul_norm_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
    Real.sin (angle x (x + y)) * ‖x + y‖ = ‖y‖ := by sorry
theorem tan_angle_add_mul_norm_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x ≠ 0 ∨ y = 0) :
    Real.tan (angle x (x + y)) * ‖x‖ = ‖y‖ := by sorry
theorem norm_div_cos_angle_add_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x ≠ 0 ∨ y = 0) :
    ‖x‖ / Real.cos (angle x (x + y)) = ‖x + y‖ := by sorry
theorem norm_div_sin_angle_add_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x = 0 ∨ y ≠ 0) :
    ‖y‖ / Real.sin (angle x (x + y)) = ‖x + y‖ := by sorry
theorem norm_div_tan_angle_add_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x = 0 ∨ y ≠ 0) :
    ‖y‖ / Real.tan (angle x (x + y)) = ‖x‖ := by sorry
theorem angle_sub_eq_arccos_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
    angle x (x - y) = Real.arccos (‖x‖ / ‖x - y‖) := by sorry
theorem angle_sub_eq_arcsin_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x ≠ 0 ∨ y ≠ 0) :
    angle x (x - y) = Real.arcsin (‖y‖ / ‖x - y‖) := by sorry
theorem angle_sub_eq_arctan_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x ≠ 0) :
    angle x (x - y) = Real.arctan (‖y‖ / ‖x‖) := by sorry
theorem angle_sub_pos_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x = 0 ∨ y ≠ 0) :
    0 < angle x (x - y) := by sorry
theorem angle_sub_le_pi_div_two_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
    angle x (x - y) ≤ π / 2 := by sorry
theorem angle_sub_lt_pi_div_two_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x ≠ 0) :
    angle x (x - y) < π / 2 := by sorry
theorem cos_angle_sub_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
    Real.cos (angle x (x - y)) = ‖x‖ / ‖x - y‖ := by sorry
theorem sin_angle_sub_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x ≠ 0 ∨ y ≠ 0) :
    Real.sin (angle x (x - y)) = ‖y‖ / ‖x - y‖ := by sorry
theorem tan_angle_sub_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
    Real.tan (angle x (x - y)) = ‖y‖ / ‖x‖ := by sorry
theorem cos_angle_sub_mul_norm_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
    Real.cos (angle x (x - y)) * ‖x - y‖ = ‖x‖ := by sorry
theorem sin_angle_sub_mul_norm_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
    Real.sin (angle x (x - y)) * ‖x - y‖ = ‖y‖ := by sorry
theorem tan_angle_sub_mul_norm_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x ≠ 0 ∨ y = 0) :
    Real.tan (angle x (x - y)) * ‖x‖ = ‖y‖ := by sorry
theorem norm_div_cos_angle_sub_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x ≠ 0 ∨ y = 0) :
    ‖x‖ / Real.cos (angle x (x - y)) = ‖x - y‖ := by sorry
theorem norm_div_sin_angle_sub_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x = 0 ∨ y ≠ 0) :
    ‖y‖ / Real.sin (angle x (x - y)) = ‖x - y‖ := by sorry
theorem norm_div_tan_angle_sub_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x = 0 ∨ y ≠ 0) :
    ‖y‖ / Real.tan (angle x (x - y)) = ‖x‖ := by sorry
end InnerProductGeometry

namespace EuclideanGeometry

open InnerProductGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- **Pythagorean theorem**, if-and-only-if angle-at-point form. -/
theorem dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two (p₁ p₂ p₃ : P) :
    dist p₁ p₃ * dist p₁ p₃ = dist p₁ p₂ * dist p₁ p₂ + dist p₃ p₂ * dist p₃ p₂ ↔
      ∠ p₁ p₂ p₃ = π / 2 := by sorry
theorem angle_eq_arccos_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) :
    ∠ p₂ p₃ p₁ = Real.arccos (dist p₃ p₂ / dist p₁ p₃) := by sorry
theorem angle_eq_arcsin_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
    (h0 : p₁ ≠ p₂ ∨ p₃ ≠ p₂) : ∠ p₂ p₃ p₁ = Real.arcsin (dist p₁ p₂ / dist p₁ p₃) := by sorry
theorem angle_eq_arctan_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
    (h0 : p₃ ≠ p₂) : ∠ p₂ p₃ p₁ = Real.arctan (dist p₁ p₂ / dist p₃ p₂) := by sorry
theorem angle_pos_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
    (h0 : p₁ ≠ p₂ ∨ p₃ = p₂) : 0 < ∠ p₂ p₃ p₁ := by sorry
theorem angle_le_pi_div_two_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) :
    ∠ p₂ p₃ p₁ ≤ π / 2 := by sorry
theorem angle_lt_pi_div_two_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
    (h0 : p₃ ≠ p₂) : ∠ p₂ p₃ p₁ < π / 2 := by sorry
theorem cos_angle_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) :
    Real.cos (∠ p₂ p₃ p₁) = dist p₃ p₂ / dist p₁ p₃ := by sorry
theorem sin_angle_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
    (h0 : p₁ ≠ p₂ ∨ p₃ ≠ p₂) : Real.sin (∠ p₂ p₃ p₁) = dist p₁ p₂ / dist p₁ p₃ := by sorry
theorem tan_angle_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) :
    Real.tan (∠ p₂ p₃ p₁) = dist p₁ p₂ / dist p₃ p₂ := by sorry
theorem cos_angle_mul_dist_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) :
    Real.cos (∠ p₂ p₃ p₁) * dist p₁ p₃ = dist p₃ p₂ := by sorry
theorem sin_angle_mul_dist_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) :
    Real.sin (∠ p₂ p₃ p₁) * dist p₁ p₃ = dist p₁ p₂ := by sorry
theorem tan_angle_mul_dist_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
    (h0 : p₁ = p₂ ∨ p₃ ≠ p₂) : Real.tan (∠ p₂ p₃ p₁) * dist p₃ p₂ = dist p₁ p₂ := by sorry
theorem dist_div_cos_angle_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
    (h0 : p₁ = p₂ ∨ p₃ ≠ p₂) : dist p₃ p₂ / Real.cos (∠ p₂ p₃ p₁) = dist p₁ p₃ := by sorry
theorem dist_div_sin_angle_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
    (h0 : p₁ ≠ p₂ ∨ p₃ = p₂) : dist p₁ p₂ / Real.sin (∠ p₂ p₃ p₁) = dist p₁ p₃ := by sorry
theorem dist_div_tan_angle_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
    (h0 : p₁ ≠ p₂ ∨ p₃ = p₂) : dist p₁ p₂ / Real.tan (∠ p₂ p₃ p₁) = dist p₃ p₂ := by sorry
end EuclideanGeometry

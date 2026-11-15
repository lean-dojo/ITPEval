/-
Copyright (c) 2021 Manuel Candales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Candales, Benjamin Davidson, Li Jiale
-/
module


public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Geometry.Euclidean.Sphere.Tangent

import Mathlib.Geometry.Euclidean.Angle.Sphere
import Mathlib.Geometry.Euclidean.Similarity

/-!
# Power of a point (intersecting chords and secants)

This file proves basic geometrical results about power of a point (intersecting chords and
secants) in spheres in real inner product spaces and Euclidean affine spaces.

## Main definitions

* `Sphere.power`: The power of a point with respect to a sphere.

## Main theorems

* `mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_pi`: Intersecting Chords Theorem (Freek No. 55).
* `mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_zero`: Intersecting Secants Theorem.
* `Sphere.mul_dist_eq_abs_power`: The product of distances equals the absolute value of power.
* `Sphere.dist_sq_eq_mul_dist_of_tangent_and_secant`: Tangent-Secant Theorem.
-/

@[expose] public section


open Real EuclideanGeometry RealInnerProductSpace Real Module FiniteDimensional

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

namespace InnerProductGeometry

/-!
### Geometrical results on spheres in real inner product spaces

This section develops some results on spheres in real inner product spaces,
which are used to deduce corresponding results for Euclidean affine spaces.
-/


theorem mul_norm_eq_abs_sub_sq_norm {x y z : V} (h₁ : ∃ k : ℝ, x = k • y)
    (h₃ : ‖z - y‖ = ‖z + y‖) : ‖x - y‖ * ‖x + y‖ = |‖z + y‖ ^ 2 - ‖z - x‖ ^ 2| := by sorry
end InnerProductGeometry

namespace EuclideanGeometry

/-!
### Geometrical results on spheres in Euclidean affine spaces

This section develops some results on spheres in Euclidean affine spaces.
-/


open InnerProductGeometry EuclideanGeometry

variable {P : Type*} [MetricSpace P] [NormedAddTorsor V P]

/-- If `P` is a point on the line `AB` and `Q` is equidistant from `A` and `B`, then
`AP * BP = abs (BQ ^ 2 - PQ ^ 2)`. -/
theorem mul_dist_eq_abs_sub_sq_dist {a b p q : P} (hp : p ∈ line[ℝ, a, b])
    (hq : dist a q = dist b q) : dist a p * dist b p = |dist b q ^ 2 - dist p q ^ 2| := by sorry
theorem mul_dist_eq_mul_dist_of_cospherical {a b c d p : P} (h : Cospherical ({a, b, c, d} : Set P))
    (hapb : p ∈ line[ℝ, a, b]) (hcpd : p ∈ line[ℝ, c, d]) :
    dist a p * dist b p = dist c p * dist d p := by sorry
theorem mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_pi {a b c d p : P}
    (h : Cospherical ({a, b, c, d} : Set P)) (hapb : ∠ a p b = π) (hcpd : ∠ c p d = π) :
    dist a p * dist b p = dist c p * dist d p := by sorry
theorem cospherical_of_mul_dist_eq_mul_dist_of_angle_eq_pi {p₁ p₂ p₃ p₄ p : P}
    (h : dist p₁ p * dist p₂ p = dist p₃ p * dist p₄ p)
    (hp₁p₂ : ∠ p₁ p p₂ = π) (hp₃p₄ : ∠ p₃ p p₄ = π) (hn : ¬ Collinear ℝ ({p₁, p, p₃} : Set P)) :
    Cospherical ({p₁, p₂, p₃, p₄} : Set P) := by sorry
    #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
    (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal.
    It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in the new
    canonicalizer; a minimization would help. The original proof was:
    `grind [Set.image_insert_eq, Set.image_singleton]` -/
    simpa [Set.image_insert_eq, Set.image_singleton] using Cospherical.subtype_val h_cospherical'
  have hf2 : Fact (finrank ℝ S.direction = 2) := ⟨by
    rw [hS, direction_affineSpan, t.independent.finrank_vectorSpan]
    simp⟩
  letI : Module.Oriented ℝ S.direction (Fin 2) :=
    ⟨Basis.orientation (finBasisOfFinrankEq _ _ hf2.out)⟩
  have hncol : ¬ Collinear ℝ {p₁', p', p₃'} := by sorry
theorem mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_zero {a b c d p : P}
    (h : Cospherical ({a, b, c, d} : Set P)) (hab : a ≠ b) (hcd : c ≠ d) (hapb : ∠ a p b = 0)
    (hcpd : ∠ c p d = 0) : dist a p * dist b p = dist c p * dist d p := by sorry
namespace Sphere

/-- The power of a point with respect to a sphere. For a point and a sphere,
this is defined as the square of the distance from the point to the center
minus the square of the radius. This value is positive if the point is outside
the sphere, negative if inside, and zero if on the sphere. -/
def power (s : Sphere P) (p : P) : ℝ :=
  dist p s.center ^ 2 - s.radius ^ 2

/-- A point lies on the sphere if and only if its power with respect to
the sphere is zero. -/
theorem power_eq_zero_iff_mem_sphere {s : Sphere P} {p : P} (hr : 0 ≤ s.radius) :
    s.power p = 0 ↔ p ∈ s := by sorry
theorem power_pos_iff_radius_lt_dist_center {s : Sphere P} {p : P} (hr : 0 ≤ s.radius) :
    0 < s.power p ↔ s.radius < dist p s.center := by sorry
theorem power_neg_iff_dist_center_lt_radius {s : Sphere P} {p : P} (hr : 0 ≤ s.radius) :
  s.power p < 0 ↔ dist p s.center < s.radius := by sorry
theorem power_nonneg_iff_radius_le_dist_center {s : Sphere P} {p : P} (hr : 0 ≤ s.radius) :
    0 ≤ s.power p ↔ s.radius ≤ dist p s.center := by sorry
theorem power_nonpos_iff_dist_center_le_radius {s : Sphere P} {p : P} (hr : 0 ≤ s.radius) :
    s.power p ≤ 0 ↔ dist p s.center ≤ s.radius := by sorry
theorem mul_dist_eq_abs_power {s : Sphere P} {p a b : P}
    (hp : p ∈ line[ℝ, a, b])
    (ha : a ∈ s) (hb : b ∈ s) :
    dist p a * dist p b = |s.power p| := by sorry
theorem mul_dist_eq_zero_of_mem_sphere {s : Sphere P} {p a b : P}
    (hp : p ∈ line[ℝ, a, b])
    (ha : a ∈ s) (hb : b ∈ s)
    (hp_on : p ∈ s) :
    dist p a * dist p b = 0 := by sorry
theorem mul_dist_eq_power_of_radius_le_dist_center {s : Sphere P} {p a b : P}
    (hr : 0 ≤ s.radius)
    (hp : p ∈ line[ℝ, a, b])
    (ha : a ∈ s) (hb : b ∈ s)
    (hle : s.radius ≤ dist p s.center) :
    dist p a * dist p b = s.power p := by sorry
theorem mul_dist_eq_neg_power_of_dist_center_le_radius {s : Sphere P} {p a b : P}
    (hr : 0 ≤ s.radius)
    (hp : p ∈ line[ℝ, a, b])
    (ha : a ∈ s) (hb : b ∈ s)
    (hle : dist p s.center ≤ s.radius) :
    dist p a * dist p b = -s.power p := by sorry
theorem dist_sq_eq_mul_dist_of_tangent_and_secant {a b t p : P} {s : Sphere P}
    (ha : a ∈ s) (hb : b ∈ s)
    (hp : p ∈ line[ℝ, a, b])
    (h_tangent : s.IsTangentAt t (line[ℝ, p, t])) :
    dist p t ^ 2 = dist p a * dist p b := by sorry
theorem IsTangentAt.power_eq_dist_sq {s : Sphere P} {t p : P}
    (h_tangent : s.IsTangentAt t (line[ℝ, p, t])) :
    s.power p = dist p t ^ 2 := by sorry
theorem isTangentAt_iff_dist_sq_eq_power {t p : P} {s : Sphere P} (ht : t ∈ s) :
    s.IsTangentAt t (line[ℝ, p, t]) ↔ dist p t ^ 2 = s.power p :=
  ⟨fun h ↦ h.power_eq_dist_sq.symm, fun h_dist_eq ↦ by
    have h_orth : ⟪p -ᵥ t, t -ᵥ s.center⟫ = 0 := by sorry
end Sphere

end EuclideanGeometry

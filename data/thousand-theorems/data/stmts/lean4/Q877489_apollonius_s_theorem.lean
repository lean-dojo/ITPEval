-- Canonical Lean registration for Thousand Theorems artifact Q877489,
-- "Apollonius's theorem". The statement is copied exactly from
-- the imported `EuclideanGeometry.dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq`; the body reuses Mathlib's checked proof.

module

public import Mathlib.Geometry.Euclidean.Triangle

@[expose] public section

namespace ThousandTheorems.Q877489

/-- The Mathlib statement selected as the canonical Lean form of Apollonius's theorem. -/
theorem canonical_statement : type_of% @EuclideanGeometry.dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq :=
  @EuclideanGeometry.dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq

end ThousandTheorems.Q877489

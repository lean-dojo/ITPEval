-- Canonical Lean registration for Thousand Theorems artifact Q739403,
-- "Stewart's theorem". The statement is copied exactly from
-- the imported `EuclideanGeometry.dist_sq_mul_dist_add_dist_sq_mul_dist`; the body reuses Mathlib's checked proof.

module

public import Mathlib.Geometry.Euclidean.Triangle

@[expose] public section

namespace ThousandTheorems.Q739403

/-- The Mathlib statement selected as the canonical Lean form of Stewart's theorem. -/
theorem canonical_statement : type_of% @EuclideanGeometry.dist_sq_mul_dist_add_dist_sq_mul_dist :=
  @EuclideanGeometry.dist_sq_mul_dist_add_dist_sq_mul_dist

end ThousandTheorems.Q739403

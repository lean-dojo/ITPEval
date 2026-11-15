-- Canonical Lean registration for Thousand Theorems artifact Q2226868,
-- "Geometric mean theorem". The statement is copied exactly from
-- the imported `EuclideanGeometry.dist_sq_eq_dist_mul_dist_of_angle_eq_pi_div_two`; the body reuses Mathlib's checked proof.

module

public import Mathlib.Geometry.Euclidean.Angle.Unoriented.RightAngle

@[expose] public section

namespace ThousandTheorems.Q2226868

/-- The Mathlib statement selected as the canonical Lean form of Geometric mean theorem. -/
theorem canonical_statement :
    type_of% @EuclideanGeometry.dist_sq_eq_dist_mul_dist_of_angle_eq_pi_div_two :=
  @EuclideanGeometry.dist_sq_eq_dist_mul_dist_of_angle_eq_pi_div_two

end ThousandTheorems.Q2226868

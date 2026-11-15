-- Canonical Lean registration for Thousand Theorems artifact Q5421989,
-- "Exterior angle theorem". The statement is copied exactly from
-- the imported `EuclideanGeometry.exterior_angle_eq_angle_add_angle`; the body reuses Mathlib's checked proof.

module

public import Mathlib.Geometry.Euclidean.Triangle

@[expose] public section

namespace ThousandTheorems.Q5421989

/-- The Mathlib statement selected as the canonical Lean form of Exterior angle theorem. -/
theorem canonical_statement : type_of% @EuclideanGeometry.exterior_angle_eq_angle_add_angle :=
  @EuclideanGeometry.exterior_angle_eq_angle_add_angle

end ThousandTheorems.Q5421989

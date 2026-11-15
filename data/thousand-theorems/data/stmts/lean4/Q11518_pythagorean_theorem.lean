-- Statement-only formalization of Thousand Theorems artifact Q11518
-- (thousand-theorems__lean4__Q11518), "Pythagorean theorem": for three points in a
-- real Euclidean affine space, the squared-distance identity holds exactly when
-- the displacement vectors from the second point are orthogonal, equivalently when
-- the angle there is π / 2. This file contains no proof.

module

public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Group.Defs

@[expose] public section

namespace Q11518

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P]

/-- The Pythagorean theorem, with the right-angle condition encoded by orthogonality. -/
theorem dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two (p₁ p₂ p₃ : P) :
    dist p₁ p₃ * dist p₁ p₃ = dist p₁ p₂ * dist p₁ p₂ + dist p₃ p₂ * dist p₃ p₂ ↔
      inner ℝ (p₁ -ᵥ p₂ : V) (p₃ -ᵥ p₂ : V) = 0 := sorry

end Q11518

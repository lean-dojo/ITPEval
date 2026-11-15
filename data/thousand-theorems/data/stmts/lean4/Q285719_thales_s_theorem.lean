-- Statement-only formalization of Thousand Theorems artifact Q285719
-- (thousand-theorems__lean4__Q285719), "Thales's theorem": the angle subtended
-- at a point by the endpoints of a sphere's diameter is a right angle exactly
-- when that point lies on the sphere, with right angles encoded by zero inner
-- product. This file contains no proof.

module

public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Group.Defs

@[expose] public section

namespace Q285719

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P]

structure Sphere (P : Type*) where
  center : P
  radius : ℝ

namespace Sphere

/-- Membership in the metric sphere with the bundled center and radius. -/
def Mem {P : Type*} [MetricSpace P] (s : Sphere P) (p : P) : Prop :=
  dist p s.center = s.radius

instance {P : Type*} [MetricSpace P] : Membership P (Sphere P) where
  mem s p := s.Mem p

/-- The endpoints lie oppositely about the center, equivalently their midpoint is the center. -/
structure IsDiameter {V P : Type*} [NormedAddCommGroup V] [MetricSpace P]
    [NormedAddTorsor V P] (s : Sphere P) (p₁ p₃ : P) : Prop where
  left_mem : p₁ ∈ s
  endpoints_opposite : (p₁ -ᵥ s.center : V) = -(p₃ -ᵥ s.center : V)

end Sphere

/-- Thales's theorem, with a right angle represented by orthogonality. -/
theorem thales_theorem {p₁ p₂ p₃ : P} {s : Sphere P}
    (hd : s.IsDiameter (V := V) p₁ p₃) :
    inner ℝ (p₁ -ᵥ p₂ : V) (p₃ -ᵥ p₂ : V) = 0 ↔ p₂ ∈ s := sorry

end Q285719

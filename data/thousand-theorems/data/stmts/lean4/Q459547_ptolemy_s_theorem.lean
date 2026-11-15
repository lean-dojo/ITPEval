-- Statement-only formalization of Thousand Theorems artifact Q459547
-- (thousand-theorems__lean4__Q459547), "Ptolemy's theorem": four cospherical
-- points whose diagonals meet at a point with straight angles satisfy the
-- classical equality relating the products of side and diagonal lengths.
-- This file contains no proof.

module

public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Group.Defs

@[expose] public section

open scoped RealInnerProductSpace Real

namespace Q459547

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {P : Type*} [MetricSpace P] [NormedAddTorsor V P]

/-- The defining common-center-and-radius condition for a cospherical set. -/
def Cospherical (ps : Set P) : Prop :=
  ∃ (center : P) (radius : ℝ), ∀ q ∈ ps, dist q center = radius

/--
The exact antiparallel-vector characterization of the affine angle
`∠ p₁ p₂ p₃ = π`.
-/
def AngleEqPi (p₁ p₂ p₃ : P) : Prop :=
  (p₁ -ᵥ p₂ : V) ≠ 0 ∧
    ∃ r : ℝ, r < 0 ∧ (p₃ -ᵥ p₂ : V) = r • (p₁ -ᵥ p₂ : V)

/-- Ptolemy's theorem for four cospherical points with intersecting diagonals. -/
theorem ptolemy_s_theorem {a b c d p : P}
    (h : Cospherical ({a, b, c, d} : Set P))
    (hapc : AngleEqPi (V := V) a p c) (hbpd : AngleEqPi (V := V) b p d) :
    dist a b * dist c d + dist b c * dist d a = dist a c * dist b d := sorry

end Q459547

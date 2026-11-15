-- Statement-only formalization of Thousand Theorems artifact Q3527250
-- (thousand-theorems__lean4__Q3527250), "Hadamard three-lines theorem": a bounded
-- function that is continuous on a closed vertical strip and complex differentiable on
-- its interior is bounded by the interpolation of its boundary suprema. This file contains no proof.

module

public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.Complex.Trigonometric

@[expose] public section

open Set Filter Function Complex Topology

-- These two instances reproduce the canonical complex normed-field instances, which are
-- unavailable through the statement checker's reduced Mathlib module graph.
noncomputable local instance : NormedField ℂ where
  dist_eq _ _ := rfl
  norm_mul := Complex.norm_mul

noncomputable local instance : NontriviallyNormedField ℂ where
  non_trivial := ⟨2, Complex.norm_two.symm ▸ one_lt_two⟩

/-- A function differentiable on a set and continuous on its closure. -/
structure DiffContOnCl (𝕜 : Type*) {E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    (f : E → F) (s : Set E) : Prop where
  protected differentiableOn : DifferentiableOn 𝕜 f s
  protected continuousOn : ContinuousOn f (closure s)

namespace Complex
namespace HadamardThreeLines

/-- The order-theoretic inverse of the real exponential on a positive input. -/
noncomputable def realLog (x : ℝ) : ℝ :=
  sSup {y : ℝ | Real.exp y ≤ x}

/-- The canonical complex power for a nonnegative real base, including the standard zero branch. -/
noncomputable def realCpow (x : ℝ) (y : ℂ) : ℂ :=
  if x = 0 then if y = 0 then 1 else 0
  else Complex.exp (realLog x * y)

/-- The open vertical strip consisting of complex numbers whose real parts lie in `(a, b)`. -/
def verticalStrip (a b : ℝ) : Set ℂ := re ⁻¹' Ioo a b

/-- The closed vertical strip consisting of complex numbers whose real parts lie in `[a, b]`. -/
def verticalClosedStrip (a b : ℝ) : Set ℂ := re ⁻¹' Icc a b

/-- The supremum of the norm of `f` along the vertical line with real part `x`. -/
noncomputable def sSupNormIm {E : Type*} [NormedAddCommGroup E]
    (f : ℂ → E) (x : ℝ) : ℝ :=
  sSup ((norm ∘ f) '' (re ⁻¹' {x}))

/-- The interpolation of the boundary suprema on the vertical strip from `l` to `u`. -/
noncomputable def interpStrip' {E : Type*} [NormedAddCommGroup E]
    (f : ℂ → E) (l u : ℝ) (z : ℂ) : ℂ :=
  -- `sSupNormIm` is nonnegative, so `realCpow` agrees here with Mathlib's real-base
  -- specialization of `Complex.cpow`.
  if sSupNormIm f l = 0 ∨ sSupNormIm f u = 0 then
    0
  else
    realCpow (sSupNormIm f l) (1 - ((z - l) / (u - l))) *
      realCpow (sSupNormIm f u) ((z - l) / (u - l))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Hadamard's three-lines theorem on an arbitrary vertical strip. -/
lemma norm_le_interpStrip_of_mem_verticalClosedStrip {l u : ℝ} (hul : l < u)
    {f : ℂ → E} {z : ℂ}
    (hz : z ∈ verticalClosedStrip l u) (hd : DiffContOnCl ℂ f (verticalStrip l u))
    (hB : BddAbove ((norm ∘ f) '' verticalClosedStrip l u)) :
    ‖f z‖ ≤ ‖interpStrip' f l u z‖ := sorry

end HadamardThreeLines
end Complex

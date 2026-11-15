-- Statement-only formalization of Thousand Theorems artifact Q4378868
-- (thousand-theorems__lean4__Q4378868), "Phragmén–Lindelöf theorem": the
-- Phragmén–Lindelöf principle bounds a complex-differentiable normed-space-valued
-- function throughout a closed horizontal strip from its boundary bound, under a
-- controlled double-exponential growth condition. This file contains no proof.

module

public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

open Set Function Filter Asymptotics Metric Complex Bornology
open scoped Topology Filter Real

local notation "expR" => Real.exp

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

namespace PhragmenLindelof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {a b C : ℝ} {f : ℂ → E} {z : ℂ}

/-- The Phragmén–Lindelöf principle for a function on a horizontal strip. -/
theorem horizontal_strip (hfd : DiffContOnCl ℂ f (im ⁻¹' Ioo a b))
    (hB : ∃ c < Real.pi / (b - a), ∃ B,
      f =O[comap (_root_.abs ∘ re) atTop ⊓ 𝓟 (im ⁻¹' Ioo a b)]
        fun w ↦ expR (B * expR (c * |w.re|)))
    (hle_a : ∀ w : ℂ, im w = a → ‖f w‖ ≤ C)
    (hle_b : ∀ w : ℂ, im w = b → ‖f w‖ ≤ C)
    (hza : a ≤ im z) (hzb : im z ≤ b) : ‖f z‖ ≤ C := sorry

end PhragmenLindelof

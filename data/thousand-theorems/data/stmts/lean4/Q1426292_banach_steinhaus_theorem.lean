-- Statement-only formalization of Thousand Theorems artifact Q1426292
-- (thousand-theorems__lean4__Q1426292), "Banach–Steinhaus theorem": a pointwise
-- bounded family of continuous semilinear maps from a Banach space is uniformly
-- bounded in operator norm. This file contains no proof.

module

public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.LocallyConvex.Barrelled
public import Mathlib.Topology.Baire.CompleteMetrizable

@[expose] public section

variable {E F 𝕜 𝕜₂ : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
  [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NormedSpace 𝕜 E]
  [NormedSpace 𝕜₂ F] {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂]

/-- The Banach–Steinhaus theorem, or uniform boundedness principle. -/
theorem banach_steinhaus {ι : Type*} [CompleteSpace E] {g : ι → E →SL[σ₁₂] F}
    (h : ∀ x, ∃ C, ∀ i, ‖g i x‖ ≤ C) : ∃ C', ∀ i, ‖g i‖ ≤ C' := sorry

-- Statement-only formalization of Thousand Theorems artifact Q6813106
-- (thousand-theorems__lean4__Q6813106), "Mellin inversion theorem": the inverse
-- Mellin transform of the Mellin transform recovers a function at a positive point
-- under the source convergence, integrability, and continuity hypotheses.
-- This file contains no proof.

module

public import Mathlib.Analysis.MellinTransform

@[expose] public section

open Real Complex Set MeasureTheory

namespace Q6813106

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Mellin inversion at a positive point. -/
theorem mellin_inversion (σ : ℝ) (f : ℝ → E) {x : ℝ} (hx : 0 < x)
    (hf : MellinConvergent f σ) (hFf : VerticalIntegrable (mellin f) σ)
    (hfx : ContinuousAt f x) :
    mellinInv σ (mellin f) x = f x := sorry

end Q6813106

-- Statement-only formalization of Thousand Theorems artifact Q3984053
-- (thousand-theorems__lean4__Q3984053), "Fourier inversion theorem": the inverse
-- Fourier transform recovers a continuous integrable function whose Fourier transform
-- is integrable. This file contains no proof.

module

public import Mathlib.Analysis.Fourier.Inversion

@[expose] public section

open MeasureTheory

open scoped FourierTransform RealInnerProductSpace

namespace Q3984053

variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {f : V → E}

/-- Fourier inversion for a continuous function. -/
theorem continuous_fourier_inversion
    (h : Continuous f) (hf : Integrable f) (h'f : Integrable (𝓕 f)) :
    𝓕⁻ (𝓕 f) = f := sorry

end Q3984053

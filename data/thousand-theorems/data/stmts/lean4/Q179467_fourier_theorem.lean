-- Statement-only formalization of Thousand Theorems artifact Q179467
-- (thousand-theorems__lean4__Q179467), "Fourier theorem": Fourier inversion holds
-- pointwise at continuity points for an integrable function with integrable Fourier
-- transform, and globally when the function is continuous. This file contains no proof.

import Mathlib.Analysis.Fourier.FourierTransform

@[expose] public section

open MeasureTheory

open scoped FourierTransform RealInnerProductSpace

namespace Q179467

variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {f : V → E}

/-- Fourier inversion at a continuity point. -/
theorem integrable_fourier_inversion
    (hf : Integrable f) (h'f : Integrable (𝓕 f)) {v : V}
    (hv : ContinuousAt f v) : 𝓕⁻ (𝓕 f) v = f v := sorry

/-- Fourier inversion for a continuous function. -/
theorem continuous_fourier_inversion
    (h : Continuous f) (hf : Integrable f) (h'f : Integrable (𝓕 f)) :
    𝓕⁻ (𝓕 f) = f := sorry

end Q179467

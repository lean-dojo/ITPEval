-- Statement-only formalization of Thousand Theorems artifact Q2096184
-- (thousand-theorems__lean4__Q2096184), "Plancherel theorem": the Fourier transform
-- preserves the integral inner product of Hilbert-valued Schwartz functions on a
-- finite-dimensional real inner-product space. This file contains no proof.

import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

open Real MeasureTheory MeasureTheory.Measure
open scoped FourierTransform ComplexInnerProductSpace SchwartzMap

noncomputable section

namespace Q2096184

variable
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Plancherel's theorem for Hilbert-valued Schwartz functions. -/
theorem integral_inner_fourier_fourier (f g : 𝓢(V, H)) :
    ∫ ξ, ⟪𝓕 f ξ, 𝓕 g ξ⟫ = ∫ x, ⟪f x, g x⟫ := sorry

end Q2096184

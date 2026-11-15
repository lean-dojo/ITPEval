-- Statement-only formalization of Thousand Theorems artifact Q4116459
-- (thousand-theorems__lean4__Q4116459), "Niven's theorem": a rational value
-- of cosine at a rational multiple of pi is one of -1, -1/2, 0, 1/2, or 1.
-- This file contains no proof.

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

namespace Q4116459

variable {θ : ℝ}

open Real

/-- Niven's theorem for rational cosine values at rational multiples of pi. -/
theorem niven (hθ : ∃ r : ℚ, θ = r * π) (hcos : ∃ q : ℚ, cos θ = q) :
    cos θ ∈ ({-1, -1 / 2, 0, 1 / 2, 1} : Set ℝ) := sorry

end Q4116459

-- Statement-only formalization of "The Hermite-Lindemann Transcendence Theorem" from Hundred
-- Theorems item 056: the complex exponential of every nonzero algebraic number is
-- transcendental over the rationals. This file contains no proof.

module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.RingTheory.Algebraic.Defs

public section

namespace Theorems100

/-- The exponential of a nonzero algebraic complex number is transcendental. -/
theorem hermite_lindemann_transcendence_theorem (x : ℂ) (hx : x ≠ 0)
    (hx_alg : IsAlgebraic ℚ x) :
    ¬ IsAlgebraic ℚ (Complex.exp x) := sorry

end Theorems100

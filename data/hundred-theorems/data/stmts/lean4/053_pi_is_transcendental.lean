-- Statement-only formalization of Hundred Theorems artifact 053, "Pi is Transcendental":
-- the real number pi is not algebraic over the rationals. This file contains no proof.

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.RingTheory.Algebraic.Defs

namespace Theorems100

/-- The real number pi is transcendental over the rationals. -/
theorem pi_is_transcendental : ¬ IsAlgebraic ℚ Real.pi := by
  sorry

end Theorems100

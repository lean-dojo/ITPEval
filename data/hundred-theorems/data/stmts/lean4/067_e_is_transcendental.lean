-- Statement-only formalization of Hundred Theorems artifact 067, "e is Transcendental":
-- Euler's number `exp 1` is not algebraic over the rationals. This file contains no proof.

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.RingTheory.Algebraic.Defs

namespace Theorems100

/-- Euler's number is transcendental over the rationals. -/
theorem e_is_transcendental : ¬ IsAlgebraic ℚ (Real.exp 1) := by
  sorry

end Theorems100

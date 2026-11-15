-- Statement-only formalization of Thousand Theorems artifact Q2919401
-- (thousand-theorems__lean4__Q2919401), "Ostrowski's theorem": every nontrivial
-- real-valued absolute value on the rationals is equivalent either to the standard
-- absolute value or uniquely to a prime-adic absolute value. This file contains no proof.

module

public import Mathlib.NumberTheory.Ostrowski

@[expose] public section

namespace Q2919401

/-- Ostrowski's theorem for nontrivial real-valued absolute values on `ℚ`. -/
theorem ostrowski_statement (f : AbsoluteValue ℚ ℝ) (hf_nontriv : f.IsNontrivial) :
    f ≈ Rat.AbsoluteValue.real ∨
      ∃! p : ℕ, ∃ (_ : Fact p.Prime), f ≈ Rat.AbsoluteValue.padic p := sorry

end Q2919401

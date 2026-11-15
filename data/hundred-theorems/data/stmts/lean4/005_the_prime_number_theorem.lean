-- Statement-only formalization of Hundred Theorems artifact 005, "The Prime Number Theorem":
-- the natural prime-counting function divided by n / log n tends to one. This file contains no
-- proof.

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.PrimeCounting

@[expose] public section

open Filter Topology

/-- The Prime Number Theorem. -/
theorem prime_number_theorem :
    Tendsto
      (fun n : ℕ =>
        (Nat.primeCounting n : ℝ) / ((n : ℝ) / Real.log (n : ℝ)))
      atTop
      (𝓝 1) := by
  sorry

-- Statement-only formalization of Thousand Theorems artifact Q22952648
-- (thousand-theorems__lean4__Q22952648), "Uncountability of the continuum":
-- the universal set of real numbers is not countable. This file contains no proof.

module

public import Mathlib.Algebra.Order.Group.Pointwise.Interval
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Rat.Cardinal
public import Mathlib.SetTheory.Cardinal.Continuum

@[expose] public section

namespace Q22952648

/-- The universal set of real numbers is not countable. -/
theorem uncountability_of_the_continuum : ¬(Set.univ : Set ℝ).Countable := sorry

end Q22952648

-- Statement-only formalization of Thousand Theorems artifact Q257387
-- (thousand-theorems__lean4__Q257387), "Vitali theorem": a set containing one
-- representative from each rational-difference class in `[0, 1]` is not
-- Lebesgue measurable. This file contains no proof.

module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

@[expose] public section

noncomputable section

open Set

namespace Q257387

/-- The rational-difference equivalence class of a point of `[0, 1]`. -/
def rationalClass (x : {x : ℝ // x ∈ Icc 0 1}) : Set ℝ :=
  {y | (x : ℝ) - y ∈ range ((↑) : ℚ → ℝ)}

/-- Two points of `[0, 1]` are equivalent when they have the same
rational-difference class. -/
def vS : Setoid {x : ℝ // x ∈ Icc 0 1} :=
  Setoid.ker rationalClass

/-- The quotient of `[0, 1]` by rational difference. -/
def vT : Type :=
  Quotient vS

/-- A chosen representative of each rational-difference class. -/
def vRep : vT → {x : ℝ // x ∈ Icc 0 1} :=
  Quotient.out

/-- The Vitali set formed by the chosen representatives. -/
def vitaliSet : Set ℝ :=
  {x | ∃ t : vT, (vRep t : ℝ) = x}

/-- The Vitali set is not Lebesgue measurable. -/
theorem vitaliSet_not_measurable : ¬MeasurableSet vitaliSet := sorry

end Q257387

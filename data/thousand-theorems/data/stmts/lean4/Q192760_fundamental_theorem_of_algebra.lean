-- Statement-only formalization of Thousand Theorems artifact Q192760
-- (thousand-theorems__lean4__Q192760), "Fundamental theorem of algebra": every
-- positive-degree complex polynomial has a complex root. This file contains no proof.

module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Complex.Trigonometric

@[expose] public section

open Polynomial

namespace Q192760

/-- Every positive-degree complex polynomial has a complex root. -/
theorem exists_root_statement {f : ℂ[X]} (hf : 0 < degree f) : ∃ z : ℂ, IsRoot f z := sorry

end Q192760

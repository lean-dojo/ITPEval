-- Statement-only formalization of Thousand Theorems artifact Q1933521
-- (thousand-theorems__lean4__Q1933521), "Kleene's recursion theorem": every
-- partial-recursive operation mapping a program code to a partial function has
-- a code whose evaluation equals the operation applied to that code. This file contains no proof.

module

public import Mathlib.Computability.PartrecCode

@[expose] public section

namespace Q1933521

open Nat.Partrec

/-- Kleene's second recursion theorem for codes of partial recursive functions. -/
theorem fixed_point₂_statement {f : Code → ℕ →. ℕ} (hf : Partrec₂ f) :
    ∃ c : Code, Code.eval c = f c := sorry

end Q1933521

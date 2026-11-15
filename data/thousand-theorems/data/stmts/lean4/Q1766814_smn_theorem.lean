-- Statement-only formalization of Thousand Theorems artifact Q1766814
-- (thousand-theorems__lean4__Q1766814), "Smn theorem": the S-m-n theorem gives
-- a computable operation that specializes a partial-recursive program code at
-- its first natural-number input. This file contains no proof.

module

public import Mathlib.Computability.PartrecCode

@[expose] public section

namespace Q1766814

open Nat.Partrec

/-- The S-m-n theorem for codes of partial recursive functions. -/
theorem smn_statement :
    ∃ f : Code → ℕ → Code, Computable₂ f ∧
      ∀ c n x, Code.eval (f c n) x = Code.eval c (Nat.pair n x) := sorry

end Q1766814

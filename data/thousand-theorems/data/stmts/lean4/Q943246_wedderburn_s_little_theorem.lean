-- Statement-only formalization of Thousand Theorems artifact Q943246
-- (thousand-theorems__lean4__Q943246), "Wedderburn's little theorem": every
-- finite division ring has commutative multiplication and hence is a field.
-- This file contains no proof.

module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Data.Finite.Defs

@[expose] public section

namespace Q943246

/-- Wedderburn's little theorem: multiplication in a finite division ring is commutative. -/
theorem littleWedderburn_statement (D : Type*) [DivisionRing D] [Finite D] :
    ∀ x y : D, x * y = y * x := sorry

end Q943246

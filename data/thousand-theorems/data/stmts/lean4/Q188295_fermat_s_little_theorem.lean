-- Statement-only formalization of Thousand Theorems artifact Q188295
-- (thousand-theorems__lean4__Q188295), "Fermat's little theorem": for a prime
-- modulus, every nonzero residue class raised to one less than the modulus is one.
-- This file contains no proof.

module

public import Mathlib.Data.ZMod.Basic

@[expose] public section

namespace Q188295

variable {p : ℕ} [Fact p.Prime]

/-- Fermat's little theorem for a nonzero residue class modulo a prime. -/
theorem fermat_little_theorem {a : ZMod p} (ha : a ≠ 0) :
    a ^ (p - 1) = 1 := sorry

end Q188295

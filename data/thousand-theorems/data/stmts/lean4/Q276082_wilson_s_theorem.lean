-- Statement-only formalization of Thousand Theorems artifact Q276082
-- (thousand-theorems__lean4__Q276082), "Wilson's theorem": for every prime
-- natural number p, (p - 1)! is congruent to -1 modulo p. This file contains no proof.

module

public import Mathlib.Data.ZMod.Basic

@[expose] public section

open scoped Nat

namespace Q276082

variable (p : ℕ) [Fact p.Prime]

/-- Wilson's lemma, the prime-modulus direction of Wilson's theorem. -/
theorem wilsons_lemma_statement : ((p - 1)! : ZMod p) = -1 := sorry

end Q276082

-- Statement-only formalization of Thousand Theorems artifact Q632546
-- (thousand-theorems__lean4__Q632546), "Bertrand's postulate": for every
-- nonzero natural number n, there is a prime p with n < p and p ≤ 2 * n.
-- This file contains no proof.

module

public import Mathlib.Data.Nat.Prime.Defs

@[expose] public section

namespace Q632546

/-- Bertrand's postulate for nonzero natural numbers. -/
theorem bertrand_s_postulate_statement (n : ℕ) (hn0 : n ≠ 0) :
    ∃ p : ℕ, Nat.Prime p ∧ n < p ∧ p ≤ 2 * n := sorry

end Q632546

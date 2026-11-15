-- Statement-only formalization of Thousand Theorems artifact Q1506253
-- (thousand-theorems__lean4__Q1506253), "Euclid's theorem": for every natural
-- number, there exists a prime number at least as large. This file contains no proof.

module

public import Mathlib.Data.Nat.Prime.Defs

@[expose] public section

namespace Q1506253

/-- Euclid's theorem on the infinitude of prime numbers. -/
theorem euclid_s_theorem_statement (n : ℕ) :
    ∃ p : ℕ, n ≤ p ∧ Nat.Prime p := sorry

end Q1506253

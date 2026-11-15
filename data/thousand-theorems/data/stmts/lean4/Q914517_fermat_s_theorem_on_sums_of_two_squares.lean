-- Statement-only formalization of Thousand Theorems artifact Q914517
-- (thousand-theorems__lean4__Q914517), "Fermat's theorem on sums of two squares":
-- every prime natural number not congruent to 3 modulo 4 is a sum of two squares
-- of natural numbers. This file contains no proof.

module

public import Mathlib.Data.Nat.Prime.Defs

@[expose] public section

namespace Q914517

/-- Fermat's theorem on sums of two squares for prime natural numbers. -/
theorem fermat_s_theorem_on_sums_of_two_squares {p : ℕ} [Fact p.Prime]
    (hp : p % 4 ≠ 3) :
    ∃ a b : ℕ, a ^ 2 + b ^ 2 = p := sorry

end Q914517

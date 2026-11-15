-- Statement-only formalization of Thousand Theorems artifact Q756946
-- (thousand-theorems__lean4__Q756946), "Lagrange's four-square theorem":
-- every natural number is a sum of four squares of natural numbers. This file
-- contains no proof.

module

@[expose] public section

namespace Q756946

/-- Lagrange's four-square theorem for natural numbers. -/
theorem lagrange_four_square_theorem (n : Nat) :
    ∃ a b c d : Nat, a * a + b * b + c * c + d * d = n := sorry

end Q756946

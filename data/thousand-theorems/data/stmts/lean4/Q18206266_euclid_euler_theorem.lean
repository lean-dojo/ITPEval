-- Statement-only formalization of Thousand Theorems artifact Q18206266
-- (thousand-theorems__lean4__Q18206266), "Euclid–Euler theorem": every even
-- perfect natural number is a power of two times a Mersenne prime. This file
-- contains no proof.

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace Nat

/-- The positive divisors of `n` that are strictly smaller than `n`. -/
def properDivisors (n : ℕ) : Finset ℕ :=
  {d ∈ Finset.Ico 1 n | d ∣ n}

/-- A positive natural number equal to the sum of its proper divisors. -/
def Perfect (n : ℕ) : Prop :=
  (properDivisors n).sum id = n ∧ 0 < n

end Nat

/-- The Mersenne number with exponent `p`. -/
def mersenne (p : ℕ) : ℕ :=
  2 ^ p - 1

namespace Theorems100

namespace Nat

/-- Euler's direction of the Euclid–Euler theorem for even perfect numbers. -/
theorem eq_two_pow_mul_prime_mersenne_of_even_perfect {n : ℕ} (ev : Even n)
    (perf : Nat.Perfect n) :
    ∃ k : ℕ, Nat.Prime (mersenne (k + 1)) ∧ n = 2 ^ k * mersenne (k + 1) := sorry

end Nat

end Theorems100

-- Statement-only formalization of Thousand Theorems artifact Q670235
-- (thousand-theorems__lean4__Q670235), "Fundamental theorem of arithmetic":
-- any list of primes whose product is a natural number is a permutation of that
-- number's canonical prime-factor list. This file contains no proof.

module

public import Mathlib.Data.Nat.Factors

@[expose] public section

namespace Q670235

/-- Uniqueness of prime factorization, expressed using the canonical prime-factor list. -/
theorem fundamental_theorem_of_arithmetic {n : ℕ} {l : List ℕ}
    (h₁ : l.prod = n) (h₂ : ∀ p ∈ l, Nat.Prime p) :
    List.Perm l n.primeFactorsList := sorry

end Q670235

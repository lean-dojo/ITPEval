-- Statement-only formalization of Thousand Theorems artifact Q550402
-- (thousand-theorems__lean4__Q550402), "Dirichlet's theorem on arithmetic progressions":
-- for a nonzero modulus, every invertible residue class contains infinitely many natural
-- primes. This file contains no proof.

module

public import Mathlib.Data.ZMod.Coprime

@[expose] public section

namespace Q550402

variable {q : ℕ} [NeZero q] {a : ZMod q}

/-- Dirichlet's theorem on primes in an invertible residue class. -/
theorem infinite_setOf_prime_and_eq_mod (ha : IsUnit a) :
    {p : ℕ | p.Prime ∧ (p : ZMod q) = a}.Infinite := sorry

end Q550402

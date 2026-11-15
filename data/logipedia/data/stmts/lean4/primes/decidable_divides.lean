-- Statement-only formalization of Logipedia corpus artifact
-- "primes.decidable_divides" (catalog title "primes.decidable_divides"):
-- divisibility is decidable for every pair of natural numbers. This file
-- contains no proof.

namespace primes

def divides (n m : Nat) : Prop :=
  ∃ q : Nat, m = n * q

theorem decidable_divides (n m : Nat) : divides n m ∨ ¬divides n m := sorry

end primes

-- Statement-only formalization of Logipedia corpus artifact
-- "primes.reflexive_divides" (catalog title "primes.reflexive_divides"):
-- natural-number divisibility is reflexive. This file contains no proof.

namespace primes

def divides (n m : Nat) : Prop :=
  ∃ q : Nat, m = n * q

theorem reflexive_divides : ∀ n : Nat, divides n n := sorry

end primes

-- Statement-only formalization of Logipedia corpus artifact
-- "primes.divides_to_le" (catalog title "primes.divides_to_le"): a natural
-- divisor of a positive natural number is at most that number. This file
-- contains no proof.

namespace primes

def divides (n m : Nat) : Prop :=
  ∃ q : Nat, m = n * q

theorem divides_to_le :
    ∀ n m : Nat, 0 < m → divides n m → n ≤ m := sorry

end primes

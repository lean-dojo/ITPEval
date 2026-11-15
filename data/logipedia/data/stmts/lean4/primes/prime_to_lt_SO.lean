-- Statement-only formalization of Logipedia corpus artifact
-- "primes.prime_to_lt_SO" (catalog title "primes.prime_to_lt_SO"): every prime
-- natural number is strictly greater than one. This file contains no proof.

namespace primes

def divides (n m : Nat) : Prop :=
  ∃ q : Nat, m = n * q

def prime (n : Nat) : Prop :=
  1 < n ∧ ∀ m : Nat, divides m n → 1 < m → m = n

theorem prime_to_lt_SO :
    ∀ p : Nat, prime p → 1 < p := sorry

end primes

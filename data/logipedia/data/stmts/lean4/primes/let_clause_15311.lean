-- Statement-only formalization of Logipedia corpus artifact
-- "primes.let_clause_15311" (catalog title "primes.let_clause_15311"): a
-- positive divisible natural number written as a multiple of a successor is
-- the corresponding sum of the divisor and its preceding multiple. This file
-- contains no proof.

namespace primes

def divides (n m : Nat) : Prop :=
  ∃ q : Nat, m = n * q

theorem let_clause_15311 :
    ∀ n m : Nat, 0 < m → divides n m → ∀ d p : Nat,
      m = n * Nat.succ p → m = n + n * p := sorry

end primes

-- Statement-only formalization of Logipedia corpus artifact
-- "primes.let_clause_1531" (catalog title "primes.let_clause_1531"): for
-- natural numbers, a positive divisible number equal to a zero multiple is
-- zero. This file contains no proof.

namespace primes

def divides (n m : Nat) : Prop :=
  ∃ q : Nat, m = n * q

theorem let_clause_1531 :
    ∀ n m : Nat, 0 < m → divides n m → ∀ d : Nat, m = n * 0 → m = 0 := sorry

end primes

-- Statement-only formalization of Logipedia corpus artifact
-- "primes.divides_n_O" (catalog title "primes.divides_n_O"): every natural
-- number divides zero. This file contains no proof.

namespace primes

def divides (n m : Nat) : Prop :=
  ∃ q : Nat, m = n * q

theorem divides_n_O : ∀ n : Nat, divides n 0 := sorry

end primes

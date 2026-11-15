-- Statement-only formalization of Logipedia corpus artifact
-- "primes.divides_n_n" (catalog title "primes.divides_n_n"): every natural
-- number divides itself. This file contains no proof.

namespace primes

def divides (n m : Nat) : Prop :=
  ∃ q : Nat, m = n * q

theorem divides_n_n : ∀ n : Nat, divides n n := sorry

end primes

-- Statement-only formalization of Logipedia corpus artifact
-- "primes.quotient" (catalog title "primes.quotient"): the natural-number
-- equality m = n * q implies that n divides m. This file contains no proof.

namespace primes

def divides (n m : Nat) : Prop :=
  exists q : Nat, m = n * q

theorem quotient :
    forall n m q : Nat, m = n * q -> divides n m := sorry

end primes

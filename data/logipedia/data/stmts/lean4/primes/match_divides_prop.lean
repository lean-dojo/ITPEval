-- Statement-only formalization of Logipedia corpus artifact
-- "primes.match_divides_prop" (catalog title "primes.match_divides_prop"):
-- divisibility of natural numbers may be eliminated by supplying a result for
-- every quotient witness. This file contains no proof.

namespace primes

def divides (n m : Nat) : Prop :=
  exists q : Nat, m = n * q

theorem match_divides_prop :
    forall (n m : Nat) (return_type : Prop),
      (forall q : Nat, m = n * q -> return_type) ->
        divides n m -> return_type := sorry

end primes

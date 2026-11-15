-- Statement-only formalization of Logipedia corpus artifact "cong.divides_to_congruent"
-- (catalog title "cong.divides_to_congruent"): divisibility of a truncated
-- natural-number difference implies congruence modulo a positive modulus.
-- This file contains no proof.

namespace cong

def congruent (n m p : Nat) : Prop :=
  n % p = m % p

theorem divides_to_congruent (n m p : Nat) (hp : 0 < p) (hmn : m ≤ n)
    (hdiv : ∃ q : Nat, n - m = p * q) :
    congruent n m p := sorry

end cong

-- Statement-only formalization of Logipedia corpus artifact "cong.eq_times_plus_to_congruent"
-- (catalog title "cong.eq_times_plus_to_congruent"): an equality of the form
-- n = r * p + m implies congruence of n and m modulo a positive natural modulus.
-- This file contains no proof.

namespace cong

def congruent (n m p : Nat) : Prop :=
  n % p = m % p

theorem eq_times_plus_to_congruent (n m p r : Nat) (hp : 0 < p)
    (hn : n = r * p + m) :
    congruent n m p := sorry

end cong

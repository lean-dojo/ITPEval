-- Statement-only formalization of Logipedia corpus artifact "cong.congruent_times"
-- (catalog title "cong.congruent_times"): multiplication preserves congruence
-- modulo a positive natural modulus. This file contains no proof.

namespace cong

def congruent (n m p : Nat) : Prop :=
  n % p = m % p

theorem congruent_times (n m n1 m1 p : Nat) (hp : 0 < p)
    (hn : congruent n n1 p) (hm : congruent m m1 p) :
    congruent (n * m) (n1 * m1) p := sorry

end cong

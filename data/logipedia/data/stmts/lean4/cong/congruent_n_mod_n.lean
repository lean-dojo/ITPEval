-- Statement-only formalization of Logipedia corpus artifact "cong.congruent_n_mod_n"
-- (catalog title "cong.congruent_n_mod_n"): every natural number is congruent
-- to its remainder modulo a positive natural modulus. This file contains no proof.

namespace cong

def congruent (n m p : Nat) : Prop :=
  n % p = m % p

theorem congruent_n_mod_n (n p : Nat) (hp : 0 < p) :
    congruent n (n % p) p := sorry

end cong

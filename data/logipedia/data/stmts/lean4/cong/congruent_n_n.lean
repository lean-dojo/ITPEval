-- Statement-only formalization of Logipedia corpus artifact "cong.congruent_n_n"
-- (catalog title "cong.congruent_n_n"): every natural number is congruent to
-- itself modulo every natural modulus. This file contains no proof.

namespace cong

def congruent (n m p : Nat) : Prop :=
  n % p = m % p

theorem congruent_n_n (n p : Nat) :
    congruent n n p := sorry

end cong

-- Statement-only formalization of Logipedia corpus artifact "cong.congruent_to_divides"
-- (catalog title "cong.congruent_to_divides"): congruence modulo a positive
-- natural modulus implies divisibility of the truncated difference. This file contains no proof.

namespace cong

def congruent (n m p : Nat) : Prop :=
  n % p = m % p

theorem congruent_to_divides (n m p : Nat) (hp : 0 < p)
    (hcong : congruent n m p) :
    ∃ q : Nat, n - m = p * q := sorry

end cong

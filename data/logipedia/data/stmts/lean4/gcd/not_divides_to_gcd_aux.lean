-- Statement-only formalization of Logipedia corpus artifact
-- "gcd.not_divides_to_gcd_aux" (catalog title "gcd.not_divides_to_gcd_aux"):
-- for natural numbers p, m, and positive n, if n does not divide m, then the
-- successor step of the fuel-recursive greatest-common-divisor auxiliary is
-- its recursive call on n and the remainder of m modulo n.
-- This file contains no proof.

namespace gcd

def gcdAux : Nat → Nat → Nat → Nat
  | 0, m, _n => m
  | Nat.succ p, m, n =>
      if n ∣ m then n else gcdAux p n (m % n)

theorem not_divides_to_gcd_aux :
    ∀ p m n : Nat, 0 < n → ¬n ∣ m →
      gcdAux (Nat.succ p) m n = gcdAux p n (m % n) := sorry

end gcd

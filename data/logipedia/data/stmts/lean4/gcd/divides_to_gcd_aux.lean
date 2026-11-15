-- Statement-only formalization of Logipedia corpus artifact
-- "gcd.divides_to_gcd_aux" (catalog title "gcd.divides_to_gcd_aux"):
-- for positive natural numbers p and n, if n divides m, then the fuel-recursive
-- greatest-common-divisor auxiliary applied to p, m, and n returns n.
-- This file contains no proof.

namespace gcd

def gcdAux : Nat → Nat → Nat → Nat
  | 0, m, _n => m
  | Nat.succ p, m, n =>
      if n ∣ m then n else gcdAux p n (m % n)

theorem divides_to_gcd_aux :
    ∀ p m n : Nat, 0 < p → 0 < n → n ∣ m → gcdAux p m n = n := sorry

end gcd

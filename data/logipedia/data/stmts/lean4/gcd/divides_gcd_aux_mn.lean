-- Statement-only formalization of Logipedia corpus artifact
-- "gcd.divides_gcd_aux_mn" (catalog title "gcd.divides_gcd_aux_mn"):
-- for natural numbers p, m, and positive n with n ≤ m and n ≤ p, the source
-- fuel-recursive greatest-common-divisor auxiliary divides both m and n.
-- This file contains no proof.

namespace gcd

def gcdAux : Nat → Nat → Nat → Nat
  | 0, m, _n => m
  | Nat.succ p, m, n =>
      if n ∣ m then n else gcdAux p n (m % n)

theorem divides_gcd_aux_mn :
    ∀ p m n : Nat, 0 < n → n ≤ m → n ≤ p →
      gcdAux p m n ∣ m ∧ gcdAux p m n ∣ n := sorry

end gcd

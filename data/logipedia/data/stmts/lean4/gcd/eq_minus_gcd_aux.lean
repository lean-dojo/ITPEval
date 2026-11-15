-- Statement-only formalization of Logipedia corpus artifact
-- "gcd.eq_minus_gcd_aux" (catalog title "gcd.eq_minus_gcd_aux"): for natural
-- numbers p, m, and positive n with n ≤ m and n ≤ p, the fuel-recursive
-- greatest-common-divisor auxiliary is one of the two truncated differences
-- between suitable natural multiples of n and m. This file contains no proof.

namespace gcd

def gcdAux : Nat → Nat → Nat → Nat
  | 0, m, _n => m
  | Nat.succ p, m, n =>
      if n ∣ m then n else gcdAux p n (m % n)

theorem eq_minus_gcd_aux :
    ∀ p m n : Nat, 0 < n → n ≤ m → n ≤ p → ∃ a b : Nat,
      a * n - b * m = gcdAux p m n ∨
      b * m - a * n = gcdAux p m n := sorry

end gcd

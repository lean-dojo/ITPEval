-- Statement-only formalization of Logipedia corpus artifact
-- "gcd.let_clause_15441" (catalog title "gcd.let_clause_15441"): for natural
-- numbers in the fuel-recursive Euclidean gcd construction, an equality with
-- the product b * n remains valid when that product is reordered as n * b.
-- This file contains no proof.

namespace gcd

def gcdAux : Nat → Nat → Nat → Nat
  | 0, m, _n => m
  | Nat.succ p, m, n =>
      if n ∣ m then n else gcdAux p n (m % n)

theorem let_clause_15441 :
    ∀ p q : Nat,
      (∀ m n : Nat, 0 < n → n ≤ m → n ≤ q → ∃ a b : Nat,
        a * n - b * m = gcdAux q m n ∨
        b * m - a * n = gcdAux q m n) →
      ∀ m n : Nat, 0 < n → n ≤ m → n ≤ Nat.succ q → ¬n ∣ m →
        ∀ a : Nat,
          (∃ b : Nat,
            a * (m % n) - b * n = gcdAux q n (m % n) ∨
            b * n - a * (m % n) = gcdAux q n (m % n)) →
          ∀ b : Nat,
            (a * (m % n) - b * n = gcdAux q n (m % n) ∨
              b * n - a * (m % n) = gcdAux q n (m % n)) →
            b * n - a * (m % n) = gcdAux q n (m % n) →
            n * b - a * (m % n) = gcdAux q n (m % n) := sorry

end gcd

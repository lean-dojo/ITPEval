-- Statement-only formalization of Logipedia corpus artifact "gcd.let_clause_1549"
-- (catalog title "gcd.let_clause_1549"): if a natural number m is zero, then
-- every natural number equals itself minus m, under the assumption that n is
-- positive. This file contains no proof.

theorem gcd.let_clause_1549 :
    ∀ m n : Nat, 0 < n → 0 = m → ∀ x1106 : Nat, x1106 = x1106 - m := sorry

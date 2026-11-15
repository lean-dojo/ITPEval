-- Statement-only formalization of Logipedia corpus artifact
-- "gcd.let_clause_1551" (catalog title "gcd.let_clause_1551"): for all
-- natural numbers m and n, if n is zero, then n equals every natural multiple
-- of itself. This file contains no proof.

theorem gcd.let_clause_1551 :
    ∀ m n : Nat, 0 = n → ∀ x347 : Nat, n = x347 * n := sorry

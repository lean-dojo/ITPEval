-- Statement-only formalization of Logipedia corpus artifact
-- "gcd.let_clause_15491" (catalog title "gcd.let_clause_15491"): for all
-- natural numbers m and n, if n is zero, every natural number equals itself
-- minus n. This file contains no proof.

theorem gcd.let_clause_15491 :
    ∀ m n : Nat, 0 = n → ∀ x1106 : Nat, x1106 = x1106 - n := sorry

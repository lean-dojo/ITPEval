-- Statement-only formalization of Logipedia corpus artifact
-- "gcd.let_clause_1571" (catalog title "gcd.let_clause_1571"): if a positive
-- natural number n and a natural number m have greatest common divisor zero,
-- and both m and n are zero, then m equals n. This file contains no proof.

theorem gcd.let_clause_1571 (m n : Nat) :
    0 < n → Nat.gcd m n = 0 → m = 0 → n = 0 → m = n := sorry

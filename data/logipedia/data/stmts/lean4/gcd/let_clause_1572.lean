-- Statement-only formalization of Logipedia corpus artifact
-- "gcd.let_clause_1572" (catalog title "gcd.let_clause_1572"): if n is a
-- positive natural number, the gcd of m and n is zero, and both m and n are
-- zero, then m is zero. This file contains no proof.

theorem gcd.let_clause_1572 (m n : Nat) :
    0 < n → Nat.gcd m n = 0 → m = 0 → n = 0 → m = 0 := sorry

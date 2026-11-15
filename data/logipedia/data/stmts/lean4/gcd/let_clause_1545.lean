-- Statement-only formalization of Logipedia corpus artifact
-- "gcd.let_clause_1545" (catalog title "gcd.let_clause_1545"): if a
-- natural-number gcd is zero, zero divides both inputs, and each input is a
-- zero multiple, then the first input is zero. This file contains no proof.

theorem gcd.let_clause_1545 :
    ∀ m n : Nat,
      Nat.gcd m n = 0 →
      0 ∣ n →
      ∀ q1 : Nat,
        n = 0 * q1 →
        0 ∣ m →
        ∀ q2 : Nat,
          m = 0 * q2 →
          m = 0 := sorry

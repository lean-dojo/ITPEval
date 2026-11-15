-- Statement-only formalization of Logipedia corpus artifact
-- "nat.minus_le_minus_minus_comm" (catalog title "nat.minus_le_minus_minus_comm"):
-- for natural numbers b, c, and a with c at most b, truncated subtraction gives
-- a - (b - c) = (a + c) - b. This file contains no proof.

theorem nat.minus_le_minus_minus_comm (b c a : Nat) :
    c ≤ b → a - (b - c) = (a + c) - b := sorry

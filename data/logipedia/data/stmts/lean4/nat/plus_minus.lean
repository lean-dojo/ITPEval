-- Statement-only formalization of Logipedia corpus artifact "nat.plus_minus"
-- (catalog title "nat.plus_minus"): for natural numbers m, n, and p with m at
-- most n, adding p after subtracting m from n equals subtracting m after adding
-- p to n. This file contains no proof.

theorem nat.plus_minus (m n p : Nat) :
    m ≤ n → (n - m) + p = (n + p) - m := sorry

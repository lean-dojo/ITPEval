-- Statement-only formalization of Logipedia corpus artifact "nat.plus_minus_m_m"
-- (catalog title "nat.plus_minus_m_m"): if m is at most n, adding m back to
-- the natural-number difference n - m yields n. This file contains no proof.

theorem nat.plus_minus_m_m (n m : Nat) :
    m ≤ n → n = (n - m) + m := sorry

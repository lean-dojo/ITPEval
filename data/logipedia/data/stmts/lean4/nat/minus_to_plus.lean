-- Statement-only formalization of Logipedia corpus artifact "nat.minus_to_plus"
-- (catalog title "nat.minus_to_plus"): if m is at most n and n minus m equals p,
-- then n equals m plus p. This file contains no proof.

theorem nat.minus_to_plus (n m p : Nat) :
    m ≤ n → n - m = p → n = m + p := sorry

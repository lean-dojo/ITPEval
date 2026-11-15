-- Statement-only formalization of Logipedia corpus artifact "nat.eqb_n_n"
-- (catalog title "nat.eqb_n_n"): the Boolean equality test of a natural
-- number with itself returns true. This file contains no proof.

theorem nat.eqb_n_n (n : Nat) :
    decide (n = n) = true := sorry

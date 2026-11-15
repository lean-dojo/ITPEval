-- Statement-only formalization of Logipedia corpus artifact "nat.lt_S_to_lt"
-- (catalog title "nat.lt_S_to_lt"): for all natural numbers n and m, if the
-- successor of n is less than m, then n is less than m.
-- This file contains no proof.

theorem nat.lt_S_to_lt (n m : Nat) :
    Nat.succ n < m -> n < m := sorry

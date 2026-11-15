-- Statement-only formalization of Logipedia corpus artifact "nat.plus_n_Sm"
-- (catalog title "nat.plus_n_Sm"): for all natural numbers n and m, the
-- successor of n + m equals n plus the successor of m. This file contains no proof.

theorem nat.plus_n_Sm (n m : Nat) :
    Nat.succ (n + m) = n + Nat.succ m := sorry

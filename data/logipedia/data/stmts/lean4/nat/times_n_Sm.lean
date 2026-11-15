-- Statement-only formalization of Logipedia corpus artifact "nat.times_n_Sm"
-- (catalog title "nat.times_n_Sm"): for all natural numbers n and m, n plus
-- n times m equals n times the successor of m. This file contains no proof.

theorem nat.times_n_Sm (n m : Nat) :
    n + n * m = n * Nat.succ m := sorry

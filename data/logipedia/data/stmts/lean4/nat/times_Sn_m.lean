-- Statement-only formalization of Logipedia corpus artifact "nat.times_Sn_m"
-- (catalog title "nat.times_Sn_m"): for all natural numbers n and m, m plus
-- n times m equals the product of the successor of n with m. This file contains no proof.

theorem nat.times_Sn_m (n m : Nat) :
    m + n * m = Nat.succ n * m := sorry

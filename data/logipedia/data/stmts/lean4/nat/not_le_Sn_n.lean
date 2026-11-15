-- Statement-only formalization of Logipedia corpus artifact
-- "nat.not_le_Sn_n" (catalog title "nat.not_le_Sn_n"): no natural number is
-- greater than or equal to its own successor. This file contains no proof.

namespace nat

theorem not_le_Sn_n : ∀ n : Nat, ¬ Nat.succ n ≤ n := sorry

end nat

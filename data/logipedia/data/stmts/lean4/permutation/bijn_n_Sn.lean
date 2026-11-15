-- Statement-only formalization of Logipedia corpus artifact "permutation.bijn_n_Sn"
-- (catalog title "permutation.bijn_n_Sn"): bounded surjectivity of a
-- natural-number function extends to the next initial segment when the new
-- endpoint is fixed. This file contains no proof.

namespace permutation

def bijn (f : Nat → Nat) (n : Nat) : Prop :=
  ∀ m : Nat, m ≤ n → ∃ p : Nat, p ≤ n ∧ f p = m

theorem bijn_n_Sn :
    ∀ (f : Nat → Nat) (n : Nat),
      bijn f n →
        f (Nat.succ n) = Nat.succ n →
          bijn f (Nat.succ n) := sorry

end permutation

-- Statement-only formalization of Logipedia corpus artifact "permutation.bijn_fg"
-- (catalog title "permutation.bijn_fg"): bounded surjectivity of natural-number
-- functions on an initial segment is preserved under composition.
-- This file contains no proof.

namespace permutation

def bijn (f : Nat → Nat) (n : Nat) : Prop :=
  ∀ m : Nat, m ≤ n → ∃ p : Nat, p ≤ n ∧ f p = m

theorem bijn_fg :
    ∀ (f g : Nat → Nat) (n : Nat),
      bijn f n → bijn g n → bijn (fun p ↦ f (g p)) n := sorry

end permutation

-- Statement-only formalization of Logipedia corpus artifact
-- "permutation.permut_to_bijn" (catalog title "permutation.permut_to_bijn"):
-- every natural-number function that maps an initial segment into itself and
-- is injective there is surjective on that initial segment.
-- This file contains no proof.

namespace permutation

def injn (f : Nat → Nat) (n : Nat) : Prop :=
  ∀ i j : Nat, i ≤ n → j ≤ n → f i = f j → i = j

def permut (f : Nat → Nat) (n : Nat) : Prop :=
  (∀ i : Nat, i ≤ n → f i ≤ n) ∧ injn f n

def bijn (f : Nat → Nat) (n : Nat) : Prop :=
  ∀ m : Nat, m ≤ n → ∃ p : Nat, p ≤ n ∧ f p = m

theorem permut_to_bijn :
    ∀ (n : Nat) (f : Nat → Nat), permut f n → bijn f n := sorry

end permutation

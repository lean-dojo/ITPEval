-- Statement-only formalization of Logipedia corpus artifact "bigops.sameF_p_le"
-- (catalog title "bigops.sameF_p_le"): agreement of two functions at selected
-- indices below a bound restricts monotonically to any smaller bound.
-- This file contains no proof.

namespace bigops

def sameF_p (A : Type) (k : Nat) (p : Nat → Bool) (f g : Nat → A) : Prop :=
  ∀ i : Nat, i < k → p i = true → f i = g i

theorem sameF_p_le
    (A : Type) (p : Nat → Bool) (f g : Nat → A) (n m : Nat)
    (hnm : n ≤ m) (hfg : sameF_p A m p f g) :
    sameF_p A n p f g := sorry

end bigops

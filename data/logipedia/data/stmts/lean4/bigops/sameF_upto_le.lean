-- Statement-only formalization of Logipedia corpus artifact "bigops.sameF_upto_le"
-- (catalog title "bigops.sameF_upto_le"): pointwise agreement of two functions
-- below a natural-number bound restricts monotonically to any smaller bound.
-- This file contains no proof.

namespace bigops

def sameF_upto (A : Type) (k : Nat) (f g : Nat → A) : Prop :=
  ∀ i : Nat, i < k → f i = g i

theorem sameF_upto_le
    (A : Type) (f g : Nat → A) (n m : Nat)
    (hnm : n ≤ m) (hfg : sameF_upto A m f g) :
    sameF_upto A n f g := sorry

end bigops

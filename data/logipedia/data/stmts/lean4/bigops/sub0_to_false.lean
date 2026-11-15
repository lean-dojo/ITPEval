-- Statement-only formalization of Logipedia corpus artifact "bigops.sub0_to_false"
-- (catalog title "bigops.sub0_to_false"): if the second bound of a functional
-- correspondence is zero, its first Boolean selector is false below the first bound.
-- This file contains no proof.

namespace bigops

def sub_hk
    (h k : Nat → Nat) (n1 n2 : Nat) (p1 p2 : Nat → Bool)
    (_f1 _f2 : Nat → Nat) : Prop :=
  ∀ i : Nat, i < n1 → p1 i = true →
    ((h i < n2 ∧ p2 (h i) = true) ∧ k (h i) = i)

theorem sub0_to_false
    (h k : Nat → Nat) (n1 n2 : Nat) (p1 p2 : Nat → Bool)
    (f1 f2 : Nat → Nat)
    (hn1 : n1 = 0)
    (hsub : sub_hk h k n2 n1 p2 p1 f2 f1) :
    ∀ i : Nat, i < n2 → p2 i = false := sorry

end bigops

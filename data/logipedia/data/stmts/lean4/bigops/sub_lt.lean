-- Statement-only formalization of Logipedia corpus artifact "bigops.sub_lt"
-- (catalog title "bigops.sub_lt"): a smaller natural-number bound embeds into a
-- larger one through the identity correspondence on Boolean-selected indices.
-- This file contains no proof.

namespace bigops

def sub_hk
    (h k : Nat → Nat) (n1 n2 : Nat) (p1 p2 : Nat → Bool)
    (_f1 _f2 : Nat → Nat) : Prop :=
  ∀ i : Nat, i < n1 → p1 i = true →
    ((h i < n2 ∧ p2 (h i) = true) ∧ k (h i) = i)

theorem sub_lt
    (e : Nat → Nat) (p : Nat → Bool) (n m : Nat) (hnm : n ≤ m) :
    sub_hk (fun x ↦ x) (fun x ↦ x) n m p p e e := sorry

end bigops

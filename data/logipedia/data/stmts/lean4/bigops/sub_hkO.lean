-- Statement-only formalization of Logipedia corpus artifact "bigops.sub_hkO"
-- (catalog title "bigops.sub_hkO"): the bounded correspondence predicate sub_hk
-- holds when its source bound is zero. This file contains no proof.

namespace bigops

def sub_hk
    (h k : Nat → Nat) (n1 n2 : Nat) (p1 p2 : Nat → Bool)
    (_f1 _f2 : Nat → Nat) : Prop :=
  ∀ i : Nat, i < n1 → p1 i = true →
    ((h i < n2 ∧ p2 (h i) = true) ∧ k (h i) = i)

theorem sub_hkO
    (h k : Nat → Nat) (n1 n2 : Nat) (p1 p2 : Nat → Bool)
    (f1 f2 : Nat → Nat) (hn1 : n1 = 0) :
    sub_hk h k n1 n2 p1 p2 f1 f2 := sorry

end bigops

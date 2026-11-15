-- Statement-only formalization of Logipedia corpus artifact "nat.nat_case"
-- (catalog title "nat.nat_case"): case analysis for an arbitrary predicate on a
-- natural number from equality-guarded zero and successor cases. This file contains no proof.

theorem nat.nat_case (n : Nat) (P : Nat → Prop) :
    (n = 0 → P 0) →
    (∀ m : Nat, n = Nat.succ m → P (Nat.succ m)) →
    P n := sorry

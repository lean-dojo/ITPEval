-- Statement-only formalization of Logipedia corpus artifact "nat.le_ind"
-- (catalog title "nat.le_ind"): induction over natural numbers from an
-- arbitrary lower bound. This file contains no proof.

theorem nat.le_ind (n : Nat) (Q : Nat → Prop) :
    Q n →
    (∀ m : Nat, n ≤ m → Q m → Q (Nat.succ m)) →
    ∀ m : Nat, n ≤ m → Q m := sorry

-- Statement-only formalization of Logipedia corpus artifact "nat.nat_ind"
-- (catalog title "nat.nat_ind"): mathematical induction for predicates on
-- natural numbers, from zero and preservation under successor.
-- This file contains no proof.

theorem nat.nat_ind (Q : Nat → Prop) :
    Q 0 →
    (∀ x : Nat, Q x → Q (Nat.succ x)) →
    ∀ x : Nat, Q x := sorry

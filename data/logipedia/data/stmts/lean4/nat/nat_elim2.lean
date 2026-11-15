-- Statement-only formalization of Logipedia corpus artifact "nat.nat_elim2"
-- (catalog title "nat.nat_elim2"): a two-dimensional induction principle for
-- predicates on pairs of natural numbers. This file contains no proof.

theorem nat.nat_elim2 (R : Nat → Nat → Prop) :
    (∀ n : Nat, R 0 n) →
    (∀ n : Nat, R (Nat.succ n) 0) →
    (∀ n m : Nat, R n m → R (Nat.succ n) (Nat.succ m)) →
    ∀ n m : Nat, R n m := sorry

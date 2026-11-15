-- Statement-only formalization of Logipedia corpus artifact "nat.leb_elim"
-- (catalog title "nat.leb_elim"): a predicate on the Boolean less-than-or-equal
-- test of two natural numbers follows from its order and non-order branches.
-- This file contains no proof.

theorem nat.leb_elim (n m : Nat) (P : Bool → Prop) :
    (n ≤ m → P true) →
    (¬n ≤ m → P false) →
    P (decide (n ≤ m)) := sorry

-- Statement-only formalization of Logipedia corpus artifact "nat.eqb_elim"
-- (catalog title "nat.eqb_elim"): a predicate on the Boolean equality test of
-- two natural numbers follows from its equality and inequality branches.
-- This file contains no proof.

theorem nat.eqb_elim (n m : Nat) (P : Bool → Prop) :
    (n = m → P true) →
    (n ≠ m → P false) →
    P (decide (n = m)) := sorry

-- Statement-only formalization of Logipedia corpus artifact "nat.match_nat_prop"
-- (catalog title "nat.match_nat_prop"): a predicate holding at zero and at every
-- successor holds for every natural number. This file contains no proof.

theorem nat.match_nat_prop (return_ : Nat → Prop) :
    return_ 0 →
    (∀ n : Nat, return_ (Nat.succ n)) →
    ∀ z : Nat, return_ z := sorry

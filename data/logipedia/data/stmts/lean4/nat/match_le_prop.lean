-- Statement-only formalization of Logipedia corpus artifact "nat.match_le_prop"
-- (catalog title "nat.match_le_prop"): elimination of a natural-number lower
-- bound into an arbitrary predicate from its base and successor cases. This
-- file contains no proof.

theorem nat.match_le_prop (n : Nat) (return_ : Nat → Prop) :
    return_ n →
    (∀ m : Nat, return_ (Nat.succ m)) →
    ∀ m : Nat, n ≤ m → return_ m := sorry

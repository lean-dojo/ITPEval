-- Statement-only formalization of Logipedia corpus artifact "nat.injective_S"
-- (catalog title "nat.injective_S"): the successor function on natural numbers
-- is injective. This file contains no proof.

theorem nat.injective_S :
    ∀ x y : Nat, Nat.succ x = Nat.succ y → x = y := sorry

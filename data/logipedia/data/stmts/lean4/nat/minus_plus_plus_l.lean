-- Statement-only formalization of Logipedia corpus artifact "nat.minus_plus_plus_l"
-- (catalog title "nat.minus_plus_plus_l"): adding the same natural number to both
-- operands leaves their truncated difference unchanged. This file contains no proof.

theorem nat.minus_plus_plus_l (x y h : Nat) :
    (x + h) - (y + h) = x - y := sorry

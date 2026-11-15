-- Statement-only formalization of Logipedia corpus artifact
-- "gcd.eq_minus_gcd" (catalog title "gcd.eq_minus_gcd"): for any two natural
-- numbers, their greatest common divisor is one of the two truncated differences
-- between suitable natural multiples of the inputs. This file contains no proof.

theorem gcd.eq_minus_gcd :
    ∀ m n : Nat, ∃ a b : Nat,
      a * n - b * m = Nat.gcd n m ∨
      b * m - a * n = Nat.gcd n m := sorry

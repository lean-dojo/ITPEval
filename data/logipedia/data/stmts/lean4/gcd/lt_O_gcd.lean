-- Statement-only formalization of Logipedia corpus artifact "gcd.lt_O_gcd"
-- (catalog title "gcd.lt_O_gcd"): the greatest common divisor of two natural
-- numbers is positive whenever the second number is positive. This file contains no proof.

theorem gcd.lt_O_gcd (m n : Nat) : 0 < n -> 0 < Nat.gcd m n := sorry

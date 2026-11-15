-- Statement-only formalization of Logipedia corpus artifact
-- "gcd.divides_gcd_nm" (catalog title "gcd.divides_gcd_nm"): for any two
-- natural numbers, their greatest common divisor divides both inputs.
-- This file contains no proof.

theorem gcd.divides_gcd_nm (n m : Nat) :
    Nat.gcd n m ∣ m ∧ Nat.gcd n m ∣ n := sorry

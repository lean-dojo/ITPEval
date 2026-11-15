-- Statement-only formalization of Logipedia corpus artifact
-- "gcd.divides_mod_to_divides" (catalog title "gcd.divides_mod_to_divides"):
-- a natural number dividing both a positive-modulus remainder and the modulus
-- also divides the original dividend. This file contains no proof.

theorem gcd.divides_mod_to_divides :
    ∀ p m n : Nat, 0 < n → p ∣ m % n → p ∣ n → p ∣ m := sorry

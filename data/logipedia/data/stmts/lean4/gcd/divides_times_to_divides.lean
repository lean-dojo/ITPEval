-- Statement-only formalization of Logipedia corpus artifact
-- "gcd.divides_times_to_divides" (catalog title
-- "gcd.divides_times_to_divides"): a prime natural number dividing a product
-- divides at least one factor. This file contains no proof.

theorem gcd.divides_times_to_divides :
    ∀ p n m : Nat,
      (1 < p ∧ ∀ d : Nat, d ∣ p → 1 < d → d = p) →
      p ∣ n * m →
      p ∣ n ∨ p ∣ m := sorry

-- Statement-only formalization of Logipedia corpus artifact
-- "gcd.prime_to_gcd_1" (catalog title "gcd.prime_to_gcd_1"): a prime natural
-- number that does not divide another natural number has greatest common
-- divisor one with that number. This file contains no proof.

namespace gcd

def prime (n : Nat) : Prop :=
  1 < n ∧ ∀ d : Nat, d ∣ n → 1 < d → d = n

theorem prime_to_gcd_1 (n m : Nat) :
    prime n → ¬n ∣ m → Nat.gcd n m = 1 := sorry

end gcd

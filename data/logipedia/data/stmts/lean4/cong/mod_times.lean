-- Statement-only formalization of Logipedia corpus artifact "cong.mod_times"
-- (catalog title "cong.mod_times"): reducing the product of two natural numbers
-- modulo a positive modulus agrees with multiplying their remainders and reducing again.
-- This file contains no proof.

namespace cong

theorem mod_times (n m p : Nat) (hp : 0 < p) :
    (n * m) % p = ((n % p) * (m % p)) % p := sorry

end cong

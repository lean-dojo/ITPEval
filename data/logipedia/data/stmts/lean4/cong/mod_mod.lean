-- Statement-only formalization of Logipedia corpus artifact "cong.mod_mod"
-- (catalog title "cong.mod_mod"): taking a remainder modulo a positive natural
-- modulus is idempotent. This file contains no proof.

namespace cong

theorem mod_mod (n p : Nat) (hp : 0 < p) :
    n % p = (n % p) % p := sorry

end cong

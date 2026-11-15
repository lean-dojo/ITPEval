(*
  Statement-only formalization of Logipedia corpus artifact cong.mod_mod,
  catalog title cong.mod_mod: taking the remainder of a natural number modulo
  a positive natural modulus is idempotent. This file contains no proof.
*)

theory mod_mod
  imports Main
begin

theorem mod_mod:
  fixes n p :: nat
  assumes "0 < p"
  shows "n mod p = (n mod p) mod p"
  sorry

end

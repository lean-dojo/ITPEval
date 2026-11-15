(*
  Statement-only formalization of Logipedia corpus artifact cong.mod_times,
  catalog title cong.mod_times: reduction modulo a positive natural modulus
  commutes with multiplication. This file contains no proof.
*)

theory mod_times
  imports Main
begin

theorem mod_times:
  fixes n m p :: nat
  assumes "0 < p"
  shows "(n * m) mod p = ((n mod p) * (m mod p)) mod p"
  sorry

end

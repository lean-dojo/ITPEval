(*
  Statement-only formalization of Logipedia corpus artifact
  cong.congruent_times, catalog title "cong.congruent_times": congruence
  modulo a positive natural modulus is preserved by multiplication. This file
  contains no proof.
*)

let statement =
  `!n m n1 m1 p:num.
     0 < p
     ==> n MOD p = n1 MOD p
     ==> m MOD p = m1 MOD p
     ==> (n * m) MOD p = (n1 * m1) MOD p`;;

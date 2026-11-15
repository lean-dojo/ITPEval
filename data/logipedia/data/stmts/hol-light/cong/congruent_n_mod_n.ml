(*
  Statement-only formalization of Logipedia corpus artifact
  cong.congruent_n_mod_n, catalog title "cong.congruent_n_mod_n": every
  natural number is congruent modulo a positive natural modulus to its
  remainder modulo that modulus. This file contains no proof.
*)

let statement =
  `!n p:num.
     0 < p
     ==>
     n MOD p = (n MOD p) MOD p`;;

(*
  Statement-only formalization of Logipedia corpus artifact cong.mod_times,
  catalog title "cong.mod_times": reduction modulo a positive natural modulus
  is compatible with multiplication of natural numbers. This file contains
  no proof.
*)

let statement =
  `!n m p:num.
     0 < p
     ==>
     (n * m) MOD p = ((n MOD p) * (m MOD p)) MOD p`;;

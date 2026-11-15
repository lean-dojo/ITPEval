(*
  Statement-only formalization of Logipedia corpus artifact cong.mod_mod,
  catalog title "cong.mod_mod": taking the remainder of a natural number
  modulo a positive natural modulus is idempotent. This file contains no
  proof.
*)

let statement =
  `!n p:num.
     0 < p
     ==>
     n MOD p = (n MOD p) MOD p`;;

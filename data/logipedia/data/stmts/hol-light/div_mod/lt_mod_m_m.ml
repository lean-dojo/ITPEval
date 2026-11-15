(*
  Statement-only formalization of Logipedia corpus artifact
  div_mod.lt_mod_m_m, catalog title "div_mod.lt_mod_m_m": the remainder of a
  natural number modulo a positive natural modulus is smaller than that
  modulus. This file contains no proof.
*)

let statement =
  `!n m:num.
     0 < m
     ==>
     n MOD m < m`;;

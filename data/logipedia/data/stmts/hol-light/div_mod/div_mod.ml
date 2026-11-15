(*
  Statement-only formalization of Logipedia corpus artifact div_mod.div_mod,
  catalog title "div_mod.div_mod": every natural number equals its natural
  quotient times the divisor plus its natural remainder. This file contains
  no proof.
*)

let logipedia_div_mod_div = new_definition
  `logipedia_div_mod_div n m =
     if m = 0 then SUC n else n DIV m`;;

let logipedia_div_mod_mod = new_definition
  `logipedia_div_mod_mod n m =
     if m = 0 then n else n MOD m`;;

let statement =
  `!n m:num.
     n =
       logipedia_div_mod_div n m * m +
       logipedia_div_mod_mod n m`;;

(*
  Statement-only formalization of Logipedia corpus artifact
  div_mod.eq_times_div_minus_mod, catalog title
  "div_mod.eq_times_div_minus_mod": a natural quotient times its divisor
  equals the dividend minus its natural remainder. This file contains no
  proof.
*)

let logipedia_eq_times_div_minus_mod_div = new_definition
  `logipedia_eq_times_div_minus_mod_div n m =
     if m = 0 then SUC n else n DIV m`;;

let logipedia_eq_times_div_minus_mod_mod = new_definition
  `logipedia_eq_times_div_minus_mod_mod n m =
     if m = 0 then n else n MOD m`;;

let statement =
  `!a b:num.
     logipedia_eq_times_div_minus_mod_div a b * b =
     a - logipedia_eq_times_div_minus_mod_mod a b`;;

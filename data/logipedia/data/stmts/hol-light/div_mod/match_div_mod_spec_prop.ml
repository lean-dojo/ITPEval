(*
  Statement-only formalization of Logipedia corpus artifact
  div_mod.match_div_mod_spec_prop, catalog title
  "div_mod.match_div_mod_spec_prop": the natural-number quotient-remainder
  specification eliminates to any proposition implied by the remainder bound
  and decomposition equation. This file contains no proof.
*)

let logipedia_div_mod_spec = new_definition
  `logipedia_div_mod_spec (n:num) m q r <=>
     r < m /\ n = q * m + r`;;

let statement =
  `!n m q r:num.
   !return:bool.
     (r < m ==> n = q * m + r ==> return)
     ==>
     logipedia_div_mod_spec n m q r
     ==>
     return`;;

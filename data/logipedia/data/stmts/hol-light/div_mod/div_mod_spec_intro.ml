(*
  Statement-only formalization of Logipedia corpus artifact
  div_mod.div_mod_spec_intro, catalog title "div_mod.div_mod_spec_intro":
  natural numbers satisfying the bounded-remainder decomposition conditions
  satisfy the natural-number division specification. This file contains no
  proof.
*)

let logipedia_div_mod_spec = new_definition
  `logipedia_div_mod_spec (n:num) m q r <=>
     r < m /\ n = q * m + r`;;

let statement =
  `!n m q r:num.
     r < m
     ==>
     n = q * m + r
     ==>
     logipedia_div_mod_spec n m q r`;;

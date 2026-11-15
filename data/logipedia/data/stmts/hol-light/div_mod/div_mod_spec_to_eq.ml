(*
  Statement-only formalization of Logipedia corpus artifact
  div_mod.div_mod_spec_to_eq, catalog title "div_mod.div_mod_spec_to_eq":
  two bounded-remainder decompositions of the same natural dividend by the
  same natural divisor have equal quotients. This file contains no proof.
*)

let logipedia_div_mod_spec = new_definition
  `logipedia_div_mod_spec (a:num) b q r <=>
     r < b /\ a = q * b + r`;;

let statement =
  `!a b q r q1 r1:num.
     logipedia_div_mod_spec a b q r
     ==>
     logipedia_div_mod_spec a b q1 r1
     ==>
     q = q1`;;

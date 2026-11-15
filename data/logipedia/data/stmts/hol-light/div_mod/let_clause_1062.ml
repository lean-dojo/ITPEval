(*
  Statement-only formalization of Logipedia corpus artifact
  div_mod.let_clause_1062, catalog title "div_mod.let_clause_1062": two
  bounded quotient-remainder decompositions of the same natural number,
  under an incompatible quotient ordering, retain the second decomposition
  when its sum and product operands are exchanged. This file contains no
  proof.
*)

let logipedia_div_mod_spec = new_definition
  `logipedia_div_mod_spec (a:num) b q r <=>
     r < b /\ a = q * b + r`;;

let statement =
  `!a b q r q1 r1:num.
     logipedia_div_mod_spec a b q r
     ==>
     r < b
     ==>
     a = q * b + r
     ==>
     logipedia_div_mod_spec a b q1 r1
     ==>
     r1 < b
     ==>
     a = q1 * b + r1
     ==>
     ~(q <= q1)
     ==>
     a = r1 + b * q1`;;

(*
  Statement-only formalization of Logipedia corpus artifact
  div_mod.let_clause_1078, catalog title "div_mod.let_clause_1078": under two
  natural-number quotient-remainder specifications and the stated quotient
  order assumptions, the first decomposition can be written with its
  remainder before the product. This file contains no proof.
*)

let statement =
  `let div_mod_spec =
     \(a:num) b q r. r < b /\ a = q * b + r
   in
   !a b q r q1 r1:num.
     div_mod_spec a b q r
     ==> r < b
     ==> a = q * b + r
     ==> div_mod_spec a b q1 r1
     ==> r1 < b
     ==> a = q1 * b + r1
     ==> q <= q1
     ==> q < q1
     ==> a = r + b * q`;;

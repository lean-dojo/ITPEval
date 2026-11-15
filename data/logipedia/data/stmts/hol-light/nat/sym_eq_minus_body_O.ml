(*
  Statement-only formalization of Logipedia corpus artifact
  nat.sym_eq_minus_body_O, catalog title "nat.sym_eq_minus_body_O": Leibniz
  equality transports every predicate holding of the constant-zero function
  on natural numbers to minus_body at natural zero. This file contains no
  proof.
*)

new_constant
  ("logipedia_nat_minus_body", `:num -> num -> num`);;

let statement =
  `!P:((num -> num) -> bool).
     P (\m:num. 0) ==>
     P (logipedia_nat_minus_body 0)`;;

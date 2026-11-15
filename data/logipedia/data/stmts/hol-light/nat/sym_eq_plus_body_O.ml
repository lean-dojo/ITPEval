(*
  Statement-only formalization of Logipedia corpus artifact
  nat.sym_eq_plus_body_O, catalog title "nat.sym_eq_plus_body_O": Leibniz
  equality transports every predicate holding of the identity function on
  natural numbers to plus_body at natural zero. This file contains no proof.
*)

new_constant
  ("logipedia_nat_plus_body", `:num -> num -> num`);;

let statement =
  `!P:((num -> num) -> bool).
     P (\m:num. m) ==>
     P (logipedia_nat_plus_body 0)`;;

(*
  Statement-only formalization of Logipedia corpus artifact
  nat.sym_eq_leb_body_O, catalog title "nat.sym_eq_leb_body_O": Leibniz
  equality transports every predicate holding of the constant-true
  Boolean-valued function on natural numbers to leb_body at natural zero.
  This file contains no proof.
*)

new_constant
  ("logipedia_nat_leb_body", `:num -> num -> bool`);;

let statement =
  `!P:((num -> bool) -> bool).
     P (\m:num. T) ==>
     P (logipedia_nat_leb_body 0)`;;

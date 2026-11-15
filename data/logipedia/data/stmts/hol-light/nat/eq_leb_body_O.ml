(*
  Statement-only formalization of Logipedia corpus artifact
  nat.eq_leb_body_O, catalog title "nat.eq_leb_body_O": Leibniz equality
  transports every predicate holding of leb_body at natural zero to the
  constant-true Boolean-valued function on natural numbers. This file
  contains no proof.
*)

new_constant
  ("logipedia_nat_leb_body", `:num -> num -> bool`);;

let statement =
  `!P:((num -> bool) -> bool).
     P (logipedia_nat_leb_body 0) ==>
     P (\m:num. T)`;;

(*
  Statement-only formalization of Logipedia corpus artifact
  nat.axiom_leb_body_O, catalog title "nat.axiom_leb_body_O": the Boolean
  less-than-or-equal body at natural zero is equal as a function to the
  constant-true function on natural numbers. This file contains no proof.
*)

new_constant
  ("logipedia_nat_leb_body", `:num -> num -> bool`);;

let statement =
  `(logipedia_nat_leb_body 0) = (\m:num. T)`;;

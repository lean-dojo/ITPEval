(*
  Statement-only formalization of Logipedia corpus artifact
  nat.axiom_minus_body_O, catalog title "nat.axiom_minus_body_O": the source
  equality relation identifies minus_body at natural zero with the
  constant-zero function on natural numbers. This file contains no proof.
*)

new_constant
  ("logipedia_connectives_equal", `:'a -> 'a -> bool`);;

new_constant
  ("logipedia_nat_minus_body", `:num -> num -> num`);;

let statement =
  `logipedia_connectives_equal
     (logipedia_nat_minus_body 0)
     (\m:num. 0)`;;

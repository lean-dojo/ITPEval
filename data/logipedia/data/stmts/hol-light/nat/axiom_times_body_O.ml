(*
  Statement-only formalization of Logipedia corpus artifact
  nat.axiom_times_body_O, catalog title "nat.axiom_times_body_O": the source
  equality relation identifies times_body at natural zero with the
  constant-zero function on natural numbers. This file contains no proof.
*)

new_constant
  ("logipedia_connectives_equal", `:'a -> 'a -> bool`);;

new_constant
  ("logipedia_nat_times_body", `:num -> num -> num`);;

let statement =
  `logipedia_connectives_equal
     (logipedia_nat_times_body 0)
     (\m:num. 0)`;;

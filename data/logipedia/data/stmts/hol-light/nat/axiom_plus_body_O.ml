(*
  Statement-only formalization of Logipedia corpus artifact
  nat.axiom_plus_body_O, catalog title "nat.axiom_plus_body_O": plus_body at
  natural zero is equal as a function to the identity function on natural
  numbers. This file contains no proof.
*)

new_constant
  ("logipedia_nat_plus_body", `:num -> num -> num`);;

let statement =
  `(logipedia_nat_plus_body 0) = (\m:num. m)`;;

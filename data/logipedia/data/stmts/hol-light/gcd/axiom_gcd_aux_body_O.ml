(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.axiom_gcd_aux_body_O, catalog title "gcd.axiom_gcd_aux_body_O": the
  source polymorphic equality relation identifies the greatest-common-divisor
  auxiliary body at natural index zero with the binary natural-number function
  returning its first argument. This file contains no proof.
*)

new_constant
  ("logipedia_connectives_equal", `:'a -> 'a -> bool`);;

new_constant
  ("logipedia_gcd_gcd_aux_body", `:num -> num -> num -> num`);;

let statement =
  `logipedia_connectives_equal
     (logipedia_gcd_gcd_aux_body 0)
     (\m:num. \n:num. m)`;;

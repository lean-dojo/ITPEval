(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.sym_eq_gcd_aux_body_O, catalog title "gcd.sym_eq_gcd_aux_body_O":
  Leibniz equality transports every predicate holding of the binary
  natural-number function returning its first argument to the
  greatest-common-divisor auxiliary body at natural index zero. This file
  contains no proof.
*)

new_constant
  ("logipedia_gcd_gcd_aux_body", `:num -> num -> num -> num`);;

let statement =
  `!P:((num -> num -> num) -> bool).
     P (\m:num. \n:num. m)
     ==>
     P (logipedia_gcd_gcd_aux_body 0)`;;

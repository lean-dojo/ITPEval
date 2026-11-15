(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.eq_gcd_aux_body_O, catalog title "gcd.eq_gcd_aux_body_O": Leibniz
  equality transports every predicate holding of the greatest-common-divisor
  auxiliary body at natural index zero to the binary natural-number function
  returning its first argument. This file contains no proof.
*)

new_constant
  ("logipedia_gcd_gcd_aux_body", `:num -> num -> num -> num`);;

let statement =
  `!P:((num -> num -> num) -> bool).
     P (logipedia_gcd_gcd_aux_body 0)
     ==>
     P (\m:num. \n:num. m)`;;

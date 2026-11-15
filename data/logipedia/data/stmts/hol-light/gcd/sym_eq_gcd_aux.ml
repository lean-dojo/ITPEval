(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.sym_eq_gcd_aux, catalog title "gcd.sym_eq_gcd_aux": for every natural
  index p, Leibniz equality transports every predicate holding of the
  filtered greatest-common-divisor auxiliary body at p to the designated
  auxiliary function at p. This file contains no proof.
*)

new_constant
  ("logipedia_nat_filter_nat_type", `:(num -> 'a) -> num -> 'a`);;

new_constant
  ("logipedia_gcd_gcd_aux", `:num -> num -> num -> num`);;

new_constant
  ("logipedia_gcd_gcd_aux_body", `:num -> num -> num -> num`);;

let statement =
  `!p:num.
   !P:((num -> num -> num) -> bool).
     P (logipedia_nat_filter_nat_type
          logipedia_gcd_gcd_aux_body p)
     ==>
     P (logipedia_gcd_gcd_aux p)`;;

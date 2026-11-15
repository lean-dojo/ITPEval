(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.axiom_gcd_aux, catalog title "gcd.axiom_gcd_aux": for every natural
  index p, the designated greatest-common-divisor auxiliary function at p is
  related by the source polymorphic equality relation to the filtered
  auxiliary body at p. This file contains no proof.
*)

new_constant
  ("logipedia_connectives_equal", `:'a -> 'a -> bool`);;

new_constant
  ("logipedia_nat_filter_nat_type", `:(num -> 'a) -> num -> 'a`);;

new_constant
  ("logipedia_gcd_gcd_aux", `:num -> num -> num -> num`);;

new_constant
  ("logipedia_gcd_gcd_aux_body", `:num -> num -> num -> num`);;

let statement =
  `!p:num.
     logipedia_connectives_equal
       (logipedia_gcd_gcd_aux p)
       (logipedia_nat_filter_nat_type
          logipedia_gcd_gcd_aux_body p)`;;

(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.axiom_gcd_aux_body_S, catalog title "gcd.axiom_gcd_aux_body_S": for
  every natural index p, the source polymorphic equality relation identifies
  the successor-indexed greatest-common-divisor auxiliary body with the
  binary function that returns n when n divides m and otherwise recurses at
  index p on n and the remainder of m modulo n. This file contains no proof.
*)

new_constant
  ("logipedia_connectives_equal", `:'a -> 'a -> bool`);;

new_constant
  ("logipedia_gcd_gcd_aux", `:num -> num -> num -> num`);;

new_constant
  ("logipedia_gcd_gcd_aux_body", `:num -> num -> num -> num`);;

let statement =
  `!p:num.
     logipedia_connectives_equal
       (logipedia_gcd_gcd_aux_body (SUC p))
       (\m:num. \n:num.
          if m MOD n = 0 then n
          else logipedia_gcd_gcd_aux p n (m MOD n))`;;

(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.sym_eq_gcd_aux_body_S, catalog title "gcd.sym_eq_gcd_aux_body_S": for
  every natural index p, Leibniz equality transports every predicate holding
  of the binary function that returns n when the remainder of m modulo n is
  zero and otherwise recurses at index p on n and that remainder to the
  successor-indexed greatest-common-divisor auxiliary body. This file contains
  no proof.
*)

new_constant
  ("logipedia_gcd_gcd_aux", `:num -> num -> num -> num`);;

new_constant
  ("logipedia_gcd_gcd_aux_body", `:num -> num -> num -> num`);;

let statement =
  `!p:num.
   !P:((num -> num -> num) -> bool).
     P (\m:num. \n:num.
          if m MOD n = 0 then n
          else logipedia_gcd_gcd_aux p n (m MOD n))
     ==>
     P (logipedia_gcd_gcd_aux_body (SUC p))`;;

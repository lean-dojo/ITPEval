(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.divides_to_gcd_aux, catalog title "gcd.divides_to_gcd_aux": for natural
  numbers p, m, and n, if p and n are positive and n divides m, then the
  greatest-common-divisor auxiliary value at p, m, and n equals n. This file
  contains no proof.
*)

let logipedia_gcd_gcd_aux = new_recursive_definition num_RECURSION
  `(logipedia_gcd_gcd_aux 0 m n = m) /\
   (logipedia_gcd_gcd_aux (SUC p) m n =
      if m MOD n = 0 then n
      else logipedia_gcd_gcd_aux p n (m MOD n))`;;

let statement =
  `!p m n:num.
     0 < p
     ==> 0 < n
     ==> n divides m
     ==> logipedia_gcd_gcd_aux p m n = n`;;

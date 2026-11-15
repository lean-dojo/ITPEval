(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.eq_minus_gcd, catalog title "gcd.eq_minus_gcd": for any two natural
  numbers, their module-defined greatest common divisor is one of the two
  natural differences of suitable multiples. This file contains no proof.
*)

let logipedia_gcd_gcd_aux = new_recursive_definition num_RECURSION
  `(logipedia_gcd_gcd_aux 0 m n = m) /\
   (logipedia_gcd_gcd_aux (SUC p) m n =
      if m MOD n = 0 then n
      else logipedia_gcd_gcd_aux p n (m MOD n))`;;

let logipedia_gcd_gcd = new_definition
  `logipedia_gcd_gcd (n:num) m =
     if n <= m
     then logipedia_gcd_gcd_aux n m n
     else logipedia_gcd_gcd_aux m n m`;;

let statement =
  `!m n:num.
     ?a b:num.
       a * n - b * m = logipedia_gcd_gcd n m \/
       b * m - a * n = logipedia_gcd_gcd n m`;;

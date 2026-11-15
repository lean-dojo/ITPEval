(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.eq_minus_gcd_aux, catalog title "gcd.eq_minus_gcd_aux": for natural
  numbers p, m, and positive n with n at most m and p, the recursively defined
  greatest-common-divisor auxiliary value is one of the two natural
  differences of suitable multiples of n and m. This file contains no proof.
*)

let logipedia_gcd_gcd_aux = new_recursive_definition num_RECURSION
  `(logipedia_gcd_gcd_aux 0 m n = m) /\
   (logipedia_gcd_gcd_aux (SUC p) m n =
      if m MOD n = 0 then n
      else logipedia_gcd_gcd_aux p n (m MOD n))`;;

let statement =
  `!p m n:num.
     0 < n
     ==> n <= m
     ==> n <= p
     ==> ?a b:num.
           a * n - b * m = logipedia_gcd_gcd_aux p m n \/
           b * m - a * n = logipedia_gcd_gcd_aux p m n`;;

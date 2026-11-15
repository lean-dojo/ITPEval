(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.divides_gcd_aux_mn, catalog title "gcd.divides_gcd_aux_mn": for natural
  numbers p, m, and positive n with n at most m and p, the recursively defined
  greatest-common-divisor auxiliary value divides both m and n. This file
  contains no proof.
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
     ==> (logipedia_gcd_gcd_aux p m n divides m) /\
         (logipedia_gcd_gcd_aux p m n divides n)`;;

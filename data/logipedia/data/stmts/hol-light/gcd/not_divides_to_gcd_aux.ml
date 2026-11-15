(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.not_divides_to_gcd_aux, catalog title "gcd.not_divides_to_gcd_aux":
  for natural numbers p, m, and positive n, if n does not divide m, then the
  successor-indexed greatest-common-divisor auxiliary value equals the
  recursive value at p on n and the remainder of m modulo n. This file
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
     ==> ~(n divides m)
     ==> logipedia_gcd_gcd_aux (SUC p) m n =
         logipedia_gcd_gcd_aux p n (m MOD n)`;;

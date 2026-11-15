(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.divides_gcd_nm, catalog title "gcd.divides_gcd_nm": for all natural
  numbers n and m, their module-defined greatest common divisor divides both
  m and n. This file contains no proof.
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
  `!n m:num.
     (logipedia_gcd_gcd n m divides m) /\
     (logipedia_gcd_gcd n m divides n)`;;

(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.let_clause_1545, catalog title "gcd.let_clause_1545": a nested
  natural-number clause stating that if the module-defined greatest common
  divisor is zero, zero divides both inputs, and the inputs equal zero times
  their quantified quotients, then the first input is zero. This file
  contains no proof.
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
     logipedia_gcd_gcd m n = 0
     ==> 0 divides n
     ==> !q1:num.
           n = 0 * q1
           ==> 0 divides m
           ==> !q2:num.
                 m = 0 * q2
                 ==> m = 0`;;

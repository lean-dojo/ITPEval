(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.commutative_gcd, catalog title "gcd.commutative_gcd": the module-defined
  greatest-common-divisor operation on natural numbers is commutative. This
  file contains no proof.
*)

new_constant
  ("logipedia_gcd_gcd_aux", `:num -> num -> num -> num`);;

let logipedia_gcd_gcd = new_definition
  `logipedia_gcd_gcd (n:num) m =
     if n <= m
     then logipedia_gcd_gcd_aux n m n
     else logipedia_gcd_gcd_aux m n m`;;

let statement =
  `!n m:num.
     logipedia_gcd_gcd n m = logipedia_gcd_gcd m n`;;

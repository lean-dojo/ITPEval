(*
  Statement-only formalization of Logipedia corpus artifact gcd.lt_O_gcd,
  catalog title "gcd.lt_O_gcd": for natural numbers m and n, positivity of n
  implies positivity of their greatest common divisor. This file contains no
  proof.
*)

let statement =
  `!m n:num.
     0 < n
     ==> 0 < gcd(m,n)`;;

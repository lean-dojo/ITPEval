(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_711. This file
  contains no proof.
*)

let statement =
  `!m n:num.
     0 < m /\
     0 < n /\
     gcd (m,n) = 8 /\
     lcm (m,n) = 112
     ==> 72 <= m + n`;;

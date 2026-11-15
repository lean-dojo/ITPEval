(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_435. This file
  contains no proof.
*)

let statement =
  `!k:num.
     0 < k /\
     (!n:num. gcd (6 * n + k, 6 * n + 3) = 1) /\
     (!n:num. gcd (6 * n + k, 6 * n + 2) = 1) /\
     (!n:num. gcd (6 * n + k, 6 * n + 1) = 1)
     ==> 5 <= k`;;

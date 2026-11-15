(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_314. This file
  contains no proof.
*)

let statement =
  `!r n:num.
    r = 1342 MOD 13 /\
    0 < n /\
    1342 divides n /\
    n MOD 13 < r
    ==> 6710 <= n`;;
